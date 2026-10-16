"""Master problem (HiGHS via scipy.optimize.milp): a relaxation of the least l_p perturbation.

Variables: half-widths alpha, beta in [0, zmax] (T x d) of the box [P g(-alpha), P g(beta)]
(problem.py); year signs (alpha_t = 0 or beta_t = 0).  Constraints, each satisfied by the half-widths
of a one-signed optimal Q (Lean `exists_oneSigned_le`); the master bound is therefore a lower bound over
ONE-SIGNED feasible points, which is enough since some optimum is one-signed (Lean `Problem.reduce`):
  dominance: y_t > y_s  =>  q_s^i >= q_t^i for some i, q = P g(beta - alpha) (`le_of_lt`);
  box cuts:  z_j >= zhat_j for some j in J, zhat a certified NO of the box query on some years
             (`BoxFeasible.mono`, `BoxFeasible.restrict`);
  cover cuts: some cover (t, A) of a NO certificate is absent: for its convex combination mu and some
             i, sum_s mu_s W_s^i >= W_t^i (W the corners).  Exact rows for "rel"; for "log" e^z is
             bounded above by its piecewise-linear interpolation and below by tangents.
Objective ||c o (alpha + beta)||_p, which equals the box cost ||c o max(alpha, beta)||_p on one-signed
points: p = 1 linear; p = inf via s >= c x; 1 < p < inf via tangents of (c x / UB)^p (under-estimators,
LB = UB (sum v)^(1/p) stays valid).
"""

from __future__ import annotations

import math

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


class Master:
    def __init__(self, prob, segments=16):
        self.prob, self.pairs, self.cuts, self.covers = prob, [], [], []
        self.segments = segments
        self.pts = ([[list(np.geomspace(1e-3, 1.0, 25)) for _ in range(prob.d)] for _ in range(prob.T)]
                    if 1 < prob.p < math.inf else None)

    def solve(self, UB, gap=1e-9, time_limit=None):
        pr, self.UB = self.prob, float(UB)
        T, d, p, n = pr.T, pr.d, pr.p, 2 * pr.T * pr.d
        zmax = pr.zmax(self.UB)
        lb, ub, integ, rows, cols, vals, rlo, rhi = [0.0] * n, list(zmax), [0] * n, [], [], [], [], []

        def var(lo, hi, i=0):
            lb.append(lo); ub.append(hi); integ.append(i)
            return len(lb) - 1

        def row(co, lo, hi):
            for j, v in co.items():
                rows.append(len(rlo)); cols.append(j); vals.append(v)
            rlo.append(lo); rhi.append(hi)

        A = lambda t, i: t * d + i              # noqa: E731
        B = lambda t, i: T * d + t * d + i      # noqa: E731
        for t in range(T):
            s = var(0, 1, 1)
            for i in range(d):
                row({A(t, i): 1.0, s: -zmax[A(t, i)]}, -np.inf, 0.0)
                row({B(t, i): 1.0, s: zmax[B(t, i)]}, -np.inf, zmax[B(t, i)])
        for t, s in self.pairs:
            gs = [var(0, 1, 1) for _ in range(d)]
            row({g: 1.0 for g in gs}, 1, np.inf)
            for i, g in enumerate(gs):                  # q_s^i >= q_t^i
                if pr.metric == "log":
                    co, rhs = {A(s, i): -1.0, B(s, i): 1.0, A(t, i): 1.0, B(t, i): -1.0}, pr.pi[t, i] - pr.pi[s, i]
                else:
                    r = float(pr.P[s][i] / pr.P[t][i])
                    co, rhs = {A(s, i): -r, B(s, i): r, A(t, i): 1.0, B(t, i): -1.0}, 1.0 - r
                lo_ = min(0.0, sum(v * (0.0 if v > 0 else zmax[j]) for j, v in co.items()) - rhs)
                row({**co, g: lo_}, rhs + lo_, np.inf)       # the exact big-M
        for zh in self.cuts:
            js = [j for j, v in zh.items() if v <= zmax[j]]
            gs = [var(0, 1, 1) for _ in js]
            row({g: 1.0 for g in gs}, 1, np.inf)
            for j, g in zip(js, gs):
                row({j: 1.0, g: -zh[j]}, 0.0, np.inf)
        pwl = {}

        def over(j, sg):
            """e^{sg z_j} <= 1 + sum_k slope_k delta_k: its piecewise-linear interpolation on
            [0, zmax_j] (incremental formulation, binaries order the segments)."""
            if pr.metric == "rel":
                return {j: float(sg)}                   # 1 + sg z: exact
            if j not in pwl:
                b = np.linspace(0.0, zmax[j], self.segments + 1)
                h = np.diff(b)
                ds = [var(0.0, hk) for hk in h]
                ys = [var(0, 1, 1) for _ in h[1:]]
                row({j: 1.0, **{x: -1.0 for x in ds}}, 0.0, 0.0)
                for k, yk in enumerate(ys):
                    row({ds[k]: 1.0, yk: -h[k]}, 0.0, np.inf)
                    row({ds[k + 1]: 1.0, yk: -h[k + 1]}, -np.inf, 0.0)
                pwl[j] = {x: (math.exp(sg * b[k + 1]) - math.exp(sg * b[k])) / h[k] if h[k] > 0 else float(sg)
                          for k, x in enumerate(ds)}
            return pwl[j]

        for conflict in self.covers:            # some cover of the conflict must disappear
            ds = [var(0, 1, 1) for _ in conflict]
            row({g: 1.0 for g in ds}, 1, np.inf)
            for (t, cov, mu), dl in zip(conflict, ds):
                gs = [var(0, 1, 1) for _ in range(d)]
                row({**{g: 1.0 for g in gs}, dl: -1.0}, 0, np.inf)
                for i, g in enumerate(gs):
                    for co, rhs in self._absent_rows(t, cov, mu, i, zmax, over):
                        lo_ = min(0.0, sum(v * (lb[j] if v > 0 else ub[j]) for j, v in co.items()) - rhs)
                        row({**co, g: lo_}, rhs + lo_, np.inf)
        obj = []
        if math.isinf(p):
            obj.append(var(0.0, np.inf))
            for t in range(T):
                for i in range(d):
                    row({obj[0]: 1.0, A(t, i): -pr.c[t, i], B(t, i): -pr.c[t, i]}, 0.0, np.inf)
        elif p != 1:
            for t in range(T):
                for i in range(d):
                    obj.append(var(0.0, np.inf))
                    kk = pr.c[t, i] / self.UB
                    for y0 in self.pts[t][i]:
                        g = p * y0 ** (p - 1)
                        row({obj[-1]: 1.0, A(t, i): -g * kk, B(t, i): -g * kk}, y0 ** p - g * y0, np.inf)
        c = np.zeros(len(lb))
        if obj:
            c[obj] = 1.0
        else:
            c[:n] = np.concatenate([pr.c.ravel()] * 2)
        opts = {"mip_rel_gap": gap, **({"time_limit": time_limit} if time_limit else {})}
        res = milp(c, integrality=np.array(integ), bounds=Bounds(lb, ub), options=opts,
                   constraints=[LinearConstraint(coo_matrix((vals, (rows, cols)),
                                                            shape=(len(rlo), len(lb))).tocsr(), rlo, rhi)])
        if res.x is None:
            if "infeasible" in str(res.message).lower():
                return None                      # no z of cost <= UB passes the cuts: UB is optimal
            raise RuntimeError(f"master: {res.message}")
        x = res.x
        bound = getattr(res, "mip_dual_bound", None)
        bound = res.fun if bound is None or not np.isfinite(bound) else min(bound, res.fun)
        if 1 < p < math.inf:
            bound, self._v = self.UB * max(bound, 0.0) ** (1 / p), x[obj].reshape(T, d)
        return np.maximum(x[:T * d], 0).reshape(T, d), np.maximum(x[T * d:n], 0).reshape(T, d), float(bound)

    def _corner(self, k, i):
        """Corner k (0..T-1 lower, T..2T-1 upper), coordinate i: (variable index, sign, price)."""
        T, d = self.prob.T, self.prob.d
        t = k % T
        return (t * d + i, -1, float(self.prob.P[t][i])) if k < T else (T * d + t * d + i, 1, float(self.prob.P[t][i]))

    def _absent_rows(self, t, A, mu, i, zmax, over):
        """Linear relaxation of "sum_s mu_s W_s^i >= W_t^i", W = p e^{sign z}: rows (coef, rhs) of
        coef.x >= rhs.  |A| = 1: exact in logs.  Else e^{sign z_s} <= its piecewise-linear
        interpolation `over` (left) and e^{sign z_t} >= its tangents (right); scaled by the price of t."""
        jt, st, pt = self._corner(t, i)
        if len(A) == 1 and self.prob.metric == "log":
            js, ss, ps = self._corner(A[0], i)
            return [({js: float(ss), jt: float(-st)}, math.log(pt / ps))]
        co, const = {}, 0.0
        for s, m in zip(A, mu):
            js, ss, ps = self._corner(s, i)
            for x, v in over(js, ss).items():
                co[x] = co.get(x, 0.0) + m * ps / pt * v
            const += m * ps / pt
        if self.prob.metric == "rel":                   # W_t^i / p_t = 1 + st z_t exactly
            return [({**co, jt: co.get(jt, 0.0) - st}, 1.0 - const)]
        out = []
        for z0 in np.linspace(0.0, zmax[jt], 9):
            e = math.exp(st * z0)
            out.append(({**co, jt: co.get(jt, 0.0) - e * st}, e * (1 - st * z0) - const))
        return out

    def add_violated_pairs(self, al, be, tol=1e-9):
        pr = self.prob
        eta = pr.pi + (be - al if pr.metric == "log" else np.log(np.maximum(1 - al + be, 1e-300)))
        have = set(self.pairs)
        new = [(t, s) for t in range(pr.T) for s in range(pr.T)
               if pr.y[t] > pr.y[s] and (t, s) not in have and np.all(eta[s] < eta[t] - tol)]
        self.pairs += new
        return len(new)

    def add_tangents(self, al, be, rtol):
        """1 < p < inf: refine the tangents while they under-estimate the cost at the solution by
        more than rtol."""
        pr = self.prob
        if self.pts is None:
            return 0
        x = al + be
        yv = pr.c * x / self.UB
        fv = yv ** pr.p
        if pr.norm(x) - self.UB * max(float(np.minimum(self._v, fv).sum()), 0.0) ** (1 / pr.p) \
                <= rtol * max(pr.norm(x), 1e-300):
            return 0
        new = [(t, i) for t in range(pr.T) for i in range(pr.d) if x[t, i] > 0 and self._v[t, i] < fv[t, i] * (1 - rtol)]
        for t, i in new:
            self.pts[t][i].append(float(yv[t, i]))
        return len(new)
