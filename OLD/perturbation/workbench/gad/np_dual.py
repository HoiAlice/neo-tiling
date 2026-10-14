"""np_dual.py -- rigorous (interval-arithmetic) lower bounds for rho_dom blocks, by Lagrangian duality + branch and bound over routings.

Model (log coordinates).  Points t=0..T-1 with log-prices A[t][c] = grid[t][c]*H, H = 4*ln(RHO) (RHO rational, so
prices P = RHO**(4*grid) are RATIONAL when 4*grid is an integer).  Cost of moving point t in coordinate c to x:
f(x - A) with f(u) = exp(|u|) - 1   (= max(q/p,p/q) - 1 with q = exp(x), p = exp(A)).
Conflicts: ordered pairs (a,b) with y_a > y_b.  A *routing* assigns each conflict a coordinate c; then it requires
x[a][c] <= x[b][c].  rho_dom(block) = min over routings of the separable convex program.

Weak duality (any lam >= 0, no conservation needed):   cost >= D(lam) = sum_v [ g_v*A_v + phi(g_v) ],
   g_v = sum_{e: tail v} lam_e - sum_{e: head v} lam_e,  phi(g) = |g| - 1 - |g| ln|g|  if |g|>1 else 0.
D(lam) is evaluated in INTERVAL arithmetic (mpmath.iv, 60 digits) at rationalised lam, so the returned value is a rigorous
lower bound on the real minimum of the routing class (modulo mpmath's interval log/exp correctness).
Primal point from the dual: x_v = A_v - sign(g) ln|g| for |g|>1 else A_v.

branch_and_bound(): lazy B&B over unassigned conflicts.  Node = partial routing, relaxation = drop unassigned conflicts.
Returns (lo, hi): lo = rigorous lower bound of min over ALL routings consistent with the fixed ones (B&B tolerance tol),
hi = cost of the best feasible leaf found (float, evaluated with iv upper end).
"""
import math, itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import minimize
import mpmath
from mpmath import iv
iv.dps = 60
RHO = Fraction(21, 20)
H = 4 * math.log(float(RHO))
H_IV = 4 * iv.log(iv.mpf(RHO.numerator) / RHO.denominator)


def points_from_switches(sw):
    """sw: list of (bx,by,d,ytop,ybot) in grid units.  Point 2i = top, 2i+1 = bottom."""
    G = []
    Y = []
    for bx, by, d, yt, yb in sw:
        G += [(Fraction(bx) + Fraction(d), Fraction(by) + Fraction(d)), (Fraction(bx), Fraction(by))]
        Y += [yt, yb]
    return G, Y


def conflicts_of(Y, tol=1e-9):
    return [(a, b) for a in range(len(Y)) for b in range(len(Y)) if Y[a] > Y[b] + tol]


class Block:
    def __init__(self, sw, prune=False):
        self.sw = sw
        self.G, self.Y = points_from_switches(sw)
        self.T = len(self.G)
        self.A = np.array([[float(g[0]) * H, float(g[1]) * H] for g in self.G])
        self.A_iv = [[iv.mpf(g[0].numerator) / g[0].denominator * H_IV, iv.mpf(g[1].numerator) / g[1].denominator * H_IV] for g in self.G]
        self.conf = conflicts_of(self.Y)
        if prune:   # drop pairs where the lower point is >= 1.2 (log) NE in some coordinate: relaxation (valid for LB)
            self.conf = [(a, b) for (a, b) in self.conf if not max(self.A[b][0] - self.A[a][0], self.A[b][1] - self.A[a][1]) >= 1.2]
        self.cidx = {c: k for k, c in enumerate(self.conf)}
        self.own = [self.cidx[(2 * i, 2 * i + 1)] for i in range(len(sw))]


def _phi(g):
    ag = abs(g)
    return ag - 1 - ag * math.log(ag) if ag > 1 else 0.0


def dual_float(blk, assign, lam0=None):
    """maximise D over lam>=0 on the assigned conflicts. assign: dict conflict_index -> coordinate. returns (value, lam dict, x)"""
    items = sorted(assign.items())
    m = len(items)
    T = blk.T
    if m == 0:
        return 0.0, {}, blk.A.copy()
    tail = np.array([blk.conf[k][0] for k, c in items]); head = np.array([blk.conf[k][1] for k, c in items]); co = np.array([c for k, c in items])

    def parts(lam):
        g = np.zeros((T, 2))
        np.add.at(g, (tail, co), lam); np.add.at(g, (head, co), -lam)
        return g

    def negD(lam):
        g = parts(lam)
        ag = np.abs(g)
        with np.errstate(divide='ignore', invalid='ignore'):
            ph = np.where(ag > 1, ag - 1 - ag * np.log(np.maximum(ag, 1e-300)), 0.0)
        val = np.sum(g * blk.A) + np.sum(ph)
        x = blk.A - np.where(ag > 1, np.sign(g) * np.log(np.maximum(ag, 1.0)), 0.0)
        grad = x[tail, co] - x[head, co]
        return -val, -grad

    x0 = np.zeros(m) if lam0 is None else np.array([lam0.get(k, 0.0) for k, c in items])
    r = minimize(negD, x0, jac=True, method='L-BFGS-B', bounds=[(0, None)] * m, options=dict(maxiter=2000, ftol=1e-15, gtol=1e-11, maxcor=30))
    lam = r.x
    g = parts(lam); ag = np.abs(g)
    x = blk.A - np.where(ag > 1, np.sign(g) * np.log(np.maximum(ag, 1.0)), 0.0)
    return -r.fun, {k: v for (k, c), v in zip(items, lam)}, x


def dual_rigorous(blk, assign, lam):
    """interval lower bound of D(lam)"""
    T = blk.T
    g = [[Fraction(0), Fraction(0)] for _ in range(T)]
    for k, c in assign.items():
        l = Fraction(lam.get(k, 0.0))
        a, b = blk.conf[k]
        g[a][c] += l; g[b][c] -= l
    tot = iv.mpf(0)
    for t in range(T):
        for c in range(2):
            gg = g[t][c]
            gi = iv.mpf(gg.numerator) / gg.denominator
            tot += gi * blk.A_iv[t][c]
            if abs(gg) > 1:
                ag = abs(gi)
                tot += ag - 1 - ag * iv.log(ag)
    return float(tot.a)      # lower endpoint


def cost_iv_upper(blk, x):
    tot = iv.mpf(0)
    for t in range(blk.T):
        for c in range(2):
            tot += iv.exp(abs(iv.mpf(float(x[t][c])) - blk.A_iv[t][c])) - 1
    return float(tot.b)


def violated(blk, assign, x, tol=1e-9):
    best = None
    for k, (a, b) in enumerate(blk.conf):
        if k in assign:
            continue
        s = min(x[a][0] - x[b][0], x[a][1] - x[b][1])
        if s > tol and (best is None or s > best[0]):
            best = (s, k)
    return best


def branch_and_bound(blk, fixed, tol=1e-7, target=None, max_nodes=200000, verbose=False):
    """min over routings extending `fixed` (dict conflict_idx -> coord).  Prunes nodes whose rigorous LB >= incumbent - tol
    (or >= target if given: then the answer 'lo' is only meaningful as min(lo, target))."""
    best = [float('inf'), None]
    lo_pruned = [float('inf')]
    stats = dict(nodes=0, leaves=0)
    stack = [(dict(fixed), None)]
    while stack:
        assign, lam0 = stack.pop()
        stats['nodes'] += 1
        if stats['nodes'] > max_nodes:
            raise RuntimeError("node limit")
        val, lam, x = dual_float(blk, assign, lam0)
        # quick float prune
        thr = best[0] - tol if target is None else min(best[0] - tol, target)
        if val >= thr + 1e-6:
            lb = dual_rigorous(blk, assign, lam)
            if lb >= thr:
                lo_pruned[0] = min(lo_pruned[0], lb)
                continue
        v = violated(blk, assign, x)
        if v is None:
            stats['leaves'] += 1
            lb = dual_rigorous(blk, assign, lam)
            ub = cost_iv_upper(blk, x)       # x feasible up to 1e-9 (leaf), cost is an upper bound for the class up to that tolerance
            lo_pruned[0] = min(lo_pruned[0], lb)
            if ub < best[0]:
                best[0] = ub; best[1] = dict(assign)
            continue
        k = v[1]
        for c in (0, 1):
            a2 = dict(assign); a2[k] = c
            stack.append((a2, lam))
    return lo_pruned[0], best[0], best[1], stats


def B_closed(d_grid):
    """isolated switch of box size d (grid units): own pair cost 2(exp(delta/2)-1), delta = d*H"""
    return 2 * (math.exp(float(d_grid) * H / 2) - 1)
