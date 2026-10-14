"""Weak solvability in a box of prices at d = 2 (`box-perturbation.tex`, Lean `box_iff`).
(Copied from OLD/box-perturbation/box.py; only the sys.path line differs.)

Data: lower and upper corners Q_min <= Q_max (T points of R^2_{>0}, zero widths allowed),
outputs y >= 0.  BOX(Q_min, Q_max, y): there is Q with Q_min <= Q <= Q_max coordinatewise such
that y is weakly solvable at Q.  In the code L = Q_min, U = Q_max.

Criterion: BOX <=> one flow LP on the 2T corners W = (L_1..L_T, U_1..U_T): a flow f on the chain
graph of W (poly-hardness/planar.py) and a vector g with w = sum_e f_e 1_{Out e} + g,
0 <= g <= sum_e f_e 1_{Bnd e}, and w(L_t) >= y_t >= w(U_t).  From a solution one reads off a
rational Q in [L, U] on the segments L_t -> U_t (`witness`).

No simplex is used.  The LP is solved by an interior-point method (HiGHS IPM); every answer is
certified exactly in rational arithmetic (`witness`: YES, `refute`: NO via the column oracle of
poly-hardness).  `decide` alone is a float decision.
"""

from __future__ import annotations

import itertools
import math
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "poly-hardness"))  # repo root / poly-hardness
import planar  # noqa: E402


def fr(x):
    return x if isinstance(x, F) else F(x)


def corners(L, U):
    """The 2T corners W = (L_1, ..., L_T, U_1, ..., U_T) as exact points."""
    return [(fr(a), fr(b)) for a, b in L] + [(fr(a), fr(b)) for a, b in U]


# ---------------------------------------------------------------- the LP of Theorem 1
#
# No simplex anywhere.  The LP is solved by an interior-point method (HiGHS IPM; polynomial in
# theory by the ellipsoid / interior-point algorithms).  Every answer is then certified in exact
# rational arithmetic:
#   YES: masses on weakly reachable sets of W by exact Gaussian elimination, then the witness Q
#        and an exact certificate y = sum m_S 1_S at Q (sets checked by `planar.is_reachable`);
#   NO : a rationalised Farkas vector lam with lam . y < 0 and lam(S) >= 0 on every weakly
#        reachable S of W, the latter by ONE call of the column oracle `planar.max_weight`.


class CertificateError(Exception):
    """The IPM answer could not be certified exactly (numerical support problem)."""


class SolverError(CertificateError):
    """The LP solver did not return an optimal solution (status != 0)."""


# Decision threshold on the phase-1 residual (y rescaled to max 1).  It is clearly above the
# solver tolerances (1e-9, see `_ipm`), so a truly feasible LP is not rejected by noise.  The price:
# an infeasible LP with residual below DECISION_TOL is accepted, i.e. `decide` is a FLOAT
# decision.  Only `witness` (YES) and `refute` (NO) are exact.
DECISION_TOL = 1e-6
SOLVER_OPTIONS = {"primal_feasibility_tolerance": 1e-9, "dual_feasibility_tolerance": 1e-9,
                  "ipm_optimality_tolerance": 1e-10}


def build_lp(W, y, T):
    """Phase-1 system of Theorem 1 in the variables (f, g, sigma, slack, r+, r-), all >= 0.
    Rows: flow conservation at the internal nodes; for every corner q
    sum_{e: q in Out e} f_e + g_q -/+ sigma_q + r+_q - r-_q = y_{q mod T} (minus for L: w >= y,
    plus for U: w <= y); g_q + slack_q - sum_{e: q in Bnd e} f_e = 0.  The residuals r are
    minimised: the box is feasible iff the optimum is 0."""
    G = planar.chain_graph(W)
    n2, A = len(W), len(G.arcs)
    idx = {nd: k for k, nd in enumerate(G.nodes)}
    n_int = len(G.nodes)
    gi, si, sl, rp = A, A + n2, A + 2 * n2, A + 3 * n2
    nv = rp + 2 * n2
    r, c, v = [], [], []

    def put(i, j, x):
        r.append(i)
        c.append(j)
        v.append(x)

    for k, (u, w, out, bnd) in enumerate(G.arcs):
        if u in idx:
            put(idx[u], k, -1.0)
        if w in idx:
            put(idx[w], k, 1.0)
        for q in out:
            put(n_int + q, k, 1.0)
        for q in bnd:
            put(n_int + n2 + q, k, -1.0)
    for q in range(n2):
        put(n_int + q, gi + q, 1.0)
        put(n_int + q, si + q, -1.0 if q < T else 1.0)
        put(n_int + q, rp + q, 1.0)
        put(n_int + q, rp + n2 + q, -1.0)
        put(n_int + n2 + q, gi + q, 1.0)
        put(n_int + n2 + q, sl + q, 1.0)
    M = coo_matrix((v, (r, c)), shape=(n_int + 2 * n2, nv)).tocsr()
    cost = np.zeros(nv)
    cost[rp:] = 1.0
    return G, M, cost, n_int, (A, gi, rp)


def _ipm(W, y, T):
    """Interior-point solution (HiGHS IPM) of the phase-1 LP, y rescaled to max 1."""
    ys = [float(v) for v in y]
    scale = max(max(ys, default=0.0), 1e-300)
    ys = [v / scale for v in ys]
    G, M, cost, n_int, (A, gi, rp) = build_lp(W, ys, T)
    n2 = len(W)
    b = np.zeros(M.shape[0])
    for q in range(n2):
        b[n_int + q] = ys[q % T]
    bounds = [(0, None)] * M.shape[1]
    res = None
    for opts in (SOLVER_OPTIONS, {}):        # tight tolerances first, solver defaults as fallback
        try:
            res = linprog(cost, A_eq=M, b_eq=b, bounds=bounds, method="highs-ipm", options=opts)
        except ValueError as ex:
            raise SolverError(f"LP solver failed: {ex}") from ex
        if res.status == 0:
            break
    if res is None or res.status != 0:
        raise SolverError(f"LP solver status {res.status if res is not None else None}: "
                          f"{getattr(res, 'message', '')}")
    return {"G": G, "f": res.x[:A], "g": res.x[gi:gi + n2], "obj": res.fun,
            "lam": -np.asarray(res.eqlin.marginals[n_int:n_int + n2]), "scale": scale,
            "ok": res.fun <= DECISION_TOL * max(1.0, sum(ys))}


def decide(L, U, y):
    """Theorem 1: BOX(L, U, y) as feasibility of the flow LP on the corners, by an interior-point
    method.  A FLOAT decision (threshold DECISION_TOL on the residual); `witness` / `refute`
    certify it exactly.  T <= 1 is trivially solvable (one set carries all of y).  Raises
    SolverError if the solver fails."""
    if len(L) <= 1:
        return True
    return _ipm(corners(L, U), y, len(L))["ok"]


# ---------------------------------------------------------------- exact linear algebra


def _gauss(A, b):
    """Gauss-Jordan on [A | b] (Fractions), columns in the given order.  Returns the pivot
    columns, the solution on them (other columns 0) and whether the system is consistent."""
    rows = [list(r) + [bi] for r, bi in zip(A, b)]
    ncol = len(A[0]) if A else 0
    piv, r0 = [], 0
    for j in range(ncol):
        p = next((i for i in range(r0, len(rows)) if rows[i][j] != 0), None)
        if p is None:
            continue
        rows[r0], rows[p] = rows[p], rows[r0]
        rows[r0] = [x / rows[r0][j] for x in rows[r0]]
        for i in range(len(rows)):
            if i != r0 and rows[i][j] != 0:
                fct = rows[i][j]
                rows[i] = [x - fct * z for x, z in zip(rows[i], rows[r0])]
        piv.append(j)
        r0 += 1
    consistent = all(rows[i][-1] == 0 for i in range(r0, len(rows)))
    x = [F(0)] * ncol
    for i, j in enumerate(piv):
        x[j] = rows[i][-1]
    return piv, x, consistent


def _exact_masses(W, T, sets, m_float, y, tol=1e-6):
    """Exact masses m >= 0 on the sets with w(a_t) >= y_t >= w(b_t).  Constraints tight in the
    float solution become equalities; Gaussian elimination solves for the masses on an
    independent subfamily of columns (Caratheodory), the other masses stay at rationalised float
    values.  Everything is verified exactly; raises CertificateError otherwise."""
    K = len(sets)
    y = [fr(v) for v in y]
    ymaxF = max(y, default=F(0)) or F(1)
    ymax = float(ymaxF)
    order = sorted(range(K), key=lambda k: -m_float[k])
    last = "no attempt"
    # retry loop: fewer tight rows (smaller tol) and finer rationalisation before giving up
    for tl in (tol, tol * 1e-2, tol * 1e-4):
        tight = []
        for t in range(T):
            for q in (t, T + t):
                if q < T and y[t] == 0:
                    continue          # w(a_t) >= 0 holds automatically, no equality needed
                lhs = sum(m for S, m in zip(sets, m_float) if q in S)
                if abs(lhs - float(y[t])) <= tl * ymax:
                    tight.append(q)
        A = [[F(1) if q in sets[k] else F(0) for k in order] for q in tight]
        piv = _gauss(A, [F(0)] * len(A))[0] if A else []
        free = [j for j in range(K) if j not in piv]
        for den in (10**6, 10**9, 10**12):
            # relative rationalisation: masses in units of ymax, so tiny y keep their masses
            m0 = [ymaxF * F(float(m_float[order[j]]) / ymax).limit_denominator(den)
                  for j in range(K)]
            if tight and piv:
                rhs = [y[q % T] - sum(A[i][j] * m0[j] for j in free) for i, q in enumerate(tight)]
                Ap = [[row[j] for j in piv] for row in A]
                _, xp, ok = _gauss(Ap, rhs)
                if not ok:
                    last = "tight system inconsistent"
                    continue
                for i, j in enumerate(piv):
                    m0[j] = xp[i]
            m = [F(0)] * K
            for j in range(K):
                m[order[j]] = m0[j]
            ok = all(v >= 0 for v in m)
            for t in range(T):
                wa = sum((mk for S, mk in zip(sets, m) if t in S), F(0))
                wb = sum((mk for S, mk in zip(sets, m) if T + t in S), F(0))
                ok = ok and wa >= y[t] >= wb
            if ok:
                return [(S, mk) for S, mk in zip(sets, m) if mk != 0]
            last = "exact masses violate the corner inequalities"
    raise CertificateError(last)


def sets_and_masses(W, G, f, g, eps=0):
    """Weakly reachable sets of W with masses, from a flow f and a vector g: decompose the flow
    into paths, split the g-part by the level sets of phi_q = g_q / load_q on Bnd(path)
    (`cube_mem_span`, nested form).  eps is a tolerance for floating-point input."""
    n2 = len(W)
    loads = [0] * n2
    for k, (_, _, _, bnd) in enumerate(G.arcs):
        for q in bnd:
            loads[q] += f[k]
    phi = [min(1, max(0, g[q] / loads[q])) if loads[q] > eps else 0 for q in range(n2)]
    fl = list(f)
    out_arcs = {}
    for k, (u, *_r) in enumerate(G.arcs):
        out_arcs.setdefault(u, []).append(k)
    out = []
    while any(fl[k] > eps for k in out_arcs.get(planar.SRC, [])):
        path, node = [], planar.SRC
        while node != planar.SNK:
            cand = [j for j in out_arcs.get(node, []) if fl[j] > eps]
            if not cand:      # float noise: inflow above eps, all outflow below
                raise CertificateError("flow decomposition stuck (float noise)")
            k = max(cand, key=lambda j: fl[j])
            path.append(k)
            node = G.arcs[k][1]
        m = min(fl[k] for k in path)
        for k in path:
            fl[k] -= m
        S0 = frozenset().union(*(G.arcs[k][2] for k in path))
        B = frozenset().union(*(G.arcs[k][3] for k in path))
        levels = sorted({phi[q] for q in B if phi[q] > eps}, reverse=True)
        if levels:
            cs = levels + [0]
            out.append((S0, m * (1 - levels[0])))
            for j, c in enumerate(levels):
                out.append((S0 | frozenset(q for q in B if phi[q] >= c), m * (c - cs[j + 1])))
        else:
            out.append((S0, m))
    merged = {}
    for S, m in out:
        merged[S] = merged.get(S, 0) + m
    return [(S, m) for S, m in merged.items() if m > eps]


# ---------------------------------------------------------------- witness (Theorem 3)


def facets_of_K(pts):
    """K = conv(pts) + R^2_{>=0} as {z : xi.z >= c}: list of (xi, c), exact."""
    pts = list(set(pts))
    fac = [((F(1), F(0)), min(p[0] for p in pts)), ((F(0), F(1)), min(p[1] for p in pts))]
    for a, b in itertools.combinations(pts, 2):
        dx, dy = b[0] - a[0], b[1] - a[1]
        for xi in ((dy, -dx), (-dy, dx)):
            if xi[0] >= 0 and xi[1] >= 0 and (xi[0] > 0 or xi[1] > 0):
                c = xi[0] * a[0] + xi[1] * a[1]
                if all(xi[0] * p[0] + xi[1] * p[1] >= c for p in pts):
                    fac.append((xi, c))
    return fac


def _facets(W, T, cert):
    out = []
    for S, m in cert:
        rest = [W[q] for q in range(2 * T) if q not in S]
        out.append((m, facets_of_K(rest) if rest else None))
    return out


def _place(W, T, facs, y):
    """Q_t = L_t + s_t (U_t - L_t), s_t = max{c : sum_{k : lambda_k >= c} m_k >= y_t} where
    lambda_k = min(1, max_j (c_j - xi_j.L_t) / xi_j.(U_t - L_t)) is the exit parameter of the
    segment from int K_k, K_k = conv(W minus S_k) + R^2_{>=0}."""
    Q = []
    for t in range(T):
        a, b = W[t], W[T + t]
        d = (b[0] - a[0], b[1] - a[1])
        caps = []
        for m, fac in facs:
            if fac is None:
                caps.append((F(1), m))
                continue
            best = None
            for xi, c in fac:
                den = xi[0] * d[0] + xi[1] * d[1]
                num = c - xi[0] * a[0] - xi[1] * a[1]
                sj = num / den if den > 0 else (F(10**9) if num >= 0 else F(-10**9))
                best = sj if best is None else max(best, sj)
            caps.append((min(F(1), best), m))
        s = F(1)
        if fr(y[t]) != 0:
            cands = sorted({c for c, _ in caps if c >= 0}, reverse=True)
            s = next((c for c in cands if sum(m for cc, m in caps if cc >= c) >= fr(y[t])), None)
            if s is None:
                raise CertificateError("hi(0) < y_t")
        Q.append((a[0] + s * d[0], a[1] + s * d[1]))
    return Q


def _certificate_at(Q, facs, y):
    """Exact certificate at Q (proof of Theorem 1, <=): R_min,k = {t : Q_t not in K_k},
    R_max,k = {t : Q_t not in int K_k}; y_t = sum_k m_k (1_Rmin + theta_t 1_{Rmax - Rmin})(t) with
    one theta_t in [0, 1] per t; nested level sets of theta give weakly reachable sets."""
    T = len(Q)
    rmin, rmax = [], []
    for m, fac in facs:
        if fac is None:
            rmin.append(frozenset(range(T)))
            rmax.append(frozenset(range(T)))
            continue
        rmin.append(frozenset(t for t in range(T)
                              if any(xi[0] * Q[t][0] + xi[1] * Q[t][1] < c for xi, c in fac)))
        rmax.append(frozenset(t for t in range(T)
                              if any(xi[0] * Q[t][0] + xi[1] * Q[t][1] <= c for xi, c in fac)))
    theta = []
    for t in range(T):
        lo = sum((m for (m, _), s in zip(facs, rmin) if t in s), F(0))
        hi = sum((m for (m, _), s in zip(facs, rmax) if t in s), F(0))
        if not lo <= fr(y[t]) <= hi:
            raise CertificateError("y_t outside [lo, hi] at Q")
        theta.append((fr(y[t]) - lo) / (hi - lo) if hi > lo else F(0))
    cert = {}
    for (m, _), lo, hi in zip(facs, rmin, rmax):
        levels = sorted({theta[t] for t in hi - lo if theta[t] > 0}, reverse=True)
        cs = levels + [F(0)]
        parts = [(lo, m * (1 - levels[0]))] if levels else [(lo, m)]
        for j, c in enumerate(levels):
            parts.append((lo | frozenset(t for t in hi - lo if theta[t] >= c), m * (c - cs[j + 1])))
        for S, mm in parts:
            if mm > 0:
                cert[S] = cert.get(S, F(0)) + mm
    return list(cert.items())


def witness(L, U, y):
    """Theorem 3: (Q, cert) with Q rational in [L, U] and cert a list of (S, m) with m >= 0
    rational, every S weakly reachable at Q, sum m 1_S = y, all checked exactly
    (`certify`); None if the IPM says BOX fails.  Raises CertificateError if the exact steps
    fail.  No simplex: IPM, then Gaussian elimination in Fractions."""
    T = len(L)
    if T <= 1:       # trivially solvable: Q = L, one set carrying all of y
        Q = [tuple(fr(c) for c in p) for p in L]
        return Q, ([(frozenset({0}), fr(y[0]))] if T == 1 and fr(y[0]) > 0 else [])
    W = corners(L, U)
    sol = _ipm(W, y, T)
    if not sol["ok"]:
        return None
    eps = 1e-9
    cand = [(S, m) for S, m in sets_and_masses(W, sol["G"], sol["f"], sol["g"], eps)
            if planar.is_reachable(W, sorted(S), strict=False)]
    cert_W = _exact_masses(W, T, [S for S, _ in cand], [m * sol["scale"] for _, m in cand], y)
    facs = _facets(W, T, cert_W)
    Q = _place(W, T, facs, y)
    cert = _certificate_at(Q, facs, y)
    if not (in_box(Q, L, U) and certify(Q, y, cert)):
        raise CertificateError("witness check failed")
    return Q, cert


def certify(Q, y, cert):
    """Exact check: m >= 0, every S weakly reachable at Q by the definition
    (`planar.is_reachable`), sum m 1_S = y."""
    return planar.check_certificate(Q, [fr(v) for v in y], cert)


def refute(L, U, y):
    """Exact NO certificate: a rational vector lam on the 2T corners with lam_{a_t} <= 0 <=
    lam_{b_t}, sum_t (lam_{a_t} + lam_{b_t}) y_t < 0 and lam(S) >= 0 for every weakly reachable
    S of W (one call of the column oracle `planar.max_weight`).  Then no w in the cone satisfies
    w(a_t) >= y_t >= w(b_t).  Returns lam, or None if the IPM says BOX holds or the rounded
    Farkas vector fails the exact check.  The float Farkas vector is rationalised with several
    denominators, both absolutely and relative to its max-norm (lam may be scaled by any positive
    number), before giving up; every candidate is checked exactly."""
    T = len(L)
    if T <= 1:
        return None
    W = corners(L, U)
    sol = _ipm(W, y, T)
    if sol["ok"]:
        return None
    lam_f = [float(v) for v in sol["lam"]]
    nrm = max((abs(v) for v in lam_f), default=0.0)
    for relative in (False, True):
        base = [v / nrm for v in lam_f] if (relative and nrm > 0) else lam_f
        for digits in (4, 6, 8, 10, 12):
            lam = [F(v).limit_denominator(10**digits) for v in base]
            lam = [min(F(0), v) if q < T else max(F(0), v) for q, v in enumerate(lam)]
            if sum((lam[t] + lam[T + t]) * fr(y[t]) for t in range(T)) >= 0:
                continue
            best, _ = planar.max_weight(W, [-v for v in lam])
            if best <= 0:
                return lam
    return None


def in_box(Q, L, U):
    return all(fr(L[t][i]) <= Q[t][i] <= fr(U[t][i]) for t in range(len(L)) for i in range(len(L[0])))
