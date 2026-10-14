"""proj.py: distance, exact LP helpers, breakpoints (d = 3 structure),
oracles, least radius, witness / NO certificates.  Brute-force parts are kept tiny."""

import itertools
import math
import random
from fractions import Fraction as F

import pytest

from perturb import box, proj


def rand_points(rnd, T, d, hi=9):
    return [tuple(F(rnd.randint(1, hi), rnd.randint(1, 3)) for _ in range(d)) for _ in range(T)]


def rand_instance(rnd, T, d):
    P = rand_points(rnd, T, d)
    y = [F(rnd.randint(0, 6)) for _ in range(T)]
    if max(y) == 0:
        y[0] = F(1)
    return P, y


# ---------------------------------------------------------------- (c) distance


@pytest.mark.parametrize("d", [2, 3, 4])
def test_dist_median_vs_minimisation_and_ball_geometry(d):
    rnd = random.Random(d)
    for _ in range(200):
        a = [rnd.uniform(0.1, 5) for _ in range(d)]
        b = [rnd.uniform(0.1, 5) for _ in range(d)]
        u = [math.log(x / y) for x, y in zip(a, b)]
        # brute minimisation over t: piecewise linear, minimum at t in {-u_i, 0}
        brute = min(sum(abs(ui + t) for ui in u) + abs(t) for t in [-x for x in u] + [0.0])
        assert abs(proj.dist(a, b) - brute) < 1e-12
        # fine grid cannot beat it
        for t in [i / 50 - 3 for i in range(300)]:
            assert sum(abs(ui + t) for ui in u) + abs(t) >= proj.dist(a, b) - 1e-12
        # ball in cube
        assert max(abs(x) for x in u) <= proj.dist(a, b) + 1e-12
        # diagonal
        s = rnd.uniform(-2, 2)
        assert abs(proj.dist([x * math.exp(s) for x in b], b) - abs(s)) < 1e-12
    # exact ball test agrees with float on rational data
    for _ in range(100):
        p = rand_points(rnd, 1, d)[0]
        q = rand_points(rnd, 1, d)[0]
        rho = proj.dist(q, p)
        assert proj.in_ball_exact([q], [p], F(math.exp(rho + 1e-6)).limit_denominator(10 ** 9))
        assert not proj.in_ball_exact([q], [p], F(math.exp(rho - 1e-6)).limit_denominator(10 ** 9))


# ---------------------------------------------------------------- exact LP helpers


def test_simplex_basic():
    r = proj.simplex([[F(1), F(1), F(1)]], [F(4)], [F(1), F(2), F(3)])
    assert r["status"] == "optimal" and r["obj"] == 4 and r["x"][0] == 4
    r = proj.simplex([[F(1), F(1)], [F(1), F(1)]], [F(1), F(2)])
    assert r["status"] == "infeasible"
    pi = r["pi"]
    assert pi[0] + pi[1] <= 0 and pi[0] * 1 + pi[1] * 2 > 0


@pytest.mark.parametrize("d", [2, 3])
def test_weak_reachability_two_formulations_and_planar(d):
    rnd = random.Random(10 + d)
    for _ in range(25):
        W = rand_points(rnd, 5, d, 5)
        for mask in range(1 << 5):
            S = [i for i in range(5) if mask >> i & 1]
            a = proj.is_weakly_reachable(W, S)
            assert a == proj.is_weakly_reachable_direct(W, S)
            if d == 2:
                import planar
                assert a == planar.is_reachable(W, S, strict=False)


def test_gamma_ray():
    W = [(F(1), F(4)), (F(4), F(1)), (F(3), F(3))]
    # K_S for S = {2}: conv{(1,4),(4,1)} + R^2_+ ; ray c (1,1) hits the segment at (2.5, 2.5)
    assert proj.gamma(W, {2}, (F(1), F(1))) == F(5, 2)
    assert proj.gamma(W, {0, 1, 2}, (F(1), F(1))) is None


# ---------------------------------------------------------------- breakpoints


def test_breakpoint_polynomial_shape_d3():
    """The determinant polynomial is z^{b-1}(D0 z + D1): interpolation gives zero coefficients elsewhere."""
    rnd = random.Random(5)
    P = rand_points(rnd, 5, 3)
    for _ in range(300):
        m = rnd.randint(1, 3)
        J = sorted(rnd.sample(range(3), m))
        idx = [rnd.randrange(5) for _ in range(m + 1)]
        up = [rnd.randint(0, 1) for _ in range(m + 1)]
        b = sum(up)
        c = proj.det_poly(P, idx, up, J)
        nz = [i for i, v in enumerate(c) if v != 0]
        if b == 0:
            assert all(i == 0 for i in nz)
        else:
            assert all(b - 1 <= i <= b for i in nz), (c, b)


def test_breakpoints_vs_all_determinants_d3():
    """Roots z > 1 of ALL (d+1)-subsets of the 2T + d vectors (interpolated determinants), d = 3, T = 3."""
    rnd = random.Random(7)
    P = rand_points(rnd, 3, 3)
    T, d = 3, 3
    roots = set()
    n_sub = 0
    vecs = [("c", t, u) for t in range(T) for u in (0, 1)] + [("e", i) for i in range(d)]
    for sub in itertools.combinations(vecs, d + 1):
        n_sub += 1
        E = [v[1] for v in sub if v[0] == "e"]
        C = [v for v in sub if v[0] == "c"]
        J = [i for i in range(d) if i not in E]
        if not C or len(C) != len(J) + 1:
            continue
        c = proj.det_poly(P, [v[1] for v in C], [v[2] for v in C], J)
        while c and c[-1] == 0:
            c.pop()
        # roots of c: factor z^s, then a linear factor
        s = next((i for i, v in enumerate(c) if v != 0), None)
        if s is None:
            continue
        rest = c[s:]
        assert len(rest) <= 2
        if len(rest) == 2 and -rest[0] / rest[1] > 1:
            roots.add(-rest[0] / rest[1])
    assert n_sub == math.comb(2 * T + d, d + 1)
    assert sorted(roots) == proj.breakpoints(P)


def test_gap_points():
    rnd = random.Random(3)
    P = rand_points(rnd, 5, 3)
    roots = proj.breakpoints(P)
    ks = [proj.gap_point(roots, i) for i in range(len(roots) + 1)]
    assert 1 < ks[0] ** 2 < roots[0]
    for i in range(1, len(roots)):
        assert roots[i - 1] < ks[i] ** 2 < roots[i]
    assert ks[-1] ** 2 > roots[-1]


# ---------------------------------------------------------------- oracles: flow vs brute at d = 2


@pytest.mark.parametrize("seed", range(4))
def test_oracle_flow_vs_brute_d2(seed):
    rnd = random.Random(20 + seed)
    P, y = rand_instance(rnd, 3, 2)
    lo, hi = proj.box_bounds(3, y)
    roots = proj.breakpoints(P)
    for i in range(0, len(roots) + 1, max(1, len(roots) // 4)):
        W = proj.corners(P, proj.gap_point(roots, i))
        a = proj.as_answer(proj.oracle_flow(W, lo, hi)).feasible
        b = proj.as_answer(proj.oracle_brute(W, lo, hi)).feasible
        assert a == b, (seed, i)


def test_oracle_flow_rejects_non_box():
    W = proj.corners([(F(1), F(2)), (F(2), F(1))], F(2))
    with pytest.raises(NotImplementedError):
        proj.oracle_flow(W, [F(1)] * 4, [F(1)] * 4)


# ---------------------------------------------------------------- least radius


def float_bisection(P, y, oracle, tol=1e-7):
    T = len(P)
    lo_b, hi_b = proj.box_bounds(T, y)

    def ok(rho):
        k = F(math.exp(rho)).limit_denominator(10 ** 12)
        return proj.as_answer(oracle(proj.corners(P, k), lo_b, hi_b)).feasible
    if ok(0.0):
        return 0.0
    lo, hi = 0.0, 1.0
    while not ok(hi):
        lo, hi = hi, hi * 2
    while hi - lo > tol:
        mid = (lo + hi) / 2
        lo, hi = (lo, mid) if ok(mid) else (mid, hi)
    return hi


@pytest.mark.parametrize("seed", range(4))
def test_least_radius_d2_flow(seed):
    rnd = random.Random(30 + seed)
    P, y = rand_instance(rnd, rnd.randint(3, 6), 2)
    res = proj.least_radius_exact(P, y, proj.oracle_flow)
    ref = float_bisection(P, y, proj.oracle_flow)
    assert abs(res.rho - ref) < 1e-5 and not res.notes


@pytest.mark.parametrize("seed,T", [(4, 4), (7, 3), (12, 4), (21, 3), (22, 4)])
def test_least_radius_d3_brute(seed, T):
    rnd = random.Random(40 + seed)
    P, y = rand_instance(rnd, T, 3)
    res = proj.least_radius_exact(P, y, proj.oracle_brute)
    assert not res.notes
    ref = float_bisection(P, y, proj.oracle_brute)
    assert abs(res.rho - ref) < 1e-5, (res.rho, ref)
    assert res.n_calls <= 3 + math.ceil(math.log2(res.n_breakpoints + 2))
    T = len(P)
    # YES at k_above: witness
    ans = res.ans_above
    assert ans.columns is not None
    Q, cert, checks = proj.witness(P, y, res.k_above, ans.columns, ans.masses)
    assert checks["ok"], checks
    assert proj.in_ball(Q, P, math.log(res.k_above))
    assert proj.in_ball_exact(Q, P, res.k_above)
    # exact check of the certificate against the definition at Q
    assert all(proj.is_weakly_reachable(Q, S) for S, _ in cert)
    # NO at k_below
    if res.gap >= 0:
        ans = res.ans_below
        assert ans is not None and not ans.feasible and ans.lam is not None
        lam, ch = proj.refute(P, y, res.k_below, ans.lam, column_oracle=proj.column_oracle_brute)
        assert lam is not None and ch["global_checked"] and ch["global_ok"], ch


def test_witness_and_refute_d2_flow():
    rnd = random.Random(55)
    for _ in range(20):
        P, y = rand_instance(rnd, 4, 2)
        res = proj.least_radius_exact(P, y, proj.oracle_flow)
        if res.gap < 0:
            continue
        ans = res.ans_above
        if ans.columns is not None:
            Q, cert, checks = proj.witness(P, y, res.k_above, ans.columns, ans.masses)
            assert checks["ok"], checks
        lam = res.ans_below.lam
        if lam is not None:
            lam, ch = proj.refute(P, y, res.k_below, lam, column_oracle=proj.column_oracle_planar)
            assert ch["global_ok"], ch
        break
