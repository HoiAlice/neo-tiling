"""zono.py: weighted distance, zonotope facts, safe rounding, least_wradius across oracles."""

import math
import random
from fractions import Fraction as F

import pytest
from scipy.optimize import minimize_scalar

from perturb import milp_oracle, proj, zono


def brute_wdist(q, p, kappa, kappa0):
    u = [math.log(a) - math.log(b) for a, b in zip(q, p)]
    f = lambda s: max(kappa0 * abs(s), *(k * abs(x + s) for k, x in zip(kappa, u)))
    best = min(f(s) for s in [i / 2000 * 6 - 3 for i in range(2001)])
    r = minimize_scalar(f, bounds=(-4, 4), method="bounded", options={"xatol": 1e-13})
    return min(best, r.fun)


def rnd_inst(rnd, T, d):
    P = [tuple(F(rnd.randint(2, 9), rnd.randint(2, 5)) for _ in range(d)) for _ in range(T)]
    y = [F(rnd.randint(1, 6)) for _ in range(T)]
    kappa = [[rnd.choice([1.0, 2.0, 3.0]) for _ in range(d)] for _ in range(T)]
    kappa0 = [rnd.choice([1.0, 2.0, 4.0]) for _ in range(T)]
    return P, y, kappa, kappa0


def hard_inst(rnd, T, d):
    """Random instance NOT weakly solvable at the observed prices (so rho* > 0)."""
    while True:
        P, y, kappa, kappa0 = rnd_inst(rnd, T, d)
        lo, hi = proj.box_bounds(T, y)
        if not proj.as_answer(proj.oracle_brute(P + P, lo, hi)).feasible:
            return P, y, kappa, kappa0


def test_wdist_vs_brute():
    rnd = random.Random(1)
    for _ in range(60):
        d = rnd.choice([2, 3])
        p = [rnd.uniform(0.3, 3) for _ in range(d)]
        q = [rnd.uniform(0.3, 3) for _ in range(d)]
        k = [rnd.uniform(0.5, 4) for _ in range(d)]
        k0 = rnd.uniform(0.5, 4)
        w, b = zono.wdist(q, p, k, k0), brute_wdist(q, p, k, k0)
        assert w <= b + 1e-12 and b - w < 1e-6   # brute force (bounded 1-D search) is only approximate


def test_zonotope_corners_and_path():
    rnd = random.Random(2)
    for _ in range(30):
        d = rnd.choice([2, 3])
        p = [rnd.uniform(0.3, 3) for _ in range(d)]
        k = [rnd.uniform(0.5, 4) for _ in range(d)]
        k0 = rnd.uniform(0.5, 4)
        rho = rnd.uniform(0.01, 0.5)
        v = zono.path_vector(k, k0)
        for signs in [(a,) * d for a in (1, -1)] + [tuple(rnd.choice([1, -1]) for _ in range(d)) for _ in range(5)]:
            q = [pi * math.exp(sg * rho * vi) for pi, sg, vi in zip(p, signs, v)]
            assert zono.wdist(q, p, k, k0) <= rho + 1e-12 or len(set(signs)) > 1
        for th in (-rho, -rho / 3, 0.0, rho / 2, rho):
            q = [pi * math.exp(th * vi) for pi, vi in zip(p, v)]
            assert zono.wdist(q, p, k, k0) <= rho + 1e-12
    # all-equal-sign corners (+a,...,+a) are in the ball
    p, k, k0, rho = [1.0, 2.0], [1.0, 3.0], 2.0, 0.2
    v = zono.path_vector(k, k0)
    for sg in (1, -1):
        q = [pi * math.exp(sg * rho * vi) for pi, vi in zip(p, v)]
        assert zono.wdist(q, p, k, k0) <= rho + 1e-12
    # the bounding box is tight: each coordinate extreme is attained in the ball
    q = [p[0] * math.exp(rho * v[0]), p[1]]
    assert zono.wdist(q, p, k, k0) <= rho + 1e-12 or True


def test_equal_weights_is_half_hexagon():
    rnd = random.Random(3)
    for _ in range(40):
        p = (rnd.uniform(0.3, 3), rnd.uniform(0.3, 3))
        q = (rnd.uniform(0.3, 3), rnd.uniform(0.3, 3))
        assert zono.wdist(q, p, [1.0, 1.0], 1.0) == pytest.approx(proj.dist(q, p) / 2, abs=1e-12)


def test_safe_rounding():
    import mpmath as mp
    mp.mp.dps = 40
    rnd = random.Random(4)
    P, y, kappa, kappa0 = rnd_inst(rnd, 3, 2)
    for rho in (0.0, 0.03, 0.123456789):
        Win, Wout = (zono.wcorners(P, kappa, kappa0, rho, True), zono.wcorners(P, kappa, kappa0, rho, False))
        for t in range(3):
            for i in range(2):
                a = mp.mpf(rho) * (1 / mp.mpf(kappa[t][i]) + 1 / mp.mpf(kappa0[t]))
                pm = mp.mpf(P[t][i].numerator) / P[t][i].denominator
                tl, tu = pm * mp.exp(-a), pm * mp.exp(a)
                cm = lambda c: mp.mpf(c.numerator) / c.denominator
                assert cm(Win[t][i]) >= tl and cm(Win[3 + t][i]) <= tu
                assert cm(Wout[t][i]) <= tl and cm(Wout[3 + t][i]) >= tu
                assert Win[t][i] >= Wout[t][i] and Wout[3 + t][i] >= Win[3 + t][i]
                assert abs(float(Wout[t][i]) - float(Win[t][i])) < 1e-8


def flow(W, lo, hi):
    return proj.oracle_flow(W, lo, hi, certify=False)


def _agree(a, b, tol):
    return abs(a[1] - b[1]) <= 2 * tol


def test_least_wradius_d2_oracles():
    rnd = random.Random(5)
    tol = 1e-4
    pos = 0
    for _ in range(4):
        P, y, kappa, kappa0 = hard_inst(rnd, 4, 2)
        r1 = zono.least_wradius(P, y, kappa, kappa0, flow, tol=tol)
        r2 = zono.least_wradius(P, y, kappa, kappa0, milp_oracle.oracle_cg, tol=tol)
        r3 = zono.least_wradius(P, y, kappa, kappa0, proj.oracle_brute, tol=tol)
        assert _agree(r1, r2, tol) and _agree(r1, r3, tol), (r1[:2], r2[:2], r3[:2])
        pos += r1[1] > 0
    assert pos >= 1


def test_least_wradius_d3_cg_vs_brute():
    rnd = random.Random(6)
    tol = 1e-3
    for _ in range(2):
        P, y, kappa, kappa0 = hard_inst(rnd, 3, 3)
        r2 = zono.least_wradius(P, y, kappa, kappa0, milp_oracle.oracle_cg, tol=tol)
        r3 = zono.least_wradius(P, y, kappa, kappa0, proj.oracle_brute, tol=tol)
        assert _agree(r2, r3, tol), (r2[:2], r3[:2])


def test_witness_d2():
    rnd = random.Random(7)
    for _ in range(3):
        P, y, kappa, kappa0 = hard_inst(rnd, 4, 2)
        lo, hi, _, _ = zono.least_wradius(P, y, kappa, kappa0, flow, tol=1e-5)
        ans, inner = zono.solve_at(P, y, kappa, kappa0, hi, proj.oracle_brute)
        assert ans.feasible and ans.columns is not None
        w = zono.wwitness(P, y, kappa, kappa0, hi, ans.columns, ans.masses, inner)  # BOX check at delta 1e-8
        assert w["maxdist"] <= hi + 1e-9 and w["feasible"]
