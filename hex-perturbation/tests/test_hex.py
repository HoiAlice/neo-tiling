"""hex.py: exact root arithmetic, agreement with float bisection, certificates, monotonicity."""

import math
import random
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import box  # noqa: E402
import hex as hx  # noqa: E402


# ---------------------------------------------------------------- (a) exact root arithmetic


def test_sign_lin():
    assert hx.sign_lin(F(3), F(-1), F(9)) == 0            # 3 - sqrt 9
    assert hx.sign_lin(F(3), F(-1), F(10)) == -1
    assert hx.sign_lin(F(-3), F(1), F(10)) == 1
    assert hx.sign_lin(F(0), F(5), F(2)) == 1


def test_sign3_identities():
    # sqrt 2 + sqrt 3 - sqrt(5 + 2 sqrt 6) = 0, tested through squares: (sqrt2+sqrt3)^2 = 5+2sqrt6
    assert hx.sign3(F(0), F(1), F(2), F(1), F(3)) == 1
    # sqrt 8 - 2 sqrt 2 = 0 with different radicands
    assert hx.sign3(F(0), F(1), F(8), F(-2), F(2)) == 0
    # 1 + sqrt 2 vs sqrt 6 - ...: (1 + sqrt2) - sqrt(5.8284) where sqrt(3 + 2 sqrt 2) = 1 + sqrt 2
    # sqrt 7 + sqrt 10 - sqrt 3 - ... sign checks against mpmath at high precision
    rnd = random.Random(1)
    for _ in range(300):
        A = F(rnd.randint(-30, 30), rnd.randint(1, 5))
        B = F(rnd.randint(-9, 9), rnd.randint(1, 4))
        C = F(rnd.randint(-9, 9), rnd.randint(1, 4))
        D1, D2 = F(rnd.randint(1, 40), rnd.randint(1, 3)), F(rnd.randint(1, 40), rnd.randint(1, 3))
        v = (hx.mpmath.mpf(A.numerator) / A.denominator
             + hx.mpmath.mpf(B.numerator) / B.denominator * hx.mpmath.sqrt(hx.mpmath.mpf(D1.numerator) / D1.denominator)
             + hx.mpmath.mpf(C.numerator) / C.denominator * hx.mpmath.sqrt(hx.mpmath.mpf(D2.numerator) / D2.denominator))
        s = hx.sign3(A, B, D1, C, D2)
        if abs(v) > 1e-50:
            assert s == (1 if v > 0 else -1)
        else:
            assert s == 0


def test_alg_equality_different_representations():
    a = hx.Alg(F(1, 2), F(1, 2), F(5))             # (1 + sqrt 5) / 2
    b = hx.Alg(F(1, 2), F(3, 2), F(5, 9))          # 1/2 + (3/2) sqrt(5/9) = 1/2 + sqrt5/2
    c = hx.Alg(F(1, 2), F(1, 2), F(6))
    assert a == b and a.cmp(b) == 0
    assert a < c and c > a
    assert hx.Alg(2) > a and hx.Alg(F(8, 5)) < a and hx.Alg(F(1618, 1000)) < a
    assert hx.Alg(F(1619, 1000)) > a                # 1.6180339...


def test_roots_keys_and_dedup():
    # 2 z^2 - 4 z + 1 and z^2 - 2 z + 1/2 are the same polynomial up to scaling: equal roots
    r1 = hx._poly_roots(hx._normalize([F(1), F(-4), F(2)]))
    r2 = hx._poly_roots(hx._normalize([F(1, 2), F(-2), F(1)]))
    assert {x.key for x in r1} == {x.key for x in r2}
    assert all(x == y for x, y in zip(r1, r2))
    # z^2 - 3z + 2 = (z-1)(z-2): rational roots
    r = hx._poly_roots(hx._normalize([F(2), F(-3), F(1)]))
    assert sorted(x.alpha for x in r) == [1, 2]
    # roots of z^2 - 2 are distinct, the larger is sqrt 2
    r = sorted(hx._poly_roots(hx._normalize([F(-2), F(0), F(1)])), key=float)
    assert r[0] < 0 < r[1] and abs(float(r[1]) - math.sqrt(2)) < 1e-14


def test_breakpoints_sorted_and_gap_points():
    P = [(F(1), F(5)), (F(2), F(3)), (F(3), F(2)), (F(5), F(1)), (F(7, 3), F(7, 3))]
    roots = hx.breakpoints(P)
    assert roots, "expected breakpoints"
    for u, v in zip(roots, roots[1:]):
        assert u < v
    assert all(r > 1 for r in roots)
    ks = hx.gap_points(roots)
    assert len(ks) == len(roots) + 1
    assert hx.Alg(1) < hx.Alg(ks[0] ** 2) < roots[0]
    for i, r in enumerate(roots[:-1]):
        assert r < hx.Alg(ks[i + 1] ** 2) < roots[i + 1]
    assert hx.Alg(ks[-1] ** 2) > roots[-1]


# ---------------------------------------------------------------- (b), (c) random instances


def float_bisection(P, y, tol=1e-9):
    """Least rho with box.decide(P e^{-rho}, P e^{rho}) by plain bisection (float oracle)."""
    def ok(rho):
        k = F(math.exp(rho)).limit_denominator(10 ** 14)
        return box.decide(*hx.log_box(P, k), y)
    if box.decide(P, P, y):
        return 0.0
    lo, hi = 0.0, 1.0
    while not ok(hi):
        lo, hi = hi, hi * 2
    while hi - lo > tol:
        mid = (lo + hi) / 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def random_instance(rnd, T):
    P = [(F(rnd.randint(1, 9), rnd.randint(1, 3)), F(rnd.randint(1, 9), rnd.randint(1, 3))) for _ in range(T)]
    y = [F(rnd.randint(0, 10)) for _ in range(T)]
    if max(y) == 0:
        y[0] = F(1)
    return P, y


SEEDS = list(range(12))


@pytest.mark.parametrize("seed", SEEDS)
def test_random_instance(seed):
    rnd = random.Random(seed)
    T = rnd.randint(3, 6)
    P, y = random_instance(rnd, T)
    res = hx.least_radius_exact(P, y)
    ref = float_bisection(P, y)
    assert abs(res.rho - ref) < 1e-6, (seed, res.rho, ref, res.notes)
    assert not res.notes
    assert res.n_calls <= 2 + math.ceil(math.log2(res.n_breakpoints + 2)) + 1
    cert = hx.certify_result(P, y, res)
    if res.gap >= 0:
        assert cert["no_certified"] is True
    assert cert["yes_certified"] is True and cert["witness_in_hex"] is True
    # (c) infeasible slightly below rho*
    if res.rho > 1e-4:
        k = F(math.exp(res.rho * (1 - 1e-3))).limit_denominator(10 ** 12)
        assert not box.decide(*hx.log_box(P, k), y)
        k = F(math.exp(res.rho * (1 + 1e-3))).limit_denominator(10 ** 12)
        assert box.decide(*hx.log_box(P, k), y)


def test_some_instances_nontrivial():
    """The random family is not vacuous: at least a few instances have rho* > 0."""
    positive = 0
    for seed in SEEDS:
        rnd = random.Random(seed)
        P, y = random_instance(rnd, rnd.randint(3, 6))
        positive += not box.decide(P, P, y)
    assert positive >= 3


@pytest.mark.parametrize("seed", [100, 101, 102])
def test_monotone_over_all_gaps(seed):
    """Feasibility at every gap point is monotone (False..False True..True) and the switch is at
    the gap found by least_radius_exact."""
    rnd = random.Random(seed)
    P, y = random_instance(rnd, 4)
    if box.decide(P, P, y):
        pytest.skip("feasible at z = 1")
    res = hx.least_radius_exact(P, y)
    roots = res.roots
    vals = [b for _, b in hx.monotonicity_check(P, y, roots, range(len(roots) + 1))]
    first = vals.index(True)
    assert all(not v for v in vals[:first]) and all(vals[first:])
    assert first == res.gap
