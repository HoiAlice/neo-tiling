"""oracle.flow_d2.decide (interior-point flow LP, d = 2) against exhaustive enumeration, T <= 5."""

import random
from fractions import Fraction as F

import pytest

from neotiling.geometry import reach
from neotiling.oracle import as_answer
from neotiling.oracle.brute import oracle_brute
from neotiling.oracle.flow_d2 import decide, oracle_flow


def instance(seed, T):
    rnd = random.Random(seed)
    P = [(F(rnd.randint(1, 9), rnd.randint(1, 3)), F(rnd.randint(1, 9), rnd.randint(1, 3))) for _ in range(T)]
    y = [F(rnd.randint(0, 5)) for _ in range(T)]
    y[0] = max(y[0], F(1))
    return P, y


@pytest.mark.parametrize("seed,T", [(0, 2), (1, 3), (2, 3), (3, 4)])
def test_decide_vs_brute(seed, T):
    P, y = instance(seed, T)
    lo, hi = reach.box_bounds(T, y)
    roots = reach.breakpoints(P)
    for i in range(0, len(roots) + 1, max(1, len(roots) // 3)):
        W = reach.corners(P, reach.gap_point(roots, i))
        got = decide(W[:T], W[T:], y)
        assert got == oracle_brute(W, lo, hi).feasible, (seed, i)


def test_decide_zero_width_box_is_weak_solvability():
    P, y = instance(5, 5)
    lo, hi = reach.box_bounds(5, y)
    W = P + P
    assert decide(P, P, y) == oracle_brute(W, lo, hi).feasible


def test_oracle_flow_certificates_vs_brute():
    for seed in range(3):
        P, y = instance(10 + seed, 3)
        lo, hi = reach.box_bounds(3, y)
        for k in (F(1), F(2), F(7, 2)):
            W = reach.corners(P, k)
            a, b = as_answer(oracle_flow(W, lo, hi)), oracle_brute(W, lo, hi)
            assert a.feasible == b.feasible
            if not a.feasible:
                assert reach.check_farkas(None, lo, hi, a.lam)
