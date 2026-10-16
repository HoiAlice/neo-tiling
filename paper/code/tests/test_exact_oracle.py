"""exact_oracle.py: agreement with oracle_brute (d = 2, 3) and oracle_flow (d = 2), exact certificates."""

import random
from fractions import Fraction as F

import pytest

from neotiling.geometry import reach as proj
from neotiling.oracle import as_answer
from neotiling.oracle.brute import oracle_brute
from neotiling.oracle.exact import CoverCuts, oracle_exact, price_exact
from neotiling.oracle.flow_d2 import oracle_flow
from neotiling.radius import weighted as zono
from test_weighted import rnd_inst


def flow(W, lo, hi):
    return oracle_flow(W, lo, hi, certify=False)


def unsolvable_inst(seed, T, d):
    rnd = random.Random(seed)
    while True:
        P, y, kappa, kappa0 = rnd_inst(rnd, T, d)
        lo, hi = proj.box_bounds(T, y)
        if not oracle_exact(P + P, lo, hi).feasible:
            return P, y, kappa, kappa0


@pytest.mark.slow
@pytest.mark.parametrize("d,T,ref,seed", [(3, 3, "brute", 0), (3, 4, "brute", 1), (2, 4, "brute", 2),
                                          (2, 10, "flow", 3)])
def test_agrees_and_certifies(d, T, ref, seed):
    refo = oracle_brute if ref == "brute" else flow
    P, y, kappa, kappa0 = unsolvable_inst(seed, T, d)
    _, rs, _, _ = zono.least_wradius(P, y, kappa, kappa0, refo, tol=1e-4)
    lo, hi = proj.box_bounds(T, [F(v) for v in y])
    for f in (0.5, 0.99, 1.0, 1.01, 2.0):
        W = zono.wcorners(P, kappa, kappa0, rs * f, True)
        a = oracle_exact(W, lo, hi)
        assert a.feasible == as_answer(refo(W, lo, hi)).feasible
        if a.feasible:
            assert all(proj.is_weakly_reachable(W, S) for S in a.columns)
            assert proj._cone_lp(a.columns, lo, hi)[0] is not None
        else:
            assert proj.check_farkas(None, lo, hi, a.lam)
            if ref == "brute":
                assert all(sum(F(a.lam[r]) for r in S) >= 0 for S in proj.all_reachable_sets(W))


def test_pricing_degenerate_points():
    """Points sharing a coordinate (the configuration the profile produces): every set is weakly
    reachable, so the pricing maximum is the sum of the positive weights."""
    W = [(F(1), F(k, 7)) for k in range(1, 8)]
    g = [3, -1, 2, -5, 1, 0, 4]
    S, v = price_exact(CoverCuts(W), g)
    assert S == frozenset(r for r in range(7) if g[r] > 0) and v == 10
    assert proj.is_weakly_reachable(W, S)
