"""The PLACEHOLDER MILP oracle against the exact references (brute force, d = 2 flow LP)."""

import math
import random
from fractions import Fraction as F

import pytest

from perturb import proj
from perturb.milp_oracle import oracle_cg, oracle_milp
from test_proj import rand_instance


@pytest.mark.parametrize("seed,T,d", [(1, 3, 3), (2, 4, 3), (3, 4, 3), (4, 3, 2), (5, 4, 2)])
def test_milp_vs_brute_box(seed, T, d):
    rnd = random.Random(70 + seed)
    P, y = rand_instance(rnd, T, d)
    lo, hi = proj.box_bounds(T, y)
    for k in [F(1), F(11, 10), F(3, 2), F(2), F(4)]:
        W = proj.corners(P, k)
        ref = proj.oracle_brute(W, lo, hi).feasible
        ans = oracle_milp(W, lo, hi)
        assert ans.feasible == ref, (k, ref)
        if ans.feasible and ans.columns is not None:
            w = [sum(mm for S, mm in zip(ans.columns, ans.masses) if r in S) for r in range(2 * T)]
            assert all(F(lo[r]) <= w[r] for r in range(2 * T))
            assert all(math.isinf(float(hi[r])) or w[r] <= F(hi[r]) for r in range(2 * T))


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_milp_plain_weak_solvability(seed):
    """lo = hi = y: plain weak solvability at fixed prices."""
    rnd = random.Random(90 + seed)
    P, y = rand_instance(rnd, 4, 3)
    assert oracle_milp(P, y, y).feasible == proj.oracle_brute(P, y, y).feasible


@pytest.mark.parametrize("seed,T", [(4, 4), (7, 3), (21, 3)])
def test_least_radius_d3_milp(seed, T):
    rnd = random.Random(40 + seed)
    P, y = rand_instance(rnd, T, 3)
    res = proj.least_radius_exact(P, y, oracle_milp)
    ref = proj.least_radius_exact(P, y, proj.oracle_brute)
    assert res.z_star == ref.z_star
    ans = res.ans_above
    if ans.columns is not None:
        Q, cert, checks = proj.witness(P, y, res.k_above, ans.columns, ans.masses)
        assert checks["ok"], checks
        assert proj.in_ball_exact(Q, P, res.k_above)


def test_least_radius_d2_milp_vs_flow():
    rnd = random.Random(5)
    P, y = rand_instance(rnd, 5, 2)
    assert proj.least_radius_exact(P, y, oracle_milp).z_star == \
        proj.least_radius_exact(P, y, proj.oracle_flow).z_star


# ---------------------------------------------------------------- column generation


@pytest.mark.parametrize("seed,T,d", [(1, 3, 3), (2, 4, 3), (3, 4, 3), (4, 3, 2), (5, 4, 2)])
def test_cg_vs_brute_box(seed, T, d):
    rnd = random.Random(70 + seed)
    P, y = rand_instance(rnd, T, d)
    lo, hi = proj.box_bounds(T, y)
    for k in [F(1), F(11, 10), F(3, 2), F(2), F(4)]:
        W = proj.corners(P, k)
        ref = proj.oracle_brute(W, lo, hi).feasible
        ans = oracle_cg(W, lo, hi)
        assert ans.feasible == ref, (k, ref)
        if not ans.feasible:
            assert proj.check_farkas(None, lo, hi, ans.lam)
            assert proj.column_oracle_brute(W, ans.lam) >= -1e-6


@pytest.mark.parametrize("seed,T", [(4, 4), (7, 3), (21, 3)])
def test_least_radius_d3_cg(seed, T):
    rnd = random.Random(40 + seed)
    P, y = rand_instance(rnd, T, 3)
    assert proj.least_radius_exact(P, y, oracle_cg).z_star == \
        proj.least_radius_exact(P, y, proj.oracle_brute).z_star


def test_least_radius_d2_cg_vs_flow():
    rnd = random.Random(5)
    P, y = rand_instance(rnd, 5, 2)
    assert proj.least_radius_exact(P, y, oracle_cg).z_star == \
        proj.least_radius_exact(P, y, proj.oracle_flow).z_star
