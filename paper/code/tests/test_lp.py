"""Tests of the exact algorithm on tiny instances with independent checks (brute-force oracle)."""

import math
import random
from fractions import Fraction as F

import pytest

from neotiling.oracle.brute import oracle_brute
from neotiling.lp.problem import Problem
from neotiling.lp.solve import solve


def instance(seed, T, d):
    rng = random.Random(seed)
    return ([tuple(F(rng.randint(1, 40), 10) for _ in range(d)) for _ in range(T)],
            [F(rng.randint(1, 30)) for _ in range(T)])


def ws(Q, y):
    """Independent check: weak solvability by enumeration of all weakly reachable sets."""
    return oracle_brute([tuple(q) for q in Q], y, y).feasible


def feasible_points(prob, n, seed):
    rng, out = random.Random(seed), []
    for _ in range(40 * n):
        Q = [tuple(F(pv) * F(math.exp(rng.choice((-1, 1)) * rng.random() * rng.choice((0, 0.3, 1))))
                   .limit_denominator(1000) for pv in p) for p in prob.P]
        if ws(Q, prob.y):
            out.append(Q)
            if len(out) == n:
                break
    return out


@pytest.mark.slow
@pytest.mark.parametrize("p,metric", [(1.0, "rel"), (2.0, "rel"), (math.inf, "rel"), (1.0, "log")])
@pytest.mark.parametrize("seed,T,d", [(s, 4, 2) for s in range(4)] + [(s, 4, 3) for s in range(2)])
def test_certified_bounds(seed, T, d, p, metric):
    """Whatever the status (some instances need more than the time limit): the returned Q is
    feasible by enumeration, UB is its cost, LB is below independent feasible points."""
    P, y = instance(seed, T, d)
    prob = Problem(P, y, p=p, metric=metric)
    res = solve(prob, eps=1e-5, time_limit=60)
    assert res["status"] in ("optimal", "time_limit")
    assert res["LB"] <= res["UB"] + 1e-9
    assert ws(res["Q"], y)                                    # the UB solution is feasible
    assert abs(prob.cost(res["Q"]) - res["UB"]) < 1e-12        # and has the reported cost
    for Q in feasible_points(prob, 10, seed):                 # LB below independent feasible points
        assert res["LB"] <= prob.cost(Q) + 1e-7


@pytest.mark.slow
def test_dominated_pair():
    """y_1 > y_2 and p_2 < p_1: the gap ln 4 of coordinate 1 must be closed.  l_1: ln 4; l_p: split
    between the two years, ln 4 * 2^(1/p - 1); l_inf: ln 4 / 2."""
    P, y = [(F(4), F(9)), (F(1), F(1))], [F(5), F(1)]
    for p, opt in ((1.0, math.log(4)), (2.0, math.log(4) / math.sqrt(2)), (math.inf, math.log(4) / 2)):
        res = solve(Problem(P, y, p=p), eps=1e-6, time_limit=60)
        assert abs(res["UB"] - opt) < 1e-5 and opt - 1e-5 <= res["LB"] <= opt + 1e-7
    # relative metric: l_1 lowers p_1^1 = 4 to 1 (cost 3/4); l_inf meets at 4(1 - e) = 1 + e, e = 3/5
    for p, opt in ((1.0, 0.75), (math.inf, 0.6)):
        res = solve(Problem(P, y, p=p, metric="rel"), eps=1e-6, time_limit=60)
        assert abs(res["UB"] - opt) < 1e-5 and opt - 1e-5 <= res["LB"] <= opt + 1e-7
