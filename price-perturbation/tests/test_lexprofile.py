"""lexprofile.py: staged lexicographic profile on tiny instances (d = 2 brute / flow, d = 3 brute)."""

import itertools
import random

import pytest

from perturb import lexprofile as pr
from perturb import proj, zono
from test_zono import hard_inst

TOL = 1e-6


def flow(W, lo, hi):
    return proj.oracle_flow(W, lo, hi, certify=False)


CASES = [("flow", 2, 4, flow, 0), ("flow", 2, 5, flow, 1), ("brute", 2, 3, proj.oracle_brute, 2),
         ("brute", 3, 3, proj.oracle_brute, 3), ("brute", 2, 4, proj.oracle_brute, 4)]


def inst(seed, T, d):
    return hard_inst(random.Random(seed), T, d)


@pytest.mark.parametrize("name,d,T,oracle,seed", CASES)
def test_first_stage_and_feasible_and_blocked(name, d, T, oracle, seed):
    P, y, kappa, kappa0 = inst(seed, T, d)
    out = pr.profile(P, y, kappa, kappa0, oracle, tol=TOL)
    _, hi, _, _ = zono.least_wradius(P, y, kappa, kappa0, oracle, tol=TOL)
    assert abs(out["stages"][0]["rho"] - hi) <= 2 * TOL           # first stage = least_wradius
    assert max(out["r"]) == pytest.approx(out["stages"][0]["rho"])
    assert pr.rfeasible(P, y, kappa, kappa0, out["r"], oracle)[0]    # r is feasible
    eps = 4 * TOL
    for t in range(T):                       # fixed years cannot be reduced alone (no branching case)
        if out["r"][t] > 0 and not out["meet_violated_at_stage"]:
            rr = list(out["r"])
            rr[t] = max(rr[t] - eps, 0.0)
            assert not pr.rfeasible(P, y, kappa, kappa0, rr, oracle)[0]
    assert sum(len(s["years"]) for s in out["stages"]) == T


def lex_grid_min(P, y, kappa, kappa0, oracle, rho_max, n):
    """Lexicographic minimum of sorted-decreasing r over the grid {0, h, .., n h}^T, h = rho_max / n,
    feasible vectors only."""
    T = len(P)
    h = rho_max / n
    best = None
    for idx in itertools.product(range(n + 1), repeat=T):
        key = tuple(sorted(idx, reverse=True))
        if best is not None and key >= best[0]:
            continue
        if pr.rfeasible(P, y, kappa, kappa0, [i * h for i in idx], oracle)[0]:
            best = (key, idx)
    return best[0], h


@pytest.mark.parametrize("name,d,T,oracle,seed,n", [("flow", 2, 4, flow, 0, 5), ("flow", 2, 4, flow, 7, 5),
                                                    ("brute", 2, 3, proj.oracle_brute, 2, 5),
                                                    ("brute", 3, 3, proj.oracle_brute, 3, 4)])
def test_against_grid(name, d, T, oracle, seed, n):
    P, y, kappa, kappa0 = inst(seed, T, d)
    out = pr.profile(P, y, kappa, kappa0, oracle, tol=TOL)
    rho = out["stages"][0]["rho"]
    key, h = lex_grid_min(P, y, kappa, kappa0, oracle, rho * 1.0000001, n)
    g = [k * h for k in key]
    rs = sorted(out["r"], reverse=True)
    ceil_r = sorted((-(-x // h) * h for x in out["r"]), reverse=True)     # grid point above r: feasible
    assert not pr._lex_less(g, rs, 1e-5)          # r is the lex-min over all of R, g only over a grid
    assert tuple(g) <= tuple(c + 1e-5 for c in ceil_r)
    assert all(abs(a - b) <= h + 1e-5 for a, b in zip(rs, g))           # agreement up to the grid step
