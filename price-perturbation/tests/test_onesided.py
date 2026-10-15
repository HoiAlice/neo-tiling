"""onesided.py: one-sided lexicographic profile on tiny instances (d = 2 brute / flow, d = 3 brute)."""

import random

import pytest

from perturb import onesided, proj, zono
from test_zono import hard_inst

TOL = 1e-6


def flow(W, lo, hi):
    return proj.oracle_flow(W, lo, hi, certify=False)


CASES = [("flow", 2, 4, flow, 0), ("flow", 2, 5, flow, 1), ("brute", 2, 4, proj.oracle_brute, 2),
         ("brute", 3, 3, proj.oracle_brute, 3)]


@pytest.mark.parametrize("name,d,T,oracle,seed", CASES)
def test_profile(name, d, T, oracle, seed):
    P, y, kappa, kappa0 = hard_inst(random.Random(seed), T, d)
    out = onesided.profile(P, y, kappa, kappa0, oracle, tol=TOL)
    assert out["verified"] and out["tight"] and not out["both"]
    _, hi, _, _ = zono.least_wradius(P, y, kappa, kappa0, oracle, tol=TOL)
    assert abs(out["stages"][0]["lam"] - hi) <= 2 * TOL                # first stage = rho*
    assert max(abs(th) for th in out["theta"]) == pytest.approx(hi, abs=2 * TOL)
    rev = onesided.profile(P, y, kappa, kappa0, oracle, tol=TOL,
                           order=list(reversed(onesided.units(T))), check=False)
    if out["ties"] == 0 and rev["ties"] == 0:                           # no tie: order does not matter
        assert max(abs(a - b) for a, b in zip(out["theta"], rev["theta"])) <= 10 * TOL


def test_icorners_degenerate():
    P = [(2, 3), (5, 1)]
    kappa, kappa0 = [[1.0, 2.0], [1.0, 1.0]], [1.0, 2.0]
    W = onesided.icorners(P, kappa, kappa0, [0.0, 0.0], [0.0, 0.0])
    assert W == [(2, 3), (5, 1), (2, 3), (5, 1)]
    W = onesided.icorners(P, kappa, kappa0, [0.1, -0.2], [0.3, 0.0])     # shifted intervals
    for t in range(2):
        assert all(float(a) <= float(b) for a, b in zip(W[t], W[2 + t]))
    assert all(float(a) > float(b) for a, b in zip(W[0], P[0]))          # lo > 0: L above p


def test_tie_break_and_tightening(monkeypatch):
    """Synthetic monotone feasibility 'year 0 up by 1 OR year 1 up by 1' (a tie at level 1): the
    tie-break fixes year 0 (priority order), tightening drops its unused downward half-axis."""
    def fake(P, y, kappa, kappa0, lo, hi, oracle, outer=True):
        oracle(None, None, None)
        return hi[0] >= 1 - 1e-12 or hi[1] >= 1 - 1e-12
    monkeypatch.setattr(onesided, "ifeasible", fake)
    P, y = [(1, 1), (1, 1)], [1, 1]
    kappa, kappa0 = [[1.0, 1.0]] * 2, [1.0] * 2
    out = onesided.profile(P, y, kappa, kappa0, lambda W, lo, hi: True, tol=1e-9)
    assert out["ties"] == 1 and out["tight"] and out["verified"] and not out["both"]
    assert out["beta"][0] == pytest.approx(1.0, abs=1e-8)
    assert out["alpha"] == [0.0, 0.0] and out["beta"][1] == 0.0
    assert out["theta"][0] == pytest.approx(1.0, abs=1e-8) and out["theta"][1] == 0.0


@pytest.mark.parametrize("d,T,seed,force", [(2, 4, 0, False), (2, 4, 0, True), (3, 3, 3, True)])
def test_rational_solution(d, T, seed, force):
    """Rational Q (corners, or the linear-path construction) is weakly solvable exactly and lies in
    the balls of the profile."""
    from perturb.exact_oracle import oracle_exact
    P, y, kappa, kappa0 = hard_inst(random.Random(seed), T, d)
    out = onesided.profile(P, y, kappa, kappa0, oracle_exact, tol=TOL, check=False)
    Q, ans, how = onesided.rational_solution(P, y, kappa, kappa0, out, oracle_exact, force_linear=force)
    assert ans.feasible and ans.columns is not None
    assert how == ("linear" if force else how)
    for t in range(T):
        r = max(out["alpha"][t], out["beta"][t])
        assert zono.wdist(Q[t], P[t], kappa[t], kappa0[t]) <= r + 1e-9
