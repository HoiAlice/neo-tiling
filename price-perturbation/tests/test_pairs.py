"""Tests of pairs.py on tiny random instances (d = 2, T <= 4; unit = pair (t, i))."""
import itertools
import math
import random
from fractions import Fraction as F

import pytest

from perturb import pairs as walls


def instance(seed, T):
    rnd = random.Random(seed)
    P = [(F(rnd.randint(20, 100), 50), F(rnd.randint(20, 100), 50)) for _ in range(T)]
    y = [F(rnd.randint(1, 9)) for _ in range(T)]
    return P, y


def feas(P, y, lam):
    a = [[lam[(t, i)] for i in range(2)] for t in range(len(P))]
    return walls.box_feasible(P, y, a, a)


def common_level(P, y, hi=1.0, tol=1e-6):
    T = len(P)

    def ok(r):
        return feas(P, y, {(t, i): r for t in range(T) for i in range(2)})
    if ok(0.0):
        return 0.0
    a, b = 0.0, hi
    while not ok(b):
        a, b = b, 2 * b
    while b - a > tol:
        m = (a + b) / 2
        a, b = (a, m) if ok(m) else (m, b)
    return b


def brute(P, y, res, nlev=4):
    """No grid vector with a lexicographically smaller sorted (decreasing) profile is feasible."""
    lam = res["lam"]
    keys = list(lam)
    v = sorted(lam.values(), reverse=True)
    if v[0] == 0:
        return True, 0, None
    g = v[0] / nlev
    vp = sorted((math.floor(x / g + 1e-4) * g for x in v), reverse=True)
    n_checked = 0
    for u in itertools.product(range(nlev + 1), repeat=len(keys)):
        us = sorted((k * g for k in u), reverse=True)
        if not walls.lex_less(us, vp, 1e-9):
            continue
        n_checked += 1
        if feas(P, y, {k: x * g for k, x in zip(keys, u)}):
            return False, n_checked, u
    return True, n_checked, None


@pytest.mark.parametrize("seed,T", [(s, T) for T in (2, 3, 4) for s in range(4)])
def test_wall_profile(seed, T):
    P, y = instance(seed, T)
    res = walls.wall_profile(P, y)
    lam, st = res["lam"], res["stages"]
    rho0 = common_level(P, y)
    assert abs(st[0]["rho"] - rho0) <= 2e-6                  # first stage = least common level
    assert feas(P, y, lam) and res["Q"] is not None          # final box feasible
    if not res["branched"]:                                  # every positive pair is unshrinkable
        d2 = 2 * res["ctx"].delta
        for k, x in lam.items():
            if x > 1e-12:
                l2 = dict(lam)
                l2[k] = max(x - d2, 0.0)
                assert not feas(P, y, l2)
    if T <= 3:                                               # brute force on a grid
        assert brute(P, y, res)[0] is not False
