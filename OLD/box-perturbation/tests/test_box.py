"""box.py against brute force on small instances with ties, zero widths and duplicates."""

import itertools
import random
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT.parent / "poly-hardness"))
import box  # noqa: E402
import planar  # noqa: E402
import numpy as np  # noqa: E402
from scipy.optimize import linprog  # noqa: E402


def in_cone(P, y):
    """Definition-based: y in the cone of the weakly reachable sets (brute force over 2^T sets,
    interior-point LP)."""
    fam = planar.family(P)
    M = np.array([[1.0 if q in S else 0.0 for S in fam] for q in range(len(P))])
    res = linprog(np.zeros(len(fam)), A_eq=M, b_eq=[float(v) for v in y],
                  bounds=[(0, None)] * len(fam), method="highs-ipm")
    return res.status == 0


def scaled(P, k):
    """The box [P/k, kP]."""
    k = F(k)
    return [tuple(F(c) / k for c in p) for p in P], [tuple(F(c) * k for c in p) for p in P]


def random_box(rng, T, grid=5, zero=0.6):
    L = [(F(rng.randint(1, grid)), F(rng.randint(1, grid))) for _ in range(T)]
    U = [tuple(l + (0 if rng.random() < zero else rng.randint(0, 1)) for l in p) for p in L]
    return L, U


def grid_search(L, U, y):
    """Is y weakly solvable at some Q with every Q_t in {L_t, mid, U_t}^2?"""
    opts = []
    for l, u in zip(L, U):
        xs = [(l[0] + k * (u[0] - l[0]) / 2) for k in range(3)]
        ys = [(l[1] + k * (u[1] - l[1]) / 2) for k in range(3)]
        opts.append(sorted(set(itertools.product(xs, ys))))
    for Q in itertools.product(*opts):
        if in_cone(list(Q), y):
            return list(Q)
    return None


def test_closed_box_vs_brute_force_and_witness():
    rng = random.Random(1)
    n_true = n_false = n_unref = 0
    for it in range(300):
        T = 2 if it < 200 else 3
        L, U = random_box(rng, T)
        y = [F(rng.randint(0, 9)) for _ in range(T)]
        if box.decide(L, U, y):
            n_true += 1
            Q, cert = box.witness(L, U, y)
            assert box.in_box(Q, L, U) and box.certify(Q, y, cert), (L, U, y)
        else:
            n_false += 1
            assert box.witness(L, U, y) is None
            if box.refute(L, U, y) is None:
                n_unref += 1
            assert grid_search(L, U, y) is None, (L, U, y)
    assert n_true > 20 and n_false > 20
    assert n_unref <= n_false // 10          # NO answers are certified by the column oracle


def test_fixed_prices_agree_with_definition():
    rng = random.Random(2)
    for _ in range(150):
        T = rng.randint(1, 4)
        P = [(F(rng.randint(1, 4)), F(rng.randint(1, 4))) for _ in range(T)]
        y = [F(rng.randint(0, 4)) for _ in range(T)]
        assert box.decide(P, P, y) == in_cone(P, y), (P, y)


def test_degenerate_boxes():
    # duplicated points, zero widths, collinear corners on x + y = 7
    L = [(F(2), F(5))] * 3
    y = [F(1), F(2), F(3)]
    assert box.decide(L, L, y)                # identical points are free
    U = [(F(2), F(5)), (F(3), F(5)), (F(4), F(5))]
    assert box.decide(L, U, y)
    Q, cert = box.witness(L, U, y)
    assert box.in_box(Q, L, U) and box.certify(Q, y, cert)
    L = [(F(k), F(7 - k)) for k in (1, 3, 5)]
    for y in ([1, 2, 3], [3, 1, 2], [0, 5, 0], [2, 2, 2]):
        y = [F(v) for v in y]
        assert box.decide(L, L, y) == in_cone(L, y)
        U = [(a + 1, b + 1) for a, b in L]
        if box.decide(L, U, y):
            Q, cert = box.witness(L, U, y)
            assert box.certify(Q, y, cert)


def test_critical_triangle():
    """P = (4,1), (3,3), (1,4), y = (1,5,3): the box [P/k, kP] has a solution iff k >= sqrt(1.2)."""
    P = [(4, 1), (3, 3), (1, 4)]
    y = [F(1), F(5), F(3)]
    k = F(1.2 ** 0.5).limit_denominator(10**9)
    below, above = scaled(P, k * (1 - F(1, 10**6))), scaled(P, k * (1 + F(1, 10**6)))
    assert not box.decide(*below, y) and box.decide(*above, y)
    Q, cert = box.witness(*above, y)
    assert box.in_box(Q, *above) and box.certify(Q, y, cert)
    lam = box.refute(*below, y)                # exact NO certificate (Farkas vector)
    assert lam is not None
    assert all(lam[t] <= 0 <= lam[3 + t] for t in range(3))
    assert sum((lam[t] + lam[3 + t]) * y[t] for t in range(3)) < 0


def test_trivial_sizes_and_ties():
    assert box.decide([], [], []) and box.witness([], [], []) == ([], [])
    for v in (0, 3):
        L, U = [(F(2), F(3))], [(F(4), F(5))]
        Q, cert = box.witness(L, U, [F(v)])
        assert box.in_box(Q, L, U) and box.certify(Q, [F(v)], cert)
    P = [(F(2), F(5)), (F(2), F(5)), (F(3), F(1))]
    for y in ([1, 1, 1], [0, 0, 0], [0, 2, 0], [2, 2, 5], [5, 5, 2]):
        y = [F(v) for v in y]
        assert box.decide(P, P, y) == in_cone(P, y), y
        L, U = scaled(P, F(11, 10))
        if box.decide(L, U, y):
            Q, cert = box.witness(L, U, y)
            assert box.in_box(Q, L, U) and box.certify(Q, y, cert)
