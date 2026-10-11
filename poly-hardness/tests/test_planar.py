"""planar.py against brute force on small random instances with ties and duplicates."""

import random
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import planar  # noqa: E402


def random_points(rng, T, grid):
    return [(Fraction(rng.randint(1, grid)), Fraction(rng.randint(1, grid))) for _ in range(T)]


def path_family(P, strict):
    """All sets Out(pi) u B', B' within Bnd(pi) (B' empty if strict), over all paths."""
    G = planar.chain_graph(P)
    out_arcs = {}
    for u, v, out, bnd in G.arcs:
        out_arcs.setdefault(u, []).append((v, out, bnd))
    fam = set()

    def dfs(u, out, bnd):
        for v, o, b in out_arcs.get(u, []):
            o2, b2 = out | o, bnd | b
            if v == planar.SNK:
                bl = [] if strict else sorted(b2)
                for m in range(1 << len(bl)):
                    fam.add(o2 | frozenset(bl[i] for i in range(len(bl)) if m >> i & 1))
            else:
                dfs(v, o2, b2)

    dfs(planar.SRC, frozenset(), frozenset())
    return fam


def in_cone(fam, y, T):
    if not fam:
        return all(v == 0 for v in y)
    M = np.array([[1.0 if q in S else 0.0 for S in fam] for q in range(T)])
    res = linprog(np.zeros(len(fam)), A_eq=M, b_eq=[float(v) for v in y],
                  bounds=[(0, None)] * len(fam), method="highs")
    return res.status == 0


def test_family_equals_paths():
    rng = random.Random(1)
    for _ in range(400):
        T = rng.randint(1, 7)
        P = random_points(rng, T, rng.choice([3, 5, 20]))
        for strict in (False, True):
            assert set(planar.family(P, strict)) == path_family(P, strict), (P, strict)


def test_lp_column_and_certificates():
    rng = random.Random(2)
    n_yes = 0
    for _ in range(300):
        T = rng.randint(2, 7)
        P = random_points(rng, T, rng.choice([3, 5, 20]))
        for strict in (False, True):
            fam = planar.family(P, strict)
            # column problem
            w = [rng.randint(-5, 5) for _ in range(T)]
            best, S = planar.max_weight(P, w, strict)
            assert best == max(sum(w[q] for q in F) for F in fam)
            assert S in set(fam) and sum(w[q] for q in S) == best
            # membership
            y = [Fraction(rng.randint(0, 4)) for _ in range(T)]
            lp = planar.flow_lp(P, y, strict)
            assert lp.feasible == in_cone(fam, y, T), (P, y, strict)
            if lp.feasible:
                n_yes += 1
                cert = planar.certify(P, y, strict)
                assert cert is not None and planar.check_certificate(P, y, cert, strict)
            else:  # the Farkas vector separates y from the cone
                assert float(np.dot(lp.w, [float(v) for v in y])) < 0
                assert min(sum(lp.w[q] for q in F) for F in fam) > -1e-7
    assert n_yes > 50
