"""Experiment: the d = 3 gadget. Checks
 (a) weakly reachable S containing z and all heavy points <-> independent sets (exact);
 (b) y = (1, 1 - s, 1) weakly solvable  <->  s in STAB(G)  on test points s."""
import itertools
from fractions import Fraction as Fr

from covers import family_from_covers, minimal_covers
from d3_reduction import build
from wsolv import in_cone

GRAPHS = {
    "K3": ([(0, 0), (4, 0), (2, 3)], [(0, 1), (1, 2), (0, 2)]),
    "C5": ([(0, 3), (3, 5), (6, 3), (5, 0), (1, 0)], [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
    "P4+": ([(0, 0), (3, 0), (6, 0), (3, 3), (3, 6)], [(0, 1), (1, 2), (1, 3), (3, 4)]),
    "bowtie": ([(0, 0), (0, 4), (3, 2), (6, 0), (6, 4)],
               [(0, 1), (0, 2), (1, 2), (2, 3), (2, 4), (3, 4)]),
}


def independent(I, edges):
    return not any(u in I and v in I for u, v in edges)


def in_stab(s, n, edges):
    sets = [frozenset(I) for k in range(n + 1) for I in itertools.combinations(range(n), k)
            if independent(I, edges)]
    # s in conv(stable sets) <=> (s, 1) in cone{(1_I, 1)}
    lifted = [frozenset(set(I) | {n}) for I in sets]
    return in_cone(lifted, list(s) + [1], n + 1)


def main():
  for name, (dr, E) in GRAPHS.items():
    P, idx = build(dr, E)
    T, n = len(P), len(dr)
    covers = minimal_covers(P)
    F = family_from_covers(T, covers)
    heavy = set(idx["heavy"].values())
    rew = idx["reward"]
    got = set()
    for S in F:
        if 0 in S and heavy <= S:
            got.add(frozenset(i for i, r in enumerate(rew) if r not in S))
    want = {frozenset(I) for k in range(n + 1) for I in itertools.combinations(range(n), k)
            if independent(I, E)}
    nonempty_without_z = sum(1 for S in F if S and 0 not in S)
    sizes = sorted({len(R) for _, R in covers})
    print(f"{name}: T={T} |F|={len(F)} covers={len(covers)} sizes={sizes} "
          f"indep-match={got == want} nonempty-without-z={nonempty_without_z}")
    # membership tests
    tests = [[Fr(1, 2)] * n, [Fr(2, 5)] * n, [Fr(1, 3)] * n, [Fr(1, 4)] * n]
    tests += [[Fr((i * 7 + j) % 5, 5) for i in range(n)] for j in range(4)]
    agree = 0
    for s in tests:
        y = [0.0] * T
        y[0] = 1.0
        for h in heavy:
            y[h] = 1.0
        for i, r in enumerate(rew):
            y[r] = float(1 - s[i])
        a, b = in_cone(F, y, T), in_stab([float(v) for v in s], n, E)
        agree += a == b
        if a != b:
            print("   MISMATCH s=", s, a, b)
    print(f"   membership agree {agree}/{len(tests)}")


if __name__ == "__main__":
    main()
