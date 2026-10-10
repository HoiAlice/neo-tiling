"""Experiment: the d = 3 gadget for solvability (reachable sets, closed coverings).
Heights |a_u - a_v|^2 (1/4 + gamma/2).  Checks (a) reachable sets containing z and all heavy
points <-> complements of independent sets; (b) y = (1, 1 - s, 1) solvable <-> s in STAB(G)."""
import itertools
from fractions import Fraction as Fr

from covers import family_from_covers, minimal_covers
from d3_reduction import build
from exp_d3_reduction import GRAPHS, in_stab, independent
from wsolv import in_cone

for name, (dr, E) in GRAPHS.items():
    P, idx = build(dr, E, strict=True)
    T, n = len(P), len(dr)
    covers = minimal_covers(P, closed=True)
    F = family_from_covers(T, covers)
    heavy = set(idx["heavy"].values())
    rew = idx["reward"]
    got = {frozenset(i for i, r in enumerate(rew) if r not in S)
           for S in F if 0 in S and heavy <= S}
    want = {frozenset(I) for k in range(n + 1) for I in itertools.combinations(range(n), k)
            if independent(I, E)}
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
        agree += in_cone(F, y, T) == in_stab([float(v) for v in s], n, E)
    print(f"{name}: T={T} |Sp|={len(F)} closed covers={len(covers)} "
          f"indep-match={got == want} membership agree {agree}/{len(tests)}")
