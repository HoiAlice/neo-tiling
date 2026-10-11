"""Experiment: DAG family == brute-force weakly reachable family (d = 2, exact)."""
import random
import sys

from d2_flow import enumerate_family_2d, max_weight_2d
from wsolv import family, max_weight

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
bad = 0
n = 0
for trial in range(3000):
    T = random.randint(1, 8)
    g = random.choice([3, 4, 6, 20])
    P = [(random.randint(1, g), random.randint(1, g)) for _ in range(T)]
    F1 = set(family(P, exact2d=True))
    F2 = enumerate_family_2d(P)
    n += 1
    if F1 != F2:
        bad += 1
        print("MISMATCH", P, sorted(map(sorted, F1 ^ F2))[:5])
        if bad > 5:
            break
    w = [random.randint(-5, 5) for _ in range(T)]
    if max_weight(sorted(F1, key=sorted), w) != max_weight_2d(P, w):
        print("MAXW MISMATCH", P, w)
        bad += 1
print("trials", n, "mismatches", bad)
