"""Experiment: family from exact minimal covers (|R| <= d) == brute LP family, d = 2, 3, 4."""
import random

from covers import family_from_covers, minimal_covers
from wsolv import family

random.seed(5)
bad = 0
for trial in range(150):
    d = random.choice([2, 3, 3, 4])
    T = random.randint(2, 7)
    g = random.choice([3, 5, 20])
    P = [tuple(random.randint(1, g) for _ in range(d)) for _ in range(T)]
    F1 = set(family(P, exact2d=False))
    F2 = set(family_from_covers(T, minimal_covers(P)))
    if F1 != F2:
        bad += 1
        print("MISMATCH", d, P)
print("mismatches", bad)
