"""Experiment: reachable family (closed coverings) for d = 2: exact point/pair test ==
family from exact minimal closed coverings of size <= 2; and for d = 3 the gadget below uses
closed coverings of size <= 3."""
import random

from covers import family_from_covers, minimal_covers
from wsolv import family_2d

random.seed(11)
bad = 0
for trial in range(300):
    T = random.randint(2, 7)
    g = random.choice([3, 5, 20])
    P = [(random.randint(1, g), random.randint(1, g)) for _ in range(T)]
    if set(family_2d(P, strict=True)) != set(family_from_covers(T, minimal_covers(P, closed=True))):
        bad += 1
        print("MISMATCH", P)
print("mismatches", bad)
