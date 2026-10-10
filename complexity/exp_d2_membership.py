"""Experiment: flow LP membership == brute-force cone membership (d = 2);
also exact 2D covering test == general LP covering test."""
import random
import sys

from d2_flow import weakly_solvable_2d
from wsolv import family, in_cone

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
stats = {"agree": 0, "yes": 0, "no": 0, "bad": 0, "fam_bad": 0}
for trial in range(400):
    T = random.randint(2, 9)
    g = random.choice([3, 5, 30])
    P = [(random.randint(1, g), random.randint(1, g)) for _ in range(T)]
    F = family(P, exact2d=True)
    if trial % 4 == 0 and T <= 7:
        if set(F) != set(family(P, exact2d=False)):
            stats["fam_bad"] += 1
            print("FAMILY exact vs LP mismatch", P)
    for _ in range(5):
        y = [random.randint(0, 4) for _ in range(T)]
        a, b = in_cone(F, y, T), weakly_solvable_2d(P, y)
        stats["yes" if a else "no"] += 1
        if a == b:
            stats["agree"] += 1
        else:
            stats["bad"] += 1
            print("MISMATCH", P, y, a, b)
print(stats)
