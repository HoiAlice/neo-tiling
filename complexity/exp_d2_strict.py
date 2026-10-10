"""Experiment: solvability (reachable sets, strict witnesses), d = 2.
DAG family with boundary points sent to the complement == brute-force reachable family;
longest path == brute force; flow LP without slack == brute-force cone membership."""
import random
import sys

from d2_flow import enumerate_family_2d, max_weight_2d, solvable_2d
from wsolv import family_2d, in_cone, max_weight

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
st = {"fam": 0, "fam_bad": 0, "w_bad": 0, "y": 0, "yes": 0, "y_bad": 0, "diff_weak": 0}
for trial in range(2000):
    T = random.randint(1, 8)
    g = random.choice([3, 4, 6, 20])
    P = [(random.randint(1, g), random.randint(1, g)) for _ in range(T)]
    F = set(family_2d(P, strict=True))
    st["fam"] += 1
    if F != enumerate_family_2d(P, strict=True):
        st["fam_bad"] += 1
        print("FAMILY MISMATCH", P)
    st["diff_weak"] += F != set(family_2d(P, strict=False))
    w = [random.randint(-5, 5) for _ in range(T)]
    if max_weight(sorted(F, key=sorted), w) != max_weight_2d(P, w, strict=True):
        st["w_bad"] += 1
        print("MAXW MISMATCH", P, w)
    if trial % 4 == 0:
        for _ in range(4):
            y = [random.randint(0, 4) for _ in range(T)]
            a, b = in_cone(sorted(F, key=sorted), y, T), solvable_2d(P, y)
            st["y"] += 1
            st["yes"] += a
            if a != b:
                st["y_bad"] += 1
                print("MEMBERSHIP MISMATCH", P, y, a, b)
print(st)
