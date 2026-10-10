"""Experiment: running time of the d = 2 flow LP on random instances of growing size."""
import random
import time

from d2_flow import build_dag, weakly_solvable_2d

random.seed(7)
print(f"{'T':>4} {'nodes':>7} {'arcs':>8} {'sec':>7} solvable")
for T in [10, 20, 30, 40, 60, 80]:
    P = [(random.randint(1, 10 * T), random.randint(1, 10 * T)) for _ in range(T)]
    y = [random.randint(1, 5) for _ in range(T)]
    t0 = time.time()
    g = build_dag(P)
    ok = weakly_solvable_2d(P, y)
    print(f"{T:>4} {len(g.nodes):>7} {len(g.arcs):>8} {time.time() - t0:>7.2f} {ok}")
