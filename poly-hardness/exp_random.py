"""Random planar instances: how often the cutting-plane method closes the gap, per cost.

Usage: ../.venv/bin/python exp_random.py [n_instances] [time_limit]
Writes results/random.txt.  A closed gap (upper - lower <= 1e-5) certifies rho: the lower
bound is the master value, the upper bound carries an exact certificate.
"""

import random
import sys
import time
from fractions import Fraction
from pathlib import Path

import perturb2d as pt
import planar

OUT = Path(__file__).resolve().parent / "results"


def main(n, limit):
    OUT.mkdir(exist_ok=True)
    rng = random.Random(11)
    inst = []
    for _ in range(n):
        T = rng.randint(3, 8)
        P = [(Fraction(rng.randint(1, 8)), Fraction(rng.randint(1, 8))) for _ in range(T)]
        y = [Fraction(rng.randint(0, 5)) for _ in range(T)]
        inst.append((P, y))
    lines = [f"{n} instances, T in [3, 8], prices on an 8x8 grid, time limit {limit:.0f} s"]
    for name in ("log", "pi", "eps"):
        cost = pt.COSTS[name]
        closed, zero, pair, times = 0, 0, 0, []
        for P, y in inst:
            t0 = time.time()
            r = pt.solve(P, y, cost, time_limit=limit)
            assert planar.check_certificate(r.Q, y, r.certificate)
            assert r.lower <= r.upper + 1e-7
            times.append(time.time() - t0)
            ndom = sum(1 for t in range(len(y)) for s in range(len(y)) if y[t] > y[s])
            closed += r.upper - r.lower <= 1e-5
            zero += r.upper <= 1e-9
            pair += r.cuts > ndom
        times.sort()
        line = (f"{cost.name}: closed {closed}/{n} (rho = 0: {zero}, pair cuts needed: {pair}),"
                f" median {times[n // 2]:.2f} s, max {times[-1]:.1f} s")
        print(line, flush=True)
        lines.append(line)
    (OUT / "random.txt").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 100,
         float(sys.argv[2]) if len(sys.argv) > 2 else 60.0)
