"""Independent check: perturb2d (cost pi) against the SCIP covering-cut method of
code/perturbation (general d, exact MINLP master), on random planar instances.

Usage: ../.venv/bin/python exp_compare_scip.py [n_instances]
"""

import random
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "code"))
from perturbation.cuts import solve_cuts  # noqa: E402
from perturbation.prep import Problem, prepare  # noqa: E402

import perturb2d as pt  # noqa: E402


def main(n):
    rng = random.Random(7)
    worst = 0.0
    for k in range(n):
        T = rng.randint(3, 6)
        P = [(Fraction(rng.randint(1, 6)), Fraction(rng.randint(1, 6))) for _ in range(T)]
        y = [Fraction(rng.randint(0, 4)) for _ in range(T)]
        mine = pt.solve(P, y, pt.PI, time_limit=300)
        ref = solve_cuts(prepare(Problem(tuple(P), tuple(y))), time_limit=300)
        # intervals [lower, upper] must overlap
        lo, hi = max(mine.lower, ref.bound), min(mine.upper, ref.upper)
        bad = lo > hi + 1e-5
        worst = max(worst, lo - hi)
        print(f"{k}: T={T} perturb2d [{mine.lower:.6f}, {mine.upper:.6f}]  "
              f"scip [{ref.bound:.6f}, {ref.upper:.6f}]  {'MISMATCH' if bad else 'ok'}",
              flush=True)
    print("worst overlap violation", worst)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 30)
