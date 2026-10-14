"""Meet-property experiment: is R = {r : feasible(r)} closed under coordinatewise min?

Random tiny instances (not weakly solvable at the observed prices).  For each instance: sample
boundary points r = ceil_6(s w) of R along random nonnegative directions w (some coordinates 0), s
the least scale found by bisection, then test min(r, r') for all pairs.  A VIOLATION is: r, r'
feasible (checked), min(r, r') infeasible (safe-rounded query: inner AND outer box say NO).
Also runs the exact `profile` and counts the instances where it had to branch
(meet_violated_at_stage nonempty).  Everything is a function of the seed.

Run: nice -n 19 ../.venv/bin/python experiments/meet_check.py [seconds_total=480]
"""

import math
import random
import sys
import time
from fractions import Fraction as F

from _common import ROOT  # noqa: E402

sys.path.insert(0, str(ROOT / "tests"))
from perturb import lexprofile as pr  # noqa: E402
from perturb import proj  # noqa: E402
from test_zono import hard_inst  # noqa: E402


def flow(W, lo, hi):
    return proj.oracle_flow(W, lo, hi, certify=False)


def ceil6(x):
    return math.ceil(x * 1e6 - 1e-9) / 1e6


def boundary_point(P, y, k, k0, oracle, rnd, tol=1e-5):
    T = len(P)
    while True:
        w = [0.0 if rnd.random() < 0.3 else math.exp(rnd.gauss(0, 0.7)) for _ in range(T)]
        if any(w):
            w = [x / max(w) for x in w]
            break

    def ok(s):
        return pr.rfeasible(P, y, k, k0, [ceil6(s * x) for x in w], oracle)[0]
    b = 0.25
    while not ok(b):
        b *= 2
        if b > 2:
            return None
    a = 0.0
    while b - a > tol:
        m = (a + b) / 2
        a, b = (a, m) if ok(m) else (m, b)
    return [ceil6(b * x) for x in w]


def run_config(name, d, T, oracle, nvec, budget, seed0):
    t_end = time.time() + budget
    stats = {"instances": 0, "pairs": 0, "violations": 0, "branched": 0, "profiles": 0,
             "calls_profile": 0}
    examples = []
    seed = seed0
    while time.time() < t_end:
        seed += 1
        rnd = random.Random(seed)
        P, y, k, k0 = hard_inst(rnd, T, d)
        vecs = []
        for _ in range(nvec):
            v = boundary_point(P, y, k, k0, oracle, rnd)
            if v is not None:
                vecs.append(v)
        stats["instances"] += 1
        for i in range(len(vecs)):
            for j in range(i + 1, len(vecs)):
                m = [min(a, b) for a, b in zip(vecs[i], vecs[j])]
                stats["pairs"] += 1
                if not pr.rfeasible(P, y, k, k0, m, oracle)[0]:
                    stats["violations"] += 1
                    examples.append({"config": name, "seed": seed, "d": d, "T": T, "P": P, "y": y,
                                     "kappa": k, "kappa0": k0, "r": vecs[i], "r2": vecs[j], "min": m})
        out = pr.profile(P, y, k, k0, oracle)
        stats["profiles"] += 1
        stats["calls_profile"] += out["calls"]
        if out["meet_violated_at_stage"]:
            stats["branched"] += 1
            examples.append({"config": name, "seed": seed, "branching profile": out["r"],
                             "stages": out["stages"]})
    return stats, examples


def fmt(v):
    return "(" + ", ".join(str(x) for x in v) + ")"


def main():
    total = float(sys.argv[1]) if len(sys.argv) > 1 else 480
    configs = [("flow d=2 T=3", 2, 3, flow, 8, 0.12), ("flow d=2 T=4", 2, 4, flow, 8, 0.2),
               ("flow d=2 T=5", 2, 5, flow, 8, 0.2), ("brute d=2 T=3", 2, 3, proj.oracle_brute, 6, 0.2),
               ("brute d=3 T=3", 3, 3, proj.oracle_brute, 5, 0.28)]
    allex = []
    print("config | instances | pairs | meet violations | profiles that branched")
    for i, (name, d, T, orc, nvec, frac) in enumerate(configs):
        st, ex = run_config(name, d, T, orc, nvec, total * frac, 1000 * i)
        allex += ex
        print(f"{name} | {st['instances']} | {st['pairs']} | {st['violations']} | {st['branched']}"
              f" (of {st['profiles']})", flush=True)
    viol = [e for e in allex if "min" in e]
    if viol:
        e = viol[0]
        print("\nFIRST COUNTEREXAMPLE (", e["config"], "seed", e["seed"], ")")
        print("d =", e["d"], " T =", e["T"])
        print("P  =", [fmt(p) for p in e["P"]])
        print("y  =", [str(v) for v in e["y"]])
        print("kappa =", e["kappa"], " kappa0 =", e["kappa0"])
        print("r   =", e["r"])
        print("r'  =", e["r2"])
        print("min =", e["min"], "(infeasible), r and r' feasible")
    for e in allex:
        if "branching profile" in e:
            print("\nbranching profile example:", e["config"], "seed", e["seed"], e["branching profile"],
                  e["stages"])
            break


if __name__ == "__main__":
    main()
