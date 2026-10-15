"""Does aggregation lose information?  BEA industries at full detail (d = 8: five capital types, two
labour types and II, all divided by the output price pGO; y = GO_Q, T = 40) versus a placebo detail.

Placebo: for every capital / labour type the deviations ln p_{k,t} - ln p_{K,t} from its aggregate
(pK or pL of the aggregate file) are permuted over the years (seeded).  The size of the detail is kept,
its link to the years is destroyed.  If the real detail lowers rho* much more than the placebo, the
drop is not the mechanical effect of more coordinates.  rho* by bisection with the exact oracle.
Output: results/aggregation.log.  Run (long, ~3 min per case):
nice -n 19 ../.venv/bin/python experiments/aggregation.py real 15 1 24 ...
nice -n 19 ../.venv/bin/python experiments/aggregation.py placebo 15:1 15:2 24:1 ...
"""

import csv
import math
import random
import sys
import time
from fractions import Fraction as F

from _common import RESULTS
from perturb import zono
from perturb.data import DATA
from perturb.exact_oracle import oracle_exact
from ratio_d3 import rho_bar

K = ["pKit", "pKsoft", "pKrd", "pKart", "pKoth"]
L = ["pLcol", "pLn"]
BASE = {"pKit": 1, "pKsoft": 1, "pKrd": 1, "pKart": 1, "pKoth": 1, "pLcol": 3, "pLn": 3, "pII": 3, "GO": 4}


def load(ind, seed=None, T=40):
    det = sorted([r for r in csv.DictReader(open(DATA / "bea_klems_detail_1963_2016.csv"))
                  if int(r["indnum"]) == ind], key=lambda r: int(r["year"]))[-T:]
    agg = {int(r["year"]): r for r in csv.DictReader(open(DATA / "bea_klems_1963_2016.csv"))
           if int(r["indnum"]) == ind}
    years = [int(r["year"]) for r in det]
    cols = []
    rnd = random.Random(seed)
    for group, ac in ((K, "pK"), (L, "pL")):
        for c in group:
            if seed is None:
                cols.append([float(r[c]) for r in det])
                continue
            dev = [math.log(float(r[c])) - math.log(float(agg[y][ac])) for r, y in zip(det, years)]
            perm = list(range(T))
            rnd.shuffle(perm)
            cols.append([math.exp(math.log(float(agg[y][ac])) + dev[perm[t]]) for t, y in enumerate(years)])
    cols.append([float(r["pII"]) for r in det])
    P = [tuple(col[t] / float(det[t]["pGO"]) for col in cols) for t in range(T)]
    return P, [F(r["GO_Q"]) for r in det], years


def run(ind, seed=None):
    P, y, years = load(ind, seed)
    names = K + L + ["pII", "GO"]
    kap, k0 = zono.default_weights(years, 8, names, base=BASE)
    rb = min(rho_bar(P, kap, k0))
    t0 = time.time()
    lo, hi, calls, _ = zono.least_wradius(P, y, kap, k0, oracle_exact, tol=1e-5)
    tag = "real" if seed is None else f"placebo seed {seed}"
    line = (f"BEA {ind:2d} d=8 {tag}: rho* in [{lo:.5f}, {hi:.5f}], rho_bar {rb:.5f}, ratio {hi / rb:.3f}, "
            f"{calls} calls, {time.time() - t0:.0f}s")
    print(line, flush=True)
    with open(RESULTS / "aggregation.log", "a") as f:
        f.write(line + "\n")


if __name__ == "__main__":
    mode, args = sys.argv[1], sys.argv[2:]
    for a in args:
        if mode == "real":
            run(int(a))
        else:
            i, s = a.split(":")
            run(int(i), int(s))
