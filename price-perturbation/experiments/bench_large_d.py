"""Column generation at d >= 3 on real data: bisection in rho (no breakpoint enumeration).

Output of the final run: results/bench_large_d.log.  Run: ../.venv/bin/python experiments/bench_large_d.py
"""
import time

import _common  # noqa: F401
from perturb import zono
from perturb.data import load_bea, load_berndt_wood, load_us_d3
from perturb.milp_oracle import oracle_cg


def bea(ind, d, T=40):
    return load_bea(ind, d, T)[:2]


cases = [("US EU-KLEMS d=3 T=26", *load_us_d3()[:2], ["K", "L", "II", "GO"], {"K": 1, "L": 3, "II": 3, "GO": 4}),
         ("Berndt-Wood d=4 T=25", *load_berndt_wood()[:2], ["K", "L", "E", "M", "Y"], {"K": 1, "L": 3, "E": 2, "M": 3, "Y": 4})]
B4 = ["K", "Lcol", "Ln", "II", "GO"]; B4b = {"K": 1, "Lcol": 3, "Ln": 3, "II": 3, "GO": 4}
B7 = ["Kit", "Ksoft", "Krd", "Kart", "Koth", "Lcol", "Ln", "II"]
B7b = {"Kit": 1, "Ksoft": 1, "Krd": 1, "Kart": 1, "Koth": 1, "Lcol": 3, "Ln": 3, "II": 3}
for ind in (12, 24, 46, 6):
    cases.append((f"BEA {ind} d=4 T=40", *bea(ind, 4), B4, B4b))
for ind in (12, 24, 46, 6):
    cases.append((f"BEA {ind} d=7 T=40", *bea(ind, 7), B7, B7b))

for name, P, y, names, base in cases:
    times, its = [], []
    def orc(W, lo, hi):
        t0 = time.time()
        try: return oracle_cg(W, lo, hi, time_limit=600)
        finally:
            times.append(time.time() - t0); its.append(oracle_cg.last_stats["iterations"])
    kap, k0 = zono.default_weights(list(range(len(P))), len(P[0]), names, base=base)
    t0 = time.time()
    try:
        a, b, calls, ans = zono.least_wradius(P, y, kap, k0, orc, tol=1e-5)
        print({"case": name, "rho": (round(a, 6), round(b, 6)), "calls": calls, "ambig": sum(x[1] == "AMBIG" for x in ans), "total": round(time.time() - t0, 1),
               "max_call": round(max(times), 2), "iter_max": max(its), "iter_mean": round(sum(its) / len(its), 1)}, flush=True)
    except Exception as e:
        print({"case": name, "error": f"{type(e).__name__}: {e}", "calls": len(times), "total": round(time.time() - t0, 1)}, flush=True)
