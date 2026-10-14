"""Weighted benchmark 1: d=2 real data, flow vs CG inside zono.least_wradius.

Output of the final run: results/bench_d2_real.log.  Run: ../.venv/bin/python experiments/bench_d2_real.py
"""
import time

import _common  # noqa: F401
from perturb import proj, zono
from perturb.data import load_bea, load_us_d2
from perturb.milp_oracle import oracle_cg

cases = []
P, y, years = load_us_d2()
cases.append(("US T=26", [tuple(float(c) for c in p) for p in P], y, years))
for ind in (1, 6, 12, 15, 24, 27, 31, 46, 49, 63):
    P, y, years = load_bea(ind, d=2, T=40)
    cases.append((f"BEA {ind}", P, y, years))

for name, P, y, years in cases:
    kap, k0 = zono.default_weights(years, 2, ["K", "L", "II"])
    out = {"case": name, "T": len(P)}; br = {}
    for on, orc in [("flow", lambda W, lo, hi: proj.oracle_flow(W, lo, hi, certify=False)),
                    ("cg", lambda W, lo, hi: oracle_cg(W, lo, hi, time_limit=600))]:
        times, its = [], []
        def w(W, lo, hi, orc=orc, on=on):
            t0 = time.time()
            try: return orc(W, lo, hi)
            finally:
                times.append(time.time() - t0)
                if on == "cg": its.append(oracle_cg.last_stats["iterations"])
        t0 = time.time()
        try:
            lo_, hi_, calls, ans = zono.least_wradius(P, y, kap, k0, w, tol=1e-6)
            br[on] = (lo_, hi_)
            out[on] = {"rho": (round(lo_, 6), round(hi_, 6)), "total": round(time.time() - t0, 1), "max_call": round(max(times), 2),
                       "calls": calls, "ambig": sum(a[1] == "AMBIG" for a in ans)}
            if its: out[on]["max_iter"] = max(its)
        except Exception as e:
            out[on] = f"ERR {type(e).__name__}: {e}"[:150]
    if len(br) == 2:
        out["agree"] = abs(br["flow"][1] - br["cg"][1]) <= 2e-6 and abs(br["flow"][0] - br["cg"][0]) <= 2e-6
    print(out, flush=True)
