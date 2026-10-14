"""Synthetic d = 2 instances: one box-oracle call, flow LP (decision only) vs column generation.

Output of the final run: results/bench_d2_synthetic.log.  Run: ../.venv/bin/python experiments/bench_d2_synthetic.py
"""
import math, random, time
from fractions import Fraction as F

import _common  # noqa: F401
from perturb import proj, zono
from perturb.milp_oracle import oracle_cg

def q(x):
    return F(x).limit_denominator(10**6)

def family(name, T, rnd):
    if name == "A_random":
        P = [(math.exp(rnd.uniform(-1, 1)), math.exp(rnd.uniform(-1, 1))) for _ in range(T)]
    elif name in ("B_concave", "E_concave_randy"):
        P = [(1 + math.cos(a) + rnd.gauss(0, 1e-3), 1 + math.sin(a) + rnd.gauss(0, 1e-3))
             for a in sorted(rnd.uniform(0.05, math.pi / 2 - 0.05) for _ in range(T))]
    elif name == "C_convex":
        P = [(math.exp(u), math.exp(-u) * (1 + rnd.gauss(0, 1e-3))) for u in sorted(rnd.uniform(-1, 1) for _ in range(T))]
    elif name == "D_grid":
        m = max(2, int(math.isqrt(T)) + 1)
        P = [(1 + rnd.randrange(m), 1 + rnd.randrange(m)) for _ in range(T)]
    P = [(q(a), q(b)) for a, b in P]
    if name == "E_concave_randy":
        y = [F(rnd.randint(1, 1000)) for _ in range(T)]
    else:
        y = [F(rnd.randint(0, 10)) for _ in range(T)]
    return P, y

rnd = random.Random(1)
for T in (20, 30, 40, 50, 60):
    for name in ("A_random", "B_concave", "C_convex", "D_grid", "E_concave_randy"):
        P, y = family(name, T, rnd)
        kap, k0 = zono.default_weights(list(range(T)), 2, ["K", "L", "II"])
        lo, hi = proj.box_bounds(T, y)
        W = zono.wcorners(P, kap, k0, 0.05, True)
        out = {"T": T, "fam": name}
        t0 = time.time(); a = proj.oracle_flow(W, lo, hi, certify=False); out["flow"] = round(time.time() - t0, 2)
        t0 = time.time()
        try:
            b = oracle_cg(W, lo, hi, time_limit=600).feasible
            out["cg"] = round(time.time() - t0, 2); out["it"] = oracle_cg.last_stats["iterations"]
            out["agree"] = bool(a) == b; out["feas"] = bool(a)
        except Exception as e:
            out["cg"] = f"ERR {e}"[:80]
        print(out, flush=True)
