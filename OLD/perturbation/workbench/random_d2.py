"""Random d=2 instances: compare rho vs rho_dom. Report any gap and the structure."""
import sys, random, time, json
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from explore_d2 import rho_small, rho_dom, TRIANGLE_P, TRIANGLE_Y

def rand_instance(T, rng, grid=5):
    while True:
        P = np.array([[rng.randint(1, grid), rng.randint(1, grid)] for _ in range(T)], float)
        y = np.array([rng.randint(0, 5) for _ in range(T)], float)
        if P.min() > 0 and y.max() > 0: return P, y

def summarize(seed, T, N, max_fam):
    rng = random.Random(seed); out = []
    for k in range(N):
        P, y = rand_instance(T, rng)
        try:
            t0 = time.time()
            r = rho_small(P, y, max_family_size=max_fam)
            trs = time.time() - t0
            t0 = time.time()
            rd = rho_dom(P, y)
            trd = time.time() - t0
            gap = r.rho - rd
            print(f"T={T} k={k} P={P.tolist()} y={y.tolist()}  rho={r.rho:.6f} rho_dom={rd:.6f} gap={gap:+.6f}  tr={trs:.1f}s td={trd:.1f}s  |F|={len(r.family) if r.family else None}", flush=True)
            out.append(dict(T=T, k=k, P=P.tolist(), y=y.tolist(), rho=r.rho, rho_dom=rd, gap=gap, trs=trs, trd=trd, family=[list(S) for S in (r.family or [])]))
        except Exception as e:
            print(f"T={T} k={k} ERROR {e}", flush=True)
    return out

if __name__ == "__main__":
    seed = int(sys.argv[1]); T = int(sys.argv[2]); N = int(sys.argv[3])
    max_fam = int(sys.argv[4]) if len(sys.argv) > 4 else min(T, 4)
    rows = summarize(seed, T, N, max_fam)
    with open(f"/private/tmp/claude-501/-Users-olegoleg-Code-neo-tiling/75c6aa21-1546-4d6f-8f41-0b1e36d1074e/scratchpad/random_d2_T{T}_s{seed}.json", "w") as f:
        json.dump(rows, f)
