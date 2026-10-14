"""Sweep random d=2 instances: compute rho_full and rho_dom, report."""
import sys, random, time, json
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from fast_d2 import rho_dom_exact, rho_full_small

def rand_instance(T, rng, grid=5, max_y=5):
    while True:
        P = np.array([[rng.randint(1, grid), rng.randint(1, grid)] for _ in range(T)], float)
        y = np.array([rng.randint(0, max_y) for _ in range(T)], float)
        if y.max() > 0: return P, y

def summarize(seed, T, N, max_fam):
    rng = random.Random(seed); out = []
    for k in range(N):
        P, y = rand_instance(T, rng)
        try:
            t0 = time.time(); rf = rho_full_small(P, y, max_family_size=max_fam); tf = time.time()-t0
            t0 = time.time(); rd = rho_dom_exact(P, y); td = time.time()-t0
            gap = rf.rho - rd.rho
            tag = " GAP" if gap > 1e-5 else ""
            print(f"T={T} k={k:2d} rho={rf.rho:.6f} rho_dom={rd.rho:.6f} gap={gap:+.6f} tf={tf:.1f}s td={td:.1f}s{tag}", flush=True)
            out.append(dict(T=T, k=k, P=P.tolist(), y=y.tolist(), rho=rf.rho, rho_dom=rd.rho, gap=gap,
                            family=[sorted(S) for S in (rf.family or [])],
                            sigma=rd.sigma, conflicts=rd.conflicts))
        except Exception as e:
            print(f"T={T} k={k} ERROR {e}", flush=True)
    return out

if __name__ == "__main__":
    seed, T, N, mf = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 4
    rows = summarize(seed, T, N, mf)
    with open(f"/private/tmp/claude-501/-Users-olegoleg-Code-neo-tiling/75c6aa21-1546-4d6f-8f41-0b1e36d1074e/scratchpad/sweep_d2_T{T}_s{seed}.json", "w") as f:
        json.dump(rows, f)
    gaps = [r for r in rows if r["gap"] > 1e-5]
    print(f"\nSummary T={T}: {len(gaps)}/{len(rows)} have rho > rho_dom; max gap = {max((r['gap'] for r in rows), default=0):.4f}", flush=True)
