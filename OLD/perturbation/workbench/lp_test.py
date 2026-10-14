"""Test agent's hypothesis: rho_dom at d=2 with L1 cost equals LP relaxation value.

MIP formulation:
  variables u_t, v_t for each t; cost = sum |u_t - a_t| + |v_t - b_t| (L1 in log coords).
  for each (t, s) with y_t > y_s: binary x_{t,s} ∈ {0, 1} with
     u_t - u_s <= M (1 - x) and v_t - v_s <= M x.
     x = 1 forces coord-0 constraint; x = 0 forces coord-1.

LP relaxation: x in [0, 1]. If LP = MIP for all instances, polynomial.
"""
import sys, itertools, random
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
import numpy as np
from scipy.optimize import linprog


def rho_dom_lp(P, y, strict=False, M=20.0):
    """MIP or LP for L1 rho_dom. If strict=True use binary x, else continuous."""
    T = len(P)
    a = np.log(P[:, 0]); b = np.log(P[:, 1])
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    nc = len(conflicts)
    # Variables: u^+, u^-, v^+, v^-, x. Total 4T + nc.
    nvars = 4 * T + nc
    def idx(kind, i):
        if kind == 'up': return i
        if kind == 'um': return T + i
        if kind == 'vp': return 2 * T + i
        if kind == 'vm': return 3 * T + i
        if kind == 'x':  return 4 * T + i
    c = np.zeros(nvars)
    for t in range(T):
        c[idx('up', t)] = c[idx('um', t)] = c[idx('vp', t)] = c[idx('vm', t)] = 1
    # Deviation equations: u^+ - u^- = u - a, so u = a + u^+ - u^-. We don't need explicit u.
    # Constraints: for each (t, s), coord-0 constraint and coord-1 constraint.
    #   u_t - u_s = (a_t - a_s) + (u^+_t - u^-_t) - (u^+_s - u^-_s)
    #   u_t - u_s <= M (1 - x) ⇔ (u^+_t - u^-_t) - (u^+_s - u^-_s) + M*x <= M - (a_t - a_s)
    rows = []
    rhs = []
    for k, (t, s) in enumerate(conflicts):
        row = np.zeros(nvars)
        row[idx('up', t)] = 1
        row[idx('um', t)] = -1
        row[idx('up', s)] = -1
        row[idx('um', s)] = 1
        row[idx('x', k)] = M
        rows.append(row)
        rhs.append(M - (a[t] - a[s]))
        # coord-1: v_t - v_s <= M * x
        row = np.zeros(nvars)
        row[idx('vp', t)] = 1
        row[idx('vm', t)] = -1
        row[idx('vp', s)] = -1
        row[idx('vm', s)] = 1
        row[idx('x', k)] = -M
        rows.append(row)
        rhs.append(-(b[t] - b[s]))
    A_ub = np.array(rows); b_ub = np.array(rhs)
    bounds = [(0, None)] * (4 * T) + [(0, 1)] * nc
    integrality = np.array([0] * (4 * T) + [1] * nc) if strict else None
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, integrality=integrality, method="highs")
    return res.fun, res.x


def iso_cost_l1(a, edges):
    """L1 isotonic regression with order constraints u_t <= u_s for (t, s) in edges."""
    T = len(a)
    nvars = 2 * T
    c = np.ones(nvars)  # minimize sum u^+ + u^-
    rows = []; rhs = []
    for t, s in edges:
        # u_t - u_s <= 0: (u^+_t - u^-_t) - (u^+_s - u^-_s) <= a_s - a_t
        row = np.zeros(nvars)
        row[t] = 1; row[T + t] = -1
        row[s] = -1; row[T + s] = 1
        rows.append(row); rhs.append(a[s] - a[t])
    A_ub = np.array(rows) if rows else None
    b_ub = np.array(rhs) if rhs else None
    bounds = [(0, None)] * nvars
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    return res.fun


def rho_dom_brute(P, y):
    """Enumerate sigma, compute L1 iso regression costs on each coord."""
    T = len(P)
    a = np.log(P[:, 0]); b = np.log(P[:, 1])
    conflicts = [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]
    best = float("inf")
    for sigma in itertools.product((0, 1), repeat=len(conflicts)):
        e0 = [c for c, s in zip(conflicts, sigma) if s == 0]
        e1 = [c for c, s in zip(conflicts, sigma) if s == 1]
        c0 = iso_cost_l1(a, e0)
        c1 = iso_cost_l1(b, e1)
        best = min(best, c0 + c1)
    return best


if __name__ == "__main__":
    seed = int(sys.argv[1]); T = int(sys.argv[2]); N = int(sys.argv[3])
    rng = random.Random(seed)
    mismatches = 0; errs = []
    for k in range(N):
        P = np.array([[rng.randint(1, 10), rng.randint(1, 10)] for _ in range(T)], float)
        y = np.array([rng.randint(0, 5) for _ in range(T)], float)
        if y.max() == 0: continue
        try:
            mip, _ = rho_dom_lp(P, y, strict=True)
            lp,  _ = rho_dom_lp(P, y, strict=False)
            bf       = rho_dom_brute(P, y)
            diff_bf_mip = abs(mip - bf)
            diff_mip_lp = mip - lp
            tag = " MISMATCH" if diff_mip_lp > 1e-5 else ""
            if diff_mip_lp > 1e-5: mismatches += 1; errs.append((k, mip, lp, bf, P.tolist(), y.tolist()))
            print(f"k={k} T={T} brute={bf:.4f} MIP={mip:.4f} LP={lp:.4f} gap={diff_mip_lp:+.4f}{tag}", flush=True)
        except Exception as e:
            print(f"k={k} ERROR {e}", flush=True)
    print(f"\nSummary: {mismatches}/{N} MIP > LP (LP relaxation NOT tight)")
    if errs:
        print("Sample mismatch:", errs[0])
