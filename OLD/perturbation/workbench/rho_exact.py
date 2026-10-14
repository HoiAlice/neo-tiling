"""Compute rho(P, y) at d=2 exactly for small T via family enumeration + SCIP."""
import sys, itertools, math
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from pyscipopt import Model, quicksum
from scipy.optimize import linprog
import planar

TOL = 1e-9

def pi(p, q): return max(q/p, p/q) - 1
def total_pi(P, Q): return float(sum(pi(P[t,i], Q[t,i]) for t in range(len(P)) for i in range(2)))

def check_wsolv_planar(Q, y, strict=False):
    """Use poly-hardness/planar.py (fast chain LP) to check weak solvability."""
    from fractions import Fraction
    T = len(Q)
    Qf = [tuple(Fraction(float(v)).limit_denominator(10**12) for v in row) for row in Q]
    yf = [Fraction(float(v)).limit_denominator(10**12) for v in y]
    return planar.flow_lp(planar.chain_graph(Qf, strict=strict), yf, strict=strict).feasible

def rho_exact(P, y, D=50.0, time_limit=120, max_fam=5):
    """Compute rho(P, y) by enumerating candidate families."""
    T = len(P)
    subsets = [frozenset(S) for n in range(1, T+1) for S in itertools.combinations(range(T), n)]
    best_val, best_Q, best_F = math.inf, None, None
    for k in range(1, max_fam + 1):
        for F in itertools.combinations(subsets, k):
            # LP check: is y in cone of indicators?
            A = np.array([[1.0 if t in S else 0.0 for S in F] for t in range(T)])
            res = linprog(np.zeros(len(F)), A_eq=A, b_eq=np.asarray(y, float), bounds=[(0, None)] * len(F), method="highs")
            if res.status != 0: continue
            # Convex-with-bilinear-witness subproblem (SCIP)
            m = Model(); m.hideOutput()
            lo, hi = 1 / (1 + D), 1 + D
            a = {(t, i): m.addVar(lb=lo, ub=hi) for t in range(T) for i in range(2)}
            g = {(t, i): m.addVar(lb=0, ub=D) for t in range(T) for i in range(2)}
            for t in range(T):
                for i in range(2):
                    m.addCons(g[t, i] >= a[t, i] - 1)
                    m.addCons(g[t, i] >= 1 / a[t, i] - 1)
            for kk, S in enumerate(F):
                others = [s for s in range(T) if s not in S]
                for t in S:
                    lam = m.addVar(f"lam_{kk}_{t}", lb=0, ub=1)
                    for s in others:
                        d0 = P[s, 0] * a[s, 0] - P[t, 0] * a[t, 0]
                        d1 = P[s, 1] * a[s, 1] - P[t, 1] * a[t, 1]
                        m.addCons(lam * d0 + (1 - lam) * d1 >= 0)
            m.setObjective(quicksum(g.values()))
            m.setParam("limits/time", time_limit); m.setParam("limits/gap", 1e-7); m.setParam("numerics/feastol", 1e-9)
            m.optimize()
            if m.getNSols() == 0: continue
            A2 = np.array([[m.getVal(a[t, i]) for i in range(2)] for t in range(T)])
            Q = P * A2
            val = total_pi(P, Q)
            if val < best_val - 1e-10:
                best_val, best_Q, best_F = val, Q, list(F)
    return best_val, best_Q, best_F

if __name__ == "__main__":
    # Triangle sanity
    P = np.array([[4,1],[3,3],[1,4]], float); y = np.array([1,5,3], float)
    v, Q, F = rho_exact(P, y, max_fam=4)
    print(f"triangle rho = {v:.6f} (expected 0.4)  F = {[sorted(S) for S in F]}")
    print(f"   Q = {Q.tolist()}")
