"""rho_dom via MILP (HiGHS) with tangent-cut cost, polished by exact convex solve; full-weak-solvability check."""
import sys, itertools, math
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/perturbation/experiments")
sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
from iso_scipy import iso_cost
import planar
from fractions import Fraction

def cuts_points():
    pts = [0.0]
    d = 0.0
    while d < 4:
        d += 0.01 if d < 0.5 else (0.05 if d < 1.5 else 0.25)
        pts += [d, -d]
    return pts
CP = cuts_points()

def conflicts_of(y):
    T = len(y)
    return [(t, s) for t in range(T) for s in range(T) if y[t] > y[s]]

def solve_dom(a, y, fixed=None, conflicts=None, want_sigma=False, time_limit=60):
    """a: T x 2 log-coords. conflicts (t,s): q_t <= q_s in some coord. fixed: dict conflict index -> coord.
    returns (lower bound value from MILP, sigma, exact cost after polishing, u)"""
    T = len(a)
    if conflicts is None: conflicts = conflicts_of(y)
    C = len(conflicts)
    nu = 2 * T; ng = 2 * T
    nz = C
    n = nu + ng + nz
    rows = []; lo = []; hi = []
    A = lil_matrix((len(CP) * ng + 2 * C * 2 + 10, n)); r = 0
    # tangent cuts: g >= e^{|d0|}*(sgn... ) ; for d0: g >= e^{|d0|}(sgn(d0)(d-d0)+1) - 1 where d = u - a
    for t in range(T):
        for i in range(2):
            ui = 2 * t + i; gi = nu + ui
            for d0 in CP:
                s = 1 if d0 >= 0 else -1
                # g - e^{|d0|}*s*(u - a) >= e^{|d0|}(1 - s*d0) - 1
                e = math.exp(abs(d0))
                A[r, gi] = 1; A[r, ui] = -e * s
                rows.append(r); lo.append(e * (1 - s * d0) - 1 - e * s * a[t][i] + 0.0); hi.append(np.inf)
                # careful: g - e s u >= e(1-s d0) -1 - e s a
                r += 1
    M = 40.0
    for k, (t, s) in enumerate(conflicts):
        zi = nu + ng + k
        for i in range(2):
            # u_t^i - u_s^i <= M (1 - [sigma=i]) ; sigma=1 means z=1
            ut = 2 * t + i; us = 2 * s + i
            # i=1: u_t - u_s + M z <= M ; i=0: u_t - u_s - M z <= 0
            A[r, ut] = 1; A[r, us] = -1
            if i == 1:
                A[r, zi] = M; rows.append(r); lo.append(-np.inf); hi.append(M)
            else:
                A[r, zi] = -M; rows.append(r); lo.append(-np.inf); hi.append(0.0)
            r += 1
    A = A[:r].tocsr()
    c = np.zeros(n); c[nu:nu + ng] = 1
    lb = np.full(n, -np.inf); ub = np.full(n, np.inf)
    for t in range(T):
        for i in range(2):
            lb[2*t+i] = a[t][i] - 4; ub[2*t+i] = a[t][i] + 4
    lb[nu:nu+ng] = 0; ub[nu:nu+ng] = 60
    lb[nu+ng:] = 0; ub[nu+ng:] = 1
    if fixed:
        for k, v in fixed.items():
            lb[nu+ng+k] = ub[nu+ng+k] = v
    integrality = np.zeros(n); integrality[nu+ng:] = 1
    res = milp(c, constraints=LinearConstraint(A, lo, hi), bounds=Bounds(lb, ub), integrality=integrality,
               options=dict(time_limit=time_limit, mip_rel_gap=1e-9))
    if res.x is None: return None
    sigma = [int(round(v)) for v in res.x[nu+ng:]]
    # polish exactly
    edges = [[], []]
    for (t, s), i in zip(conflicts, sigma): edges[i].append((t, s))
    c0, u0 = iso_cost(a[:, 0], edges[0]); c1, u1 = iso_cost(a[:, 1], edges[1])
    return res.fun, sigma, c0 + c1, np.column_stack([u0, u1])

def pi_cost(a, u):
    return float(np.sum(np.exp(np.abs(u - a)) - 1))

def weakly_solvable(P, y, relax=1e-7):
    """Full weak solvability at Q=P (rows are points) via flow LP. relax shrinks nothing; uses closure."""
    Pf = [tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in P]
    yf = [Fraction(float(v)).limit_denominator(10**9) for v in y]
    return planar.flow_lp(Pf, yf, strict=False).feasible

def polish_margin(a, conflicts, sigma, m=1e-6):
    """exact convex solve with strict margin u_t <= u_s - m on chosen coordinate; returns cost,u"""
    from scipy.optimize import minimize
    T=len(a); a=np.asarray(a,float)
    x0=a.flatten()
    def f(x): return np.sum(np.exp(np.abs(x-a.flatten()))-1)
    def fp(x):
        d=x-a.flatten(); return np.exp(np.abs(d))*np.sign(d)
    cons=[]
    for (t,s),i in zip(conflicts,sigma):
        v=np.zeros(2*T); v[2*s+i]=1; v[2*t+i]=-1
        cons.append({"type":"ineq","fun":lambda x,v=v:v@x-m,"jac":lambda x,v=v:v})
    res=minimize(f,x0,jac=fp,constraints=cons,method="SLSQP",options=dict(ftol=1e-14,maxiter=2000))
    return float(res.fun), res.x.reshape(T,2)
