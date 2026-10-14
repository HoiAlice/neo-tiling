"""l1.py -- phi(r)=|r| (L1 in logs): exact-LP branch and bound over routings (HiGHS, float).  Library tables as in run_tables.py.
Degeneracy test: which violated patterns have zero excess."""
import sys, os, math, itertools, time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import phi_dual as pd
sys.modules['np_dual'] = pd
sys.path.insert(0, '/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad')
pd.set_phi('pow', p=1.5)    # only for Block construction
H = 4 * math.log(1.05); pd.H = H

def lp(blk, assign):
    T = blk.T; n = 2 * T
    # vars: x (n), u (n) >= |x - A|;  min sum u
    A = blk.A.reshape(-1)
    rows = []; rhs = []
    M = lil_matrix((2 * n + len(assign), 2 * n)); b = np.zeros(2 * n + len(assign))
    for i in range(n):
        M[2 * i, i] = 1; M[2 * i, n + i] = -1; b[2 * i] = A[i]          # x - u <= A
        M[2 * i + 1, i] = -1; M[2 * i + 1, n + i] = -1; b[2 * i + 1] = -A[i]  # -x - u <= -A
    for r, (k, c) in enumerate(sorted(assign.items())):
        a_, b_ = blk.conf[k]
        M[2 * n + r, 2 * a_ + c] = 1; M[2 * n + r, 2 * b_ + c] = -1
    cost = np.concatenate([np.zeros(n), np.ones(n)])
    res = linprog(cost, A_ub=M.tocsr(), b_ub=b, bounds=[(None, None)] * n + [(0, None)] * n, method='highs')
    x = res.x[:n].reshape(T, 2)
    return res.fun, x

def bb(blk, fixed, tol=1e-9):
    best = [float('inf')]; lo = [float('inf')]
    stack = [dict(fixed)]
    while stack:
        asg = stack.pop()
        val, x = lp(blk, asg)
        if val >= best[0] - tol: lo[0] = min(lo[0], val); continue
        v = pd.violated(blk, asg, x, tol=1e-8)
        if v is None:
            best[0] = val; lo[0] = min(lo[0], val); continue
        for c in (0, 1):
            a2 = dict(asg); a2[v[1]] = c; stack.append(a2)
    return best[0], best[0]

def table(sw, terms, rels):
    blk = pd.Block(sw)
    res = {}
    for p in itertools.product((0, 1), repeat=len(terms)):
        res[p] = bb(blk, {blk.own[i]: b for i, b in zip(terms, p)})
    ix = {t: k for k, t in enumerate(terms)}
    def viol(p): return sum(c for (i, j, k, c) in rels if ((p[ix[i]] == p[ix[j]]) != (k == 'eq')))
    SB = sum(2 * (s[2] * H / 2) for s in sw)   # B(d) = 2 phi(d h/2) = d h
    sat = [p for p in res if viol(p) == 0]; S = min(res[p][0] for p in sat)
    ex = {p: res[p][0] - S for p in res}
    return dict(S=S, SB=SB, X=S - SB, ex=ex, viol=viol, nsat=len(sat))

if __name__ == '__main__':
    from np_pair_exact import U
    from np_chain import uchain, vchain
    from np_cross import crossing
    from np_star import star
    print("h = %.6f ; unit h" % H)
    for a in (3.0, 3.75, 3.99):
        r = table([U(0, 0), U(a, -a)], [0, 1], [(0, 1, 'ne', 1)])
        print("U pair a=%.2f: S-sumB = %.2e ; excess by pattern %s   (natural J would be %.4f)" % (a, r['X'], {p: round(v, 9) for p, v in r['ex'].items()}, (4 - a) * H))
    for n in (2, 3):
        r = table(vchain(n), list(range(n)), [(i, i + 1, 'eq', 1) for i in range(n - 1)])
        print("V chain %d: S-sumB %.2e; min excess over violated %.6f (units h: %.4f)" % (n, r['X'], min(v for p, v in r['ex'].items() if r['viol'](p) > 0), min(v for p, v in r['ex'].items() if r['viol'](p) > 0) / H))
    r = table(crossing(), [0, 3, 4, 8], [(4, 8, 'eq', 1), (0, 3, 'ne', 1)])
    print("K: S-sumB (X_K) = %.6f (units h %.4f)" % (r['X'], r['X'] / H))
    for p in sorted(r['ex']): print("   K", p, "excess %.6f  units h %.4f" % (r['ex'][p], r['ex'][p] / H))
    r = table(*(lambda s: (s[0], list(range(len(s[0]))), s[2]))(star(('NW', 'SE', 'SW'), True)))
    print("star deg3: S-sumB %.2e; min excess over violated %.6f" % (r['X'], min(v for p, v in r['ex'].items() if r['viol'](p) > 0)))
