"""phi_dual.py -- generalisation of gad/np_dual.py to a cost phi(log Q - log P) (phi even, convex, phi(0)=0), smooth case.
API identical to np_dual (Block, branch_and_bound, B_closed, H, ...), so that gad/np_*.py builders can be reused through
    sys.modules['np_dual'] = phi_dual
Select the cost with set_phi(name, h, **kw).  Weak duality: cost >= D(lam) = sum_v [ g_v a_v - phi*(|g_v|) ],  phi* = convex conjugate
(for phi_pi this is np_dual's  |g| - 1 - |g| ln|g|  for |g|>1)."""
import math
from fractions import Fraction
import numpy as np
from scipy.optimize import minimize
from mpmath import iv
iv.dps = 60

RHO = Fraction(21, 20)
H = 4 * math.log(float(RHO))
H_IV = 4 * iv.log(iv.mpf(RHO.numerator) / RHO.denominator)
PHI = None

class Phi:
    def __init__(self, name, f, fiv, fstar, fstar_iv, invd, s0=0.0):
        self.name, self.f, self.fiv, self.fstar, self.fstar_iv, self.invd, self.s0 = name, f, fiv, fstar, fstar_iv, invd, s0

def make_phi(name, p=None):
    if name == 'pi':      # e^|u| - 1
        return Phi('pi', lambda u: np.expm1(np.abs(u)), lambda u: iv.exp(abs(u)) - 1,
                   lambda s: np.where(s > 1, s * np.log(np.maximum(s, 1.0)) - s + 1, 0.0),
                   lambda s: (s * iv.log(s) - s + 1) if s > 1 else iv.mpf(0),
                   lambda s: np.log(np.maximum(s, 1.0)), s0=1.0)
    if name == 'sq':      # u^2
        return Phi('sq', lambda u: u * u, lambda u: u * u, lambda s: s * s / 4, lambda s: s * s / 4, lambda s: s / 2)
    if name == 'cosh':    # cosh u - 1
        return Phi('cosh', lambda u: np.cosh(u) - 1, lambda u: (iv.exp(u) + iv.exp(-u)) / 2 - 1,
                   lambda s: s * np.arcsinh(s) - np.sqrt(1 + s * s) + 1,
                   lambda s: s * iv.log(s + iv.sqrt(1 + s * s)) - iv.sqrt(1 + s * s) + 1 if s != 0 else iv.mpf(0),
                   lambda s: np.arcsinh(s))
    if name == 'pow':     # |u|^p, p>1
        q = p / (p - 1)
        return Phi('pow%g' % p, lambda u: np.abs(u) ** p, lambda u: iv.exp(p * iv.log(abs(u))) if u != 0 else iv.mpf(0),
                   lambda s: (p - 1) * (s / p) ** q,
                   lambda s: (p - 1) * iv.exp(q * iv.log(s / p)) if s != 0 else iv.mpf(0),
                   lambda s: (s / p) ** (1 / (p - 1)))
    if name == 'pi2':     # u + u^2/2*c ... "huber-like" |u| + u^2 (test of a kink + curvature)
        return Phi('lin+sq', lambda u: np.abs(u) + u * u, lambda u: abs(u) + u * u,
                   lambda s: np.where(s > 1, (s - 1) ** 2 / 4, 0.0),
                   lambda s: (s - 1) ** 2 / 4 if s > 1 else iv.mpf(0),
                   lambda s: np.maximum(s - 1, 0) / 2, s0=1.0)
    raise ValueError(name)

def set_phi(name, h=None, p=None):
    global PHI, H, H_IV
    PHI = make_phi(name, p)
    if h is not None:
        H = h
        H_IV = iv.mpf(h)       # h given as float; interval of the exact float (the instance then uses prices exp(m h/4) -- only used for tests)

set_phi('pi')

def phi1(x):    # float, scalar/array
    return PHI.f(x)

def points_from_switches(sw):
    G = []; Y = []
    for bx, by, d, yt, yb in sw:
        G += [(Fraction(bx) + Fraction(d), Fraction(by) + Fraction(d)), (Fraction(bx), Fraction(by))]
        Y += [yt, yb]
    return G, Y

def conflicts_of(Y, tol=1e-9):
    return [(a, b) for a in range(len(Y)) for b in range(len(Y)) if Y[a] > Y[b] + tol]

class Block:
    def __init__(self, sw, prune=False):
        self.sw = sw
        self.G, self.Y = points_from_switches(sw)
        self.T = len(self.G)
        self.A = np.array([[float(g[0]) * H, float(g[1]) * H] for g in self.G])
        self.A_iv = [[iv.mpf(g[0].numerator) / g[0].denominator * H_IV, iv.mpf(g[1].numerator) / g[1].denominator * H_IV] for g in self.G]
        self.conf = conflicts_of(self.Y)
        self.cidx = {c: k for k, c in enumerate(self.conf)}
        self.own = [self.cidx[(2 * i, 2 * i + 1)] for i in range(len(sw))]

def dual_float(blk, assign, lam0=None):
    items = sorted(assign.items()); m = len(items); T = blk.T
    if m == 0:
        return 0.0, {}, blk.A.copy()
    tail = np.array([blk.conf[k][0] for k, c in items]); head = np.array([blk.conf[k][1] for k, c in items]); co = np.array([c for k, c in items])
    P = PHI
    def parts(lam):
        g = np.zeros((T, 2)); np.add.at(g, (tail, co), lam); np.add.at(g, (head, co), -lam); return g
    def pos(g):
        ag = np.abs(g)
        return ag, blk.A - np.sign(g) * np.where(ag > P.s0, P.invd(ag), 0.0)
    def negD(lam):
        g = parts(lam); ag, x = pos(g)
        val = np.sum(g * blk.A) - np.sum(P.fstar(ag))
        grad = x[tail, co] - x[head, co]
        return -val, -grad
    x0 = np.zeros(m) if lam0 is None else np.array([lam0.get(k, 0.0) for k, c in items])
    r = minimize(negD, x0, jac=True, method='L-BFGS-B', bounds=[(0, None)] * m, options=dict(maxiter=3000, ftol=1e-15, gtol=1e-11, maxcor=30))
    lam = r.x; g = parts(lam); ag, x = pos(g)
    return -r.fun, {k: v for (k, c), v in zip(items, lam)}, x

def dual_rigorous(blk, assign, lam):
    T = blk.T
    g = [[Fraction(0), Fraction(0)] for _ in range(T)]
    for k, c in assign.items():
        l = Fraction(lam.get(k, 0.0)); a, b = blk.conf[k]
        g[a][c] += l; g[b][c] -= l
    tot = iv.mpf(0)
    for t in range(T):
        for c in range(2):
            gg = g[t][c]; gi = iv.mpf(gg.numerator) / gg.denominator
            tot += gi * blk.A_iv[t][c]
            tot -= PHI.fstar_iv(abs(gi))
    return float(tot.a)

def cost_iv_upper(blk, x):
    tot = iv.mpf(0)
    for t in range(blk.T):
        for c in range(2):
            tot += PHI.fiv(iv.mpf(float(x[t][c])) - blk.A_iv[t][c])
    return float(tot.b)

def violated(blk, assign, x, tol=1e-9):
    best = None
    for k, (a, b) in enumerate(blk.conf):
        if k in assign: continue
        s = min(x[a][0] - x[b][0], x[a][1] - x[b][1])
        if s > tol and (best is None or s > best[0]): best = (s, k)
    return best

def branch_and_bound(blk, fixed, tol=1e-7, target=None, max_nodes=400000, verbose=False):
    best = [float('inf'), None]; lo_pruned = [float('inf')]; stats = dict(nodes=0, leaves=0)
    stack = [(dict(fixed), None)]
    while stack:
        assign, lam0 = stack.pop(); stats['nodes'] += 1
        if stats['nodes'] > max_nodes: raise RuntimeError("node limit")
        val, lam, x = dual_float(blk, assign, lam0)
        thr = best[0] - tol if target is None else min(best[0] - tol, target)
        if val >= thr + 1e-6:
            lb = dual_rigorous(blk, assign, lam)
            if lb >= thr:
                lo_pruned[0] = min(lo_pruned[0], lb); continue
        v = violated(blk, assign, x)
        if v is None:
            stats['leaves'] += 1
            lb = dual_rigorous(blk, assign, lam); ub = cost_iv_upper(blk, x)
            lo_pruned[0] = min(lo_pruned[0], lb)
            if ub < best[0]: best[0] = ub; best[1] = dict(assign)
            continue
        k = v[1]
        for c in (0, 1):
            a2 = dict(assign); a2[k] = c; stack.append((a2, lam))
    return lo_pruned[0], best[0], best[1], stats

def B_closed(d_grid):
    return 2 * float(PHI.f(float(d_grid) * H / 2))
