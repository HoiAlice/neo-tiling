"""ws_g.py -- (WS) test for r^2 at geometry G*: 25-switch two-edge crossing instance (cprime layout rebuilt at G*), all 16 vertex-bit patterns.
glued optimum (K optimum + isolated switches + pooled kinks), snapped, y = F(s_c) rule (ws_rule4.y_pw), flow-LP check (gad core.weakly_solvable).
usage: ws_g.py h u att aw [c1,c2,sstar ...]"""
import sys, os, itertools, math
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
GAD = '/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad'
import numpy as np
import phi_dual as pd
import lib_u as L
import glue_u as GU
sys.path.insert(0, GAD); sys.path.insert(0, "/Users/olegoleg/Code/neo-tiling/poly-hardness")
os.chdir(GAD)
from ws_rule import sc
from ws_rule4 import y_pw
from core import weakly_solvable
os.chdir(HERE)

def build_cp(u, att, aw):
    """switch list (bx,by,d) for the cprime layout at G*; ids as in gad/cprime2.out: V 0..8, corner U 9..13, vertex2 14, A 15, E2 U 16..23, B 24"""
    sw = []
    for s in range(-4, 5): sw.append((s - 0.5, s - 0.5, 5))
    steps = [u, u, aw, u, att]; p = 0
    sw.append((-4.5, -4.5, 4))
    for st in steps[:-1]:
        p += st; sw.append((-4.5 - p, -4.5 + p, 4))
    P = sum(steps); c = (-4.5 - P + 2, -4.5 + P + 2); sw.append((c[0] - 2.5, c[1] - 2.5, 5))
    def vert(b): return (b + 2 - 2.5, -b + 2 - 2.5, 5)
    def usw(b): return (b, -b, 4)
    bA = -3.5 * u - aw - att
    sw.append(vert(bA))
    for b in (bA + att, bA + att + aw, -2.5 * u, -1.5 * u, -0.5 * u, 0.5 * u, 1.5 * u, 2.5 * u): sw.append(usw(b))
    sw.append(vert(2.5 * u + att))
    return sw
def with_y(sw3, y):
    return [(a, b, d, y[2 * i], y[2 * i + 1]) for i, (a, b, d) in enumerate(sw3)]
def bits_for(v1, v2, A, B):
    bits = [None] * 25
    for i in range(9): bits[i] = v1
    bits[9] = v1; kinks = []
    chain = [9, 10, 11, 12, 13, 14]
    for a_, c_ in zip(chain, chain[1:]):
        if (a_, c_) == (11, 12) and v2 == v1: bits[c_] = bits[a_]; kinks.append((a_, c_))
        else: bits[c_] = 1 - bits[a_]
    bits[15] = A
    for a_, c_ in zip(range(15, 24), range(16, 25)):
        if (a_, c_) == (16, 17) and A == B: bits[c_] = bits[a_]; kinks.append((a_, c_))
        else: bits[c_] = 1 - bits[a_]
    return bits, kinks
def snap(x, tol=1e-5):
    x = x.copy()
    for c in (0, 1):
        idx = np.argsort(x[:, c]); i = 0
        while i < len(idx):
            j = i
            while j + 1 < len(idx) and x[idx[j + 1], c] - x[idx[j], c] < tol: j += 1
            if j > i: x[idx[i:j + 1], c] = x[idx[i:j + 1], c].mean()
            i = j + 1
    return x
def optima(sw3, u):
    out = {}
    swy = with_y(sw3, np.ones(2 * len(sw3)))
    for pat in itertools.product((0, 1), repeat=4):
        v1, v2, A, B = pat
        bits, kinks = bits_for(*pat)
        K = [19, 20, 21, 22, 2, 3, 4, 5, 6]
        kp = (bits[19], bits[22], bits[2], bits[6])
        cost, worst, wk, D, blk = GU.glue(swy, bits, [(K, kp, u)], kinks)
        # need x: re-run glue internals
        out[pat] = (bits, kinks, kp)
    return out
def glued_x(sw3, u, pat):
    """returns snapped log-coordinate array x (T,2) for the instance"""
    h = pd.H
    sw = [(a, b, d, 1.01, 1.0) for (a, b, d) in sw3]
    blk = pd.Block(sw); x = blk.A.copy()
    bits, kinks = bits_for(*pat); K = [19, 20, 21, 22, 2, 3, 4, 5, 6]
    kp = (bits[19], bits[22], bits[2], bits[6])
    xK, bK, _ = GU.kopt(u, kp)
    for k, s in enumerate(K):
        x[2*s] = xK[2*k]; x[2*s+1] = xK[2*k+1]; bits[s] = bK[k]
    for s in range(25):
        if s in K: continue
        dl = sw3[s][2] * h; b = bits[s]; x[2*s][b] -= dl / 2; x[2*s+1][b] += dl / 2
    # pooled kinks: the two cross conflicts (t_i,b_j),(t_j,b_i) in the other coordinate; pool the violated one
    for (i, j) in kinks:
        c = 1 - bits[i]
        for a_, b_ in [(2*i, 2*j+1), (2*j, 2*i+1)]:
            d = x[a_][c] - x[b_][c]
            if d > 1e-12 and x[a_][1-c] > x[b_][1-c] + 1e-12:
                x[a_][c] -= d / 2; x[b_][c] += d / 2
    return snap(x), bits
if __name__ == '__main__':
    h = float(sys.argv[1]); u, att, aw = float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
    pd.set_phi(os.environ.get('PHI', 'sq'), h=h)
    sw3 = build_cp(u, att, aw)
    xs = {}; 
    for pat in itertools.product((0, 1), repeat=4): xs[pat] = glued_x(sw3, u, pat)[0]
    Qs = {p: np.exp(x) for p, x in xs.items()}
    s = sc([(a, b, d, 0, 0) for (a, b, d) in sw3]); print("s_c: V chain", s[:9], "corner/arm", s[9:15], "E2", s[15:], flush=True)
    specs = [tuple(float(v) for v in a.split(',')) for a in sys.argv[5:]] or [(0.02, 0.07, 4), (0.02, 0.08, 4), (0.03, 0.08, 4), (0.02, 0.12, 4)]
    sw_dummy = [(a, b, d, 0, 0) for (a, b, d) in sw3]
    for (c1, c2, ss) in specs:
        y = y_pw(sw_dummy, c1, c2, ss)
        swy = with_y(sw3, y)
        blk = pd.Block(swy)
        # dominance feasibility of the glued optimum (all conflicts, y_a > y_b => some coordinate x_a <= x_b)
        bad = {}
        for p, x in xs.items():
            nb = [(a, b) for (a, b) in blk.conf if min(x[a][0] - x[b][0], x[a][1] - x[b][1]) > 1e-9]
            if nb: bad[p] = nb[:3]
        ok = {p: bool(weakly_solvable(Q, y)) for p, Q in Qs.items()}
        print("kinks (c1,c2,s*)=(%g,%g,%g) ratio %.2f  dominance-violations at %d patterns %s | weakly solvable %d/16 ; failing %s" % (c1, c2, ss, y.max() / y.min(), len(bad), list(bad.items())[:1], sum(ok.values()), [p for p, o in ok.items() if not o]), flush=True)
