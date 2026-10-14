"""ws_k3g.py -- (WS) for K_3 at G* (r^2 or other phi): layout of gad/k3.py with strong step u, arm (u0,aw,att), glued optimum = isolated + pooled kinks, 8 patterns."""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np
import phi_dual as pd
import ws_g as W
from ws_g import *
def build_k3(arm, n=6, aw=3.75):
    P = sum(arm); sw = []
    def corner_edge(K, dirU):
        e = []
        for j in range(n): e.append((K[0] + j, K[1] + j, 5))
        e.append((K[0], K[1], 4)); p = 0
        for st in arm[:-1]:
            p += st; e.append((K[0] + dirU[0] * p, K[1] + dirU[1] * p, 4))
        Bv = (K[0] + n, K[1] + n); Av = (K[0] + dirU[0] * P - 0.5, K[1] + dirU[1] * P - 0.5)
        return e, Bv, Av
    K1 = (0.0, 0.0); K2 = (2 * P, -2 * P)
    e1, Y, X1 = corner_edge(K1, (1, -1)); e2, Z, X2 = corner_edge(K2, (-1, 1))
    sw += e1 + e2; iX = len(sw); sw.append((X1[0], X1[1], 5)); iY = len(sw); sw.append((Y[0], Y[1], 5)); iZ = len(sw); sw.append((Z[0], Z[1], 5))
    m = 2 * P; s = (m - aw) / 6; steps = [s, s, s, aw, s, s, s]
    cy = (Y[0] + 2.5, Y[1] + 2.5); p = 0
    for st in steps[:-1]:
        p += st; c = (cy[0] + p, cy[1] - p); sw.append((c[0] - 2, c[1] - 2, 4))
    return sw, (iX, iY, iZ), s
def bits_k3(bX, bY, bZ, n=6):
    bits = [None] * 27; kinks = []
    def edge(base, bend, bX):    # base index offset of the edge (V 0..n-1, u0=n, u1, u2), V-end vertex bit bend
        for j in range(n): bits[base + j] = bend
        bits[base + n] = bend                 # u0 eq with V0
        bits[base + n + 1] = 1 - bend         # u1 ne u0
        # u2: ne u1 unless the weak link (u1,u2) carries the mismatch; vertex X ne u2 normally
        sat = (bX != bend)
        if sat: bits[base + n + 2] = bend; 
        else: bits[base + n + 2] = bits[base + n + 1]; kinks.append((base + n + 1, base + n + 2))
        # need X != u2 when sat:   bits u2 = 1-bX; with sat: bend = 1-bX  and u1 = 1-bend = bX, u2 must be 1-u1 = 1-bX = bend ok
    edge(0, bY, bX); edge(n + 3, bZ, bX)
    bits[18], bits[19], bits[20] = bX, bY, bZ
    # pure edge Y-Z: switches 21..26, links Y-21,...,26-Z (7), weak = (23,24); all ne unless bY == bZ
    chain = [19] + list(range(21, 27)) + [20]
    b = bY
    for a_, c_ in zip(chain, chain[1:]):
        weak = (a_, c_) == (23, 24)
        if weak and bY == bZ: bits[c_] = bits[a_]; kinks.append((a_, c_))
        else: bits[c_] = 1 - bits[a_]
    return bits, kinks
if __name__ == '__main__':
    h = float(sys.argv[1]); arm = tuple(float(v) for v in sys.argv[2].split(',')); aw = float(sys.argv[3])
    pd.set_phi(os.environ.get('PHI', 'sq'), h=h)
    sw3, (iX, iY, iZ), s = build_k3(arm, aw=aw); print("switches", len(sw3), "pure-edge strong step %.4f" % s, flush=True)
    xs = {}
    for pat in itertools.product((0, 1), repeat=3):
        bits, kinks = bits_k3(*pat)
        assert all(b is not None for b in bits)
        sw = [(a, b, d, 1.01, 1.0) for (a, b, d) in sw3]; blk = pd.Block(sw); x = blk.A.copy()
        for k in range(len(sw3)):
            dl = sw3[k][2] * pd.H; b = bits[k]; x[2*k][b] -= dl / 2; x[2*k+1][b] += dl / 2
        for (i, j) in kinks:
            c = 1 - bits[i]
            for a_, b_ in [(2*i, 2*j+1), (2*j, 2*i+1)]:
                d = x[a_][c] - x[b_][c]
                if d > 1e-12 and x[a_][1-c] > x[b_][1-c] + 1e-12: x[a_][c] -= d / 2; x[b_][c] += d / 2
        xs[pat] = snap(x)
    sw_dummy = [(a, b, d, 0, 0) for (a, b, d) in sw3]
    specs = [tuple(float(v) for v in a.split(',')) for a in sys.argv[4:]] or [(0.02, 0.08, 4)]
    for (c1, c2, ss) in specs:
        y = y_pw(sw_dummy, c1, c2, ss); swy = with_y(sw3, y); blk = pd.Block(swy)
        bad = {}
        for p, x in xs.items():
            nb = [(a, b) for (a, b) in blk.conf if min(x[a][0] - x[b][0], x[a][1] - x[b][1]) > 1e-9]
            if nb: bad[p] = nb[:2]
        ok = {p: bool(weakly_solvable(np.exp(x), y)) for p, x in xs.items()}
        print("K3 kinks (c1,c2,s*)=(%g,%g,%g) ratio %.2f dominance-violating patterns %d %s | weakly solvable %d/8 ; failing %s" % (c1, c2, ss, y.max() / y.min(), len(bad), list(bad.items())[:1], sum(ok.values()), [p for p, o in ok.items() if not o]), flush=True)
