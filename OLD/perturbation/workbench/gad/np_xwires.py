"""np_xwires.py -- crossing core + incident wire stretches (m switches each side on both wires): glued point feasibility, all conflicts."""
import math
from np_cluster import *
from np_cross import vlev, g
def build(mU, mV):
    sw = []; Uidx = []; Vidx = []
    ts = [(-4.5 - 3*i) for i in range(mU, 0, -1)] + [-4.5, -1.5, 1.5, 4.5] + [4.5 + 3*i for i in range(1, mU+1)]
    for t in ts: Uidx.append(len(sw)); sw.append((t, -t, 4, 1+g, 1.0))
    for s in range(-2-mV, 3+mV):
        tp, bt = vlev(s); Vidx.append(len(sw)); sw.append((s-0.5, s-0.5, 5, tp, bt))
    return sw, Uidx, Vidx
SB0 = None
for (mU, mV) in [(1,1),(3,3),(5,5),(8,8)]:
    sw, Ui, Vi = build(mU, mV); SB = sum(B_closed(s[2]) for s in sw)
    for pat in [(0,1,0,0),(1,0,0,0),(0,1,1,1),(1,0,1,1)]:
        bits = [None]*len(sw)
        for k, i in enumerate(Ui): bits[i] = (pat[0] + k - mU) % 2   # alternate; K's first U is index mU
        for i in Vi: bits[i] = pat[2]
        idx = Ui[mU:mU+4] + Vi[mV:mV+5]
        cost, worst, D, x, blk, wk = glue(sw, bits, [(idx, pat)], [])
        print("mU,mV", (mU, mV), pat, "cost - (sumB + X_K) = %.2e" % (cost - SB - 0.1229644), "min slack outside core %.4f" % worst[0], worst[1], "D %.4f" % D, flush=True)
