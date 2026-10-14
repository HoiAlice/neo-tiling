"""np_pair_classes.py -- routing-class table of the U pair (a = 3 and a = 3.75): all 2^4 routings of (own0, own1, c01, c10), interval-certified lower bounds.
Shows: natural class value = 2B (+J) exactly, every other class >= natural + margin."""
import itertools
from np_dual import *
from np_pair_exact import U
for a in (3.0, 3.75):
    blk = Block([U(0, 0), U(a, -a)])
    idx = {c: k for k, c in enumerate(blk.conf)}
    print("a =", a, "conflicts (a,b):", blk.conf)
    B2 = 2 * B_closed(4)
    rows = []
    for rt in itertools.product((0, 1), repeat=4):
        assign = dict(zip(range(4), rt))
        val, lam, x = dual_float(blk, assign)
        lb = dual_rigorous(blk, assign, lam)
        rows.append((rt, lb - B2))
    for rt, ex in rows: print("  routing", rt, "excess over 2B (lower bound) %.9f" % ex)
