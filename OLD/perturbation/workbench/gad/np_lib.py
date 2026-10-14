"""np_lib.py -- interval-certified credit certificates for the non-crossing blocks of the 25-switch instance (cprime2.out switch list),
at the rational-price step H = 4 ln(21/20).  Same relations/credits as LOCALITY.md Sec. 3 (strong 2 J_e, weak J_e)."""
import re, itertools, math, time
from np_dual import *
from np_chain import JE
sw = {}
for line in open('cprime2.out'):
    m = re.match(r"^(\d+) \((.*)\)$", line.strip())
    if m: sw[int(m.group(1))] = tuple(float(v) for v in m.group(2).split(','))
def cert(name, ids, rels):
    """rels: list of (i,j,kind,credit) with global ids"""
    S_ = [sw[i] for i in ids]; blk = Block(S_); n = len(ids); SB = sum(B_closed(s[2]) for s in S_)
    ix = {g: k for k, g in enumerate(ids)}
    res = {}
    for bits in itertools.product((0, 1), repeat=n):
        fixed = {blk.own[i]: b for i, b in enumerate(bits)}
        lo, hi, _, st = branch_and_bound(blk, fixed, tol=1e-9); res[bits] = (lo, hi)
    def viol(b): return sum(c for (i, j, k, c) in rels if ((b[ix[i]] == b[ix[j]]) != (k == 'eq')))
    sat = [b for b in res if viol(b) == 0]; S = min(res[b][1] for b in sat)
    worst = min(((res[b][0] - S - JE * viol(b)), b) for b in res if viol(b) > 0)
    print("%-26s ids=%s S-sumB=%.2e margin=%.6f at %s" % (name, ids, S - SB, worst[0], worst[1]), flush=True)
if __name__ == "__main__":
    cert("corner pair (V0,u0)", [0, 9], [(0, 9, 'eq', 2)])
    cert("vertex-U pair (13,14)", [13, 14], [(13, 14, 'ne', 2)])
    cert("U-vertex pair (23,24)", [23, 24], [(23, 24, 'ne', 2)])
    cert("5-block 9..13 (weak 11-12)", [9, 10, 11, 12, 13], [(9, 10, 'ne', 2), (10, 11, 'ne', 2), (11, 12, 'ne', 1), (12, 13, 'ne', 2)])
    cert("4-block 15..18 (weak 16-17)", [15, 16, 17, 18], [(15, 16, 'ne', 2), (16, 17, 'ne', 1), (17, 18, 'ne', 2)])
    cert("weak pair (11,12)", [11, 12], [(11, 12, 'ne', 1)])
    cert("V pair (0,1)", [0, 1], [(0, 1, 'eq', 2)])
    cert("V pair (7,8)", [7, 8], [(7, 8, 'eq', 2)])
