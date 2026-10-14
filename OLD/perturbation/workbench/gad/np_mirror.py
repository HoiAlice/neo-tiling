"""np_mirror.py -- direct certification of R (x<->y) and P (point reflection, levels reversed) images of the corner windows (item 4).
Image switch: R: (bx,by,d,yt,yb) -> (by,bx,d,yt,yb);  P: -> (-bx-d, -by-d, d, C-yb, C-yt).  Bits: R flips all, P keeps; eq/ne preserved, so the same relations/credits apply."""
import re, itertools, math
from np_dual import *
from np_chain import JE
sw = {}
for line in open('cprime2.out'):
    m = re.match(r"^(\d+) \((.*)\)$", line.strip())
    if m: sw[int(m.group(1))] = tuple(float(v) for v in m.group(2).split(','))
def Rm(s): return (s[1], s[0], s[2], s[3], s[4])
def Pm(s): return (-s[0]-s[2], -s[1]-s[2], s[2], 3.0-s[4], 3.0-s[3])
def cert(name, ids, rels, tf):
    S_ = [tf(sw[i]) for i in ids]; blk = Block(S_); n = len(ids); SB = sum(B_closed(s[2]) for s in S_)
    ix = {g: k for k, g in enumerate(ids)}; res = {}
    for bits in itertools.product((0, 1), repeat=n):
        fixed = {blk.own[i]: b for i, b in enumerate(bits)}
        lo, hi, _, st = branch_and_bound(blk, fixed, tol=1e-9); res[bits] = (lo, hi)
    def viol(b): return sum(c for (i, j, k, c) in rels if ((b[ix[i]] == b[ix[j]]) != (k == 'eq')))
    sat = [b for b in res if viol(b) == 0]; S = min(res[b][1] for b in sat)
    worst = min(((res[b][0] - S - JE*viol(b)), b) for b in res if viol(b) > 0)
    print("%-28s S-sumB=%.1e margin=%.6f" % (name, S - SB, worst[0]), flush=True)
E, N = 'eq', 'ne'
W = [("corner 4: V1,V0,u0,u1", [1,0,9,10], [(1,0,E,2),(0,9,E,2),(9,10,N,2)]),
     ("corner 4: V0,u0,u1,u2", [0,9,10,11], [(0,9,E,2),(9,10,N,2),(10,11,N,2)]),
     ("corner 4: V2,V1,V0,u0", [2,1,0,9], [(2,1,E,2),(1,0,E,2),(0,9,E,2)]),
     ("crossing-side V triple 6,7,8", [6,7,8], [(6,7,E,2),(7,8,E,2)])]
if __name__ == "__main__":
  for tn, tf in (("R", Rm), ("P", Pm), ("RP", lambda s: Rm(Pm(s)))):
    for nm, ids, rels in W: cert(tn + " " + nm, ids, rels, tf)
