import sys, os, re, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import l1
from l1 import *
sw = {}
for line in open('/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad/cprime2.out'):
    m = re.match(r"^(\d+) \((.*)\)$", line.strip())
    if m: sw[int(m.group(1))] = tuple(float(v) for v in m.group(2).split(','))
SW = [sw[i] for i in range(25)]
blk = pd.Block(SW)
SB = sum(s[2] * l1.H for s in SW)
t0 = time.time()
# greedy: LP relaxation with no routing, then branch (depth-first, first violated)
val, x = lp(blk, {})
print("LP root", val, "sumB", SB)
asg = {}
n = 0
while True:
    val, x = lp(blk, asg); v = pd.violated(blk, asg, x, tol=1e-8)
    if v is None: break
    asg[v[1]] = int(0 if (x[blk.conf[v[1]][0]][0] - x[blk.conf[v[1]][1]][0]) <= (x[blk.conf[v[1]][0]][1] - x[blk.conf[v[1]][1]][1]) else 1)
    n += 1
print("feasible leaf (greedy routing) cost", val, "sumB", SB, "excess", val - SB, "steps", n, "time %.1f" % (time.time() - t0))
import itertools
t0 = time.time()
# fix the four terminal bits as in cprime (terminals 8,14,15,24) to limit branching; take the minimum over the 16 patterns
best = 1e9
for pat in itertools.product((0, 1), repeat=4):
    fixed = {blk.own[i]: b for i, b in zip((8, 14, 15, 24), pat)}
    v, _ = l1.bb(blk, fixed)
    print(pat, "min cost %.6f excess over sumB %.2e" % (v, v - SB), "%.0fs" % (time.time() - t0), flush=True)
