import re, itertools, math
from np_cluster import *
sw = {}
for line in open('cprime2.out'):
    m = re.match(r"^(\d+) \((.*)\)$", line.strip())
    if m: sw[int(m.group(1))] = tuple(float(v) for v in m.group(2).split(','))
SW = [sw[i] for i in range(25)]
SB = sum(B_closed(s[2]) for s in SW)
JE = 2*(math.exp(H/8)-1)
XK = 0.1229644
for v1, v2, A, B in itertools.product((0,1), repeat=4):
    bits = [None]*25
    for i in range(0, 9): bits[i] = v1
    bits[9] = v1
    b = v1; chain = [9,10,11,12,13,14]; kinks = []
    bits[9] = v1
    for a_, c_ in zip(chain, chain[1:]):
        weak = (a_, c_) == (11, 12)
        unsat = (v2 == v1)          # 5 inversions: bit14 = 1-v1 iff sat
        if weak and unsat: bits[c_] = bits[a_]; kinks.append((a_, c_))
        else: bits[c_] = 1 - bits[a_]
    chain = list(range(15, 25))
    bits[15] = A
    for a_, c_ in zip(chain, chain[1:]):
        weak = (a_, c_) == (16, 17); unsat = (A == B)
        if weak and unsat: bits[c_] = bits[a_]; kinks.append((a_, c_))
        else: bits[c_] = 1 - bits[a_]
    pat = (bits[19], bits[22], bits[2], bits[6])
    cost, worst, D, x, blk, wk = glue(SW, bits, [([19,20,21,22,2,3,4,5,6], pat)], kinks)
    unsat = (v1 == v2) + (A == B)
    print((v1,v2,A,B), "cost-closed %.9f" % (cost - (SB + XK + JE*unsat)), "min slack non-core %.4f" % worst[0], worst[1], "min kink-pair slack %.2e" % wk[0], "Dmax %.4f" % D, flush=True)
