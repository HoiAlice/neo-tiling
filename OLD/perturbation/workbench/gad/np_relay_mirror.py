import math, relay
from np_cluster import *
from np_mirror import Rm, Pm
sw0, term = relay.build_relay_cp(); S0 = [tuple(float(v) for v in s) for s in sw0]
JE = 2*(math.exp(H/8)-1)
for tn, tf, flip in (("id", lambda s: s, 0), ("R", Rm, 1), ("P", Pm, 0), ("RP", lambda s: Rm(Pm(s)), 1)):
    SW = [tf(s) for s in S0]; n = len(SW); SB = sum(B_closed(s[2]) for s in SW)
    for v in (0, 1):
        for w in (0, 1):
            bits = [None]*n
            for i in range(4): bits[i] = v
            bits[8] = v
            for k in range(4): bits[4+k] = v if k == 0 else 1-bits[3+k]
            bits[9] = 1-bits[7]; unsat = (w == bits[9]); bits[10] = 1-bits[9]
            kinks = []
            if unsat: bits[11] = bits[10]; kinks.append((10, 11))
            else: bits[11] = 1-bits[10]
            bits[12] = w
            bits = [b ^ flip for b in bits]; kk = kinks
            cost, worst, D, x, blk, wk = glue(SW, bits, [], kk)
            print(tn, (v, w), "cost-closed %.1e" % (cost-SB-JE*unsat), "min slack %.4f" % worst[0], "kink %.1e" % wk[0], flush=True)
