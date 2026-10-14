"""np_relay_glue.py -- relay cluster (corner - relay - pure U with weak link), built with gadget agent's relay.build_relay_cp (read only); glue test, all conflicts."""
import itertools, math
import relay
from np_cluster import *
sw, term = relay.build_relay_cp()
SW = [tuple(float(v) for v in s) for s in sw]
n = len(SW); SB = sum(B_closed(s[2]) for s in SW); JE = 2*(math.exp(H/8)-1)
print("switches", n, "terminals", term)
for i, s in enumerate(SW): print(i, s)
nV = 4; nU = 4
for v in (0, 1):
    for w in (0, 1):
        bits = [None]*n
        for i in range(nV): bits[i] = v
        iu, ir = term[0], n  # placeholders
        bits[iu] = v
        for k in range(nU): bits[nV + k] = v if k == 0 else 1 - bits[nV + k - 1]
        irl = iu + 1; bits[irl] = 1 - bits[nV + nU - 1]
        # pure wire: irl+1, irl+2, then vertex term[1]; links strong, weak (middle), strong; relation ne
        chain = [irl, irl+1, irl+2, term[1]]; kinks = []
        bits[term[1]] = w
        b = bits[irl]
        for a_, c_ in zip(chain[:-1], chain[1:]):
            if c_ == term[1]: break
            weak = (c_ == irl+2)
            sat_expected = (w != bits[irl]) if True else True
            unsat = (w == b) if False else None
        # propagate: 3 ne links, weak is the middle one; kink iff w == bits[irl]
        unsat = (w == bits[irl])
        bits[irl+1] = 1 - bits[irl]
        if unsat: bits[irl+2] = bits[irl+1]; kinks.append((irl+1, irl+2))
        else: bits[irl+2] = 1 - bits[irl+1]
        cost, worst, D, x, blk, wk = glue(SW, bits, [], kinks)
        print("v", v, "w", w, "unsat", int(unsat), "cost - (sumB + J*unsat) %.2e" % (cost - SB - JE*unsat), "min slack (non-kink) %.4f" % worst[0], worst[1], "kink slack %.1e" % wk[0], "D %.4f" % D, flush=True)
