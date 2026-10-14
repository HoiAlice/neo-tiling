"""np_cross.py -- interval-certified terminal table of the 4U x 5V crossing core K (B&B over all routings, interior bits free)."""
import sys, time, itertools
from np_dual import *
g, h0, h2 = 0.01, 0.02, 0.04
def vlev(s):
    sh = -h0 * s if s < 0 else -h2 * s
    return (1 + g + sh, 1 + sh)
def crossing(prune=False):
    sw = []
    for t in (-4.5, -1.5, 1.5, 4.5):  # U switches: bottoms (-4.5,4.5) ... hmm in grid units centre coordinates
        sw.append((t, -t, 4, 1 + g, 1.0))
    for s in range(-2, 3):
        tp, bt = vlev(s); sw.append((s - 0.5, s - 0.5, 5, tp, bt))
    return sw
if __name__ == "__main__":
    sw = crossing()
    blk = Block(sw, prune=(len(sys.argv) > 1 and sys.argv[1] == 'prune'))
    print("points", blk.T, "conflicts", len(blk.conf), flush=True)
    U_in, U_out, V_in, V_out = 0, 3, 4, 8
    pats = [tuple(map(int, a)) for a in sys.argv[2:]] or [(0, 1, 0, 0)]
    for p in pats:
        fixed = {blk.own[i]: b for i, b in zip((U_in, U_out, V_in, V_out), p)}
        t0 = time.time()
        lo, hi, asg, st = branch_and_bound(blk, fixed, tol=1e-6)
        print(p, "lo %.9f hi %.9f" % (lo, hi), st, "%.0fs" % (time.time() - t0), flush=True)
