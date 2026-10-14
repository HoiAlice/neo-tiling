"""np_pair_exact.py -- exact (interval-certified) pair-block tables.  Usage: python np_pair_exact.py
For each pair block (two switches), all 4 own-bit patterns, B&B over all routings of the cross conflicts,
rigorous lo/hi, compared to closed forms 2B(d) (satisfied) and 2B + J (violated)."""
import sys, math, itertools, time
from np_dual import *
g = 0.01
def U(bx, by, base=1.0, d=4): return (bx, by, d, base + g, base)
BLOCKS = {
 'U strong a=3':    ([U(0, 0), U(3, -3)], 'ne'),
 'U weak a=3.75':   ([U(0, 0), U(3.75, -3.75)], 'ne'),
 'V link k=1 d=5':  ([(0, 0, 5, 1 + g - 0.02, 1 - 0.02), (1, 1, 5, 1 + g - 0.04, 1 - 0.04)], 'eq'),
}
if __name__ == "__main__":
    for name, (sw, rel) in BLOCKS.items():
        blk = Block(sw)
        print(name, "points", blk.T, "conflicts", len(blk.conf), flush=True)
        res = {}
        for bits in itertools.product((0, 1), repeat=2):
            fixed = {blk.own[i]: bits[i] for i in range(2)}
            t0 = time.time()
            lo, hi, asg, st = branch_and_bound(blk, fixed, tol=1e-9)
            res[bits] = (lo, hi)
            print("  bits", bits, "lo %.12f hi %.12f" % (lo, hi), st, "%.1fs" % (time.time() - t0), flush=True)
        B2 = sum(B_closed(s[2]) for s in sw)
        sat = [b for b in res if (b[0] == b[1]) == (rel == 'eq')]
        S = min(res[b][1] for b in sat)
        print("  closed form 2B-sum %.12f ; sat value %.12f" % (B2, S))
        for b in res:
            tag = 'sat' if b in sat else 'viol'
            print("   ", b, tag, "excess over sum B  lo %.9f hi %.9f" % (res[b][0] - B2, res[b][1] - B2))
