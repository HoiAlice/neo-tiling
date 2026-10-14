"""np_chain.py -- interval-certified credit tables for wire blocks (U chains with strong/weak links, V chains), all bit patterns.
cert:  m(tau) - S >= sum_l c_l * viol_l(tau)  for every bit pattern tau,  S = m(satisfied pattern) = sum of B."""
import itertools, math, sys, time
from np_dual import *
g = 0.01
def uchain(steps, base=1.0):
    sw = [(0.0, 0.0, 4, base + g, base)]; p = 0.0
    for st in steps:
        p += st; sw.append((p, -p, 4, base + g, base))
    return sw
def vchain(n, step=0.04, base=1.0):
    return [(float(j), float(j), 5, base + g - step * j, base - step * j) for j in range(n)]
JE = 2 * (math.exp(H / 8) - 1)
def run(name, sw, kinds, credits):
    """kinds[i] in {'ne','eq'} relation of link i (between switch i and i+1); credits[i] in units of J_e"""
    blk = Block(sw); n = len(sw)
    SB = sum(B_closed(s[2]) for s in sw)
    res = {}
    for bits in itertools.product((0, 1), repeat=n):
        fixed = {blk.own[i]: b for i, b in enumerate(bits)}
        lo, hi, _, st = branch_and_bound(blk, fixed, tol=1e-9); res[bits] = (lo, hi)
    def viol(bits): return sum(c for i, (k, c) in enumerate(zip(kinds, credits)) if ((bits[i] == bits[i + 1]) != (k == 'eq')))
    sat = [b for b in res if viol(b) == 0]
    S = min(res[b][1] for b in sat)
    worst = min(((res[b][0] - S - JE * viol(b)), b) for b in res if viol(b) > 0)
    print("%-28s n=%d  S-sumB=%.2e  satisfied=%d  min margin (lo-S-J_e*credits)=%.6f at %s" % (name, n, S - SB, len(sat), worst[0], worst[1]), flush=True)
    return worst[0]
if __name__ == "__main__":
    run("U pair S (credit 2)", uchain([3]), ['ne'], [2])
    run("U pair W (credit 1)", uchain([3.75]), ['ne'], [1])
    run("U triple S,S (2,2)", uchain([3, 3]), ['ne', 'ne'], [2, 2])
    run("U triple S,W (2,1)", uchain([3, 3.75]), ['ne', 'ne'], [2, 1])
    run("U triple W,S (1,2)", uchain([3.75, 3]), ['ne', 'ne'], [1, 2])
    run("U 4-chain S,W,S (2,1,2)", uchain([3, 3.75, 3]), ['ne'] * 3, [2, 1, 2])
    run("U 4-chain S,S,S (2,2,2)", uchain([3, 3, 3]), ['ne'] * 3, [2, 2, 2])
    run("V pair (2)", vchain(2), ['eq'], [2])
    run("V triple (2,2)", vchain(3), ['eq', 'eq'], [2, 2])
    run("V 4-chain (2,2,2)", vchain(4), ['eq'] * 3, [2, 2, 2])
