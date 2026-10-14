"""np_kplus.py -- credit certificate for the enlarged crossing block K^+ (13 switches), all 2^8 terminal patterns, interval dual B&B.
Relations (eq = equal bits, ne = different bits) and credits (units of J_e): K-internal V (2,6) eq 1, U (19,22) ne 1; neighbour links 2."""
import sys, time, itertools, math
from multiprocessing import Pool
from np_dual import *
from np_cross import vlev, g
def kplus():
    sw = []
    for t in (-7.5, -4.5, -1.5, 1.5, 4.5, 7.5): sw.append((t, -t, 4, 1 + g, 1.0))      # idx 0..5  (K U = 1..4)
    for s in range(-3, 4):
        tp, bt = vlev(s); sw.append((s - 0.5, s - 0.5, 5, tp, bt))                       # idx 6..12 (K V = 7..11)
    return sw
SW = kplus()
BLK = Block(SW)
JE = 2 * (math.exp(H / 8) - 1)
# terminals: U0,U1,U4,U5 ; V6,V7,V11,V12
TERM = (0, 1, 4, 5, 6, 7, 11, 12)
RELS = [(0, 1, 'ne', 2), (4, 5, 'ne', 2), (6, 7, 'eq', 2), (11, 12, 'eq', 2), (1, 4, 'ne', 1), (7, 11, 'eq', 1)]
def work(p):
    fixed = {BLK.own[i]: b for i, b in zip(TERM, p)}
    lo, hi, asg, st = branch_and_bound(BLK, fixed, tol=1e-7)
    return p, lo, hi, st['nodes']
if __name__ == "__main__":
    SB = sum(B_closed(s[2]) for s in SW)
    t0 = time.time()
    with Pool(8) as pool: out = pool.map(work, list(itertools.product((0, 1), repeat=8)), chunksize=4)
    val = {p: (lo, hi) for p, lo, hi, n in out}
    ix = {t: i for i, t in enumerate(TERM)}
    def viol(p):
        tot = 0
        for a, b, k, c in RELS:
            eq = p[ix[a]] == p[ix[b]]
            if (k == 'eq') != eq: tot += c
        return tot
    sat = [p for p in val if viol(p) == 0]
    S = min(val[p][1] for p in sat)
    print("h", H, "J_e", JE, "sumB(13)", SB, "S_{K+} =", S, " S - sumB =", S - SB, "time %.0fs" % (time.time() - t0))
    print("satisfied patterns", len(sat), "spread", max(val[p][1] for p in sat) - S)
    worst = min((val[p][0] - S - JE * viol(p), p) for p in val if viol(p) > 0)
    print("min over violated of (lo - S - J_e*credits) =", worst)
    for p in sorted(val, key=lambda q: val[q][0] - S - JE * viol(q))[:6]: print(p, viol(p), "lo-S %.6f" % (val[p][0] - S), "margin %.6f" % (val[p][0] - S - JE * viol(p)))
