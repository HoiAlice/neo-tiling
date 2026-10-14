"""np_star.py -- interval-certified credit certificate for vertex stars with outward neighbours (degree 3 and 4), all bit patterns.
Geometry (grid units, centre switch bottom (-0.5,-0.5), d=5 => centre (2,2)); y = 1 - 0.02*(x+y of switch centre), top = bottom + 0.01.
Arms: NW U-attach centre offset (-3,+3), SE (+3,-3) (d=4); SW V neighbour bottom (-1.5,-1.5), NE (0.5,0.5) (d=5);
outward neighbours: one more switch on each present arm (U: another 3 along the arm; V: another 1).  Relations: centre=SW, centre=NE (eq), centre!=NW, centre!=SE (ne),
star-internal credit 1 (units J_e), outward link credit 2."""
import itertools, math, sys, time
from multiprocessing import Pool
from np_dual import *
JE = 2 * (math.exp(H / 8) - 1)
g = 0.01
def lev(sc): b = 1 - 0.02 * sc; return (b + g, b)
def vsw(bx, by): return (bx, by, 5) + lev(bx + by + 5)
def usw(cx, cy): return (cx - 2, cy - 2, 4) + lev(cx + cy)
def star(arms, outward=True):
    sw = [vsw(-0.5, -0.5)]; names = ['c']; rel = []
    cen = (2.0, 2.0)
    for a in arms:
        if a in ('NW', 'SE'):
            sgn = -1 if a == 'NW' else 1
            n1 = usw(cen[0] + 3 * sgn, cen[1] - 3 * sgn); n2 = usw(cen[0] + 6 * sgn, cen[1] - 6 * sgn)
            i1 = len(sw); sw.append(n1); names.append(a)
            rel += [(0, i1, 'ne', 1)]
            if outward:
                i2 = len(sw); sw.append(n2); names.append(a + '+'); rel += [(i1, i2, 'ne', 2)]
        else:
            sgn = -1 if a == 'SW' else 1
            n1 = vsw(-0.5 + sgn, -0.5 + sgn); n2 = vsw(-0.5 + 2 * sgn, -0.5 + 2 * sgn)
            i1 = len(sw); sw.append(n1); names.append(a)
            rel += [(0, i1, 'eq', 1)]
            if outward:
                i2 = len(sw); sw.append(n2); names.append(a + '+'); rel += [(i1, i2, 'eq', 2)]
    return sw, names, rel
def work(args):
    sw, p = args
    blk = Block(sw); fixed = {blk.own[i]: b for i, b in enumerate(p)}
    lo, hi, _, st = branch_and_bound(blk, fixed, tol=1e-8); return p, lo, hi
if __name__ == "__main__":
    import sys
    ARMS = [('NW', 'SE', 'SW'), ('NW', 'SE', 'NE'), ('NW', 'SW', 'NE'), ('SE', 'SW', 'NE'), ('NW', 'SE', 'SW', 'NE')]
    if len(sys.argv) > 1 and sys.argv[1] == 'deg2':
        ARMS = [('NW', 'SW'), ('NW', 'NE'), ('SE', 'SW'), ('SE', 'NE'), ('NW', 'SE'), ('SW', 'NE')]
    OUT = not (len(sys.argv) > 2 and sys.argv[2] == 'core')
    if len(sys.argv) > 1 and sys.argv[1] == 'all': ARMS = [('NW','SW'),('NW','NE'),('SE','SW'),('SE','NE'),('NW','SE'),('SW','NE')] + ARMS
    for arms in ARMS:
        sw, names, rel = star(arms, OUT); n = len(sw); SB = sum(B_closed(s[2]) for s in sw)
        t0 = time.time()
        with Pool(8) as pool: out = pool.map(work, [(sw, p) for p in itertools.product((0, 1), repeat=n)], chunksize=4)
        res = {p: (lo, hi) for p, lo, hi in out}
        def viol(p): return sum(c for (i, j, k, c) in rel if ((p[i] == p[j]) != (k == 'eq')))
        sat = [p for p in res if viol(p) == 0]; S = min(res[p][1] for p in sat)
        worst = min(((res[p][0] - S - JE * viol(p)), p) for p in res if viol(p) > 0)
        print(arms, "n", n, "S-sumB %.2e" % (S - SB), "sat", len(sat), "min margin %.6f at %s" % worst, "%.0fs" % (time.time() - t0), flush=True)
