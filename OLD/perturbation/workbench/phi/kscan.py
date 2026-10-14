"""kscan.py -- crossing core K (gad/np_cross geometry) under a family of costs; prints X_K and the excess of the 12 non-satisfied patterns over S.
usage: kscan.py NAME p h1,h2,..."""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_tables as rt
from run_tables import *
def go(name, p, hs):
    from np_cross import crossing
    for h in hs:
        rt.init(name, p, h)
        pool = Pool(8, initializer=rt.init, initargs=(name, p, h))
        r = table(pool, crossing(), [0, 3, 4, 8], [(4, 8, 'eq', 1), (0, 3, 'ne', 1)])
        pool.close()
        ex = {pat: r['res'][pat][0] - r['S'] for pat in r['res']}
        grp = {'Vbrk(0101)': ex[(0,1,0,1)], 'Ubrk(0011)': ex[(0,0,1,1)], 'Ubrk(0000)': ex[(0,0,0,0)], 'both(0001)': ex[(0,0,0,1)]}
        ES = 2 * float(pd.PHI.f(h / 2))
        print("%s p=%s h=%.4f  X_K=%.6g  X_K/E_S=%.3f  spread %.1e | " % (pd.PHI.name, p, h, r['X'], r['X'] / ES, r['spread']) + "  ".join("%s %.4g (%.3f E_S)" % (k, v, v / ES) for k, v in grp.items()), "OK" if min(grp.values()) > 0 else "FAIL", flush=True)
if __name__ == '__main__':
    name = sys.argv[1]; p = None if sys.argv[2] == '-' else float(sys.argv[2])
    go(name, p, [float(x) for x in sys.argv[3].split(',')])
