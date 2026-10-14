"""kvar.py -- variants of the crossing core geometry (U step u, V box dV, V step vs) under a given cost; K table (16 patterns)."""
import sys, os, math, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import run_tables as rt
from run_tables import *
from np_cross import vlev, g
def crossing_var(u=3.0, dV=5, vs=1.0, nU=4):
    sw = []
    for j in range(nU):
        t = (j - (nU - 1) / 2) * u
        sw.append((t, -t, 4, 1 + g, 1.0))
    for s in range(-2, 3):
        tp, bt = vlev(s); c = 2 + s * vs
        sw.append((c - dV / 2, c - dV / 2, dV, tp, bt))
    return sw
def run(name, p, h, u, dV, vs, pool):
    sw = crossing_var(u, dV, vs)
    try:
        r = table(pool, sw, [0, 3, 4, 8], [(4, 8, 'eq', 1), (0, 3, 'ne', 1)])
    except Exception as e:
        print(u, dV, vs, "ERR", e); return None
    ES = 2 * float(pd.PHI.f(h * (4 - u) / 2)) if u < 4 else float('nan')
    ex = {k: v[0] - r['S'] for k, v in r['res'].items()}
    nsat = r['nsat']
    viol = {k: ex[k] for k in ex if r['viol'](k) > 0}
    print("%s u=%.2f dV=%g vs=%.2f nsat %d spread %.1e X=%.5f  min viol-excess %.5f at %s | V %.4f Ub0011 %.4f Ub0000 %.4f" % (pd.PHI.name, u, dV, vs, nsat, r['spread'], r['X'], min(viol.values()), min(viol, key=viol.get), ex[(0,1,0,1)], ex[(0,0,1,1)], ex[(0,0,0,0)]), flush=True)
    return r
if __name__ == '__main__':
    name = sys.argv[1]; p = None if sys.argv[2] == '-' else float(sys.argv[2]); h = float(sys.argv[3])
    rt.init(name, p, h)
    pool = Pool(8, initializer=rt.init, initargs=(name, p, h))
    for u in [float(x) for x in sys.argv[4].split(',')]:
        for dV in [float(x) for x in sys.argv[5].split(',')]:
            for vs in [float(x) for x in sys.argv[6].split(',')]:
                run(name, p, h, u, dV, vs, pool)
