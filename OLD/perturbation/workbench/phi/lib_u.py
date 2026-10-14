"""lib_u.py -- whole library with parametrised strong step u (and attach offset att, weak offset aw), cost chosen by NAME.
usage: lib_u.py NAME p h u att aw [blocks]"""
import sys, os, math, itertools, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import run_tables as rt
from run_tables import *
G = 0.01
def lev(sc): b = 1 - 0.02 * sc; return (b + G, b)
def vsw(bx, by): return (bx, by, 5) + lev(bx + by + 5)
def usw(cx, cy): return (cx - 2, cy - 2, 4) + lev(cx + cy)
def uchain(steps, base=1.0):
    sw = [(0.0, 0.0, 4, base + G, base)]; p = 0.0
    for st in steps: p += st; sw.append((p, -p, 4, base + G, base))
    return sw
def vchain(n, step=0.04, base=1.0): return [(float(j), float(j), 5, base + G - step * j, base - step * j) for j in range(n)]
def vlev(s):
    sh = -0.02 * s if s < 0 else -0.04 * s
    return (1 + G + sh, 1 + sh)
def crossing(u):
    sw = [((j - 1.5) * u, -(j - 1.5) * u, 4, 1 + G, 1.0) for j in range(4)]
    for s in range(-2, 3):
        tp, bt = vlev(s); sw.append((s - 0.5, s - 0.5, 5, tp, bt))
    return sw
def kplus(u):
    sw = [((j - 2.5) * u, -(j - 2.5) * u, 4, 1 + G, 1.0) for j in range(6)]
    for s in range(-3, 4):
        tp, bt = vlev(s); sw.append((s - 0.5, s - 0.5, 5, tp, bt))
    return sw
def star(arms, u, att, outward=True):
    sw = [vsw(-0.5, -0.5)]; rel = []; cen = (2.0, 2.0)
    for a in arms:
        if a in ('NW', 'SE'):
            sg = -1 if a == 'NW' else 1
            i1 = len(sw); sw.append(usw(cen[0] + att * sg, cen[1] - att * sg)); rel.append((0, i1, 'ne', 1))
            if outward:
                i2 = len(sw); sw.append(usw(cen[0] + (att + u) * sg, cen[1] - (att + u) * sg)); rel.append((i1, i2, 'ne', 2))
        else:
            sg = -1 if a == 'SW' else 1
            i1 = len(sw); sw.append(vsw(-0.5 + sg, -0.5 + sg)); rel.append((0, i1, 'eq', 1))
            if outward:
                i2 = len(sw); sw.append(vsw(-0.5 + 2 * sg, -0.5 + 2 * sg)); rel.append((i1, i2, 'eq', 2))
    return sw, rel
def corner(u, nV, nU):
    """V chain (V_{nV-1}..V0) ending at the corner switch u0 aligned with V0, then U chain u0..u_{nU-1} NW with step u"""
    sw = []
    for j in range(nV - 1, -1, -1):
        sw.append((-4.5 + j, -4.5 + j, 5, 1.09 - 0.02 * j + 0.01, 1.09 - 0.02 * j) if False else (-4.5 + j, -4.5 + j, 5, 1.09 - 0.02 * j, 1.08 - 0.02 * j))
    for k in range(nU):
        sw.append((-4.5 - k * u, -4.5 + k * u, 4, 1.1, 1.09))
    rel = [(i, i + 1, 'eq', 2) for i in range(nV - 1)] + [(nV - 1, nV, 'eq', 2)] + [(nV + k, nV + k + 1, 'ne', 2) for k in range(nU - 1)]
    return sw, rel

def main():
    name = sys.argv[1]; p = None if sys.argv[2] == '-' else float(sys.argv[2]); h = float(sys.argv[3])
    u, att, aw = float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6])
    only = sys.argv[7].split(',') if len(sys.argv) > 7 else None
    rt.init(name, p, h)
    f = lambda x: float(pd.PHI.f(x))
    JE = 2 * f((4 - aw) * h / 2); ES = 2 * f((4 - u) * h / 2)
    print("PHI %s h=%g u=%g att=%g aw=%g  E_S=%.6g J_e=%.6g  E_S/J_e=%.3f" % (pd.PHI.name, h, u, att, aw, ES, JE, ES / JE), flush=True)
    pool = Pool(8, initializer=rt.init, initargs=(name, p, h))
    rep = {}; t0 = time.time()
    def want(k): return only is None or k in only
    def show(k, r, extra=''):
        rep[k] = r['rho']
        print("%-24s S-sumB=%.2e spread %.1e nsat %d  rho=%.6g  rho/J_e=%.2f at %s %s" % (k, r['X'], r['spread'], r['nsat'], r['rho'], r['rho'] / JE, r['rho_pat'], extra), flush=True)
    def tab(sw, rel):
        n = len(sw); return table(pool, sw, list(range(n)), rel)
    if want('pair'):
        r = tab(uchain([u]), [(0, 1, 'ne', 1)]); print("U strong pair: true e_S=%.6g natural %.6g" % (r['rho'], ES))
        r = tab(uchain([aw]), [(0, 1, 'ne', 1)]); print("U weak pair:   true e_W=%.6g natural %.6g" % (r['rho'], JE), flush=True)
    if want('U'):
        for st in ([u, u], [u, aw], [aw, u], [u, aw, u], [u, u, u]):
            sw = uchain(st); show("U chain %s" % st, tab(sw, [(i, i + 1, 'ne', 1 if abs(st[i] - aw) < 1e-9 else 2) for i in range(len(st))]))
    if want('V'):
        for n in (2, 3, 4): show("V chain %d" % n, tab(vchain(n), [(i, i + 1, 'eq', 2) for i in range(n - 1)]))
    if want('corner'):
        for nV, nU in [(1, 2), (2, 1), (2, 2), (3, 1), (1, 3), (2, 3)]:
            sw, rel = corner(u, nV, nU); show("corner V%d U%d" % (nV, nU), tab(sw, rel))
    if want('K'):
        r = table(pool, crossing(u), [0, 3, 4, 8], [(4, 8, 'eq', 1), (0, 3, 'ne', 1)]); show("K", r, "X_K=%.7g" % r['X'])
        print("   K excess over S:", {k: round(v[0] - r['S'], 6) for k, v in sorted(r['res'].items())})
    if want('star'):
        for arms in [('NW', 'SW'), ('NW', 'NE'), ('SE', 'SW'), ('SE', 'NE'), ('NW', 'SE'), ('SW', 'NE'), ('NW', 'SE', 'SW'), ('NW', 'SE', 'NE'), ('NW', 'SW', 'NE'), ('SE', 'SW', 'NE'), ('NW', 'SE', 'SW', 'NE')]:
            sw, rel = star(arms, u, att); show("star %s" % ('+'.join(arms),), tab(sw, rel))
    if want('Kplus'):
        TERM = (0, 1, 4, 5, 6, 7, 11, 12)
        RELS = [(0, 1, 'ne', 2), (4, 5, 'ne', 2), (6, 7, 'eq', 2), (11, 12, 'eq', 2), (1, 4, 'ne', 1), (7, 11, 'eq', 1)]
        r = table(pool, kplus(u), list(TERM), RELS); show("K+", r, "S_{K+}-sumB=%.7g" % r['X'])
    print("done %.0fs; rho_min/J_e = %.2f" % (time.time() - t0, min(rep.values()) / JE if rep else float('nan')))
    pool.close()
if __name__ == '__main__':
    main()
