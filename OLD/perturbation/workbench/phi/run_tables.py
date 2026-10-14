"""run_tables.py -- library tables for a cost phi.  usage: run_tables.py NAME [p] [h] [a_weak]
Reports, for each block, S - sum B (excess of satisfied pattern) and rho_B = min over violated patterns of (lo - S)/credit(tau)
(credits in units of J_e; rho_B is the largest admissible J_e for that block).  Rigorous lower bounds `lo` (interval dual)."""
import sys, os, math, itertools, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
GAD = '/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad'
import phi_dual as pd
sys.modules['np_dual'] = pd
sys.path.insert(0, GAD)
from multiprocessing import Pool

CFG = {}
def init(name, p, h):
    pd.set_phi(name, h=h, p=p)

def blockrun(args):
    sw, fixedown = args
    blk = pd.Block(sw)
    fixed = {blk.own[i]: b for i, b in fixedown}
    lo, hi, _, st = pd.branch_and_bound(blk, fixed, tol=1e-8)
    return lo, hi

def table(pool, sw, terms, rels):
    """terms: indices of switches whose bits are enumerated; rels (i,j,kind,credit) among terms (indices in sw). returns dict"""
    pats = list(itertools.product((0, 1), repeat=len(terms)))
    out = pool.map(blockrun, [(sw, list(zip(terms, p))) for p in pats], chunksize=2)
    res = dict(zip(pats, out))
    ix = {t: k for k, t in enumerate(terms)}
    def viol(p): return sum(c for (i, j, k, c) in rels if ((p[ix[i]] == p[ix[j]]) != (k == 'eq')))
    sat = [p for p in res if viol(p) == 0]
    S = min(res[p][1] for p in sat)
    SB = sum(pd.B_closed(s[2]) for s in sw)
    spread = max(res[p][1] for p in sat) - S
    rho = min(((res[p][0] - S) / viol(p), p) for p in res if viol(p) > 0)
    return dict(S=S, SB=SB, X=S - SB, spread=spread, rho=rho[0], rho_pat=rho[1], res=res, viol=viol, sat=sat, nsat=len(sat))

def main():
    name = sys.argv[1]; p = float(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2] != '-' else None
    h = float(sys.argv[3]) if len(sys.argv) > 3 else 4 * math.log(1.05)
    aw = float(sys.argv[4]) if len(sys.argv) > 4 else 3.75
    only = sys.argv[5].split(',') if len(sys.argv) > 5 else None
    init(name, p, h)
    print("PHI", pd.PHI.name, "h", h, "a_weak", aw, flush=True)
    JE = 2 * float(pd.PHI.f((4 - aw) * h / 2)); ES = 2 * float(pd.PHI.f(h / 2))
    print("closed forms: B(4)=%.6f B(5)=%.6f  E_S(natural)=2phi(h/2)=%.6f  J_e=2phi((4-a)h/2)=%.6f  E_S/J_e=%.3f" % (pd.B_closed(4), pd.B_closed(5), ES, JE, ES / JE), flush=True)
    from np_pair_exact import U
    from np_chain import uchain, vchain
    from np_cross import crossing
    from np_star import star
    from np_kplus import kplus, TERM as KT, RELS as KR
    pool = Pool(8, initializer=init, initargs=(name, p, h))
    rep = {}
    def want(k): return only is None or k in only
    def show(k, r, extra=''):
        rep[k] = r['rho']
        print("%-26s S-sumB=%.3e (spread %.1e, nsat %d)  rho=%.6f (rho/J_e=%.3f) at %s %s" % (k, r['X'], r['spread'], r['nsat'], r['rho'], r['rho'] / JE, r['rho_pat'], extra), flush=True)
    t0 = time.time()
    if want('pair'):
        sw = [U(0, 0), U(3, -3)]; r = table(pool, sw, [0, 1], [(0, 1, 'ne', 1)]); print("U strong a=3: true equal-bits excess e_S = %.9f (natural %.9f)" % (r['rho'], ES), flush=True)
        eS = r['rho']
        sw = uchain([aw]); r = table(pool, sw, [0, 1], [(0, 1, 'ne', 1)]); print("U weak a=%g: true equal-bits excess e_W = %.9f (natural J_e %.9f)" % (aw, r['rho'], JE), "e_S/e_W = %.3f" % (eS / r['rho']), flush=True)
    if want('V'):
        for n in (2, 3, 4):
            sw = vchain(n); show("V chain %d" % n, table(pool, sw, list(range(n)), [(i, i + 1, 'eq', 2) for i in range(n - 1)]))
    if want('Uchain'):
        for steps in ([3, 3], [3, aw], [aw, 3], [3, aw, 3], [3, 3, 3]):
            sw = uchain(steps); n = len(sw)
            show("U chain %s" % steps, table(pool, sw, list(range(n)), [(i, i + 1, 'ne', (1 if abs(steps[i] - aw) < 1e-9 else 2)) for i in range(n - 1)]))
    if want('corner'):
        os.chdir(GAD)
        import np_lib
        sw25 = np_lib.sw
        for nm, ids, rels in [("corner V0,u0,u1", [0, 9, 10], [(0, 9, 'eq'), (9, 10, 'ne')]), ("corner V1,V0,u0", [1, 0, 9], [(1, 0, 'eq'), (0, 9, 'eq')]),
                              ("corner V1,V0,u0,u1", [1, 0, 9, 10], [(1, 0, 'eq'), (0, 9, 'eq'), (9, 10, 'ne')]), ("corner V0,u0,u1,u2", [0, 9, 10, 11], [(0, 9, 'eq'), (9, 10, 'ne'), (10, 11, 'ne')]),
                              ("corner V2,V1,V0,u0", [2, 1, 0, 9], [(2, 1, 'eq'), (1, 0, 'eq'), (0, 9, 'eq')]), ("vertex-U pair", [13, 14], [(13, 14, 'ne')])]:
            S_ = [sw25[i] for i in ids]
            show(nm, table(pool, S_, list(range(len(ids))), [(ids.index(i), ids.index(j), k, 2) for (i, j, k) in rels]))
        os.chdir(HERE)
    if want('K'):
        sw = crossing(); terms = [0, 3, 4, 8]
        r = table(pool, sw, terms, [(4, 8, 'eq', 1), (0, 3, 'ne', 1)])
        show("crossing K", r, "X_K=%.7f" % r['X'])
        for pat in sorted(r['res']):
            print("    K pattern", pat, "excess over S: %.6f" % (r['res'][pat][0] - r['S']), "viol credit", r['viol'](pat))
    if want('star'):
        for arms in [('NW', 'SE', 'SW')]:
            sw, names, rel = star(arms, True); n = len(sw)
            show("star %s" % (arms,), table(pool, sw, list(range(n)), rel))
    if want('Kplus'):
        sw = kplus(); TERM = KT
        r = table(pool, sw, list(TERM), KR)
        K = rep.get('K')
        show("K+ (13 switches)", r, "S_{K+}-sumB=%.7f" % r['X'])
    print("done %.0fs" % (time.time() - t0))
    pool.close()
    print("SUMMARY rho_min = %.6f  rho_min/J_e = %.3f ; E_S/4J_e = %.3f" % (min(rep.values()), min(rep.values()) / JE, ES / (4 * JE)))

if __name__ == '__main__':
    main()
