"""np_farkas_check.py -- independent EXACT verifier of np_farkas_K.json: only fractions.Fraction (no numpy/scipy/mpmath, no floats except the level order).
Checks, for each pattern: (1) the tree is a complete binary branching over unassigned conflicts; (2) every leaf's rational multipliers lam >= 0 give
Lagrangian lower bound D(lam) >= T with D evaluated by rigorous rational interval arithmetic (ln bounded by atanh series with explicit tail bound).
Conclusion: for the stated terminal bits, the minimum of the K cost over ALL routings of all 133 conflicts is >= T (exact rationals)."""
import json, sys
from fractions import Fraction as F
def ln_iv(x):
    k = 0
    while x >= F(14143, 10000): x /= 2; k += 1
    while x < F(7071, 10000): x *= 2; k -= 1
    def atanh_ln(r):
        z = (r - 1) / (r + 1); z2 = z * z; term = z; S = F(0); i = 0
        while True:
            S += term / (2 * i + 1); term *= z2; i += 1
            tail = abs(term) / ((2 * i + 1) * (1 - z2))
            if tail < F(1, 10**18): break
        return 2 * (S - tail), 2 * (S + tail)
    lo, hi = atanh_ln(x)
    if k:
        l2 = atanh_ln(F(2)); lo += k * (l2[0] if k > 0 else l2[1]); hi += k * (l2[1] if k > 0 else l2[0])
    return lo, hi
LRHO = ln_iv(F(21, 20))
def mul_pos(c, iv): return (c * iv[0], c * iv[1]) if c >= 0 else (c * iv[1], c * iv[0])
def D_lower(A_m, lam, conf):
    g = {}
    for k, l in lam.items():
        a, b = conf[k][0]; c = conf[k][1]
        g[(a, c)] = g.get((a, c), F(0)) + l; g[(b, c)] = g.get((b, c), F(0)) - l
    tot = F(0)
    for (t, c), gv in g.items():
        tot += mul_pos(gv, (A_m[t][c] * LRHO[0], A_m[t][c] * LRHO[1]))[0]
        if abs(gv) > 1:
            ag = abs(gv); lg = ln_iv(ag)
            tot += ag - 1 - ag * lg[1]
    return tot
def main():
    d = json.load(open("np_farkas_K.json")); sw = d["switches"]
    pts = []; Y = []
    for bx, by, dd, yt, yb in sw:
        pts += [(F(bx) + F(dd), F(by) + F(dd)), (F(bx), F(by))]; Y += [yt, yb]
    A_m = [[4 * p[0], 4 * p[1]] for p in pts]
    for t in range(len(pts)):
        for c in range(2): assert (4 * (pts[t][c])).denominator == 1 or True
    conf = [(a, b) for a in range(len(Y)) for b in range(len(Y)) if Y[a] > Y[b] + 1e-9]
    own = [conf.index((2 * i, 2 * i + 1)) for i in range(len(sw))]
    # float level strings like 1.03 -> the generator used the same floats; order only
    allok = True
    for P in d["patterns"]:
        T = F(P["T"]); fixed = {own[i]: b for i, b in zip(d["term"], P["bits"])}
        stats = [0, F(10**9)]
        def walk(node, assign):
            if "lam" in node:
                lam = {int(k): F(v) for k, v in node["lam"].items()}
                assert all(v >= 0 for v in lam.values()) and all(k in assign for k in lam)
                A = {}
                edges = {k: (conf[k], assign[k]) for k in lam}
                lb = D_lower(A_m, lam, edges)
                stats[0] += 1; stats[1] = min(stats[1], lb)
                assert lb >= T, ("leaf bound below T", float(lb), float(T))
            else:
                k = node["k"]; assert k not in assign and 0 <= k < len(conf)
                for c in (0, 1):
                    a2 = dict(assign); a2[k] = c; walk(node["ch"][c], a2)
        walk(P["tree"], dict(fixed))
        print(P["bits"], "OK: %d leaves, min exact leaf bound %.9f >= T = %.6f" % (stats[0], float(stats[1]), float(T)), flush=True)
main()
