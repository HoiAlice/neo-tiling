"""np_farkas_gen.py -- dump rational dual (Farkas-type) certificates for the crossing core K: for each of the 5 symmetry classes of terminal patterns a branch tree
whose leaves carry RATIONAL multipliers (denominator 2^20); np_farkas_check.py re-verifies them with exact Fraction arithmetic only (no mpmath, no numpy)."""
import json, sys
from fractions import Fraction
from np_dual import *
from np_cross import crossing
sw = crossing(); blk = Block(sw)
PATS = [(0,1,0,0), (0,1,0,1), (0,0,1,1), (0,0,0,0), (0,0,0,1)]
TERM = (0, 3, 4, 8)
Q = 2**20
def tree(assign, lam0, T, depth=0):
    val, lam, x = dual_float(blk, assign, lam0)
    if val >= T + 2e-9:
        return {"lam": {str(k): str(Fraction(round(v * Q), Q)) for k, v in lam.items() if v > 0}}
    v = violated(blk, assign, x)
    if v is None: raise RuntimeError("leaf below target %.9f < %.9f" % (val, T))
    k = v[1]; ch = []
    for c in (0, 1):
        a2 = dict(assign); a2[k] = c; ch.append(tree(a2, lam, T, depth + 1))
    return {"k": k, "ch": ch}
def count(t): return 1 if "lam" in t else count(t["ch"][0]) + count(t["ch"][1])
out = {"switches": sw, "rho": "21/20", "term": TERM, "patterns": []}
for p in PATS:
    fixed = {blk.own[i]: b for i, b in zip(TERM, p)}
    lo, hi, _, st = branch_and_bound(blk, fixed, tol=1e-9)
    T = Fraction(round((lo - 1e-6) * 10**6), 10**6)
    t = tree(dict(fixed), None, float(T))
    out["patterns"].append({"bits": p, "T": str(T), "tree": t})
    print(p, "claimed lower bound T =", float(T), "leaves", count(t), flush=True)
json.dump(out, open("np_farkas_K.json", "w"))
