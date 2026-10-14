"""np_pgap.py -- interval-certified version of P-GAP.md for the crossing core K (layout level order, rational step).
C = conflicts, C^P = {(tau b, tau a) : (a,b) in C} with tau = point reflection about the centre (2,2) of K (swaps tops/bottoms).
Claim: for each U phase, every Q feasible for C_sym = C cap C^P with cost < E_sym + margin satisfies the pairs of C \\ C^P; hence E = E_sym and
E(phase 0) = E_sym(phase 0) = E_sym(phase 1) = E(phase 1) (Thm 1 of CROSSING-PROOF.md, tau-invariance of C_sym).
Lower bounds: B&B with interval duals; a violated pair (a,b) is imposed as the two forced edges x_b,c <= x_a,c (c=0,1)."""
import itertools, sys
from fractions import Fraction
import numpy as np
from np_dual import *
from np_cross import crossing
sw = crossing(); blk0 = Block(sw)
G = blk0.G
tau = []
for p in G:
    q = (Fraction(4) - p[0], Fraction(4) - p[1]); tau.append(G.index(q))
assert all(tau[tau[i]] == i for i in range(len(G)))
C = set(blk0.conf)
CP = {(tau[b], tau[a]) for (a, b) in C}
asym = sorted(C - CP); asym2 = sorted(CP - C)
print("|C|", len(C), "|C^P|", len(CP), "|C \\ C^P|", len(asym), "|C^P \\ C|", len(asym2))
print("C \\ C^P (point index pairs, a higher):", asym)
Csym = sorted(C & CP)
def make_block(extra=None):
    b = Block(sw); b.conf = list(Csym)
    if extra:
        a_, b_ = extra
        b.conf += [(b_, a_), (b_, a_)]          # two pseudo conflicts, forced to coordinates 0 and 1: x_b <= x_a in both coordinates
    b.cidx = {c: k for k, c in enumerate(b.conf)}
    b.own = [b.cidx[(2 * i, 2 * i + 1)] for i in range(len(sw))]
    return b
T = (0, 3, 4, 8)
def phase_bits(phi):   # U terminals: U_in=U0 bit phi, U_out=U3 bit 1-phi (antiferro 4 switches), V bit 0
    return (phi, 1 - phi, 0, 0)
for phi in (0, 1):
    b = make_block()
    fixed = {b.own[i]: v for i, v in zip(T, phase_bits(phi))}
    lo, hi, asg, st = branch_and_bound(b, fixed, tol=1e-7)
    print("phase", phi, "E_sym lo %.9f hi %.9f" % (lo, hi), flush=True)
    Es = hi
    for (a_, b_) in asym:
        bb = make_block(extra=(a_, b_)); n = len(bb.conf)
        fixed = {bb.own[i]: v for i, v in zip(T, phase_bits(phi))}
        fixed[n - 2] = 0; fixed[n - 1] = 1
        lo2, hi2, _, st2 = branch_and_bound(bb, fixed, tol=1e-7, target=Es + 0.5)
        print("   pair", (a_, b_), "violated: lower bound %.6f  (E_sym + %.4f)" % (min(lo2, Es + 0.5), min(lo2, Es + 0.5) - Es), flush=True)
