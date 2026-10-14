"""Independent test of Theorem 5: rho_inf (boxes [P/k, kP]) is a critical value; LP truth constant between critical values; exact closed-box LP."""
import sys
from fractions import Fraction as F
import numpy as np
from exactbox import decide_closed
from crit import critical_kappas
def fk(x): return F(float(x)).limit_denominator(10**13)
def dec(P,y,k):
    k=fk(k);return decide_closed([(p0/k,p1/k) for p0,p1 in P],[(p0*k,p1*k) for p0,p1 in P],y)
rng=np.random.default_rng(int(sys.argv[1]));N=int(sys.argv[2]);ok=0;tested=0
for it in range(N):
    T=int(rng.integers(3,5))
    P=[(F(int(a),4),F(int(b),4)) for a,b in rng.integers(2,17,(T,2))]
    y=[F(int(v)) for v in rng.integers(0,4,T)]
    if dec(P,y,1.0): continue
    cr=[c for c in critical_kappas([(float(a),float(b)) for a,b in P]) if c>=1.0]
    if not dec(P,y,max(cr)*1.5): continue
    tested+=1
    pts=[]
    for i in range(len(cr)-1): pts.append(("mid",i,(cr[i]+cr[i+1])/2,dec(P,y,(cr[i]+cr[i+1])/2)))
    pts.append(("above",len(cr),cr[-1]*1.5,True))
    seq=[p[3] for p in pts]
    mono=all(not(seq[i] and not seq[i+1]) for i in range(len(seq)-1))      # F..F T..T
    first=next(i for i,v in enumerate(seq) if v)                                  # first True interval (cr[first-1],cr[first]) hmm
    # the transition is at the critical value separating the last False interval from the first True interval
    kc=cr[first] if first>0 else cr[0]
    below=dec(P,y,kc*(1-1e-9)); at_above=dec(P,y,kc*(1+1e-11))
    good=mono and (not below) and at_above
    # and the transition lies exactly at kc: BOX true at kc itself (closed)
    ok+=good
    if not good: print("FAIL",it,seq,kc)
print("Theorem 5 test: instances with kappa*>1:",tested,"; monotone, transition exactly at a critical value, BOX false at kc(1-1e-9), true at kc(1+1e-11) (kc is irrational in general, so exact equality cannot be tested in rationals):",ok)
