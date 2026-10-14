import sys, itertools, numpy as np
import scheme, scheme2, qstar, gluelib
from schemerun2 import surrogate_Y, GRAPHS
for g in ("K3","K4","K33"):
    n,edges=GRAPHS[g]; L=scheme2.build(n,edges,8,20,RW=13); lib=qstar.library(); A,dsz=qstar.point_arrays(L); Y=surrogate_Y(L)
    pats=list(itertools.product((0,1),repeat=n))[:16]
    worst_cost=0; worst_sl=1e9; worst_shift=0; viol=0
    for vb in pats:
        sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz); Q=A+D
        Qs=gluelib.snap(Q,1e-5); Ds=Qs-A
        worst_shift=max(worst_shift,float(np.abs(Qs-Q).max())); worst_cost=max(worst_cost,abs(qstar.cost(Ds)-qstar.cost(D)))
        chk=qstar.check(A,Ds,Y,tol=0.0,chunk=300); worst_sl=min(worst_sl,chk['min_slack']); viol+=chk['violations']
    print(g,"patterns",len(pats),"max snapping shift of a coordinate %.2e"%worst_shift,"| |cost(snapped)-cost(unsnapped)| max %.2e"%worst_cost,"| snapped Q: violations with tolerance 0:",viol,"min slack %.2e"%worst_sl,flush=True)
