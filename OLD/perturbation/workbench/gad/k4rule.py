import sys, time, numpy as np
from k4weak import *
import planar
from fractions import Fraction
def yrule(lv,F,g=0.01):
    y=[]
    for (bx,by,d,_,_) in lv:
        sc=bx+by+d; b=F(sc); y+= [b+g,b]
    return np.array(y)
def conc(c1,c2,sstar,smax):
    return lambda s: 1+ (c2*(smax-max(s,sstar)) if True else 0) + c1*max(sstar-s,0)
if __name__=="__main__":
    init(); pat=(0,0,1,1)
    u,c=glue_Q(pat); Q=np.exp(snap(u,1e-5))
    Pf=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]
    t0=time.time(); g=planar.chain_graph(Pf); print("graph built",round(time.time()-t0),flush=True)
    from layout import levels
    sol,inst=G["sol"],G["inst"]; lv=levels(inst["sw"])
    sc=[bx+by+d for (bx,by,d,_,_) in lv]; smax=max(sc); smin=min(sc); print("s range",smin,smax,flush=True)
    rules=[("lin c=0.02",lambda s:1+0.02*(smax-s)),("lin c=0.05",lambda s:1+0.05*(smax-s)),("lin c=0.2",lambda s:1+0.2*(smax-s))]
    for sst in (-12,-8,-4,0,4):
        rules.append(("conc(0.02,0.07,s*=%d)"%sst,conc(0.02,0.07,sst,smax)))
    for name,F in rules:
        y=yrule(lv,F); yf=[Fraction(float(v)).limit_denominator(10**9) for v in y]
        r=planar.flow_lp(Pf,yf,graph=g); print(name,"max/min %.3f"%(y.max()/y.min()),"weakly solvable:",r.feasible,"t",round(time.time()-t0),flush=True)
