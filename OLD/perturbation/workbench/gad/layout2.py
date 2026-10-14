import itertools, numpy as np, pickle, sys
import layout as Lm
from layout import *
import milp_layout2
SQ=(2.75,3.0,3.25,3.5)
def q_steps(total,l):
    """l steps, multiples of 1/4 in [2.75,3.5], summing to total (total multiple of 1/4) or None"""
    T=round(total*4)
    if abs(T-total*4)>1e-6: return None
    lo,hi=11,14   # in quarters
    if not (lo*l<=T<=hi*l): return None
    base=T//l; rem=T-base*l
    st=[base]*l
    for i in range(rem): st[i]+=1
    # spread: alternate to be symmetric-ish
    st=sorted(st)
    return [x/4 for x in st]
def arm_steps2(P,weak):
    if weak is None:
        for l in range(3,30):
            s=q_steps(P,l)
            if s: return s
        return None
    l=weak
    s=q_steps(P-3.75,l-1)
    if s is None: return None
    h=(l-1)//2
    return s[:h]+[3.75]+s[h:]
def link_options2(P,weak,kind):
    out=[]
    if weak:
        for l in range(7,16,2):
            st=arm_steps2(P,l)
            if st: out.append((l,st))
    else:
        for l in range(5 if kind=='pure' else 3,30):
            s=q_steps(P,l)
            if s: out.append((l,s))
    return out
Lm.link_options=link_options2
Lm.arm_steps=arm_steps2
# the module-level name used inside build_instance is link_options (looked up in layout globals)
def gen(nv,edges,rs,seed,tl=40):
    sol=milp_layout2.solve_layout(nv,edges,set(rs),time_limit=tl,seed=seed)
    if sol is None: return None
    inst,err=Lm.build_instance(sol,edges,set(rs),nv)
    if inst is None: return None
    return sol,inst

import np_tiling
from k4ub import build_chains
def tiling_check(sol,inst):
    chains,by_edge=build_chains(sol,inst); rep=[]; ok=True
    for k,(ids,kinds,A,B,hw) in chains.items():
        w=ids[1:-1]                  # w[0]=core switch next to A ... w[-1]=core switch next to B
        r=len(w)-2
        j=None
        for i,kd in enumerate(kinds):
            if kd=='W': j=i-1        # kinds[i] links ids[i],ids[i+1]; w_0=ids[1] -> link index i-1
        if r<2 or (j is not None and not (2<=j<=r-2)): ok=False; rep.append((k,"FAIL",r,j)); continue
        P2,P1=np_tiling.construct(r,j); np_tiling.verify(r,j); rep.append((k,"ok",r,j,P2,P1))
    return ok,rep
