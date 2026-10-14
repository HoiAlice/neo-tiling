import sys, itertools, numpy as np
import cx2
from core import solve_dom, polish_margin, weakly_solvable
from ysolve import find_y
import term
g,h0,h2=0.01,0.01,0.04
BASE=1.0
def vertex(cx,cy,base=BASE,stubs=('SW','NE')):
    """center box (d=5) with box-centre (cx,cy); returns list of switches (center first)."""
    out=[(cx-2.5,cy-2.5,5,base+g,base)]
    if 'SW' in stubs: out.append((cx-1-2.5,cy-1-2.5,5,base+g+h0,base+h0))
    if 'NE' in stubs: out.append((cx+1-2.5,cy+1-2.5,5,base+g-h2,base-h2))
    return out
def uwire(cx,cy,steps,base=BASE,dirn=(1,-1)):
    """U switches (d=4) whose box centres start at (cx,cy)+step along dirn; returns (list, endcentre)"""
    out=[]; p=0
    for s in steps:
        p+=s; c=(cx+dirn[0]*p,cy+dirn[1]*p); out.append((c[0]-2,c[1]-2,4,base+g,base))
    return out,(cx+dirn[0]*p,cy+dirn[1]*p)
def table(sw,idx,procs=5,verbose=True):
    tb=term.term_table(sw,idx,procs=procs); mn=min(tb.values())
    if verbose:
        for s,v in sorted(tb.items()): print(s,round(v-mn,5),flush=True)
    return tb,mn
def solv(sw,idx,combos):
    A,Y,conf,ks=cx2.setup(sw); Qs=[]
    for fx in combos:
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=500)
        cm,u=polish_margin(A,conf,r[1],1e-6); Qs.append(np.exp(u))
    per=[find_y([Q],Y,1e-6,100) is not None for Q in Qs]
    y=find_y(Qs,Y,1e-6,100)
    w0=[weakly_solvable(Q,Y) for Q in Qs]
    wy=None if y is None else [weakly_solvable(Q,y) for Q in Qs]
    # minimal infeasible set if joint infeasible
    mi=None
    if y is None:
        keep=list(range(len(sw))); 
        for i in range(len(sw)):
            tr=[j for j in keep if j!=i]; ii=[2*j+c for j in tr for c in (0,1)]
            if find_y([Q[ii] for Q in Qs],Y[ii],1e-6,100) is None: keep=tr
        mi=keep
    return dict(per_combo_feasible=per,joint=y is not None,weak_at_given_y=w0,weak_at_found_y=wy,minimal_infeasible=mi)
if __name__=="__main__":
    v1=vertex(2.5,2.5)
    w,end=uwire(2.5,2.5,[3,3,3.75,3,3])    # last switch is vertex2's centre position -> build vertex2 there
    v2=vertex(end[0],end[1])
    sw=v1+w[:-1]+v2
    idx=[0,len(v1)+len(w)-1]
    for i,s in enumerate(sw): print(i,tuple(round(float(x),3) for x in s))
    tb,mn=table(sw,idx)
    print(solv(sw,idx,[(0,1),(1,0)]))
