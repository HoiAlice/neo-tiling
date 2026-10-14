"""Minimal-mass exact certificate: flow LP minimising the total flow (= total mass of sets), candidates from its path decomposition, exact simplex on the support."""
import sys; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as Fr
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
from ws_exact2 import exact_simplex, check, Fq
from ws_simplex import exact_lp
def min_flow(P,y):
    T=len(y); G=planar.chain_graph(P); A=len(G.arcs); idx={n:k for k,n in enumerate(G.nodes)}; n_int=len(G.nodes)
    nv=A+T; Aeq=lil_matrix((n_int+T,nv)); beq=np.zeros(n_int+T); Aub=lil_matrix((T,nv))
    for k,(u,v,out,bnd) in enumerate(G.arcs):
        if u in idx: Aeq[idx[u],k]-=1
        if v in idx: Aeq[idx[v],k]+=1
        for q in out: Aeq[n_int+q,k]+=1
        for q in bnd: Aub[q,k]-=1
    for q in range(T): Aeq[n_int+q,A+q]+=1; beq[n_int+q]=float(y[q]); Aub[q,A+q]+=1
    c=np.zeros(nv)
    for k,(u,v,out,bnd) in enumerate(G.arcs):
        if u==planar.SRC: c[k]=1
    r=linprog(c,A_ub=Aub.tocsr(),b_ub=np.zeros(T),A_eq=Aeq.tocsr(),b_eq=beq,bounds=[(0,None)]*nv,method="highs")
    return G,r
def certify3(P,y):
    G,r=min_flow(P,y)
    if r.status!=0: return None,"min-flow LP infeasible",None
    A=len(G.arcs); f=r.x[:A]; g=r.x[A:]; T=G.T; cand=set(); bl=np.zeros(T)
    for k,(_,_,_,bnd) in enumerate(G.arcs):
        for q in bnd: bl[q]+=f[k]
    for _,path in planar.decompose_flow(G,f):
        out=frozenset().union(*(G.arcs[k][2] for k in path)); bnd=frozenset().union(*(G.arcs[k][3] for k in path))
        cand.add(out); share=sorted((q for q in bnd if g[q]>1e-12),key=lambda q:-g[q]/bl[q])
        for j in range(1,len(share)+1): cand.add(out|frozenset(share[:j]))
        for q in bnd: cand.add(out|frozenset([q]))
    cand=[S for S in cand if planar.is_reachable(P,S,False)]
    cols=[tuple(1 if q in S else 0 for q in range(T)) for S in cand]
    Mx=np.array(cols,float).T
    res=linprog(np.ones(len(cols)),A_eq=Mx,b_eq=[float(v) for v in y],bounds=[(0,None)]*len(cols),method="highs-ds")
    if res.status!=0: return None,"candidate LP infeasible (%d)"%len(cand),r.fun
    sol=exact_lp(cols,y)
    if sol is None: return None,"exact solve failed",res.fun
    return [(cand[k],m) for k,m in sol],"ok",res.fun
