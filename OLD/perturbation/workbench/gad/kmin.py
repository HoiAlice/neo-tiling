"""kappa_min: minimal b (real) such that b*1 + eta is weakly solvable at Q (window cone).  LP over the chain graph with a free variable b."""
import sys; sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as Fr
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
def kmin_lp(P,eta,graph=None):
    """P: list of Fraction pairs; eta: list of floats (profile).  returns b*"""
    G=graph or planar.chain_graph(P); T,A=G.T,len(G.arcs)
    idx={node:k for k,node in enumerate(G.nodes)}; n_int=len(G.nodes)
    nv=A+T+1; bcol=A+T
    rows,cols,vals=[],[],[]
    for k,(u,v,out,_) in enumerate(G.arcs):
        if u in idx: rows.append(idx[u]); cols.append(k); vals.append(-1.0)
        if v in idx: rows.append(idx[v]); cols.append(k); vals.append(1.0)
        for q in out: rows.append(n_int+q); cols.append(k); vals.append(1.0)
    for q in range(T):
        rows.append(n_int+q); cols.append(A+q); vals.append(1.0)
        rows.append(n_int+q); cols.append(bcol); vals.append(-1.0)
    Aeq=coo_matrix((vals,(rows,cols)),shape=(n_int+T,nv)).tocsr()
    beq=np.concatenate([np.zeros(n_int),np.asarray(eta,float)])
    rows,cols,vals=[],[],[]
    for k,(_,_,_,bnd) in enumerate(G.arcs):
        for q in bnd: rows.append(q); cols.append(k); vals.append(-1.0)
    for q in range(T): rows.append(q); cols.append(A+q); vals.append(1.0)
    Aub=coo_matrix((vals,(rows,cols)),shape=(T,nv)).tocsr()
    c=np.zeros(nv); c[bcol]=1.0
    bounds=[(0,None)]*(A+T)+[(None,None)]
    res=linprog(c,A_ub=Aub,b_ub=np.zeros(T),A_eq=Aeq,b_eq=beq,bounds=bounds,method="highs")
    assert res.status==0,res.message
    return res.fun
