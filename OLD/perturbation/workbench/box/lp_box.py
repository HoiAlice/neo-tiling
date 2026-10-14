"""Full BOX at d=2 as a polynomial LP.
LP(P,y,kappa): points W = {SW_t = P_t/kappa} u {NE_t = kappa*P_t} (2T points in Q-space).
Feasible iff exists w in WeaklySolvableCone(W) with w(SW_t) >= y_t >= w(NE_t).
Reuses planar.chain_graph (exact rational combinatorics) and builds the flow LP with one-sided y-rows."""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from fractions import Fraction
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
import planar

def W_points(P,kappa):
    """kappa: scalar, or array (T,2) of per-coordinate factors kappa_ti >= 1 (box [P/kappa, kappa*P])."""
    K=np.broadcast_to(np.asarray(kappa,float),np.shape(P))
    Kf=[[Fraction(float(v)).limit_denominator(10**9) for v in row] for row in K]
    Pf=[[Fraction(float(v)).limit_denominator(10**9) for v in row] for row in P]
    return [(Pf[t][0]/Kf[t][0],Pf[t][1]/Kf[t][1]) for t in range(len(Pf))]+[(Pf[t][0]*Kf[t][0],Pf[t][1]*Kf[t][1]) for t in range(len(Pf))]

def lp_box(P,y,kappa,tol=1e-9,return_sol=False):
    T=len(P); W=W_points(P,kappa); G=planar.chain_graph(W); n2=2*T
    A=len(G.arcs); idx={nd:k for k,nd in enumerate(G.nodes)}; n_int=len(G.nodes)
    # vars: f(A), g(n2), p(n2) violation cost, m(n2) free slack
    nv=A+3*n2
    rows,cols,vals=[],[],[]
    for k,(u,v,out,_) in enumerate(G.arcs):
        if u in idx: rows.append(idx[u]);cols.append(k);vals.append(-1.0)
        if v in idx: rows.append(idx[v]);cols.append(k);vals.append(1.0)
        for q in out: rows.append(n_int+q);cols.append(k);vals.append(1.0)
    for q in range(n2):
        # row: w_q + c_q - d_q = y ; SW: w>=y: cost var is p (+), free is m (-):  w + p - m = y
        # NE: w<=y: w + p - m = y with p free, m costed.  Encode: var1 (coef +1) var2 (coef -1)
        rows+= [n_int+q]*3; cols+=[A+q,A+n2+q,A+2*n2+q]; vals+=[1.0,1.0,-1.0]
    Aeq=coo_matrix((vals,(rows,cols)),shape=(n_int+n2,nv)).tocsr()
    yy=[float(v) for v in y]
    beq=np.concatenate([np.zeros(n_int),np.asarray(yy+yy)])
    rows,cols,vals=[],[],[]
    for k,(_,_,_,bnd) in enumerate(G.arcs):
        for q in bnd: rows.append(q);cols.append(k);vals.append(-1.0)
    for q in range(n2): rows.append(q);cols.append(A+q);vals.append(1.0)
    Aub=coo_matrix((vals,(rows,cols)),shape=(n2,nv)).tocsr()
    c=np.zeros(nv)
    # SW rows: costed = p (index A+n2+q) (w+p>=y); NE rows: costed = m (A+2*n2+q)
    for q in range(T): c[A+n2+q]=1.0
    for q in range(T,n2): c[A+2*n2+q]=1.0
    res=linprog(c,A_ub=Aub,b_ub=np.zeros(n2),A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*nv,method="highs")
    assert res.status==0,res.message
    if return_sol: return res.fun<=tol*max(1.0,sum(yy)), res.fun, G, res.x[:A], W
    return res.fun<=tol*max(1.0,sum(yy)), res.fun

def kappa_lp(P,y,hi=None,iters=40):
    """bisection on kappa>=1 (monotone). returns kappa*"""
    if lp_box(P,y,1.0)[0]: return 1.0
    lo=1.0; hi=hi or 2.0
    while not lp_box(P,y,hi)[0]:
        hi*=2
        if hi>1e6: return np.inf
    for _ in range(iters):
        m=(lo*hi)**0.5
        if lp_box(P,y,m)[0]: hi=m
        else: lo=m
    return hi
