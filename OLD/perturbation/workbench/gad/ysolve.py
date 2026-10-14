"""Find numeric y (same strict order/ties as the given y) such that several fixed Q are all weakly solvable."""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def find_y(Qs, Y0, delta=1e-3, ymax_ratio=1.9):
    T=len(Y0)
    levels=sorted(set(np.round(Y0,9)),reverse=True); L=len(levels)
    lev=[levels.index(round(v,9)) for v in Y0]
    graphs=[planar.chain_graph([tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]) for Q in Qs]
    # variable layout: z (L), then per graph: f (A_m), g (T)
    offs=[L]; 
    for G in graphs: offs.append(offs[-1]+len(G.arcs)+T)
    nv=offs[-1]
    Aeq=lil_matrix((sum(len(G.nodes)+T for G in graphs),nv)); r=0
    Aub=lil_matrix((sum(T for G in graphs)+L+2,nv)); ru=0; bub=[]
    for G,o in zip(graphs,offs):
        A=len(G.arcs); idx={n:k for k,n in enumerate(G.nodes)}; n_int=len(G.nodes)
        for k,(u,v,out,bnd) in enumerate(G.arcs):
            if u in idx: Aeq[r+idx[u],o+k]-=1
            if v in idx: Aeq[r+idx[v],o+k]+=1
            for q in out: Aeq[r+n_int+q,o+k]+=1
            for q in bnd: Aub[ru+q,o+k]-=1
        for q in range(T):
            Aeq[r+n_int+q,o+A+q]+=1; Aeq[r+n_int+q,lev[q]]-=1   # sum out f + g - z = 0
            Aub[ru+q,o+A+q]+=1; bub.append(0)
        r+=n_int+T; ru+=T
    for i in range(L-1):          # z_{i+1} - z_i <= -delta
        Aub[ru,i+1]=1; Aub[ru,i]=-1; bub.append(-delta); ru+=1
    Aub[ru,L-1]=-1; bub.append(-1.0); ru+=1              # z_min >= 1
    Aub[ru,0]=1; Aub[ru,L-1]=-ymax_ratio; bub.append(0); ru+=1   # z_max <= ratio*z_min
    res=linprog(np.zeros(nv),A_ub=Aub[:ru].tocsr(),b_ub=bub,A_eq=Aeq.tocsr(),b_eq=np.zeros(Aeq.shape[0]),bounds=[(0,None)]*nv,method="highs")
    if res.status!=0: return None
    z=res.x[:L]; return np.array([z[lev[q]] for q in range(T)])
