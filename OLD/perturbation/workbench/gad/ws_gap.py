"""Scale-free problem: maximise the minimal gap between consecutive levels subject to range<=1, order/ties of Y, weakly solvable (y=1+eps*eta, eps tiny: use scale 1e-3 and normalise)."""
import sys; sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def solve(Qs,Y0,scale=1e-3,fixgap=None):
    T=len(Y0); levels=sorted(set(np.round(Y0,9)),reverse=True); L=len(levels)
    lev=[levels.index(round(v,9)) for v in Y0]
    graphs=[planar.chain_graph([tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]) for Q in Qs]
    offs=[L]
    for G in graphs: offs.append(offs[-1]+len(G.arcs)+T)
    nv=offs[-1]+1  # t
    Aeq=lil_matrix((sum(len(G.nodes)+T for G in graphs),nv)); r=0
    Aub=lil_matrix((sum(T for G in graphs)+L+3,nv)); ru=0; bub=[]
    for G,o in zip(graphs,offs):
        A=len(G.arcs); idx={n:k for k,n in enumerate(G.nodes)}; n_int=len(G.nodes)
        for k,(u,v,out,bnd) in enumerate(G.arcs):
            if u in idx: Aeq[r+idx[u],o+k]-=1
            if v in idx: Aeq[r+idx[v],o+k]+=1
            for q in out: Aeq[r+n_int+q,o+k]+=1
            for q in bnd: Aub[ru+q,o+k]-=1
        for q in range(T):
            Aeq[r+n_int+q,o+A+q]+=1; Aeq[r+n_int+q,lev[q]]-=1
            Aub[ru+q,o+A+q]+=1; bub.append(0)
        r+=n_int+T; ru+=T
    tv=nv-1
    for i in range(L-1): Aub[ru,i+1]=1; Aub[ru,i]=-1; Aub[ru,tv]=1; bub.append(0); ru+=1   # z_{i+1}-z_i + t <= 0
    Aub[ru,L-1]=-1; bub.append(-1.0); ru+=1                                                # zmin>=1
    Aub[ru,0]=1; bub.append(1.0+scale); ru+=1                                              # zmax <= 1+scale
    c=np.zeros(nv); c[tv]=-1
    res=linprog(c,A_ub=Aub[:ru].tocsr(),b_ub=bub,A_eq=Aeq.tocsr(),b_eq=np.zeros(Aeq.shape[0]),bounds=[(0,None)]*nv,method="highs")
    if res.status!=0: return None
    z=res.x[:L]; return levels,z,res.x[tv]
if __name__=="__main__":
    d=np.load(sys.argv[1]); Qs=list(d['Qs']); Y=d['Y']
    r=solve(Qs,Y)
    if r is None: print("infeasible"); sys.exit()
    levels,z,t=r; print("min gap / range = ",t/1e-3)
    eta=(z-z.min())/(z.max()-z.min())
    for lv,e in zip(levels,eta): print("level %.4f eta %.4f"%(lv,e))
