"""find_y with an objective (copy of ysolve.find_y, not editing it): minimise sum_i |z_i - z0_i| (L1 deviation from the given level profile Y0, normalised by Y0.min),
or minimise ratio zmax/zmin if mode='ratio'.  Same strict order/ties as Y0, margin delta between consecutive levels."""
import sys
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
def find_y_obj(Qs,Y0,delta=1e-4,mode="dev",ratio_cap=100.0):
    T=len(Y0); levels=sorted(set(np.round(Y0,9)),reverse=True); L=len(levels)
    lev=[levels.index(round(v,9)) for v in Y0]
    graphs=[planar.chain_graph([tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]) for Q in Qs]
    offs=[L]
    for G in graphs: offs.append(offs[-1]+len(G.arcs)+T)
    extra=L if mode=="dev" else 1           # |z-z0| aux (dev) or the ratio variable r=zmax (with zmin fixed =1)
    nv=offs[-1]+extra
    Aeq=lil_matrix((sum(len(G.nodes)+T for G in graphs),nv)); r=0
    Aub=lil_matrix((sum(T for G in graphs)+L+2+2*L,nv)); ru=0; bub=[]
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
    for i in range(L-1): Aub[ru,i+1]=1; Aub[ru,i]=-1; bub.append(-delta); ru+=1
    Aub[ru,L-1]=-1; bub.append(-1.0); ru+=1
    Aub[ru,0]=1; Aub[ru,L-1]=-ratio_cap; bub.append(0); ru+=1
    c=np.zeros(nv); z0=np.array(levels)/min(levels)
    if mode=="dev":
        base=offs[-1]
        for i in range(L):
            # d_i >= z_i - z0_i ; d_i >= z0_i - z_i
            Aub[ru,i]=1; Aub[ru,base+i]=-1; bub.append(z0[i]); ru+=1
            Aub[ru,i]=-1; Aub[ru,base+i]=-1; bub.append(-z0[i]); ru+=1
            c[base+i]=1
    else:
        base=offs[-1]; Aub[ru,0]=1; Aub[ru,base]=-1; bub.append(0); ru+=1; c[base]=1
    res=linprog(c,A_ub=Aub[:ru].tocsr(),b_ub=bub,A_eq=Aeq.tocsr(),b_eq=np.zeros(Aeq.shape[0]),bounds=[(0,None)]*nv,method="highs")
    if res.status!=0: return None
    z=res.x[:L]; return np.array([z[lev[q]] for q in range(T)]),levels,z,res.fun
if __name__=="__main__":
    d=np.load(sys.argv[1]); Qs=list(d['Qs']); Y=d['Y']; mode=sys.argv[2]
    r=find_y_obj(Qs,Y,float(sys.argv[3]) if len(sys.argv)>3 else 1e-4,mode)
    if r is None: print("infeasible"); sys.exit()
    y,levels,z,f=r; print("obj",f,"ratio",y.max()/y.min())
    z0=np.array(levels)/min(levels)
    for lv,a,b in zip(levels,z0,z): print("level %.4f  handset(norm) %.5f  found %.5f"%(lv,a,b))
    np.savez(sys.argv[4] if len(sys.argv)>4 else "ws_y_%s.npz"%mode,y=y,Y=Y,Qs=np.array(Qs))
