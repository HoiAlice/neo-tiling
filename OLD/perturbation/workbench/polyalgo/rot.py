import numpy as np, sys
sys.path.insert(0,'.')
from lib import brute_L1
from scipy.optimize import linprog
def rot_lp(U, lev, signs=None):
    """K=2 (or any K: pair constraints between levels). Variables xi',eta' (2T), c (T). cost = sum c_t, c>=|dxi|,|deta| (Linf = L1 in x,y).
    pair (t high, s low): eta'_t-eta'_s <= sg*(xi'_t-xi'_s), sg=+-1 fixed from ORIGINAL xi order unless given."""
    T=len(U); xi=U[:,0]-U[:,1]; et=U[:,0]+U[:,1]
    A=[];b=[]
    def row(): return np.zeros(3*T)
    for t in range(T):
        for k,(v,o) in enumerate(((xi[t],0),(et[t],T))):
            r=row(); r[o+t]=1; r[2*T+t]=-1; A.append(r); b.append(v)
            r=row(); r[o+t]=-1; r[2*T+t]=-1; A.append(r); b.append(-v)
    for t in range(T):
        for s in range(T):
            if lev[s]<lev[t]:
                sg=1 if (signs is None and xi[t]>=xi[s]) else (-1 if signs is None else signs[t,s])
                r=row(); r[T+t]=1; r[T+s]=-1; r[t]=-sg; r[s]=sg; A.append(r); b.append(0)
    c=np.zeros(3*T); c[2*T:]=1
    res=linprog(c,A_ub=np.array(A),b_ub=b,bounds=[(None,None)]*(2*T)+[(0,None)]*T,method="highs")
    return res.fun
if __name__=="__main__":
    rng=np.random.default_rng(int(sys.argv[1])); n=bad=0; worst=0
    for K in (2,3):
      for it in range(40):
        T=int(rng.integers(4,11)); U=rng.normal(size=(T,2)); lev=rng.integers(1,K+1,size=T)
        if len(set(lev))<K: continue
        b=brute_L1(U,lev); r=rot_lp(U,lev); n+=1
        if r>b+1e-7: bad+=1; worst=max(worst,r-b)
        assert r>=b-1e-7
    print("n",n,"rotLP(fixed original xi-order) > brute:",bad,"max gap",worst)
