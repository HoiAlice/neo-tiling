import numpy as np, sys, itertools
sys.path.insert(0,'.')
from lib import brute_L1
from scipy.optimize import linprog
def lp_inter(U,lev,order,keep_within=True):
    """order: list of point indices = ξ' order (a total order of all points). cross pairs signs from it; optionally within-class order kept."""
    T=len(U); xi=U[:,0]-U[:,1]; et=U[:,0]+U[:,1]; pos={p:k for k,p in enumerate(order)}
    A=[];b=[]
    def row(): return np.zeros(3*T)
    for t in range(T):
        for v,o in ((xi[t],0),(et[t],T)):
            r=row(); r[o+t]=1; r[2*T+t]=-1; A.append(r); b.append(v)
            r=row(); r[o+t]=-1; r[2*T+t]=-1; A.append(r); b.append(-v)
    for t in range(T):
        for s in range(T):
            if lev[s]<lev[t]:
                sg=1 if pos[t]>pos[s] else -1
                r=row(); r[T+t]=1; r[T+s]=-1; r[t]=-sg; r[s]=sg; A.append(r); b.append(0)
    for a in range(T):
        for c in range(a+1,T):
            if pos[a]<pos[c]:   # keep consecutive order xi'_a <= xi'_c (all pairs, total order)
                r=row(); r[a]=1; r[c]=-1; A.append(r); b.append(0)
    cc=np.zeros(3*T); cc[2*T:]=1
    res=linprog(cc,A_ub=np.array(A),b_ub=b,bounds=[(None,None)]*(2*T)+[(0,None)]*T,method="highs")
    return res.fun if res.status==0 else np.inf
def best_interleave(U,lev):
    T=len(U); xi=U[:,0]-U[:,1]
    H=sorted([t for t in range(T) if lev[t]==2],key=lambda t:xi[t]); L=sorted([t for t in range(T) if lev[t]==1],key=lambda t:xi[t])
    best=np.inf
    for pos in itertools.combinations(range(T),len(H)):
        order=[None]*T; hi=iter(H); li=iter(L)
        for k in range(T): order[k]=next(hi) if k in pos else next(li)
        best=min(best,lp_inter(U,lev,order))
    return best
if __name__=="__main__":
    rng=np.random.default_rng(int(sys.argv[1])); n=bad=0
    for it in range(60):
        T=int(rng.integers(4,9)); U=rng.normal(size=(T,2)); lev=rng.integers(1,3,size=T)
        if len(set(lev))<2: continue
        b=brute_L1(U,lev); r=best_interleave(U,lev); n+=1
        if abs(r-b)>1e-6: bad+=1; print("mismatch",T,b,r)
        assert r>=b-1e-7
    print("n",n,"interleaving-LP != brute:",bad)
