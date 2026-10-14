"""Weakly reachable sets at d=2 = prefixes (with tie freedom) of the order of xi.Q, xi=(th,1-th), th in [0,1].
Enumerate them and decompose y = sum m_S 1_S by LP (sparse, min total mass)."""
import sys, numpy as np, itertools
from scipy.optimize import linprog
def breakpoints(Q,tol=1e-12):
    n=len(Q); th=set([0.0,1.0])
    for a in range(n):
        for b in range(a+1,n):
            d=Q[a]-Q[b]; den=d[0]-d[1]
            if abs(den)>tol:
                t=-d[1]/den
                if 0<t<1: th.add(float(t))
    return sorted(th)
def family(Q,tie=1e-9,maxtie=3):
    th=breakpoints(Q); pts=[]
    for i,t in enumerate(th):
        pts.append(t)
        if i+1<len(th): pts.append((t+th[i+1])/2)
    fam={}
    for t in pts:
        v=Q@np.array([t,1-t]); o=np.argsort(v,kind="stable"); vs=v[o]
        n=len(Q); cuts=[]
        # prefixes at cluster boundaries; inside a tie cluster allow every subset (size<=maxtie)
        k=0
        while k<n:
            j=k
            while j+1<n and vs[j+1]-vs[j]<=tie*max(1,abs(vs[j])): j+=1
            base=frozenset(o[:k].tolist()); grp=o[k:j+1].tolist()
            if len(grp)<=maxtie:
                for r in range(len(grp)+1):
                    for sub in itertools.combinations(grp,r): fam[base|frozenset(sub)]=t
            else: fam[base]=t; fam[base|frozenset(grp)]=t
            k=j+1
    fam.pop(frozenset(),None)
    return fam
def decompose(Q,y,fam=None,ties=1e-9):
    fam=fam or family(Q,ties); S=list(fam); n=len(Q)
    A=np.zeros((n,len(S)))
    for j,s in enumerate(S): A[list(s),j]=1
    r=linprog(np.ones(len(S)),A_eq=A,b_eq=y,bounds=(0,None),method="highs")
    if r.status!=0: return None,S
    return {S[j]:r.x[j] for j in np.nonzero(r.x>1e-9)[0]},S
if __name__=="__main__":
    d=np.load(sys.argv[1]); y=d['y']; k=int(sys.argv[2]) if len(sys.argv)>2 else 0
    Q=d['Qs'][k]; fam=family(Q); print("family size",len(fam))
    dec,_=decompose(Q,y,fam)
    print("decomposable",dec is not None)
    if dec:
        for s,m in sorted(dec.items(),key=lambda x:-x[1]): print(round(m,5),"th=%.3f"%fam[s],len(s),sorted(s))
