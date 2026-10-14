"""Search integer V-lengths n_e and solve vertex positions + arm lengths for K4 using the 4 CE corner types and pure U edges."""
import itertools, numpy as np, sys
from wedge import options, N
# allowed arm length P (sum of steps) : links 2k+1, steps s in [SMIN,SMAX] plus one weak 3.75
SMIN,SMAX,W=2.6,3.5,3.75
def okP(P):
    k=1
    while 3.75+2*k*SMIN<=P+1e-9+ (0):
        if 3.75+2*k*SMIN-1e-9<=P<=3.75+2*k*SMAX+1e-9: return True
        k+=1
        if k>12: break
    return False
def edge_vec(typ,n,L):
    """displacement B-A in bottoms; L = arm length P (CE) or m (pure). typ: ('pure') or (aa,bb)"""
    if typ=="pure": return np.array([L,-L])
    aa,bb=typ
    if (aa,bb)==("NW","SW"): return np.array([n-L+0.5,n+L+0.5])
    if (aa,bb)==("SE","SW"): return np.array([n+L+0.5,n-L+0.5])
    if (aa,bb)==("SE","NE"): return np.array([L-n-0.5,-n-L-0.5])
    if (aa,bb)==("NW","NE"): return np.array([-n-L-0.5,L-n-0.5])
def solve(combo,ns,nv=4):
    """unknowns: positions p_v (2*nv), L_e per edge; equations p_B-p_A=edge_vec(n,L)  (affine in L). fix p_0=0."""
    E=len(combo); nu=2*nv+E
    M=[];rhs=[]
    for e,(kind,A,B,aa,bb) in enumerate(combo):
        typ="pure" if kind=="pure" else (aa,bb)
        v0=edge_vec(typ,ns[e],0.0); v1=edge_vec(typ,ns[e],1.0)-v0
        for c in range(2):
            r=np.zeros(nu); r[2*B+c]=1; r[2*A+c]=-1; r[2*nv+e]=-v1[c]; M.append(r); rhs.append(v0[c])
    for c in range(2):
        r=np.zeros(nu); r[c]=1; M.append(r); rhs.append(0.0)
    M=np.array(M); rhs=np.array(rhs)
    if abs(np.linalg.det(M))<1e-9: return None
    x=np.linalg.solve(M,rhs); return x
def search(nv,Eg,nrange=range(3,13),limit=20):
    from wedge import search as wsearch
    sols=wsearch(nv,Eg,True)
    found=[]
    for combo in sols:
        ce=[e for e,c in enumerate(combo) if c[0]=="CE"]
        for nsel in itertools.product(nrange,repeat=len(ce)):
            ns=[0]*len(combo)
            for e,nn in zip(ce,nsel): ns[e]=nn
            x=solve(combo,ns,nv)
            if x is None: continue
            L=x[2*nv:]
            good=True
            for e,c in enumerate(combo):
                if c[0]=="pure":
                    # pure: 3.75+2k s, m allowed like arm lengths (odd links)
                    if not okP(L[e]): good=False
                else:
                    if not okP(L[e]): good=False
            if good: found.append((combo,ns,x))
        if len(found)>=limit: break
    return found
if __name__=="__main__":
    K3=[(0,1),(0,2),(1,2)]; K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    for name,nv,Eg in (("K4",4,K4),):
        f=search(nv,Eg,limit=50); print(name,"layouts with integer n and allowed arm lengths:",len(f))
        for combo,ns,x in f[:5]:
            print(" combo",[(c[0],c[1],c[2],c[3],c[4]) for c in combo]," n",ns)
            print("   pos",np.round(x[:2*nv].reshape(nv,2),2).tolist()," L",np.round(x[2*nv:],2).tolist())
