import numpy as np, itertools
from scipy.optimize import milp, LinearConstraint, Bounds, linprog
from scipy.sparse import lil_matrix

def brute_L1(U, lev, M=None):
    """Exact rho_dom, L1 cost in log coords, by big-M MILP over per-pair coordinate choice.
    Constraint: lev_s < lev_t  =>  not (u_s < u_t strictly in both)  i.e. u_t,x<=u_s,x or u_t,y<=u_s,y."""
    T=len(U); M = M or (np.ptp(U)+5)*2
    # vars: u(2T), d(2T), sigma(npairs*2)
    pairs=[(t,s) for t in range(T) for s in range(T) if lev[s]<lev[t]]
    nv=4*T+2*len(pairs); rows=[];lo=[];hi=[]
    A=lil_matrix((4*T+3*len(pairs),nv)); r=0
    for t in range(T):
        for c in range(2):
            ui=2*t+c; di=2*T+2*t+c
            A[r,di]=1;A[r,ui]=-1;lo.append(-U[t,c]);hi.append(np.inf);r+=1
            A[r,di]=1;A[r,ui]=1;lo.append(U[t,c]);hi.append(np.inf);r+=1
    for k,(t,s) in enumerate(pairs):
        b=4*T+2*k
        A[r,b]=1;A[r,b+1]=1;lo.append(1);hi.append(np.inf);r+=1
        for c in range(2):
            # u_t,c - u_s,c <= M(1-sig)
            A[r,2*t+c]=1;A[r,2*s+c]=-1;A[r,b+c]=M;lo.append(-np.inf);hi.append(M);r+=1
    A=A[:r].tocsr()
    cost=np.zeros(nv);cost[2*T:4*T]=1
    integ=np.zeros(nv);integ[4*T:]=1
    lb=np.full(nv,-np.inf);ub=np.full(nv,np.inf)
    lb[:2*T]=U.min()-3;ub[:2*T]=U.max()+3;lb[2*T:4*T]=0;lb[4*T:]=0;ub[4*T:]=1
    res=milp(cost,constraints=LinearConstraint(A,lo,hi),integrality=integ,bounds=Bounds(lb,ub))
    return res.fun

def grid_model(U, lev, costfun=None, xs=None, ys=None, relax=False):
    """Staircase / assignment formulation on a grid.  K-1 down-sets w^k, each point assigned a cell.
    Level j (1..K): w^k_c=1 for k<j ; w^k_{c+(1,1)}=0 for k>=j."""
    T=len(U); K=int(max(lev))
    xs=np.unique(U[:,0]) if xs is None else xs; ys=np.unique(U[:,1]) if ys is None else ys
    nx,ny=len(xs),len(ys)
    cf=costfun or (lambda d:abs(d))
    cx=lambda t,i:cf(U[t,0]-xs[i]); cy=lambda t,j:cf(U[t,1]-ys[j])
    nc=nx*ny; cell=lambda i,j:i*ny+j
    nW=(K-1)*nc; nA=T*nc; nv=nW+nA
    W=lambda k,i,j:(k-1)*nc+cell(i,j)  # k=1..K-1
    Aa=lambda t,i,j:nW+t*nc+cell(i,j)
    rows=[];  # (dict,lo,hi)
    def add(d,l,h): rows.append((d,l,h))
    for k in range(1,K):
        for i in range(nx):
            for j in range(ny):
                if i+1<nx: add({W(k,i,j):1,W(k,i+1,j):-1},0,np.inf)
                if j+1<ny: add({W(k,i,j):1,W(k,i,j+1):-1},0,np.inf)
    cost=np.zeros(nv)
    for t in range(T):
        add({Aa(t,i,j):1 for i in range(nx) for j in range(ny)},1,1)
        for i in range(nx):
            for j in range(ny):
                cost[Aa(t,i,j)]=cx(t,i)+cy(t,j)
                for k in range(1,K):
                    if k<lev[t]: add({Aa(t,i,j):1,W(k,i,j):-1},-np.inf,0)
                    else:
                        if i+1<nx and j+1<ny: add({Aa(t,i,j):1,W(k,i+1,j+1):1},-np.inf,1)
    A=lil_matrix((len(rows),nv));lo=[];hi=[]
    for r,(d,l,h) in enumerate(rows):
        for c,v in d.items(): A[r,c]=v
        lo.append(l);hi.append(h)
    integ=np.zeros(nv) if relax else np.ones(nv)
    res=milp(cost,constraints=LinearConstraint(A.tocsr(),lo,hi),integrality=integ,bounds=Bounds(0,1))
    return res.fun, res.x[nW:].reshape(T,nx,ny) if res.x is not None else None
