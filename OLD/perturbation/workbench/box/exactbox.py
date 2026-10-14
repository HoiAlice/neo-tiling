"""Exact (rational) decision and construction for an ARBITRARY box  L <= Q <= U  at d = 2.
 delta_bound(L,U)  : explicit rational delta (Theorem A)
 decide(L,U,y)     : BOX(closed box)  <=>  LP(E_delta(box)),  exact simplex in Fractions
 construct(L,U,y,eps): exact rational Q in E_eps(box) (eps > delta) with y weakly solvable at Q (certified by planar.certify)
 dom_decide / dom_witness : dominance-only, any d, arbitrary boxes."""
import sys, itertools
sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
from fractions import Fraction as F
from math import gcd
import planar

def fr(x): return x if isinstance(x,F) else F(x)

# ---------------------------------------------------------------- delta
def delta_bound(L,U):
    """delta = min( 1/(2N(1+32A^2)), min L / 2 ), N = common denominator, A = N*max|coordinate|."""
    vals=[fr(v) for row in list(L)+list(U) for v in row]
    N=1
    for v in vals: N=N*v.denominator//gcd(N,v.denominator)
    A=max(abs(v) for v in vals)*N
    d1=F(1,1)/(2*N*(1+32*A*A))
    return min(d1, min(fr(v) for row in L for v in row)/2)

def corners(L,U,delta):
    d=fr(delta)
    return [(fr(a)-d,fr(b)-d) for a,b in L]+[(fr(a)+d,fr(b)+d) for a,b in U]

# ---------------------------------------------------------------- exact simplex (phase 1, Bland)
def simplex_feasible(rows,b,nvars):
    """rows: list of dict col->Fraction, b: list of Fractions. find x>=0 with Ax=b. returns x (list) or None."""
    m=len(rows)
    T=[]
    for r,bi in zip(rows,b):
        sgn=1 if bi>=0 else -1
        row=[F(0)]*(nvars+m+1)
        for c,v in r.items(): row[c]=sgn*v
        row[nvars+len(T)]=F(1); row[-1]=sgn*bi
        T.append(row)
    basis=[nvars+i for i in range(m)]
    # objective: minimize sum artificials -> reduced cost row z_j = -sum_i T[i][j] for j<nvars
    z=[F(0)]*(nvars+m+1)
    for i in range(m):
        for j in range(nvars): z[j]-=T[i][j]
        z[-1]-=T[i][-1]
    while True:
        enter=next((j for j in range(nvars) if z[j]<0),None)
        if enter is None: break
        # ratio test with Bland tie-break
        best=None;leave=None
        for i in range(m):
            a=T[i][enter]
            if a>0:
                ratio=T[i][-1]/a
                if best is None or ratio<best or (ratio==best and basis[i]<basis[leave]): best=ratio;leave=i
        if leave is None: return None  # unbounded cannot happen
        piv=T[leave][enter]
        T[leave]=[v/piv for v in T[leave]]
        for i in range(m):
            if i!=leave and T[i][enter]!=0:
                f=T[i][enter];Ti=T[i];Tl=T[leave]
                T[i]=[Ti[j]-f*Tl[j] for j in range(len(Ti))]
        f=z[enter];z=[z[j]-f*T[leave][j] for j in range(len(z))]
        basis[leave]=enter
    if z[-1]!=0: return None   # -z[-1] = sum artificials > 0 ... (z[-1] = -value)
    x=[F(0)]*nvars
    for i in range(m):
        if basis[i]<nvars: x[basis[i]]=T[i][-1]
    return x

def build_lp(W,y,T):
    G=planar.chain_graph(W); n2=len(W); A=len(G.arcs)
    idx={nd:k for k,nd in enumerate(G.nodes)}; n_int=len(G.nodes)
    # variables: f(A) g(n2) sigma(T) slack(n2)
    gi=A; si=A+n2; sl=A+2*n2; nv=sl+n2
    rows=[dict() for _ in range(n_int+n2+n2)]; b=[F(0)]*(n_int+n2+n2)
    for k,(u,v,out,bnd) in enumerate(G.arcs):
        if u in idx: rows[idx[u]][k]=F(-1)
        if v in idx: rows[idx[v]][k]=rows[idx[v]].get(k,F(0))+1
        for q in out: rows[n_int+q][k]=F(1)
        for q in bnd: rows[n_int+n2+q][k]=F(-1)
    for q in range(n2):
        rows[n_int+q][gi+q]=F(1)
        rows[n_int+q][si+q]=F(-1) if q<T else F(1)   # L: w-sigma=y (w>=y);  U: w+sigma=y (w<=y)
        b[n_int+q]=fr(y[q % T])
        rows[n_int+n2+q][gi+q]=F(1); rows[n_int+n2+q][sl+q]=F(1)
    return G,rows,b,nv,(A,gi,si,sl)

def decide_W(W,y,T,want=False):
    G,rows,b,nv,(A,gi,si,sl)=build_lp(W,y,T)
    x=simplex_feasible(rows,b,nv)
    if not want: return x is not None
    return (None if x is None else (G,x[:A],x[gi:gi+len(W)]))

def decide(L,U,y,delta=None):
    """exact decision of BOX(closed box) (Theorem A)."""
    T=len(L); d=delta_bound(L,U) if delta is None else fr(delta)
    return decide_W(corners(L,U,d),y,T)

# ---------------------------------------------------------------- sets and masses from the LP solution
def sets_and_masses(W,G,f,g):
    n2=len(W); loads=[F(0)]*n2
    for k,(_,_,_,bnd) in enumerate(G.arcs):
        for q in bnd: loads[q]+=f[k]
    phi=[ (g[q]/loads[q] if loads[q]>0 else F(0)) for q in range(n2)]
    fl=list(f); out=[]
    # exact path decomposition
    out_arcs={}
    for k,(u,*_r) in enumerate(G.arcs): out_arcs.setdefault(u,[]).append(k)
    SRC,SNK=planar.SRC,planar.SNK
    while True:
        start=[k for k in out_arcs[SRC] if fl[k]>0]
        if not start: break
        path=[];node=SRC
        while node!=SNK:
            k=max((j for j in out_arcs[node] if fl[j]>0),key=lambda j:fl[j]); path.append(k); node=G.arcs[k][1]
        m=min(fl[k] for k in path)
        for k in path: fl[k]-=m
        S0=frozenset().union(*(G.arcs[k][2] for k in path)); B=frozenset().union(*(G.arcs[k][3] for k in path))
        levels=sorted({phi[q] for q in B if phi[q]>0},reverse=True)
        prev=F(1)
        for c in levels:
            # mass for sets with boundary points of fraction >= c : (c - next)
            pass
        cs=levels+[F(0)]
        # set_j = S0 + {q in B: phi_q >= cs[j]}, mass m*(cs[j]-cs[j+1]) ; plus S0 alone with mass m*(1-cs[0]) if levels
        if levels:
            out.append((S0,m*(1-levels[0])))
            for j,c in enumerate(levels):
                Sj=S0|frozenset(q for q in B if phi[q]>=c)
                out.append((Sj,m*(c-cs[j+1])))
        else:
            out.append((S0,m))
    return [(S,m) for S,m in out if m>0]

# ---------------------------------------------------------------- exact construction of Q in E_eps(box)
def facets_of_K(Tp):
    """closed convex up-set K = conv(Tp)+R^2_+ as list of (xi, c): K = {z : xi.z >= c for all}.  Exact."""
    pts=list(set(Tp)); fac=[((F(1),F(0)),min(p[0] for p in pts)),((F(0),F(1)),min(p[1] for p in pts))]
    for a,b in itertools.combinations(pts,2):
        dx,dy=b[0]-a[0],b[1]-a[1]
        for xi in ((dy,-dx),(-dy,dx)):
            if xi[0]>=0 and xi[1]>=0 and (xi[0]>0 or xi[1]>0):
                c=xi[0]*a[0]+xi[1]*a[1]
                if all(xi[0]*p[0]+xi[1]*p[1]>=c for p in pts): fac.append((xi,c))
    return fac
def s_of(fac,z):
    return max((c-xi[0]*z[0]-xi[1]*z[1])/(xi[0]+xi[1]) for xi,c in fac)

def construct(L,U,y,eps,delta=None):
    T=len(L); d=delta_bound(L,U) if delta is None else fr(delta); eps=fr(eps); assert eps>d
    W=corners(L,U,d); res=decide_W(W,y,T,want=True)
    if res is None: return None
    G,f,g=res
    cert=sets_and_masses(W,G,f,g)
    cert=[(S,m) for S,m in cert if planar.is_reachable(W,sorted(S),strict=False)]
    Wp=corners(L,U,eps)                 # corners of the bigger box E_eps
    info=[]; eta=F(1)
    for S,m in cert:
        Tp=[W[q] for q in range(2*T) if q not in S]
        fac=facets_of_K(Tp) if Tp else None
        info.append((m,fac))
        if fac is None: continue
        for t in range(T):
            if t in S:                       # L_t in S -> need s_k(L'_t) > 0
                v=s_of(fac,Wp[t]); assert v>0,("margin",v); eta=min(eta,v)
            if (T+t) not in S:               # U_t not in S -> need s_k(U'_t) < 0
                v=s_of(fac,Wp[T+t]); assert v<0,("margin",v); eta=min(eta,-v)
    eta=eta/2
    def phi_at(z):
        tot=F(0)
        for m,fac in info:
            if fac is None: tot+=m; continue
            sv=s_of(fac,z); tot+=m*min(F(1),max(F(0),sv/eta))
        return tot
    Q=[]
    for t in range(T):
        lo,hi=Wp[t],Wp[T+t]
        pt=lambda s:(lo[0]+s*(hi[0]-lo[0]),lo[1]+s*(hi[1]-lo[1]))
        # breakpoints of phi(pt(s)) on [0,1]
        bps={F(0),F(1)}
        for m,fac in info:
            if fac is None: continue
            aff=[]   # s_j(z(s)) = (c - xi.lo - s xi.(hi-lo))/|xi| = a + b s
            for xi,c in fac:
                nrm=xi[0]+xi[1]
                aff.append(((c-xi[0]*lo[0]-xi[1]*lo[1])/nrm, -(xi[0]*(hi[0]-lo[0])+xi[1]*(hi[1]-lo[1]))/nrm))
            for (a1,b1),(a2,b2) in itertools.combinations(aff,2):
                if b1!=b2: bps.add((a2-a1)/(b1-b2))
            for a,bb in aff:
                if bb!=0: bps.add(-a/bb); bps.add((eta-a)/bb)
        bl=sorted(p for p in bps if 0<=p<=1)
        vals=[phi_at(pt(p)) for p in bl]
        assert vals[0]>=y[t] and vals[-1]<=y[t],("IVT bracket",vals[0],vals[-1],y[t])
        sol=None
        for i in range(len(bl)-1):
            v0,v1=vals[i],vals[i+1]
            if v0>=y[t]>=v1:
                sol=bl[i] if v0==v1 else bl[i]+(bl[i+1]-bl[i])*(v0-fr(y[t]))/(v0-v1); break
        if sol is None: sol=bl[-1]
        Q.append(pt(sol))
    return Q

def certify_Q(Q,y):
    c=planar.certify(Q,[fr(v) for v in y])
    return c is not None and planar.check_certificate(Q,[fr(v) for v in y],c)

# ---------------------------------------------------------------- dominance only (any d, arbitrary boxes)
def dom_decide(L,U,y):
    T=len(L); d=len(L[0])
    return all(any(fr(L[s][i])<=fr(U[t][i]) for i in range(d)) for s in range(T) for t in range(T) if y[s]>y[t])
def dom_witness(L,U,y):
    """Q_t = L_t + tau_t (U_t-L_t); tau_t = clip(max_{p: y_p>y_t} beta(p,t),0,1); beta = min_i b_i."""
    T=len(L);d=len(L[0]);INF=None
    Q=[]
    for t in range(T):
        tau=F(0)
        for p in range(T):
            if y[p]>y[t]:
                bs=[]
                for i in range(d):
                    w=fr(U[t][i])-fr(L[t][i]); diff=fr(L[p][i])-fr(L[t][i])
                    if w>0: bs.append(diff/w)
                    elif diff<=0: bs.append(F(-10**9))
                    else: bs.append(F(10**9))
                tau=max(tau,min(bs))
        tau=min(F(1),tau)
        Q.append(tuple(fr(L[t][i])+tau*(fr(U[t][i])-fr(L[t][i])) for i in range(d)))
    return Q

# ---------------------------------------------------------------- FINAL: closed-box decision and witness (no delta)
def decide_closed(L,U,y):
    """BOX(closed box) <=> LP(0): exists w in C(W_0), W_0 = (L_1..L_T,U_1..U_T), w(L_t) >= y_t >= w(U_t)."""
    return decide_W([(fr(a),fr(b)) for a,b in L]+[(fr(a),fr(b)) for a,b in U],y,len(L))

def construct_closed(L,U,y):
    """exact rational Q in [L,U] with y weakly solvable at Q (or None if LP(0) infeasible)."""
    T=len(L); W=[(fr(a),fr(b)) for a,b in L]+[(fr(a),fr(b)) for a,b in U]
    res=decide_W(W,y,T,want=True)
    if res is None: return None
    G,f,g=res
    cert=[(S,m) for S,m in sets_and_masses(W,G,f,g) if planar.is_reachable(W,sorted(S),strict=False)]
    # check that the reachable sets still reproduce the LP inequalities (exactness of the split)
    wL=[sum((m for S,m in cert if t in S),F(0)) for t in range(T)]
    wU=[sum((m for S,m in cert if T+t in S),F(0)) for t in range(T)]
    assert all(wL[t]>=fr(y[t])>=wU[t] for t in range(T)),"split lost"
    facs=[]
    for S,m in cert:
        Tp=[W[q] for q in range(2*T) if q not in S]
        facs.append((m,facets_of_K(Tp) if Tp else None))
    Q=[]
    for t in range(T):
        a,b=W[t],W[T+t]; dxy=(b[0]-a[0],b[1]-a[1])
        # lam_k = max over facets of s_j where xi.z(s) <= c  <=> s <= s_j ; None facet set => +inf (cap 1)
        caps=[]
        for m,fac in facs:
            if fac is None: caps.append((F(1),m)); continue
            best=None
            for xi,c in fac:
                den=xi[0]*dxy[0]+xi[1]*dxy[1]; num=c-xi[0]*a[0]-xi[1]*a[1]
                if den>0: sj=num/den
                else: sj= F(10**9) if num>=0 else F(-10**9)
                best=sj if best is None else max(best,sj)
            caps.append((min(F(1),best),m))
        yt=fr(y[t])
        if yt==0: s=F(1)
        else:
            cands=[c for c,m in caps if c>=0]
            s=None
            for c in sorted(set(cands),reverse=True):
                if sum((m for cc,m in caps if cc>=c),F(0))>=yt: s=c;break
            assert s is not None,"hi(0) < y"
        Q.append((a[0]+s*dxy[0],a[1]+s*dxy[1]))
    return Q
