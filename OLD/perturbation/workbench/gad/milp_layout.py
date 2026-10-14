"""MILP over segment types, arms, integer V lengths n_j, arm lengths L_j; potentials (s,t) of vertices."""
import itertools, numpy as np, sys
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
BIG=2000.0
WEAKV=3.75
def seg_options(p,q):
    out=[]
    for (A,B) in ((p,q),(q,p)):
        out.append(dict(kind="pure",A=A,B=B,aa="SE",bb="NW"))
    for (A,B) in ((p,q),(q,p)):
        for aa in ("NW","SE"):
            for bb in ("SW","NE"):
                out.append(dict(kind="CE",A=A,B=B,aa=aa,bb=bb))
    return out
def solve_layout(nv_orig,edges,relay_edges,deg_orig=3,time_limit=120,minsep=0.0,seed=None):
    """vertices 0..nv_orig-1 original; each edge in relay_edges gets a relay vertex (2 segments). returns dict or None"""
    verts=nv_orig; segs=[]; relay_of={}
    for e,(u,v) in enumerate(edges):
        if e in relay_edges:
            r=verts; verts+=1; relay_of[e]=r; segs.append((u,r,e)); segs.append((r,v,e))
        else: segs.append((u,v,e))
    S=len(segs); opts=[seg_options(p,q) for (p,q,e) in segs]
    # variable layout
    idx={}; n=0
    def new(name,k=1):
        nonlocal n; idx[name]=n; n+=k; return idx[name]
    for v in range(verts): new(("s",v)); new(("t",v))
    for j in range(S): new(("n",j)); new(("L",j))
    for j in range(S):
        for o in range(len(opts[j])): new(("z",j,o))
    LK=(3,5,7,9)
    for j in range(S):
        new(("w",j))
        for l in LK: new(("v",j,l))
    lb=np.full(n,-np.inf); ub=np.full(n,np.inf); integ=np.zeros(n)
    for v in range(verts):
        lb[idx[("s",v)]]=-400; ub[idx[("s",v)]]=400; lb[idx[("t",v)]]=-400; ub[idx[("t",v)]]=400
    lb[idx[("s",0)]]=ub[idx[("s",0)]]=0; lb[idx[("t",0)]]=ub[idx[("t",0)]]=0
    for j in range(S):
        lb[idx[("n",j)]]=3; ub[idx[("n",j)]]=14; integ[idx[("n",j)]]=1
        lb[idx[("L",j)]]=8.0; ub[idx[("L",j)]]=60
        for o in range(len(opts[j])): lb[idx[("z",j,o)]]=0; ub[idx[("z",j,o)]]=1; integ[idx[("z",j,o)]]=1
        lb[idx[("w",j)]]=0; ub[idx[("w",j)]]=1; integ[idx[("w",j)]]=1
        for l in LK: lb[idx[("v",j,l)]]=0; ub[idx[("v",j,l)]]=1; integ[idx[("v",j,l)]]=1
    rows=[];lo=[];hi=[]
    def add(coefs,l,h):
        rows.append(coefs); lo.append(l); hi.append(h)
    for j in range(S):
        add({idx[("z",j,o)]:1 for o in range(len(opts[j]))},1,1)
        for o,op in enumerate(opts[j]):
            z=idx[("z",j,o)]; A,B=op["A"],op["B"]
            dS={idx[("s",B)]:1,idx[("s",A)]:-1}; dT={idx[("t",B)]:1,idx[("t",A)]:-1}
            if op["kind"]=="pure":
                # dS = 0 ; dT = -2 L
                c=dict(dS); c[z]=BIG; add(c,-np.inf,BIG)         # dS <= BIG(1-z)
                c=dict(dS); c[z]=-BIG; add(c,-BIG,np.inf)        # dS >= -BIG(1-z)
                c=dict(dT); c[idx[("L",j)]]=2; c[z]=BIG; add(c,-np.inf,BIG)   # dT+2L <= BIG(1-z)
                c=dict(dT); c[idx[("L",j)]]=2; c[z]=-BIG; add(c,-BIG,np.inf)
            else:
                sg=1 if op["bb"]=="SW" else -1; tg=1 if op["aa"]=="NW" else -1
                # dS - sg(2n+1) =0 ; dT - tg*2L = 0
                c=dict(dS); c[idx[("n",j)]]=-2*sg; c[z]=BIG; add(c,-np.inf,sg+BIG)
                c=dict(dS); c[idx[("n",j)]]=-2*sg; c[z]=-BIG; add(c,sg-BIG,np.inf)
                c=dict(dT); c[idx[("L",j)]]=-2*tg; c[z]=BIG; add(c,-np.inf,BIG)
                c=dict(dT); c[idx[("L",j)]]=-2*tg; c[z]=-BIG; add(c,-BIG,np.inf)
    # exactly one weak holder per original edge; weak holder length in allowed union
    by_e={}
    for j,(p,q,e) in enumerate(segs): by_e.setdefault(e,[]).append(j)
    for e,js in by_e.items(): add({idx[("w",j)]:1 for j in js},1,1)
    for j in range(S):
        c={idx[("v",j,l)]:1 for l in LK}; c[idx[("w",j)]]=-1; add(c,0,0)
        for l in LK:
            vv=idx[("v",j,l)]; lo_=WEAKV+(l-1)*2.65; hi_=WEAKV+(l-1)*3.45
            add({idx[("L",j)]:1,vv:-BIG},-np.inf,hi_-BIG) if False else None
            c={idx[("L",j)]:1,vv:BIG}; add(c,-np.inf,hi_+BIG)      # L <= hi + BIG(1-v)
            c={idx[("L",j)]:1,vv:-BIG}; add(c,lo_-BIG,np.inf)      # L >= lo - BIG(1-v)
    # arm uniqueness
    use={}
    for j in range(S):
        for o,op in enumerate(opts[j]):
            use.setdefault((op["A"],op["aa"]),[]).append(idx[("z",j,o)])
            use.setdefault((op["B"],op["bb"]),[]).append(idx[("z",j,o)])
    for key,vs in use.items(): add({v:1 for v in vs},0,1)
    A_=lil_matrix((len(rows),n))
    for r,c in enumerate(rows):
        for k,val in c.items(): A_[r,k]=val
    cvec=np.zeros(n)
    rng=np.random.default_rng(seed)
    for j in range(S):
        cvec[idx[("n",j)]]=1 if seed is None else rng.uniform(0.2,2); cvec[idx[("L",j)]]=0.2 if seed is None else rng.uniform(0.05,0.6)
    if seed is not None:
        for v in range(verts):
            cvec[idx[("s",v)]]=rng.normal()*0.3; cvec[idx[("t",v)]]=rng.normal()*0.3
    res=milp(cvec,constraints=LinearConstraint(A_.tocsr(),lo,hi),bounds=Bounds(lb,ub),integrality=integ,options=dict(time_limit=time_limit))
    if res.x is None: return None
    x=res.x
    sol=dict(segs=[],verts=[(x[idx[("s",v)]],x[idx[("t",v)]]) for v in range(verts)],obj=res.fun)
    for j in range(S):
        o=int(np.argmax([x[idx[("z",j,o)]] for o in range(len(opts[j]))]))
        sol["segs"].append((segs[j],opts[j][o],round(x[idx[("n",j)]]),x[idx[("L",j)]]))
    return sol
if __name__=="__main__":
    K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    for k in range(0,4):
        for rs in itertools.combinations(range(6),k):
            sol=solve_layout(4,K4,set(rs),time_limit=60)
            print("relay edges",rs,"feasible" if sol else "infeasible",flush=True)
            if sol:
                for sgm in sol["segs"]: print("   ",sgm[0][:2],sgm[1]["kind"],sgm[1]["A"],sgm[1]["B"],sgm[1]["aa"],sgm[1]["bb"],"n",sgm[2],"L",round(sgm[3],2))
                print("   verts (s,t)",[tuple(round(a,1) for a in v) for v in sol["verts"]]); break
        else: continue
        break
