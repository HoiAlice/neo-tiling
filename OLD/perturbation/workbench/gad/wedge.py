"""Feasibility of drawing a graph with the verified edge types.  Edge options (u->w displacement constraints on (s,t)=(dx+dy, dy-dx)):
 pure U  : u uses SE arm, w uses NW arm : s=0, t=-2m (m>=M)          [Q-P=(m,-m)]
 CE(A,B) : A arm in {NW,SE}, B arm in {SW,NE}
   (NW,SW): s>=2N, t>=2P ; (SE,SW): s>=2N, t<=-2P ; (NW,NE): s<=-2N, t>=2P ; (SE,NE): s<=-2N, t<=-2P   (displacement B-A)
Pure edges and CE with the mirrored/reflected corners; NE-arm CEs need the point-reflected corner (NOT yet verified)."""
import itertools, numpy as np, sys
from scipy.optimize import linprog
N=3.0; P=9.0; M=9.0
def options(u,w):
    out=[]
    for (a,b) in ((u,w),(w,u)):
        out.append(("pure",a,b,"SE","NW"))
    for (A,B) in ((u,w),(w,u)):
        for aa in ("NW","SE"):
            for bb in ("SW","NE"):
                out.append(("CE",A,B,aa,bb))
    return out
def feasible(edges,nv,allow_NE):
    # variables: s_i,t_i for each vertex ; displacement (B-A) in (s,t): need s_B-s_A, t_B-t_A constraints
    A_ub=[];b_ub=[];A_eq=[];b_eq=[]
    def row(i,j,ci,cj):
        r=np.zeros(2*nv); return r
    for (kind,A,B,aa,bb) in edges:
        rs=np.zeros(2*nv); rs[2*B]=1; rs[2*A]=-1           # s_B - s_A
        rt=np.zeros(2*nv); rt[2*B+1]=1; rt[2*A+1]=-1       # t_B - t_A
        if kind=="pure":
            A_eq.append(rs); b_eq.append(0.0)
            A_ub.append(rt); b_ub.append(-2*M)              # t_B-t_A <= -2M
        else:
            sg= 1 if bb=="SW" else -1
            tg= 1 if aa=="NW" else -1
            A_ub.append(-sg*rs); b_ub.append(-2*N)
            A_ub.append(-tg*rt); b_ub.append(-2*P)
    r=linprog(np.zeros(2*nv),A_ub=np.array(A_ub) if A_ub else None,b_ub=b_ub if b_ub else None,A_eq=np.array(A_eq) if A_eq else None,b_eq=b_eq if b_eq else None,bounds=[(-1000,1000)]*(2*nv),method="highs")
    return r.status==0
def search(nv,E,allow_NE,limit=3):
    sols=[]
    opts=[options(u,w) for (u,w) in E]
    for combo in itertools.product(*opts):
        used=set(); ok=True
        for (kind,A,B,aa,bb) in combo:
            for key in ((A,aa),(B,bb)):
                if key in used: ok=False
                used.add(key)
            if not allow_NE and bb=="NE": ok=False
        if not ok: continue
        if feasible(combo,nv,allow_NE): sols.append(combo)
    return sols
if __name__=="__main__":
    K3=[(0,1),(0,2),(1,2)]; K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    for name,nv,E in (("K3",3,K3),("K4",4,K4)):
        for allow in (False,True):
            s=search(nv,E,allow); print(name,"allow NE arms (reflected corner)" if allow else "verified corners only","solutions:",len(s),flush=True)
            if s: print("   example:",s[0])
