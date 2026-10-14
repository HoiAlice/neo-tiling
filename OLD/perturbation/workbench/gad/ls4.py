from layout_search import okP, SMIN, SMAX
from wedge import search as wsearch
import itertools, numpy as np
from scipy.optimize import linprog
K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
sols=wsearch(4,K4,True)
print(len(sols),"type assignments",flush=True)
def sgn_s(c): return 0 if c[0]=="pure" else (1 if c[4]=="SW" else -1)
def eps_t(c): return -1 if c[0]=="pure" else (1 if c[3]=="NW" else -1)   # t_B - t_A = eps*2L (pure: -2m)
rng=np.random.default_rng(0)
out=[]
stat=dict(s_ok=0,t_lp=0,okP=0)
import numpy as np
def cycle_basis(Eg,nv):
    # fundamental cycles of K4 via incidence nullspace
    M=np.zeros((nv,len(Eg)))
    for e,(u,w) in enumerate(Eg): M[u,e]=1; M[w,e]=-1
    u_,s_,vt=np.linalg.svd(M); null=vt[np.sum(s_>1e-9):]
    return null
EG=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
NB=cycle_basis(EG,4)
grid=np.array(list(itertools.product(range(3,15),repeat=4)))
for combo in sols:
    ce=[e for e,c in enumerate(combo) if c[0]=="CE"]
    # orientation: combo edge e connects EG[e] but A->B direction may be reversed; signed incidence for s: s_B - s_A
    inc=np.zeros((6,4))
    for e,c in enumerate(combo): inc[e,c[2]]+=1; inc[e,c[1]]-=1
    # cycle condition: for every y in left-null of inc (cols space), y . r = 0
    u_,s_,vt=np.linalg.svd(inc.T); rank=np.sum(s_>1e-9)
    cyc=vt[rank:]            # vectors z with inc^T z = 0 -> z.r must be 0 for r in colspace(inc)
    cyc=np.round(cyc,12)
    for nsel in grid:
        ns=[0]*6
        for e,nn in zip(ce,nsel): ns[e]=nn
        r=np.array([sgn_s(c)*(2*ns[e]+1) for e,c in enumerate(combo)],float)
        if np.abs(cyc@r).max()>1e-7: continue
        M=inc; M2=np.vstack([M,[1,0,0,0]]); r2=np.append(r,0)
        x=np.linalg.lstsq(M2,r2,rcond=None)[0]
        stat['s_ok']+=1
        nvar=10; Aeq=[];beq=[]
        for e,c in enumerate(combo):
            row=np.zeros(nvar); row[6+c[2]]=1; row[6+c[1]]=-1; row[e]=-eps_t(c)*2; Aeq.append(row); beq.append(0)
        row=np.zeros(nvar); row[6]=1; Aeq.append(row); beq.append(0)
        ok=False
        for trial in range(6):
            cvec=rng.normal(size=nvar)*np.r_[np.ones(6),np.zeros(4)]
            r_=linprog(cvec,A_eq=np.array(Aeq),b_eq=beq,bounds=[(8.95,80)]*6+[(-400,400)]*4,method="highs")
            if r_.status==0: stat['t_lp']+=1
            if r_.status==0 and all(okP(l) for l in r_.x[:6]): ok=True; break
        if ok:
            out.append((combo,ns,np.round(x,2).tolist(),np.round(r_.x[:6],2).tolist(),np.round(r_.x[6:],2).tolist()))
            break
    if len(out)>=10: break
print('stats',stat,flush=True)
print("layouts found:",len(out),flush=True)
for o in out[:6]: print(o)
