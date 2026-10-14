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
for combo in sols:
    ce=[e for e,c in enumerate(combo) if c[0]=="CE"]
    # s-system: s_B - s_A = sgn*(2n+1)
    for nsel in itertools.product(range(3,15),repeat=len(ce)):
        ns=[0]*6
        for e,nn in zip(ce,nsel): ns[e]=nn
        # solve s for 4 vertices (s_0=0) via least squares on 6 equations
        M=np.zeros((6,4)); r=np.zeros(6)
        for e,c in enumerate(combo):
            A,B=c[1],c[2]; M[e,B]+=1; M[e,A]-=1; r[e]=sgn_s(c)*(2*ns[e]+1)
        M2=np.vstack([M,[1,0,0,0]]); r2=np.append(r,0)
        x,res,rk,_=np.linalg.lstsq(M2,r2,rcond=None)
        if np.abs(M2@x-r2).max()>1e-9: continue
        # t-system: unknown L_e in [8.95,80], t_v: t_B-t_A=eps*2L
        # variables: L (6) ; cycle equations => use t variables too (4): 
        nvar=6+4
        Aeq=[];beq=[]
        for e,c in enumerate(combo):
            row=np.zeros(nvar); row[6+c[2]]=1; row[6+c[1]]=-1; row[e]=-eps_t(c)*2; Aeq.append(row); beq.append(0)
        row=np.zeros(nvar); row[6]=1; Aeq.append(row); beq.append(0)
        ok=False
        for trial in range(6):
            cvec=rng.normal(size=nvar)*np.r_[np.ones(6),np.zeros(4)]
            r_=linprog(cvec,A_eq=np.array(Aeq),b_eq=beq,bounds=[(8.95,80)]*6+[(-400,400)]*4,method="highs")
            if r_.status==0 and all(okP(l) for l in r_.x[:6]): ok=True; break
        if ok:
            out.append((combo,ns,np.round(x,2).tolist(),np.round(r_.x[:6],2).tolist(),np.round(r_.x[6:],2).tolist()))
            if len(out)>=10: break
    if len(out)>=10: break
print("layouts found:",len(out),flush=True)
for o in out[:6]: print(o)
