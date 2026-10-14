import itertools, numpy as np
from scipy.optimize import linprog
rng=np.random.default_rng(1)
def blocks(Q,t,r,s=None):
    # does conv{q_r,q_s} meet open quadrant strictly below q_t ?
    if s is None: return bool(np.all(Q[r]<Q[t]))
    # mu in [0,1]: mu*Q[r]+(1-mu)*Q[s] < Q[t]; interval intersection
    lo,hi=0.0,1.0
    for i in range(2):
        a=Q[r,i]-Q[s,i]; b=Q[t,i]-Q[s,i]   # mu*a < b
        if abs(a)<1e-12:
            if not (0<b): return False
        elif a>0: hi=min(hi,b/a) if True else hi; 
        else: lo=max(lo,b/a)
        # strictness handled below
    # need open interval: mu<b/a for a>0 (strict), mu> b/a for a<0 (strict)
    # recompute strictly
    lo,hi=0.0,1.0; lo_strict=False;hi_strict=False
    for i in range(2):
        a=Q[r,i]-Q[s,i]; b=Q[t,i]-Q[s,i]
        if abs(a)<1e-12:
            if not (0<b): return False
        elif a>0:
            v=b/a
            if v<hi or (v==hi): hi=v; hi_strict=True
        else:
            v=b/a
            if v>lo or v==lo: lo=v; lo_strict=True
    if lo<hi: return True
    return False
def valid_sets(Q):
    T=len(Q); res=[]
    for m in range(1,2**T):
        S=[t for t in range(T) if m>>t&1]; C=[t for t in range(T) if not m>>t&1]
        ok=True
        for t in S:
            for r in C:
                if blocks(Q,t,r): ok=False;break
            if not ok:break
            for r,s in itertools.combinations(C,2):
                if blocks(Q,t,r,s): ok=False;break
            if not ok:break
        if ok: res.append(S)
    return res
def in_cone(y,sets):
    T=len(y); A=np.zeros((T,len(sets)))
    for j,S in enumerate(sets): A[S,j]=1
    r=linprog(np.zeros(len(sets)),A_eq=A,b_eq=y,bounds=(0,None),method='highs')
    return r.status==0
def pairwise(Q,y):
    T=len(Q)
    for t in range(T):
        for r in range(T):
            if r!=t and blocks(Q,t,r) and y[r]<y[t]-1e-9: return False
            for s in range(r+1,T):
                if s!=t and r!=t and blocks(Q,t,r,s) and y[r]+y[s]<y[t]-1e-9: return False
    return True
bad=0;n=0
for trial in range(3000):
    T=int(rng.integers(4,8))
    Q=rng.random((T,2))+0.05
    y=rng.integers(0,6,T).astype(float)
    if y.sum()==0: continue
    vs=valid_sets(Q)
    a=in_cone(y,vs); b=pairwise(Q,y)
    n+=1
    if a!=b:
        bad+=1
        if bad<=3: print("MISMATCH",T,Q.tolist(),y.tolist(),a,b)
print(n,bad)
