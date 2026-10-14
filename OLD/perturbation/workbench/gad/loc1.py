import numpy as np, cx2, sys
from cprime import build_c
sw,idx=build_c()
A,Y,conf,ks=cx2.setup(sw)
d=np.load('cprime_Q_1010.npz'); U=np.log(d['Q']); T=len(A)
D=np.abs(U-A); print("max disp",D.max(),"cost",np.sum(np.exp(D)-1))
# slack of each conflict: coordinate i with max (u_s,i-u_t,i)
sl=[(max(U[s,i]-U[t,i] for i in range(2)),t,s) for t,s in conf]
print("conflicts",len(conf),"min slack",min(sl)[0])
tight=[(t,s) for (v,t,s) in sl if v<1e-4]
print("tight pairs",len(tight))
# all pairs y_t>y_s NOT in conf (pruned) slack
full=[(t,s) for t in range(T) for s in range(T) if Y[t]>Y[s]]
pr=[p for p in full if p not in set(conf)]
print("full",len(full),"pruned",len(pr), "min slack pruned at Q", min(max(U[s,i]-U[t,i] for i in range(2)) for t,s in pr))
print("min sep at P over pruned", min(max(A[s,i]-A[t,i] for i in range(2)) for t,s in pr))
# components of variable graph from tight edges
par=list(range(2*T))
def f(x):
    while par[x]!=x: par[x]=par[par[x]]; x=par[x]
    return x
for (t,s) in tight:
    i=0 if (U[s,0]-U[t,0])<(U[s,1]-U[t,1]) else 1
    par[f(2*t+i)]=f(2*s+i)
from collections import Counter
c=Counter(f(x) for x in range(2*T)); print(sorted(Counter(c.values()).items()))
# per switch max displacement
for k in range(len(sw)): print(k, round(D[2*k].max(),3), round(D[2*k+1].max(),3))
print("---eps per switch")
Bs=lambda d: 2*(np.exp(d*0.2/2)-1)
tot=0
for k,s in enumerate(sw):
    e=np.sum(np.exp(D[2*k:2*k+2])-1)-Bs(s[2]); tot+=e
    print(k,s[2],round(e,5))
print(tot)
