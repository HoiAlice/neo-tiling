import numpy as np, cx2
from loc3 import chain, B, J
def psi(x): return np.where(x>1, x*np.log(np.maximum(x,1e-300))-x+1, 0.0)
def dual(A, flows):
    """flows: dict ((t,s,i)->f>=0) meaning edge u_t,i <= u_s,i. returns D(f)=sum f*(a_t-a_s)-sum psi(|g_v|)"""
    g={}; lin=0.0
    for (t,s,i),f in flows.items():
        lin+=f*(A[t,i]-A[s,i]); g[(t,i)]=g.get((t,i),0)+f; g[(s,i)]=g.get((s,i),0)-f
    return lin-sum(float(psi(abs(v))) for v in g.values())
def wire_flow(n,bits,a=3):
    sw=chain(n,a); A,Y,conf,ks=cx2.setup(sw)
    fl={}
    for s in range(n): fl[(2*s,2*s+1,bits[s])]=np.exp(0.4)   # own pair: top 2s, bottom 2s+1
    # link (k-1,k): V=k-1 NW, U=k. pairs: (t_U,b_V) coord y(1) gap1 ; (t_V,b_U) coord x(0) gap1
    for k in range(1,n):
        U,V=k,k-1
        # (t_U,b_V) in y is supported by own iff bits[U]==1 or bits[V]==1 ; unsupported if both bits==0
        if bits[U]==0 and bits[V]==0: fl[(2*U,2*V+1,1)]=np.exp(0.1)
        if bits[U]==1 and bits[V]==1: fl[(2*V,2*U+1,0)]=np.exp(0.1)
    return A,fl
for bits in [(0,1,0,1),(0,0,0,0),(0,0,1,1),(0,0,1,0,0),(1,1,1,1,1)]:
    n=len(bits); A,fl=wire_flow(n,bits); un=sum(bits[k]==bits[k-1] for k in range(1,n))
    print(bits,"dual LB",round(dual(A,fl),6),"nB+J*unsat",round(n*B+J*un,6))
