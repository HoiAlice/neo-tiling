import numpy as np, cx2
from scipy.optimize import minimize
from cprime import build_c
sw,idx=build_c(); A,Y,conf,ks=cx2.setup(sw); T=len(A)
d=np.load('cprime_Q_1010.npz'); U=np.log(d['Q'])
coord=[0 if (U[s,0]-U[t,0])>=(U[s,1]-U[t,1]) else 1 for t,s in conf]
w=np.array([A[t,i]-A[s,i] for (t,s),i in zip(conf,coord)])
def D_and_grad(f):
    g={}
    for k,((t,s),i) in enumerate(zip(conf,coord)):
        g[(t,i)]=g.get((t,i),0)+f[k]; g[(s,i)]=g.get((s,i),0)-f[k]
    val=float(f@w); 
    for x in g.values():
        a=abs(x)
        if a>1: val-=a*np.log(a)-a+1
    grad=w.copy()
    dpsi=lambda x: np.sign(x)*np.log(abs(x)) if abs(x)>1 else 0.0
    for k,((t,s),i) in enumerate(zip(conf,coord)):
        grad[k]-= dpsi(g[(t,i)])-dpsi(g[(s,i)])
    return val,grad
f0=np.ones(len(conf))*1.0
r=minimize(lambda f:tuple(-z for z in D_and_grad(f)),f0,jac=True,bounds=[(0,None)]*len(conf),method="L-BFGS-B",options=dict(maxiter=20000,ftol=1e-15,gtol=1e-10))
f=r.x; print("dual value",-r.fun,"primal",np.sum(np.exp(np.abs(U-A))-1))
supp=[(k,round(f[k],3)) for k in range(len(conf)) if f[k]>1e-4]
print("support size",len(supp))
own={k for k in ks}
print("own-pair flows",sum(1 for k,_ in supp if k in own),"of",len(ks),"; non-own flows:",[(conf[k],coord[k],v) for k,v in supp if k not in own])
print("own flows deviating from isolated e^{d*0.1}:")
for j,k in enumerate(ks):
    iso=np.exp(sw[j][2]*0.1)
    if abs(f[k]-iso)>2e-3: print(" switch",j,"coord",coord[k],"flow",round(f[k],4),"iso",round(iso,4))
print("max dev others", max(abs(f[k]-np.exp(sw[j][2]*0.1)) for j,k in enumerate(ks) if j not in (4,20,21)))
print("cross edges",[(conf[k],coord[k],round(f[k],4),round(w[k],3)) for k,_ in supp if k not in own])
print("switch of points: pt//2")
