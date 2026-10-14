import sys, time, numpy as np
sys.path.insert(0,'..')
from rho_exact import rho_exact
from pyscipopt import Model, quicksum
def rho_dom_true(P,y,D=50.0):
    T=len(P); m=Model(); m.hideOutput()
    a={(t,i):m.addVar(lb=1/(1+D),ub=1+D) for t in range(T) for i in range(2)}
    g={(t,i):m.addVar(lb=0,ub=D) for t in range(T) for i in range(2)}
    for k in a:
        m.addCons(g[k]>=a[k]-1); m.addCons(g[k]*a[k]>=1-a[k])
    M=1e3
    for t in range(T):
        for s in range(T):
            if y[s]<y[t]:
                sg=[m.addVar(vtype='B') for _ in range(2)]; m.addCons(sg[0]+sg[1]>=1)
                for c in range(2):
                    # q_t,c <= q_s,c when sg[c]
                    m.addCons(P[t,c]*a[t,c]-P[s,c]*a[s,c]<=M*(1-sg[c]))
    m.setObjective(quicksum(g.values())); m.setParam("limits/gap",1e-8); m.optimize()
    return m.getObjVal()
rng=np.random.default_rng(int(sys.argv[1])); n=int(sys.argv[2])
for it in range(n):
    T=3; P=rng.uniform(1,5,size=(T,2)).round(1); y=rng.integers(1,6,size=T).astype(float)
    t0=time.time(); d=rho_dom_true(P,y); f=rho_exact(P,y,max_fam=3,time_limit=10)[0]
    print(it, "dom=%.5f full=%.5f diff=%.5f  (%.0fs)"%(d,f,f-d,time.time()-t0), P.tolist(), y.tolist(), flush=True)
