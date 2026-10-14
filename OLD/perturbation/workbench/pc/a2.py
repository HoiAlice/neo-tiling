"""rho via A2 pair-blocker model: for each t and each blocker pair (r,s) with y_r+y_s<y_t (r may equal s,
 single: y_s<y_t), exists xi in [0,1]: xi*(q_r-q_t)_0+(1-xi)*(q_r-q_t)_1>=0 and same for s.
 Weak solvability needs y_t <= sum over blocker; so forbidden blockers = those with sum < y_t.
 Global SCIP (spatial B&B)."""
import math, itertools, numpy as np
from pyscipopt import Model, quicksum
def solve(P, y, D=20.0, tl=120, verbose=False, fixed_lam=None):
    P=np.asarray(P,float); y=np.asarray(y,float); T=len(P)
    m=Model(); m.hideOutput()
    lo,hi=1/(1+D),1+D
    a={(t,i):m.addVar(lb=lo,ub=hi) for t in range(T) for i in range(2)}
    g={(t,i):m.addVar(lb=0,ub=D) for t in range(T) for i in range(2)}
    for k in a:
        m.addCons(g[k]>=a[k]-1); m.addCons(g[k]*a[k]>=1-a[k])  # g>=1/a-1  <=> g*a>=1-a (a>0)
    cnt=0; lams={}
    for t in range(T):
        # blocker pairs
        for r in range(T):
            for s in range(r,T):
                if t in (r,s): continue
                if y[r]+y[s]<y[t]-1e-12 and (r==s or y[r]+y[s]<y[t]):
                    lam=m.addVar(lb=0,ub=1); lams[(t,r,s)]=lam
                    for u in {r,s}:
                        d0=P[u,0]*a[u,0]-P[t,0]*a[t,0]; d1=P[u,1]*a[u,1]-P[t,1]*a[t,1]
                        m.addCons(lam*d0+(1-lam)*d1>=0)
                    cnt+=1
    m.setObjective(quicksum(g.values())); m.setParam("limits/time",tl); m.setParam("limits/gap",1e-7); m.setParam("numerics/feastol",1e-9)
    m.optimize()
    if m.getNSols()==0: return math.inf,None,cnt
    A=np.array([[m.getVal(a[t,i]) for i in range(2)] for t in range(T)])
    return m.getObjVal(),P*A,cnt
if __name__=="__main__":
    P=[[4,1],[3,3],[1,4]]; y=[1,5,3]
    print(solve(P,y))
