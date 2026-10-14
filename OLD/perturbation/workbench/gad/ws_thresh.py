"""Weak reachability (per-point witnesses, as in Closure.lean) and threshold test: is each upper level set {y>=c} weakly reachable at Q?"""
import sys, numpy as np
from scipy.optimize import linprog
def witness_ok(Q,t,T,tol=1e-9):
    # exists xi>=0, xi1+xi2=1 with xi.(Q_s-Q_t) >= -tol for s in T
    if len(T)==0: return True
    D=Q[T]-Q[t]
    r=linprog(np.zeros(2),A_ub=-D,b_ub=np.full(len(T),tol),A_eq=[[1,1]],b_eq=[1],bounds=[(0,None)]*2,method="highs")
    return r.status==0
def bad_points(Q,S,tol=1e-9):
    """points t in S having no witness (i.e. Q_t in int conv(Q_T)+R2+)"""
    Sset=set(S); T=np.array([i for i in range(len(Q)) if i not in Sset],int)
    return [t for t in S if not witness_ok(Q,t,T,tol)]
def thresholds(Q,y,tol=1e-9):
    lv=sorted(set(np.round(y,9)),reverse=True); out=[]
    for c in lv:
        S=[i for i in range(len(y)) if round(y[i],9)>=c]
        out.append((c,len(S),bad_points(Q,S,tol)))
    return out
if __name__=="__main__":
    d=np.load(sys.argv[1]); y=d['y']
    for k,Q in enumerate(d['Qs']):
        th=thresholds(Q,y); print("pattern",k,"levels",len(th),"failing thresholds:",[(round(c,5),n,b) for c,n,b in th if b])
