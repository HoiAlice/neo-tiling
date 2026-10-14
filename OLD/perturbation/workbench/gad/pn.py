from chain3 import *
import numpy as np
from core import weakly_solvable
def job(n):
    cs=[(-3*i,3*i) for i in range(n)]
    return n,table(cs,4)
if __name__=="__main__":
    with Pool(4) as p: res=p.map(job,[3,4,5,6])
    for n,tb in res:
        # fit E = B + J * #agree adjacent
        rows=[];rhs=[]
        for k,v in tb.items():
            rows.append([1,sum(k[i]==k[i+1] for i in range(n-1))]); rhs.append(v)
        coef,resid,_,_=np.linalg.lstsq(np.array(rows,float),np.array(rhs),rcond=None)
        err=max(abs(np.array(rows)@coef-np.array(rhs)))
        print(f"P{n}: B={coef[0]:.5f} J={coef[1]:.5f} max fit err {err:.2e}; min over all = {min(tb.values()):.5f} ; n*isolated = {n*2*(np.exp(0.4)-1):.5f}")
    # negative control for weak-solvability checker: unperturbed P of triangle example & a bad Q
    P=np.array([[4,1],[3,3],[1,4]],float); print("triangle at P weakly solvable:",weakly_solvable(P,np.array([1,5,3.])))
    # K3 gadget original P is NOT solvable (violations), but y in [1,2]:
    pts=[]
    for c in [(0,0),(-3,3),(-6,6)]: pts+=[(c[0]+4,c[1]+4),c]
    P=np.exp(0.2*np.array(pts,float)); y=np.array([2,1]*3.)
    print("P3 gadget at original P weakly solvable (expect False):",weakly_solvable(P,y))
