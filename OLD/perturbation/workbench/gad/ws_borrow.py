import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
from ws_h import *
from fractions import Fraction as Fr
from ws_exact2 import Fq, check
from ws_exact3 import certify3
h=0.2; D=float(os.environ.get("D","30")); DX=DY=D
def eta_loc(c1,c2,gap):
    s=sc3(list(sw3)); smax=s.max(); fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); return np.concatenate([[b+gap,b] for b in fb])
e=eta_loc(0.02,0.12,0.002); off=e.max()*1.5; eta=np.concatenate([e+off,e]); Y=1+0.3*eta/eta.max()
n1=2*len(sw3)
for pa,pb in [((0,0,1,0),(0,1,1,1)),((1,1,0,0),(0,1,1,0))]:
    Q=Qcat(h,DX,DY,pa,pb); P=[(Fq(a),Fq(b)) for a,b in Q]; yv=[Fr(float(v)).limit_denominator(10**12) for v in Y]
    kap=Fr(1,100); yp=[v-(1-kap) for v in yv]
    cert,msg,fun=certify3(P,yp); print(pa,pb,msg,"min total mass",fun,flush=True)
    if cert is None: continue
    types={"B1 only":Fr(0),"B1 all + B2 part":Fr(0),"mixed (partial B1 and B2 points)":Fr(0),"B2 only":Fr(0)}
    borrow=[Fr(0)]*len(P)
    for S,m in cert:
        a=sum(1 for q in S if q<n1); b=len(S)-a
        if b==0: types["B1 only"]+=m
        elif a==n1: types["B1 all + B2 part"]+=m
        elif a==0: types["B2 only"]+=m
        else:
            types["mixed (partial B1 and B2 points)"]+=m
            for q in S:
                if q>=n1: borrow[q]+=m
    print("  total mass by set type:",{k:round(float(v),5) for k,v in types.items()})
    mb=max(((float(borrow[q]/yp[q]),q) for q in range(n1,len(P)) if yp[q]>0),default=(0,None))
    print("  max over B2 points of (mixed mass through q)/(y'_q) = %.4f at point %s ; total y' on B1 %.4f, on B2 %.4f"%(mb[0],mb[1],float(sum(yp[:n1])),float(sum(yp[n1:]))),flush=True)
