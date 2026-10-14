import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
from ws_h import *
from fractions import Fraction as Fr
from ws_exact2 import certify2, check, Fq
from ws_ghost3 import moderate_ok
DX=DY=float(os.environ.get("D","30")); h=float(os.environ.get("H","0.2"))
sw1=list(sw3)
def eta_loc(c1,c2,gap):
    s=sc3(sw1); smax=s.max(); fb=np.array([Fpw(v,[4],[c1,c2],smax) for v in s]); return np.concatenate([[b+gap,b] for b in fb])
e=eta_loc(0.02,0.12,0.002); off=e.max()*1.5; eta=np.concatenate([e+off,e]); Yf=1+0.3*eta/eta.max()
Y=[Fr(float(v)).limit_denominator(10**12) for v in Yf]
n1=2*len(sw3)
for pa,pb in [(PATS[3],PATS[9]),(PATS[5],PATS[12])]:
    Q=Qcat(h,DX,DY,pa,pb); P=[(Fq(a),Fq(b)) for a,b in Q]
    cert,msg=certify2(P,Y); print("pattern",pa,pb,msg,"sets",len(cert) if cert else None,"exact check",check(P,Y,cert) if cert else None,flush=True)
    kinds={"in B1 only":0,"B1 u part of B2":0,"B1 all + B2 part":0,"other":0}
    for S,m in cert:
        a=sum(1 for q in S if q<n1); b=sum(1 for q in S if q>=n1)
        if b==0: kinds["in B1 only"]+=1
        elif a==n1: kinds["B1 all + B2 part"]+=1
        elif a==0: kinds["other"]+=1
        else: kinds["B1 u part of B2"]+=1
    print("  set types (B1 = SW copy):",kinds,"; moderate (ell=4.8):",sum(1 for S,m in cert if moderate_ok(P,S,4.8)),"of",len(cert),flush=True)
