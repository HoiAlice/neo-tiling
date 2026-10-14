import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np
from fractions import Fraction as Fr
import ws_two as W
from ws_exact import y_rational
from ws_exact2 import certify2, Fq
y=y_rational(W.s,W.K,[Fr(2,100),Fr(62,100),Fr(122,100)],Fr(2,1000),Fr(3,10)); yp=[v-1 for v in y]
n1=2*W.n1; N=len(y); Q=W.Qcat(0,5)
P=[(Fq(a),Fq(b)) for a,b in Q]
print("y' cluster2 range",float(min(yp[n1:])),float(max(yp[n1:])),"cluster1 range",float(min(yp[:n1])),float(max(yp[:n1])))
cert,msg=certify2(P[n1:],yp[n1:]); print("cluster2 cert",msg,"total mass",float(sum(m for _,m in cert)) if cert else None)
# is cluster 1 alone ok with offset c = max y'|B2 ?
for c in (0,float(max(yp[n1:])),float(max(yp[n1:]))*1.0001):
    nu=[v-Fr(c).limit_denominator(10**9) for v in yp[:n1]]
    if min(nu)<0: print("c",c,"nu negative"); continue
    cert1,msg1=certify2(P[:n1],nu); print("cluster1 with offset",c,msg1)
