"""Exact rational verification: planar.certify / check_certificate with exact rational y (rule) and Q = exact value of the snapped floats."""
import sys,os; sys.path.insert(0,"."); sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as Fr
def Fq(x): return Fr(float(x))        # exact rational of the double (equal doubles -> equal rationals: ties exact)
def y_rational(s_c, kinks, slopes, g, eps):
    smax=max(s_c); cuts=[None]+list(kinks)+[None]
    def F(v):
        val=Fr(0)
        for i,sl in enumerate(slopes):
            a=cuts[i]; b=cuts[i+1]; lo=v if a is None else max(Fr(a),v); hi=smax if b is None else min(Fr(b),Fr(smax))
            if hi>lo: val+=Fr(sl)*(hi-lo)
        return val
    fb=[F(Fr(int(v))) for v in s_c]; tops=[f+Fr(g) for f in fb]; allv=[x for t,b in zip(tops,fb) for x in (t,b)]; mx=max(allv)
    return [1+Fr(eps)*v/mx for v in allv]
def exact_check(Q,y):
    P=[(Fq(a),Fq(b)) for a,b in Q]; c=planar.certify(P,y)
    if c is None: return False
    return planar.check_certificate(P,y,c)
