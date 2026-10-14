import numpy as np
from loc7 import sat_value, milp_credit
Je=0.050630241048857716; c2=2*Je
def uchain(steps,d=4):
    p=0; sw=[(0,0,d,1.01,1.0)]
    for s in steps: p+=s; sw.append((-p,p,d,1.01,1.0))
    return sw
tests={"strong-strong":([3,3],[c2,c2]),"weak-strong":([3.75,3],[Je,c2]),"strong-weak":([3,3.75],[c2,Je]),
       "strong4":([3,3,3],[c2]*3),"strong-weak-strong":([3,3.75,3],[c2,Je,c2])}
for n,(st,cr) in tests.items():
    sw=uchain(st); rel=[(i,i+1,'ne',cr[i]) for i in range(len(st))]
    S=sat_value(sw,rel,300); C=milp_credit(sw,rel,300); print(n,"S=%.6f cert=%.6f margin=%.2e"%(S[0],C[0],C[0]-S[0]),flush=True)
