import sys,os; sys.path.insert(0,".")
from ws_h import *
n1=2*len(sw3)
for D in (20,30,40,50,60):
    out=[]
    for pa,pb in [((0,0,1,0),(0,1,1,1)),((1,0,0,1),(1,0,0,0))]:
        Q=Qcat(0.2,D,D,pa,pb); A=Q[:n1]; B=Q[n1:]
        nw=sum(1 for t in A for s in B if s[0]<t[0] and s[1]>t[1]); se=sum(1 for t in A for s in B if s[0]>t[0] and s[1]<t[1]); sw_=sum(1 for t in A for s in B if s[0]<=t[0] and s[1]<=t[1])
        out.append((pa,pb,"NW pairs",nw,"SE pairs",se,"SW pairs",sw_))
    print("D",D,out)
