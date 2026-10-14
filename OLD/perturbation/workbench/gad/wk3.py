from wk2 import *
import sys
for n in (2,3,4,5):
    sw=[(0+3*i,0-3*i,4,2,1) for i in range(n)]
    for ycomp in (0.1,):
        cm,v,w,Q,Y=check(sw,[0],[0],ycomp=ycomp); print("P",n,round(cm,5),"viol",len(v),"weak",w,flush=True)
