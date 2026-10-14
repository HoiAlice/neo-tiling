from wk2 import *
sw=build2(4,3,3,4,1,5,1.0)
for yc in (1e-3,1e-2,0.1,0.3):
    cm,v,w,Q,Y=check(sw,[0],[0],ycomp=yc); print("4U3V ycomp",yc,round(cm,5),"weak",w,flush=True)
