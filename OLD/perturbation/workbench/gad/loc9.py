import sys, numpy as np
from loc8 import build_inst
from loc7 import sat_value
aW=float(sys.argv[1]) if len(sys.argv)>1 else 3.85
sw=build_inst(aW)
links=[(i,i+1) for i in range(8)]+[(0,9)]+[(i,i+1) for i in range(9,14)]+[(i,i+1) for i in range(15,24)]
Bf=lambda d:2*(np.exp(d*0.1)-1)
for a,b in links:
    blk=[sw[a],sw[b]]
    e=sat_value(blk,[(0,1,'eq',0)],60)[0]; n=sat_value(blk,[(0,1,'ne',0)],60)[0]
    base=Bf(blk[0][2])+Bf(blk[1][2])
    print((a,b),"eq-excess",round(e-base,5),"ne-excess",round(n-base,5))
