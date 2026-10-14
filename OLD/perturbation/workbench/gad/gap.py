from cprime import *
import time
sw,idx=build_c()
A,Y,conf,ks=cx2.setup(sw)
print(len(conf),"conflicts")
for fx in [(0,1,0,1),(1,0,0,1)]:
    t=time.time()
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=400)
    print(fx,"lb",round(r[0],5),"polished",round(r[2],5),"time",round(time.time()-t),flush=True)
