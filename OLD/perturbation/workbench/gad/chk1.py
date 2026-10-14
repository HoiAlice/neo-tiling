from cprime import *
import time
if __name__=="__main__":
    sw,idx=build_c()
    A,Y,conf,ks=cx2.setup(sw)
    print("npts",len(A),"conflicts",len(conf))
    for fx in [(0,1,0,1),(1,0,0,1),(0,1,1,0)]:
        t=time.time()
        r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=300)
        print(fx,"milp obj",round(r[0],5),"exact polished",round(r[2],5),"time",round(time.time()-t),flush=True)
