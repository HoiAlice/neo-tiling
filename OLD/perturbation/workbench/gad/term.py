"""Terminal test: fix only the 4 end switches' sigma, free all interior. Prints min cost for each of the 16 end bit patterns."""
from cx3 import *
import cx2
def term_table(sw, fixed_idx, procs=5):
    cx2.G.clear()
    with Pool(procs,initializer=init2,initargs=(sw,fixed_idx)) as p:
        res=p.map(run2,list(itertools.product((0,1),repeat=len(fixed_idx))))
    return dict(res)
def init2(sw,fx):
    A,Y,conf,ks=cx2.setup(sw); cx2.G['s']=(A,Y,conf,[ks[i] for i in fx])
def run2(sg):
    A,Y,conf,ks=cx2.G['s']
    return sg, solve_dom(A,Y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=500)[2]
if __name__=="__main__":
    nU,nV=int(sys.argv[1]),int(sys.argv[2]); a,du,k,dv=map(float,sys.argv[3:7])
    sw=build2(nU,nV,a,du,k,dv,1.0)
    fx=[0,nU-1,nU,nU+nV-1]   # U_in,U_out,V_in,V_out
    tb=term_table(sw,fx); mn=min(tb.values())
    print("U_in U_out V_in V_out : excess over min   (min=%.5f)"%mn)
    for s,v in sorted(tb.items()): print(s, round(v-mn,5))
