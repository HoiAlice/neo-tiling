from full1 import build
from core import *
from multiprocessing import Pool
import itertools, sys
def job(args):
    a,conf,sg=args
    edges=[[],[]]
    for (t,s),i in zip(conf,sg): edges[i].append((t,s))
    c0,_=iso_cost(a[:,0],edges[0]); c1,_=iso_cost(a[:,1],edges[1]); return sg,c0+c1
def run(cs,d,name):
    a,y=build(cs,d); conf=conflicts_of(y)
    ks=[conf.index((2*i,2*i+1)) for i in range(len(cs))]
    with Pool(8) as p: res=p.map(job,[(a,conf,sg) for sg in itertools.product((0,1),repeat=len(conf))],chunksize=16)
    best={}
    for sg,c in res:
        key=tuple(sg[k] for k in ks); best[key]=min(best.get(key,1e9),c)
    print(name,"d",d,"EXACT enumeration; global min",round(min(best.values()),5))
    for k,v in sorted(best.items()): print(" ",k,round(v,5))
    sg0=min(res,key=lambda r:r[1])[0]
    c,u=polish_margin(a,conf,sg0,1e-7); Q=np.exp(u)
    print(" margin-1e-7 cost",round(c,6)," weakly solvable (flow LP):",weakly_solvable(Q,y))
if __name__=="__main__":
    run([(0,0),(-3,3),(-6,6)],4,"P3")
    run([(0,0),(-4,4),(-8,8)],11.166427612,"K3")
