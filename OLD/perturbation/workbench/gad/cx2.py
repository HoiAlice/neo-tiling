import itertools, sys
from core import *
from multiprocessing import Pool
EPS=0.2
def build_sw(nU,nV,a=3,k=3,d=4,dv=None):
    dv=dv or d
    sw=[]
    for i in range(nU):
        t=i-(nU-1)/2
        sw.append((a*t,-a*t,d,2,1))
    for j in range(nV):
        s=j-(nV-1)/2
        sw.append((k*s,k*s,dv,2-s,1-s))
    return sw
def setup(sw):
    pts=[];y=[]
    for bx,by,dd,yt,yb in sw: pts+=[(bx+dd,by+dd),(bx,by)]; y+=[yt,yb]
    A=EPS*np.array(pts,float); Y=np.array(y,float); conf=[(t,u) for (t,u) in conflicts_of(Y) if not (max(A[u,0]-A[t,0],A[u,1]-A[t,1])>=1.2)]
    ks=[conf.index((2*i,2*i+1)) for i in range(len(sw))]
    return A,Y,conf,ks
G={}
def init(sw): G['s']=setup(sw)
def run(sg):
    A,Y,conf,ks=G['s']
    return sg, solve_dom(A,Y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=60)[2]
def full_table(sw,procs=8):
    n=len(sw)
    with Pool(procs,initializer=init,initargs=(sw,)) as p: res=p.map(run,list(itertools.product((0,1),repeat=n)),chunksize=4)
    return dict(res)
if __name__=="__main__":
    nU,nV=int(sys.argv[1]),int(sys.argv[2]); a=float(sys.argv[3]);k=float(sys.argv[4]);d=float(sys.argv[5])
    sw=build_sw(nU,nV,a,k,d); print(sw)
    tb=full_table(sw)
    mn=min(tb.values())
    for kk,v in sorted(tb.items(), key=lambda x:x[1])[:24]: print(''.join(map(str,kk[:nU])),''.join(map(str,kk[nU:])),round(v,5),round(v-mn,5))
