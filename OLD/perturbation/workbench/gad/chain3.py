import itertools, sys
from core import *
from multiprocessing import Pool
EPS=0.2
def table(cs, d, eps=EPS, extra=None):
    n=len(cs); pts=[]
    for c in cs: pts += [(c[0]+d,c[1]+d),c]
    y=np.array([2.0,1.0]*n)
    a=eps*np.array(pts,float); conf=conflicts_of(y)
    ks=[conf.index((2*i,2*i+1)) for i in range(n)]
    tb={}
    for sg in itertools.product((0,1),repeat=n):
        r=solve_dom(a,y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=20)
        tb[sg]=r[2]
    return tb
def job(args):
    a,d=args
    return args, table([(0,0),(-a,a),(-2*a,2*a)],d)
if __name__=="__main__":
    jobs=[(a,d) for a in (1,2,3) for d in range(a+1, 4*a+2)]
    with Pool(8) as p: res=p.map(job,jobs)
    for (a,d),tb in res:
        print("a",a,"d",d, " ".join(f"{''.join(map(str,k))}:{v:.3f}" for k,v in tb.items()))
