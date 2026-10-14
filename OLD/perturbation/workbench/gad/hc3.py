import random, sys, time, json, itertools
from core import *
from multiprocessing import Pool
EPS=0.25; G=8
def tab3(pts, ys, nsw=3):
    a = EPS*np.array(pts,float); y=np.array(ys,float)
    conf = conflicts_of(y)
    ks=[]
    for i in range(nsw):
        try: ks.append(conf.index((2*i,2*i+1)))
        except ValueError: return None
    tb={}
    for sg in itertools.product((0,1),repeat=nsw):
        r = solve_dom(a,y,fixed=dict(zip(ks,sg)),conflicts=conf,time_limit=10)
        if r is None: return None
        tb[sg]=r[2]
    return tb
def score(tb):
    C=[tb[(0,0,0)],tb[(1,1,1)]]; N=[v for k,v in tb.items() if len(set(k))>1]
    return min(C)-max(N), (min(C),max(C),min(N),max(N))
def run(seed):
    rnd=random.Random(seed)
    nx=rnd.choice([1,2,3])
    n=6+nx
    def rand_state():
        pts=[(rnd.randint(0,G),rnd.randint(0,G)) for _ in range(n)]
        ys=[0]*n
        for i in range(3):
            ys[2*i]=rnd.choice([3,4]); ys[2*i+1]=rnd.choice([1,2])
        for j in range(6,n): ys[j]=rnd.choice([1,2,3,4,5])
        return pts,ys
    best=None; cur=None
    for _ in range(20):
        pts,ys=rand_state()
        if len(set(pts))<n: continue
        tb=tab3(pts,ys)
        if tb is None: continue
        sc=score(tb)[0]
        if cur is None or sc>cur[0]: cur=(sc,pts,ys,tb)
    best=cur
    t0=time.time()
    while time.time()-t0<float(sys.argv[2]):
        sc,pts,ys,_=cur
        pts=list(pts); ys=list(ys)
        i=rnd.randrange(n)
        if rnd.random()<0.8:
            c=rnd.randrange(2); l=list(pts[i]); l[c]=min(G,max(0,l[c]+rnd.choice([-2,-1,1,2]))); pts[i]=tuple(l)
        else:
            if i<6: ys[i]=rnd.choice([3,4]) if i%2==0 else rnd.choice([1,2])
            else: ys[i]=rnd.choice([1,2,3,4,5])
        if len(set(pts))<n: continue
        tb=tab3(pts,ys)
        if tb is None: continue
        s2=score(tb)[0]
        if s2>=sc-1e-9 or rnd.random()<0.02:
            cur=(s2,pts,ys,tb)
            if s2>best[0]: best=cur
    return best
if __name__=="__main__":
    seeds=range(int(sys.argv[1]), int(sys.argv[1])+8)
    with Pool(8) as p: res=p.map(run,seeds)
    res.sort(key=lambda r:-r[0])
    for r in res[:5]:
        print(round(r[0],4), r[1], r[2], {k:round(v,3) for k,v in r[3].items()})
