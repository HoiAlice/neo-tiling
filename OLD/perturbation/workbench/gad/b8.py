from bias import *
from core import polish_margin, weakly_solvable
from multiprocessing import Pool
def job(args):
    sw,pat,rat=args
    n=len(sw); pts=[]
    for (cx,cy,g0,g1) in sw: pts += [(cx+g0,cy+g1),(cx,cy)]
    a=EPS*np.array(pts,float); y=np.array([2.,1.]*n); conf=conflicts_of(y)
    ks=[conf.index((2*i,2*i+1)) for i in range(n)]
    r=solve_dom(a,y,fixed=dict(zip(ks,pat)),conflicts=conf)
    cost,u=polish_margin(a,conf,r[1],1e-6); Q=np.exp(u)
    res={}
    for ra in rat: res[ra]=weakly_solvable(Q,np.array([1+ra,1.]*n)) and cost-r[2]<1e-4
    return pat,r[2],res
if __name__=="__main__":
    rat=[0.1,0.2,0.5]  # y_top = 1+ra  (ratio 1.1,1.2,1.5)
    for label,sw in [("AF n4 mixed",[(-3*i,3*i)+((4,5) if i%2==0 else (5,4)) for i in range(4)]),
                     ("AF n5 mixed",[(-3*i,3*i)+((4,5) if i%2==0 else (5,4)) for i in range(5)]),
                     ("AF n5 uniform(4,5)",[(-3*i,3*i)+(4,5) for i in range(5)])]:
        n=len(sw)
        with Pool(8) as p: out=p.map(job,[(sw,pat,rat) for pat in itertools.product((0,1),repeat=n)])
        tb={o[0]:o[1] for o in out}
        c,e=fit(tb,n,[(i,i+1) for i in range(n-1)])
        print(label,"NN Ising: E0=%.5f h=%s J=%s resid=%.1e"%(c[0],np.round(c[1:1+n],4),np.round(c[1+n:],4),e))
        for ra in rat: print("  y_top=%.2f: solvable for %d/%d patterns"%(1+ra,sum(o[2][ra] for o in out),len(out)))
        print("  min pattern",min(tb,key=tb.get),"%.5f"%min(tb.values()))
