import sys, itertools, numpy as np
from multiprocessing import Pool
import cx2
from core import solve_dom, polish_margin
from ysolve import find_y
g,h0,h2=0.01,0.01,0.04
def vsw(nVs=2):
    sw=[]
    for s in range(-nVs,nVs+1):
        sh = h0*(-s) if s<0 else -h2*s
        sw.append((s-0.5,s-0.5,5,1+g+sh,1+sh))
    return sw
def cand(args):
    end,dx,dy,xl,dc=args
    nVs=2; sw=vsw(nVs)
    s=-nVs if end=='SW' else nVs
    cen=(s+2+dx, s+2+dy)
    sh=(h0*(-s) if s<0 else -h2*s)+xl
    sw.append((cen[0]-dc/2,cen[1]-dc/2,dc,1+g+sh,1+sh))
    try:
        A,Y,conf,ks=cx2.setup(sw)
        n=len(sw); idx=[n-2 if False else (0 if end=='SW' else n-2), n-1]  # V end switch index, C
        tb={}
        for fx in itertools.product((0,1),repeat=2):
            r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],fx)),conflicts=conf,time_limit=30)
            tb[fx]=r
        e={k:v[2] for k,v in tb.items()}
        # V-uniform assumed by ferro chain; ground combos:
        lo=min(e.values()); hi=max(e.values())
        if hi-lo<0.02: return (args,'nocoupling',None)
        g0=[k for k,v in e.items() if v-lo<1e-3]
        Qs=[]
        for k in g0:
            cm,u=polish_margin(A,conf,tb[k][1],1e-6); Qs.append(np.exp(u))
        y=find_y(Qs,Y,1e-6,100)
        return (args,'ok' if y is not None else 'INFEAS',(round(hi-lo,4),g0))
    except Exception as ex:
        return (args,'err',str(ex)[:50])
if __name__=="__main__":
    jobs=[(end,dx,dy,xl,4) for end in ('SW','NE') for dx in np.arange(-6,6.1,1.5) for dy in np.arange(-6,6.1,1.5) for xl in (0.0,0.04,0.08,-0.04)]
    jobs=[j for j in jobs if abs(j[1])>=1.5 or abs(j[2])>=1.5]
    print(len(jobs),flush=True)
    with Pool(5) as p:
        for r in p.imap_unordered(cand,jobs,chunksize=2):
            if r[1] in ('ok','err'): print(r,flush=True)
    print("done",flush=True)
