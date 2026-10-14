import itertools, time, math
from multiprocessing import Pool
from np_star import *
def run(arms,outward):
    sw,names,rel=star(arms,outward); n=len(sw); SB=sum(B_closed(s[2]) for s in sw)
    t0=time.time()
    with Pool(8) as pool: out=pool.map(work,[(sw,p) for p in itertools.product((0,1),repeat=n)],chunksize=4)
    res={p:(lo,hi) for p,lo,hi in out}
    def viol(p): return sum(c for (i,j,k,c) in rel if ((p[i]==p[j])!=(k=='eq')))
    sat=[p for p in res if viol(p)==0]; S=min(res[p][1] for p in sat)
    worst=min(((res[p][0]-S-JE*viol(p)),p) for p in res if viol(p)>0)
    print(arms,"outward" if outward else "core","n",n,"S-sumB %.2e"%(S-SB),"sat",len(sat),"min margin %.6f at %s"%worst,"%.0fs"%(time.time()-t0),flush=True)
if __name__=="__main__":
    run(('NW','SW','NE'),False); run(('NW','SW','NE'),True)
