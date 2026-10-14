from bias import *
from multiprocessing import Pool
G=(6,6)
base=[(0,0)+G,(2,2)+G,(5,-3)+G]
def job(p):
    sw=base+[p+G]; tb=table(sw); c,e=fit(tb,4); return p,c,e
if __name__=="__main__":
    cand=[(x,y) for x in range(-8,9,1) for y in range(-8,9,1) if (x,y) not in [(0,0),(2,2),(5,-3)] and abs(x)+abs(y)>0 and all((x-bx)**2+(y-by)**2>=4 for bx,by,*_ in base)]
    with Pool(10) as pl: res=pl.map(job,cand,chunksize=4)
    good=[r for r in res if r[2]<1e-7]
    print(len(cand),"scanned,",len(good),"exact")
    for p,c,e in sorted(good):
        print(p,"E0=%.4f h=%s J(01,02,03,12,13,23)=%s resid=%.1e"%(c[0],np.round(c[1:5],4),np.round(c[5:],4),e))
