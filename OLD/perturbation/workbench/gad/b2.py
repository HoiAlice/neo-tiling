from bias import *
from multiprocessing import Pool
def job(a):
    off,g=a; ox,oy=off
    tb=table([(0,0,)+g[0],(ox,oy)+g[1]])
    c,e=fit(tb,2); return a,tb,c,e
if __name__=="__main__":
    jobs=[]
    for off in [(1,1),(2,2),(3,3),(5,5),(-3,3),(3,-3),(-2,3),(0,5)]:
        for g in [((4,5),(4,5)),((4,5),(5,4))]:
            jobs.append((off,g))
    with Pool(8) as p:
        for a,tb,c,e in p.map(job,jobs):
            print(a,"E0=%.4f h=%s J=%.4f"%(c[0],np.round(c[1:3],4),c[3]),"| T:",{''.join(map(str,k)):round(v,4) for k,v in tb.items()})
