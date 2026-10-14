from bias import *
from multiprocessing import Pool
def job(a):
    name,sw=a; tb=table(sw); c,e=fit(tb,3); return name,tb,c,e
if __name__=="__main__":
    pos=[(0,0),(-2,3),(-5,5)]
    jobs=[]
    for g in [((6,6),(6,6),(6,6)),((6,7),(6,7),(6,7)),((6,7),(7,6),(6,7)),((6,6),(6,6),(6,7))]:
        jobs.append((str(g),[p+gg for p,gg in zip(pos,g)]))
    with Pool(4) as p:
        for name,tb,c,e in p.map(job,jobs):
            print(name,"E0=%.4f h=%s J01,02,12=%s resid(3-body)=%.2e"%(c[0],np.round(c[1:4],4),np.round(c[4:],4),e))
            print("   ",{''.join(map(str,k)):round(v,4) for k,v in tb.items()})
