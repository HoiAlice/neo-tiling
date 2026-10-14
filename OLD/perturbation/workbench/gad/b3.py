from bias import *
from multiprocessing import Pool
def job(a):
    name,sw=a; n=len(sw)
    tb=table(sw)
    nn=[(i,i+1) for i in range(n-1)]
    c1,e1=fit(tb,n,nn); c2,e2=fit(tb,n)
    return name,n,c1,e1,e2,min(tb,key=tb.get),min(tb.values())
if __name__=="__main__":
    G1=(4,5);G2=(5,4)
    jobs=[]
    for step in [(3,3),(5,5)]:
        for n in (3,4,5):
            jobs.append((f"ferro{step} all(4,5) n={n}",[(step[0]*i,step[1]*i)+G1 for i in range(n)]))
        jobs.append((f"ferro{step} mixed (4,5),(5,4),(4,5),(5,4)",[(step[0]*i,step[1]*i)+(G1 if i%2==0 else G2) for i in range(4)]))
    jobs.append(("antiferro(-3,3) all(4,5) n=4",[(-3*i,3*i)+G1 for i in range(4)]))
    jobs.append(("antiferro(-3,3) mixed n=4",[(-3*i,3*i)+(G1 if i%2==0 else G2) for i in range(4)]))
    with Pool(8) as p:
        for name,n,c1,e1,e2,arg,mn in p.map(job,jobs):
            print(name,"\n  NN fit: E0=%.4f h=%s J=%s resid=%.2e | all-pairs resid=%.2e | argmin %s %.4f"%(c1[0],np.round(c1[1:1+n],4),np.round(c1[1+n:],4),e1,e2,arg,mn))
