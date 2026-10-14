import sys, itertools, pickle
from multiprocessing import Pool
from layout2 import *
K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def job(a):
    rs,seed=a
    try:
        r=gen(4,K4,set(rs),seed,25)
        if r is None: return None
        sol,inst=r; bc=Lm.collisions(inst,sol); ok,rep=tiling_check(sol,inst)
        return (len(inst['sw']),len(bc),ok,rs,seed,sol,inst)
    except Exception as ex:
        return ("err",str(ex)[:80],rs,seed)
if __name__=="__main__":
    jobs=[(rs,seed) for k in (1,2,3) for rs in itertools.combinations(range(6),k) for seed in range(7,19)]
    best=None; n=0; errs=0; stat=[]
    with Pool(4) as p:
        for r in p.imap_unordered(job,jobs):
            if r is None: continue
            if r[0]=="err": errs+=1; 
            if r[0]=="err": 
                if errs<3: print(r)
                continue
            n+=1; stat.append((r[0],r[1],r[2]))
            if r[1]==0 and r[2] and (best is None or r[0]<best[0]):
                best=r; print("collision-free+tiling ok: switches",r[0],"relays",r[3],"seed",r[4],flush=True)
    pickle.dump(best,open("lay2_k4b.pkl","wb")); print('collision-free',sum(1 for x in stat if x[1]==0),'tiling ok',sum(1 for x in stat if x[2]),'both',sum(1 for x in stat if x[1]==0 and x[2]),'min collisions',min(x[1] for x in stat)); print("done",n,"results; best",best[0] if best else None)
