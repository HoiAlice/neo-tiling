import sys, itertools, pickle
from multiprocessing import Pool
from layout import *
K4=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def job(args):
    rs,seed=args
    try:
        sol=solve_layout(4,K4,set(rs),time_limit=25,seed=seed)
        if sol is None: return None
        inst,err=build_instance(sol,K4,set(rs),4)
        if inst is None: return None
        bc=collisions(inst,sol)
        return (len(inst['sw']),len(bc),rs,seed,sol,inst)
    except Exception as ex:
        return None
if __name__=="__main__":
    jobs=[(rs,seed) for k in (1,2) for rs in itertools.combinations(range(6),k) for seed in range(1,7)]
    best=None; allr=[]
    with Pool(5) as p:
        for r in p.imap_unordered(job,jobs):
            if r is None: continue
            allr.append(r[:4])
            if r[1]==0 and (best is None or r[0]<best[0]):
                best=r; print("collision-free: switches",r[0],"relays",r[2],"seed",r[3],flush=True)
    pickle.dump(best,open("lay_k4_small.pkl","wb"))
    print("done; min switches",best[0] if best else None, "n results",len(allr))
