import sys, pickle, numpy as np, cx2, time
from layout import *
from core import solve_dom
def get():
    key,rs,tr,sol,inst=pickle.load(open("lay_k4_best.pkl","rb"))
    lv=levels(inst["sw"]); return sol,inst,lv
if __name__=="__main__":
    pat=tuple(int(c) for c in sys.argv[1]); tl=int(sys.argv[2])
    sol,inst,lv=get()
    A,Y,conf,ks=cx2.setup(lv)
    idx=[inst["vidx"][v] for v in range(4)]
    t=time.time()
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],pat)),conflicts=conf,time_limit=tl)
    print(pat,"npts",len(A),"conflicts",len(conf),"milp lb",round(r[0],5),"exact",round(r[2],6),"time",round(time.time()-t),flush=True)
    np.save("k4_sigma_%s.npy"%sys.argv[1],np.array(r[1]))
