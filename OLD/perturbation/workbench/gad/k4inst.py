import pickle, numpy as np
from layout import *
def load():
    key,rs,tr,sol,inst=pickle.load(open("lay_k4_best.pkl","rb"))
    return sol,inst
def instance(slope=None):
    sol,inst=load()
    sw=inst["sw"]
    global SLOPE
    lv=levels(sw)
    return sol,inst,lv
if __name__=="__main__":
    sol,inst,lv=instance()
    sc=[bx+by+d for (bx,by,d,_,_) in lv]
    ys=[b for (_,_,_,_,b) in lv]; yt=[t for (_,_,_,t,_) in lv]
    print("switches",len(lv),"s range",min(sc),max(sc),"y range",min(ys),max(yt),"ratio",max(yt)/min(ys))
    print("vertex indices",[inst["vidx"][v] for v in range(inst["nv_total"])])
    for e,(c,wk,combo) in inst["choice"].items(): print("edge",e,"weak seg",wk,"links",[x[0] for x in combo])
    for k,((p,q,e),op,n,L) in enumerate(sol["segs"]): print("seg",k,(p,q,e),op["kind"],op["A"],op["B"],op["aa"],op["bb"],"n",n,"L",round(L,2))
    print("vertex bottoms",[tuple(round(a,2) for a in x) for x in inst["pos"]])
