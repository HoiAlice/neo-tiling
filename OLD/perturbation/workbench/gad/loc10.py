import sys, json, numpy as np
from multiprocessing import Pool
from loc8 import build_inst
from loc7 import sat_value, milp_credit
aW=float(sys.argv[1]); TL=float(sys.argv[2]) if len(sys.argv)>2 else 900
Je=2*(np.exp((4-aW)*0.2/2)-1)
sw=build_inst(aW)
K=[2,3,4,5,6,19,20,21,22]
def rels(blk,spec):  # spec list of (a,b,kind,credit) in global ids
    ix={s:i for i,s in enumerate(blk)}
    return [(ix[a],ix[b],k,c) for a,b,k,c in spec]
c2=2*Je
P1=[("K1",[1,2,3,4,5,6,7,18,19,20,21,22,23],[(1,2,'eq',c2),(6,7,'eq',c2),(18,19,'ne',c2),(22,23,'ne',c2),(2,6,'eq',Je),(19,22,'ne',Je)]),
    ("c09",[0,9],[(0,9,'eq',c2)]),
    ("w1112",[11,12],[(11,12,'ne',Je)]),
    ("v1314",[13,14],[(13,14,'ne',c2)]),
    ("w1617",[16,17],[(16,17,'ne',Je)])]
P1s=[("s10",[10],[]),("s8",[8],[]),("s15",[15],[]),("s24",[24],[])]
P2=[("K2",K,[(2,6,'eq',Je),(19,22,'ne',Je)]),
    ("v01",[0,1],[(0,1,'eq',c2)]),
    ("u9_13",[9,10,11,12,13],[(9,10,'ne',c2),(10,11,'ne',c2),(11,12,'ne',Je),(12,13,'ne',c2)]),
    ("s14",[14],[]),
    ("v78",[7,8],[(7,8,'eq',c2)]),
    ("e15_18",[15,16,17,18],[(15,16,'ne',c2),(16,17,'ne',Je),(17,18,'ne',c2)]),
    ("p2324",[23,24],[(23,24,'ne',c2)])]
jobs=[("P1",n,b,s) for n,b,s in P1]+[("P2",n,b,s) for n,b,s in P2]
def work(j):
    part,name,blk,spec=j
    swb=[sw[i] for i in blk]; r=rels(blk,spec)
    S=sat_value(swb,r,TL); C=milp_credit(swb,r,TL)
    return part,name,blk,S,C
if __name__=="__main__":
    with Pool(8) as p: out=p.map(work,jobs,chunksize=1)
    Bf=lambda d:2*(np.exp(d*0.1)-1)
    tot={"P1":0.0,"P2":0.0}
    for part,name,blk,S,C in out:
        tot[part]+=S[0]; print(part,name,blk,"S=%.6f cert=%.6f margin=%.2e status=%s/%s"%(S[0],C[0],C[0]-S[0],S[2],C[2]),flush=True)
    for part,sset in (("P1",P1s),("P2",[])):
        for n,b,s in sset: tot[part]+=Bf(sw[b[0]][2])
    sb=sum(Bf(s[2]) for s in sw)
    print("aW",aW,"Je",Je,"S0(P1)",tot["P1"],"S0(P2)",tot["P2"],"sumB",sb,"X total",tot["P1"]-sb,tot["P2"]-sb)
    json.dump(dict(Je=Je,S0=tot,sumB=sb),open("loc10_%s.json"%aW,"w"))
