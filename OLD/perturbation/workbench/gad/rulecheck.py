import numpy as np, itertools, cx2
from k4ub import *
sol,inst,lv=get(); A,Y,conf,ks=cx2.setup(lv)
segs=sol["segs"]; pos=inst["pos"]
# part membership per switch index
owner=[None]*len(lv); i=0
for lab,sws in inst["parts"]:
    for _ in sws: owner[i]=lab; i+=1
def verts(lab):
    if lab.startswith("V"): return {int(lab[1:])}
    k=int(lab[1:lab.index("(")]); (p,q,e)=segs[k][0]; return {p,q}
def center(i): return (lv[i][0]+lv[i][2]/2,lv[i][1]+lv[i][2]/2)
bad=[];minsl=1e9;cnt=0
for (t,s) in conf:
    it,is_=t//2,s//2
    if it==is_: continue
    la,lb=owner[it],owner[is_]
    if la==lb: continue
    sh=verts(la)&verts(lb)
    near=False
    for v in sh:
        pv=(pos[v][0]+2.5,pos[v][1]+2.5); c1=center(it); c2=center(is_)
        if max(abs(c1[0]-pv[0]),abs(c1[1]-pv[1]))<=7.5 and max(abs(c2[0]-pv[0]),abs(c2[1]-pv[1]))<=7.5: near=True
    if near: continue
    cnt+=1
    sl=max(A[s,0]-A[t,0],A[s,1]-A[t,1])-1.285; minsl=min(minsl,sl)
    if sl<0: bad.append((la,lb,round(sl,3)))
print("inter-gadget conflicts",cnt,"min slack",round(minsl,3),"rule-R failures",len(bad))
from collections import Counter
print(Counter((a,b) for a,b,_ in bad).most_common(8))
