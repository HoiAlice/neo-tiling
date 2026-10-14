import sys, collections, itertools
import numpy as np
import scheme, audit
from schemerun import GRAPHS
import np_kplus, np_star
from np_cross import vlev
def canon(sws, Ylist):
    """sws: list of (bx,by,d); Ylist: list of (yt,yb); canonical form up to translation and monotone relabelling of levels"""
    order=sorted(range(len(sws)),key=lambda i:(sws[i][0],sws[i][1],sws[i][2]))
    bx0,by0=sws[order[0]][0],sws[order[0]][1]
    pts=[]; geo=[]
    for i in order:
        geo.append((round(float(sws[i][0]-bx0),4),round(float(sws[i][1]-by0),4),sws[i][2])); pts+=[Ylist[i][0],Ylist[i][1]]
    vals=sorted(set(round(p,12) for p in pts),reverse=True)
    rank=tuple(vals.index(round(p,12)) for p in pts)
    return (tuple(geo),rank)
def scheme_blocks(L,Y):
    star_cores,cross_cores,bus_pos=audit.build_model(L)
    out=collections.defaultdict(list)
    def lv(m): return (Y[2*m],Y[2*m+1])
    for c in star_cores:
        ctr=c['centre']; arm=c['arm']; a1,a2=arm['idx'][0],arm['idx'][1]
        v,p=c['bus']; chain=L.bus[v]
        core=[ctr,a1,chain[p-1],chain[p+1]]
        plus=core+[a2,chain[p-2],chain[p+2]]
        out['star core'].append(canon([L.sw[m] for m in core],[lv(m) for m in core]))
        out['star^+'].append(canon([L.sw[m] for m in plus],[lv(m) for m in plus]))
    for c in cross_cores:
        cr=c['cr']; arm=L.arm[cr['arm']]['idx']; pos=arm.index(cr['uidx'][0])
        un=[arm[pos-1]]+cr['uidx']+[arm[pos+4]]
        vc=cr['vcore']; tr=L.track[cr['track']]['idx']; pv=tr.index(vc[0])
        vn=[tr[pv-1]]+vc+[tr[pv+5]]
        out['K'].append(canon([L.sw[m] for m in cr['uidx']+vc],[lv(m) for m in cr['uidx']+vc]))
        out['K^+'].append(canon([L.sw[m] for m in un+vn],[lv(m) for m in un+vn]))
    return out
def library():
    lib={}
    sw=np_kplus.kplus(); idx=list(range(13))
    lib['K^+']=canon([(s[0],s[1],s[2]) for s in sw],[(s[3],s[4]) for s in sw])
    core=[1,2,3,4]+[7,8,9,10,11]
    lib['K']=canon([(sw[i][0],sw[i][1],sw[i][2]) for i in core],[(sw[i][3],sw[i][4]) for i in core])
    s,names,rel=np_star.star(('NW','SW','NE'),True)
    lib['star^+']=canon([(x[0],x[1],x[2]) for x in s],[(x[3],x[4]) for x in s])
    s,names,rel=np_star.star(('NW','SW','NE'),False)
    lib['star core']=canon([(x[0],x[1],x[2]) for x in s],[(x[3],x[4]) for x in s])
    return lib
if __name__=="__main__":
    lib=library()
    for g in ("K3","K4","K33"):
        n,edges=GRAPHS[g]; L=scheme.build(n,edges)
        yt,yb,k=scheme.levels(L); Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
        sb=scheme_blocks(L,Y)
        for kind,lst in sb.items():
            cnt=collections.Counter(lst); match=sum(v for s,v in cnt.items() if s==lib[kind])
            print(g,kind,"blocks",len(lst),"distinct",len(cnt),"equal to library geometry+order:",match)
