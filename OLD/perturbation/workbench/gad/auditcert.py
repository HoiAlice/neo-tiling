import sys, itertools, math, collections, time, pickle
import numpy as np
from multiprocessing import Pool
import scheme, audit
from np_dual import Block, branch_and_bound, B_closed
from schemerun import GRAPHS
JE=audit.JE
def signature(L,Y,members,rels):
    b0=L.sw[members[0]]
    geo=tuple((float(L.sw[m][0]-b0[0]),float(L.sw[m][1]-b0[1]),L.sw[m][2]) for m in members)
    pts=[]
    for m in members: pts+= [Y[2*m],Y[2*m+1]]
    vals=sorted(set(pts),reverse=True); rank=tuple(vals.index(p) for p in pts)
    return (geo,rank,tuple(rels))
def plain_blocks(L,T,Y):
    out=collections.Counter(); ex={}
    rel=T['rel']
    for tag,key in (("P1","P1plain"),("P2","P2plain")):
        for blk in T[key]:
            rs=[]
            for a,b in zip(blk,blk[1:]):
                ri=rel.get((a,b)) or rel.get((b,a))
                rs.append((ri['kind'],1 if ri['weak'] else 2))
            sig=signature(L,Y,blk,rs); out[(tag,sig)]+=1; ex[sig]=blk
    return out
def cert_sig(sig):
    geo,rank,rels=sig
    n=len(geo)
    # levels from rank (higher y = smaller rank number): y = len(rank)-rank
    sw=[]
    for q,(dx,dy,d) in enumerate(geo):
        yt=float(len(rank)-rank[2*q]); yb=float(len(rank)-rank[2*q+1]); sw.append((dx,dy,d,yt,yb))
    blk=Block(sw); SB=sum(B_closed(s[2]) for s in sw); res={}
    for bits in itertools.product((0,1),repeat=n):
        fixed={blk.own[i]:b for i,b in enumerate(bits)}
        lo,hi,_,st=branch_and_bound(blk,fixed,tol=1e-9); res[bits]=(lo,hi)
    def viol(b): return sum(c for i,(k,c) in enumerate(rels) if ((b[i]==b[i+1])!=(k=='eq')))
    sat=[b for b in res if viol(b)==0]; S=min(res[b][1] for b in sat)
    worst=min(((res[b][0]-S-JE*viol(b)),b) for b in res if viol(b)>0)
    return dict(n=n,S_minus_sumB=S-SB,margin=worst[0],at=worst[1])
if __name__=="__main__":
    allsig=collections.Counter(); where=collections.defaultdict(set)
    for g in ("K3","K4","K33"):
        n,edges=GRAPHS[g]; L=scheme.build(n,edges); T=audit.tilings(L)
        yt,yb,k=scheme.levels(L); import numpy as np
        Y=np.zeros(2*len(L.sw)); Y[0::2]=yt; Y[1::2]=yb
        c=plain_blocks(L,T,Y)
        for (tag,sig),cnt in c.items(): allsig[sig]+=cnt; where[sig].add(g)
    print("distinct plain block types:",len(allsig),"occurrences",sum(allsig.values()),flush=True)
    sizes=collections.Counter(len(s[0]) for s in allsig); print("by size",dict(sizes))
    pickle.dump(dict(allsig),open("audit_sigs.pkl","wb"))
