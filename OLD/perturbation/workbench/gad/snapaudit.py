import sys, itertools, collections, pickle
import numpy as np
import scheme, scheme2, qstar, descW
from schemerun2 import surrogate_Y, GRAPHS
EDGES=[1e-12,1e-9,1e-7,1e-5,1e-4]
def audit_layout(L,patterns,label):
    lib=qstar.library(); A,dsz=qstar.point_arrays(L); Y=surrogate_Y(L); T=len(A)
    hist=collections.Counter(); classes=collections.Counter(); examples={}
    nsw=lambda p:p//2
    for vb in patterns:
        sig,act=scheme.intended_bits(L,list(vb)); D=qstar.assemble(L,sig,act,lib,A,dsz); Q=A+D
        for c in (0,1):
            v=Q[:,c]; o=np.argsort(v); vs=v[o]
            d=np.diff(vs); idx=np.nonzero(d<1e-4)[0]
            for i in idx:
                # cluster neighbours: compare i with i+1 .. while within 1e-4
                j=i+1
                while True:
                    a,b=int(o[i]),int(o[j]); dd=abs(vs[j]-vs[i])
                    if dd>=1e-4: break
                    b_=np.searchsorted(EDGES,dd,side='right'); hist[b_]+=1
                    if dd<1e-5:     # would be merged by snapping
                        ia,ib=a//2,b//2
                        if ia==ib: cl='own pair (top/bottom meet)'
                        else:
                            ya,yb=Y[a],Y[b]
                            if ya==yb:
                                kp={(a1,b1) for e,(a1,b1,u) in L.kink.items() if act.get(e)}
                                core=any((ia in set(cr['uidx']+cr['vcore'])) and (ib in set(cr['uidx']+cr['vcore'])) for cr in L.crossings)
                                nearcore=any((ia in set(cr['uidx']+cr['vcore'])) or (ib in set(cr['uidx']+cr['vcore'])) for cr in L.crossings)
                                if (ia,ib) in kp or (ib,ia) in kp: cl='same level: pooled kink pair (weak link unsatisfied)'
                                elif core: cl='same level: two switches of one crossing core (library optimum)'
                                elif nearcore: cl='same level: crossing-core switch and its plain neighbour (K^+ link)'
                                else: cl='same level, different switches (UNCLASSIFIED)'
                            else:
                                hi,lo=(a,b) if ya>yb else (b,a)
                                # conflict (hi,lo): need Q_hi <= Q_lo in some coordinate; tight if slack in c ~ 0
                                sl=Q[lo,c]-Q[hi,c]
                                cl='conflict pair, tight' if abs(sl)<1e-5 else 'conflict pair, other'
                        classes[cl]+=1
                        if 'UNCLASSIFIED' in cl or cl=='conflict pair, other':
                            if cl not in examples:     examples[cl]=(vb,c,a,b,float(dd),L.meta[a//2],L.meta[b//2])
                    j+=1
                    if j>=T: break
    print(label,"patterns",len(patterns),"| pairs with |diff| in bins [<1e-12, <1e-9, <1e-7, <1e-5, <1e-4]:",[hist[k] for k in range(5)],"| classes of pairs merged by snapping (<1e-5):",dict(classes),flush=True)
    return hist,classes,examples
if __name__=="__main__":
    which=sys.argv[1]
    if which=="W":
        R=float(sys.argv[2]); RE=int(sys.argv[3]); G=int(sys.argv[4])
        n,edges,order=descW.witness(); L=scheme2.build(n,edges,RE,G,RW=int(R))
        vcomp=[]
        for k,name in enumerate(order): vcomp+= [k]*descW.COMP[name][0]
        pats=set()
        for k in range(len(order)):
            verts=[v for v in range(n) if vcomp[v]==k]
            for bits in itertools.product((0,1),repeat=len(verts)):
                vb=[0]*n
                for v,b in zip(verts,bits): vb[v]=b
                pats.add(tuple(vb))
        h,c,ex=audit_layout(L,sorted(pats),"witness W (R=%g,RE=%d,G=%d)"%(R,RE,G))
    else:
        n,edges=GRAPHS[which]; L=scheme2.build(n,edges,8,20,RW=13)
        pats=list(itertools.product((0,1),repeat=n)) if n<=6 else list(itertools.product((0,1),repeat=n))[:64]
        h,c,ex=audit_layout(L,pats,"%s (RE=8,G=20)"%which)
    for k,v in ex.items(): print("  EXAMPLE of",k,":",v)
