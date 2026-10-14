"""scheme2.py -- CANONICAL bus/track generator.  Parameters: RE (number of exact 3-steps required around every gadget), G (relay gap on a bus, V steps).
Strong U steps are exactly 3 within RE steps of every gadget (star, crossing core, corner, weak link); the only irregular steps (2.75 or 3.25, one sign per arm, a run of u steps among 12) sit in the middle of the tail,
i.e. at least RE steps from every gadget; strong steps are in {2.75, 3, 3.25}; the weak step is 3.75.  Everything else as in scheme.py (UPDATE 10/11)."""
import math
from fractions import Fraction
import numpy as np
H=4*math.log(21/20)
NIRR=12
class Layout: pass
def build(n,edges,RE=8,G=20,RW=13):
    WC=3*RE+18; C0=WC
    BUS_GAP=2*G+2*RW+34
    deg=[0]*n; inc=[[] for _ in range(n)]
    for e,(i,j) in enumerate(edges):
        assert i<j; inc[i].append(e); inc[j].append(e)
    assert all(len(x)<=3 for x in inc)
    L=Layout(); L.sw=[]; L.meta=[]; L.n=n; L.edges=edges; L.params=dict(RE=RE,G=G,RW=RW,WC=WC,C0=C0,BUS_GAP=BUS_GAP)
    def add(bx,by,d,kind,**kw):
        L.sw.append((Fraction(bx).limit_denominator(8),Fraction(by).limit_denominator(8),d)); L.meta.append(dict(kind=kind,**kw)); return len(L.sw)-1
    Kv=[5+BUS_GAP*v for v in range(n)]
    relay={}
    for v in range(n):
        for r,e in enumerate(inc[v]): relay[(v,e)]=Kv[v]+G*r
    L.bus=[]; L.star={}
    starks=collections_defaultdict(list) if False else None
    for v in range(n):
        kr=[relay[(v,e)] for e in inc[v]] or [Kv[v]]
        lo=min(kr)-5; hi=max(kr)+5; chain=[]
        for k in range(lo,hi+1):
            idx=add(k-0.5,k-0.5,5,'bus',v=v,k=k); chain.append(idx)
            if k in kr and inc[v]: L.star[(v,k)]=idx
        L.bus.append(chain)
    cE=[C0+WC*e for e in range(len(edges))]
    TE=[3+6*c for c in cE]
    arms=[]
    for e,(i,j) in enumerate(edges):
        arms.append((e,i,relay[(i,e)])); arms.append((e,j,relay[(j,e)]))
    cross_of_arm={}
    for (f,u,kf) in arms:
        lst=[e for e,(i,j) in enumerate(edges) if e!=f and TE[e]<TE[f] and relay[(i,e)]<kf<relay[(j,e)]]
        cross_of_arm[(f,u)]=sorted(lst)
    L.cross_of_arm=cross_of_arm
    plan={}
    for e,(i,j) in enumerate(edges):
        c=cE[e]; pK=(TE[e]-6)/2
        hold=0                                  # holder = arm at the smaller vertex
        # S = number of steps of the arm; parity: S_i + S_j odd: holder S=c-1 (d=+3), other S=c (d=-6)
        Ss=[c-1,c]; hs=[1,0]
        arm_plans=[]
        for q,u in enumerate((i,j)):
            cs=cross_of_arm[(e,u)]
            ctop=max([cE[x] for x in cs]) if cs else None
            head=(ctop+1+RE) if ctop is not None else (RE+1)
            S=Ss[q]; h=hs[q]
            d=12*(c-S)-6-3*h
            assert abs(d)<=NIRR,(d)
            tail=S-head
            need=NIRR+RE+(1+RE if h else 0)
            assert tail>=need,("tail too short",e,u,tail,need,head,S)
            pad=tail-NIRR-(1+RE if h else 0)    # exact steps between I and weak (holder) / to the corner (others)
            assert pad>=RE
            irr=([3.25]*d+[3.0]*(NIRR-d)) if d>=0 else ([2.75]*(-d)+[3.0]*(NIRR+d))
            if h: tail_steps=irr+[3.0]*pad+[3.75]+[3.0]*RE
            else: tail_steps=irr+[3.0]*pad
            steps=[3.0]*head+tail_steps
            assert abs(sum(steps)-pK)<1e-9,(sum(steps),pK,e,u)
            weakpos=(head+NIRR+pad) if h else None
            arm_plans.append(dict(u=u,steps=steps,weakpos=weakpos,head=head,d=d,S=S))
        plan[e]=dict(hold=hold,arms=arm_plans,pK=pK)
    L.plan=plan; L.TE=TE; L.cE=cE
    L.arm={}; L.track={}; L.kink={}; L.corner={}
    for e,(i,j) in enumerate(edges):
        pl=plan[e]; pK=pl['pK']
        for q,u in enumerate((i,j)):
            ap=pl['arms'][q]; k=relay[(u,e)]; a1=(k-3,k+3); steps=ap['steps']
            p=0.0; idxs=[]
            for si in range(len(steps)+1):
                idxs.append(add(a1[0]-p,a1[1]+p,4,'arm',e=e,u=u,pos=si))
                if si<len(steps): p+=steps[si]
            L.arm[(e,u)]=dict(idx=idxs,star=L.star[(u,k)],weak=ap['weakpos'],steps=steps,k=k)
            if ap['weakpos'] is not None: L.kink[e]=(idxs[ap['weakpos']],idxs[ap['weakpos']+1],u)
        K=(Fraction(relay[(i,e)]-3)-Fraction(pK).limit_denominator(8),Fraction(relay[(i,e)]+3)+Fraction(pK).limit_denominator(8))
        N=relay[(j,e)]-relay[(i,e)]
        tr=[add(K[0],K[1],5,'track',e=e,m=0)]
        for m in range(1,N): tr.append(add(K[0]+m-0.5,K[1]+m-0.5,5,'track',e=e,m=m))
        tr.append(add(K[0]+N-1,K[1]+N-1,5,'track',e=e,m=N))
        L.track[e]=dict(idx=tr,K=K,N=N)
    L.crossings=[]
    for (f,u,kf) in arms:
        for e in cross_of_arm[(f,u)]:
            i,j=edges[e]; m=kf-relay[(i,e)]
            vc=L.track[e]['idx'][m]; vb=L.sw[vc]; ids=[]
            pos={(L.sw[x][0],L.sw[x][1]):x for x in L.arm[(f,u)]['idx']}
            for mm in (-1,0,1,2):
                key=(vb[0]+2-3*mm,vb[1]-1+3*mm); assert key in pos,("crossing misaligned",f,e,mm)
                ids.append(pos[key])
            L.crossings.append(dict(arm=(f,u),track=e,vidx=vc,m=m,uidx=ids,vcore=L.track[e]['idx'][m-2:m+3]))
    return L
def levels(L,rho=11.0,c1=0.02,gfac=0.1,eps=0.3):
    """geometric-slope rule: kinks at the s_c of every arm; slope multiplies by rho at each kink (toward NE); gap g(s) = gfac*slope(s).  Returns yt,yb (floats, per switch), kinks."""
    sc=np.array([float(x[0]+x[1]+x[2]) for x in L.sw])
    kinks=sorted({float(L.sw[a['idx'][0]][0]+L.sw[a['idx'][0]][1]+4) for a in L.arm.values()})
    return sc,kinks
