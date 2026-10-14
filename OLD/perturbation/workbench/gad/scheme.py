"""scheme.py -- explicit bus/track layout generator (CROSSING-GADGET UPDATE 10/11).
All coordinates are grid units in (1/4)Z at the library step H = 4 ln(21/20).  Points: 2i top, 2i+1 bottom.
Input: n vertices, edge list [(i,j)] i<j (max degree 3).  Output: Layout object (switch list, chains for bit propagation, crossings, kinks)."""
import math, itertools
from fractions import Fraction
import numpy as np
H=4*math.log(21/20)
RELAY_GAP=12; BUS_GAP=46; W=54; C0=12; HALF=True
def qsteps(total,l):
    T=round(total*4)
    if abs(T-total*4)>1e-9: return None
    if not (11*l<=T<=14*l): return None
    base=T//l; rem=T-base*l; st=[base]*l
    for i in range(rem): st[i]+=1
    # interleave to keep steps spread (not sorted)
    st.sort()
    out=[]; lo,hi=0,len(st)-1
    while lo<=hi:
        out.append(st[lo]); lo+=1
        if lo<=hi: out.append(st[hi]); hi-=1
    return [x/4 for x in out]
class Layout:
    pass
def build(n,edges,W=W,C0=C0):
    deg=[0]*n; inc=[[] for _ in range(n)]
    for e,(i,j) in enumerate(edges):
        assert i<j; inc[i].append(e); inc[j].append(e)
    assert all(len(x)<=3 for x in inc)
    L=Layout(); L.sw=[]; L.meta=[]; L.n=n; L.edges=edges
    def add(bx,by,d,kind,**kw):
        L.sw.append((Fraction(bx).limit_denominator(8),Fraction(by).limit_denominator(8),d)); L.meta.append(dict(kind=kind,**kw)); return len(L.sw)-1
    Kv=[5+BUS_GAP*v for v in range(n)]
    relay={}   # (v,e) -> k
    for v in range(n):
        for r,e in enumerate(inc[v]): relay[(v,e)]=Kv[v]+RELAY_GAP*r
    L.bus=[]; L.star={}
    for v in range(n):
        kr=[relay[(v,e)] for e in inc[v]] or [Kv[v]]
        lo=min(kr)-5; hi=max(kr)+5
        chain=[]
        for k in range(lo,hi+1):
            idx=add(k-0.5,k-0.5,5,'bus',v=v,k=k); chain.append(idx)
            if (v,k) in [(vv,kk) for (vv,ee),kk in relay.items() if vv==v]:
                L.star[(v,k)]=idx
        L.bus.append(chain)
    cE=[C0+9*e for e in range(len(edges))]
    TE=[3+6*c for c in cE]
    # crossings: arm f at k_f (edge f) crosses track e if T_e<T_f and k_i(e)<k_f<k_j(e)
    arms=[]   # (edge, vertex, k)
    for e,(i,j) in enumerate(edges):
        arms.append((e,i,relay[(i,e)])); arms.append((e,j,relay[(j,e)]))
    cross_of_arm={}
    for (f,u,kf) in arms:
        lst=[]
        for e,(i,j) in enumerate(edges):
            if e==f: continue
            if TE[e]<TE[f] and relay[(i,e)]<kf<relay[(j,e)]: lst.append(e)
        cross_of_arm[(f,u)]=sorted(lst)
    L.cross_of_arm=cross_of_arm
    # arm step plans
    plan={}
    for e,(i,j) in enumerate(edges):
        pK=(TE[e]-6)/2
        info=[]
        for u in (i,j):
            cs=cross_of_arm[(e,u)]
            ctop=max([cE[x] for x in cs]) if cs else None
            pstart=3*(ctop+2) if ctop is not None else 6
            Lam=pK-pstart
            nfull=int(round(pstart/3))            # number of 3-steps before the tail
            info.append(dict(u=u,pstart=pstart,Lam=Lam,nfull=nfull))
        # choose tail step counts and weak holder: parity of (n_i+n_j) odd, n = nfull + ntail + 1
        best=None
        for hold in (0,1):
            rng=[]
            for q,inf in enumerate(info):
                lo=math.ceil(inf['Lam']/3.5-1e-9); hi=math.floor(inf['Lam']/2.75+1e-9)
                if q==hold:
                    rng.append([t for t in range(max(lo,5),hi+1) if qsteps(inf['Lam']-3.75,t-1)])
                else:
                    rng.append([t for t in range(lo,hi+1) if qsteps(inf['Lam'],t)])
            for t0 in rng[0]:
                for t1 in rng[1]:
                    n0=info[0]['nfull']+t0+1; n1=info[1]['nfull']+t1+1
                    if (n0+n1)%2==1:
                        cost=t0+t1
                        if best is None or cost<best[0]: best=(cost,hold,t0,t1)
        assert best is not None,("no step plan",e,info)
        _,hold,t0,t1=best
        plan[e]=dict(hold=hold,tails=[t0,t1],info=info,pK=pK)
    L.plan=plan; L.TE=TE; L.cE=cE
    # emit arms and tracks
    L.arm={}; L.track={}; L.kink={}; L.corner={}
    for e,(i,j) in enumerate(edges):
        pl=plan[e]; pK=pl['pK']
        armidx=[]
        for q,u in enumerate((i,j)):
            k=relay[(u,e)]; a1=(k-3,k+3)
            inf=pl['info'][q]; nt=pl['tails'][q]
            steps=[3.0]*inf['nfull']
            weakpos=None
            if q==pl['hold']:
                st=qsteps(inf['Lam']-3.75,nt-1); mid=nt//2
                tail=st[:mid]+[3.75]+st[mid:]; weakpos=len(steps)+mid
            else:
                tail=qsteps(inf['Lam'],nt)
            steps=steps+tail
            p=0.0; idxs=[]
            for si in range(len(steps)+1):
                bx,by=a1[0]-p,a1[1]+p
                idxs.append(add(bx,by,4,'arm',e=e,u=u,pos=si))
                if si<len(steps): p+=steps[si]
            assert abs(p-pK)<1e-9,(p,pK)
            armidx.append(idxs); L.arm[(e,u)]=dict(idx=idxs,star=L.star[(u,k)],weak=weakpos,steps=steps,k=k)
            if weakpos is not None: L.kink[e]=(idxs[weakpos],idxs[weakpos+1],u)
        # track: V_0 at K=a_n of arm i, V_m=K+(m-0.5), V'_0 at K'
        K=(Fraction(relay[(i,e)]-3)-Fraction(pK).limit_denominator(8),Fraction(relay[(i,e)]+3)+Fraction(pK).limit_denominator(8))
        N=relay[(j,e)]-relay[(i,e)]
        tr=[add(K[0],K[1],5,'track',e=e,m=0)]
        # T1 corner at K: V_0 shares the bottom of u0; T4 corner at K' (reflected type): V'_0 shares the TOP corner of u0', i.e. V'_0 bottom = K' - (1,1)
        for m in range(1,N): tr.append(add(K[0]+m-0.5,K[1]+m-0.5,5,'track',e=e,m=m))
        tr.append(add(K[0]+N-1,K[1]+N-1,5,'track',e=e,m=N))
        L.track[e]=dict(idx=tr,K=K,N=N)
    # crossings
    L.crossings=[]
    for (f,u,kf) in arms:
        for e in cross_of_arm[(f,u)]:
            i,j=edges[e]; m=kf-relay[(i,e)]
            vc=L.track[e]['idx'][m]
            # arm switches of f: U bottoms v+(2,-1)+mm(-3,3), mm=-1..2 ; find by position
            vb=L.sw[vc]; ids=[]
            pos={ (L.sw[x][0],L.sw[x][1]):x for x in L.arm[(f,u)]['idx']}
            for mm in (-1,0,1,2):
                key=(vb[0]+2-3*mm,vb[1]-1+3*mm)
                assert key in pos,("crossing misaligned",f,e,mm,key)
                ids.append(pos[key])
            L.crossings.append(dict(arm=(f,u),track=e,vidx=vc,m=m,uidx=ids,vcore=L.track[e]['idx'][m-2:m+3]))
    return L
def levels(L,c1=0.02,Delta=0.6,g=0.002,eps=0.3):
    sc=np.array([float(x[0]+x[1]+x[2]) for x in L.sw])
    kinks=sorted({float(L.sw[a['idx'][0]][0]+L.sw[a['idx'][0]][1]+4) for a in L.arm.values()})
    smax=sc.max()+1
    F=1+c1*(smax-sc)
    for k in kinks: F=F+Delta*np.maximum(0.0,smax-np.maximum(sc,k))
    top=F+g; m=top.max()
    yb=1+eps*F/m; yt=1+eps*top/m
    return yt,yb,kinks
def intended_bits(L,vb):
    """vb: list of bus bits.  returns sigma list, kink_active dict e->bool"""
    sig=[None]*len(L.sw); active={}
    for v,chain in enumerate(L.bus):
        for idx in chain: sig[idx]=vb[v]
    for e,(i,j) in enumerate(L.edges):
        pl=L.plan[e]; hold=pl['hold']
        arms=[L.arm[(e,i)],L.arm[(e,j)]]; verts=[i,j]
        # non-holder arm: plain alternation
        ne=1-hold; a=arms[ne]; b=vb[verts[ne]]
        bits=[(b^((k+1)%2)) for k in range(len(a['idx']))]       # a_1 = not b, ...
        tb=bits[-1]
        for idx,bb in zip(a['idx'],bits): sig[idx]=bb
        # holder arm
        h=arms[hold]; bh=vb[verts[hold]]
        plain=[(bh^((k+1)%2)) for k in range(len(h['idx']))]
        kinked = (plain[-1]!=tb)
        active[e]=kinked
        bits=[]; cur=bh
        for k in range(len(h['idx'])):
            # link from previous (star for k=0) to a_{k+1}: weak link is between a_w and a_{w+1}: link index w+? -> before element k=w+1
            flip=1
            if kinked and h['weak'] is not None and k==h['weak']+1: flip=0
            cur^=flip; bits.append(cur)
        assert bits[-1]==tb
        for idx,bb in zip(h['idx'],bits): sig[idx]=bb
        for idx in L.track[e]['idx']: sig[idx]=tb
    return sig,active
