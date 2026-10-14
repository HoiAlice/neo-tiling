"""Analytic glued point Q*(sigma): isolated optima + stored crossing-core and kink displacements (from local glue runs)."""
import math, itertools, pickle, os, numpy as np
import scheme
from scheme import H
import gluelib
LIB="qstar_lib.pkl"
def Bd(d): return 2*(math.exp(d*H/2)-1)
def local_core():
    """local crossing instance: U switches mm=-3..4 along (-3,3), V dj=-4..4; returns lib[(u0,vb)] = dict role->(disp(4,)) and cost excess"""
    sw=[]
    for mm in range(-3,5): sw.append((2-3*mm,-1+3*mm,4))
    for dj in range(-4,5): sw.append((dj,dj,5))
    uc=gluelib.cx2  # noqa
    sc_u=float(sw[0][0]+sw[0][1]+4)
    swl=gluelib.rule_levels([(float(a),float(b),d) for a,b,d in sw],[sc_u])
    A,Y,conf,ks=gluelib.setup(swl); n=len(sw)
    lib={}
    for u0,vb in itertools.product((0,1),repeat=2):
        sig=[None]*n
        for k,mm in enumerate(range(-3,5)): sig[k]=u0^(mm%2)
        for k in range(8,17): sig[k]=vb
        u,c,nv=gluelib.glue(A,conf,ks,sig)
        assert nv==0
        disp=u-A
        # isolated check on non-core switches
        iso_err=0.0
        for k in range(n):
            core = (k<8 and -1<=k-3<=2) or (k>=8 and -2<=(k-8)-4<=2)
            if core: continue
            d=sw[k][2]; s=sig[k]; e=np.zeros((2,2)); e[0,s]=-d*H/2; e[1,s]=d*H/2
            iso_err=max(iso_err,np.abs(disp[2*k:2*k+2]-e).max())
        core_cost=sum(np.sum(np.exp(np.abs(disp[2*k:2*k+2]))-1) for k in range(n) if ((k<8 and -1<=k-3<=2) or (k>=8 and -2<=(k-8)-4<=2)))
        coreB=sum(Bd(sw[k][2]) for k in range(n) if ((k<8 and -1<=k-3<=2) or (k>=8 and -2<=(k-8)-4<=2)))
        roles={}
        for k in range(n):
            if k<8 and -1<=k-3<=2: roles[('U',k-3)]=disp[2*k:2*k+2].copy()
            if k>=8 and -2<=(k-8)-4<=2: roles[('V',(k-8)-4)]=disp[2*k:2*k+2].copy()
        lib[(u0,vb)]=dict(roles=roles,X=core_cost-coreB,iso_err=iso_err,total_excess=c-sum(Bd(s[2]) for s in sw))
    return lib
def local_kink():
    sw=[(3,-3,4),(0,0,4),(-3.75,3.75,4),(-6.75,6.75,4)]
    swl=gluelib.rule_levels(sw,[])
    A,Y,conf,ks=gluelib.setup(swl); lib={}
    for c in (0,1):
        sig=[c^1,c,c,c^1]
        u,cost,nv=gluelib.glue(A,conf,ks,sig); assert nv==0
        disp=u-A
        iso_err=0.0
        for k in (0,3):
            e=np.zeros((2,2)); e[0,sig[k]]=-4*H/2; e[1,sig[k]]=4*H/2; iso_err=max(iso_err,np.abs(disp[2*k:2*k+2]-e).max())
        lib[c]=dict(mid=disp[2:6].copy(),J=cost-sum(Bd(4) for _ in sw),iso_err=iso_err)
    return lib
def library():
    if os.path.exists(LIB): return pickle.load(open(LIB,"rb"))
    lib=dict(core=local_core(),kink=local_kink()); pickle.dump(lib,open(LIB,"wb")); return lib
def point_arrays(L):
    T=2*len(L.sw); A=np.zeros((T,2)); d_=np.zeros(len(L.sw))
    for i,(bx,by,d) in enumerate(L.sw):
        A[2*i]=(float(bx+d)*H,float(by+d)*H); A[2*i+1]=(float(bx)*H,float(by)*H); d_[i]=d
    return A,d_
def assemble(L,sig,active,lib,A,dsz):
    n=len(L.sw); D=np.zeros((2*n,2))
    for i in range(n):
        s=sig[i]; D[2*i,s]=-dsz[i]*H/2; D[2*i+1,s]=dsz[i]*H/2
    # crossing cores
    for cr in L.crossings:
        u0=sig[cr['uidx'][1]]; vb=sig[cr['vidx']]
        R=lib['core'][(u0,vb)]['roles']
        for mm,idx in zip((-1,0,1,2),cr['uidx']): D[2*idx:2*idx+2]=R[('U',mm)]
        for dj,idx in zip(range(-2,3),cr['vcore']): D[2*idx:2*idx+2]=R[('V',dj)]
    # kinks
    for e,(a,b,u) in L.kink.items():
        if active.get(e):
            c=sig[a]; assert sig[b]==c
            D[2*a:2*a+4]=lib['kink'][c]['mid']
    return D
def check(A,D,Y,tol=1e-7,chunk=400):
    Q=A+D; T=len(Y); viol=0; minsl=1e9; worst=[]
    n_conf=0
    for a0 in range(0,T,chunk):
        a1=min(T,a0+chunk)
        d0=Q[None,:,0]-Q[a0:a1,None,0]      # Q_b - Q_a  (coordinate 0): need >=0
        d1=Q[None,:,1]-Q[a0:a1,None,1]
        sl=np.maximum(d0,d1)
        mask=Y[a0:a1,None]>Y[None,:]
        # exclude identical-index
        for r in range(a1-a0): mask[r,a0+r]=False
        m=np.where(mask,sl,np.inf)
        n_conf+=int(mask.sum())
        mv=float(m.min()); 
        if mv<minsl: minsl=mv
        bad=np.argwhere(m<-tol)
        viol+=len(bad)
        for r,b in bad[:5]: worst.append((a0+int(r),int(b),float(m[r,b])))
    return dict(n_conf=n_conf,violations=viol,min_slack=minsl,worst=worst[:10])
def cost(D): return float(np.sum(np.exp(np.abs(D))-1))
