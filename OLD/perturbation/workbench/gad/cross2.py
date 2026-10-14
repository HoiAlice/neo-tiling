import sys, itertools, numpy as np
from gluelib import *
def build(T,nUside=2):
    """U wire along NW (bottoms (3t',-3t')+(0,0)), switches t' with t-coordinate (y-x)=6 t'; V tracks at t=0 and t=T."""
    sw=[]; chains={}
    # U wire: t'=tU/6 ; switch bottoms (x,-x) with y-x = 2*(-x)... use bottoms (3k,-3k): t=-6k ; crossing midpoints at t=0 and t=T (T multiple of 6)
    # switches at t = -6k : we need switches at t=-3+... use half-integer k: bottoms (3k,-3k) k=m+0.5 -> t=-6m-3
    ks=[]
    mlo=-int(np.ceil(T/6))-nUside-2; mhi=nUside+2
    U=[]
    for m in range(mlo,mhi+1):
        k=m+0.5; U.append((3*k,-3*k,4)); 
    Uidx=list(range(len(sw),len(sw)+len(U))); sw+=U
    chains["U"]=(Uidx,'ne')
    # V track at t=0 : bottoms (k-0.5,k-0.5), k=-4..4 ; V track at t=T : bottoms (k-0.5-T/2,k-0.5+T/2)
    def track(Tt):
        idx=[]
        for k in range(-4,5):
            idx.append(len(sw)); sw.append((k-0.5-Tt/2,k-0.5+Tt/2,5))
        return idx
    v0=track(0.0); chains["V0"]=(v0,'eq')
    vT=track(float(T)); chains["VT"]=(vT,'eq')
    return sw,chains
def bits(chains,n,pat):
    sig=[None]*n
    for name,(idx,kind) in chains.items():
        b=pat[name]
        for i,s in enumerate(idx):
            sig[s]=b if kind=='eq' else b^(i%2)
    return sig
if __name__=="__main__":
    T=int(sys.argv[1]) if len(sys.argv)>1 else 36
    sw,chains=build(T)
    kinks=[4.0]
    swl=rule_levels(sw,kinks)
    A,Y,conf,ks=setup(swl); n=len(sw)
    print("T",T,"switches",n,"conflicts",len(conf),flush=True)
    sumB=sum(B(d) for (_,_,d) in sw)
    res={}
    for bu,b0,bt in itertools.product((0,1),repeat=3):
        pat={"U":bu,"V0":b0,"VT":bt}
        sig=bits(chains,n,pat); u,c,nv=glue(A,conf,ks,sig)
        Q=np.exp(snap(u,1e-5)); w=weak(Q,Y)
        res[(bu,b0,bt)]=(c-sumB,nv,w); print((bu,b0,bt),"cost-sumB %.6f"%(c-sumB),"violations",nv,"weakly solvable (final rule)",w,flush=True)
