import sys, itertools, numpy as np
from gluelib import *
def build(nstars=3,spacing=12,armlinks=6):
    sw=[]; chains={}
    kmin=-5; kmax=spacing*(nstars-1)+5
    bus=[]
    for k in range(kmin,kmax+1):
        bus.append(len(sw)); sw.append((k-0.5,k-0.5,5))
    chains["bus"]=(bus,'eq')
    for r in range(nstars):
        k=r*spacing; cx,cy=k-0.5,k-0.5
        arm=[]
        ax,ay=cx-2.5,cy+3.5          # first arm switch bottom (NW of star centre)
        for i in range(armlinks):
            arm.append(len(sw)); sw.append((ax-3*i,ay+3*i,4))
        chains["arm%d"%r]=(arm,'arm',bus[k-kmin])
    return sw,chains
def bitsof(chains,n,b):
    sig=[None]*n
    for name,ch in chains.items():
        if ch[1]=='eq':
            for s in ch[0]: sig[s]=b
        else:
            for i,s in enumerate(ch[0]): sig[s]=b^1^(i%2)
    return sig
if __name__=="__main__":
    ns=int(sys.argv[1]) if len(sys.argv)>1 else 3
    sw,chains=build(ns)
    # crossing kinks: none (arms/bus: no crossing)
    swl=rule_levels(sw,[])
    A,Y,conf,ks=setup(swl); n=len(sw)
    print("stars",ns,"switches",n,"conflicts",len(conf),flush=True)
    sumB=sum(B(d) for (_,_,d) in sw)
    for b in (0,1):
        sig=bitsof(chains,n,b); u,c,nv=glue(A,conf,ks,sig)
        Q=np.exp(snap(u,1e-5)); print("bus bit",b,"cost-sumB %.3e"%(c-sumB),"violations",nv,"weakly solvable (rule, no kinks):",weak(Q,Y),flush=True)
