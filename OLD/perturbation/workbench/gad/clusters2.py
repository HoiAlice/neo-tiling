import sys, itertools, time, numpy as np
import qstar, gluelib
from qstar import Bd, H
def build_cross(centres):
    """V track bottoms (j-0.5,j-0.5), j in range; U wires crossing at V switches with index c in centres (c integer): U wire bottoms v_c+(2,-1)+m(-3,3), m=-3..4"""
    sw=[]; vidx={}
    jlo=min(centres)-4; jhi=max(centres)+4
    for j in range(jlo,jhi+1): vidx[j]=len(sw); sw.append((j-0.5,j-0.5,5))
    cr=[]
    for c in centres:
        vb=(c-0.5,c-0.5); ids={}
        for m in range(-3,5):
            ids[m]=len(sw); sw.append((vb[0]+2-3*m,vb[1]-1+3*m,4))
        cr.append(dict(c=c,u=ids,vc=[vidx[c+d] for d in range(-2,3)]))
    return sw,vidx,cr
def run(centres,name):
    sw,vidx,cr=build_cross(centres)
    sc_u=sorted({float(sw[c['u'][0]][0]+sw[c['u'][0]][1]+4) for c in cr})
    swl=gluelib.rule_levels(sw,sc_u)
    A,Y,conf,ks=gluelib.setup(swl); lib=qstar.library()
    A2=np.zeros((2*len(sw),2)); dsz=np.array([s[2] for s in sw],float)
    for i,(bx,by,d) in enumerate(sw): A2[2*i]=((bx+d)*H,(by+d)*H); A2[2*i+1]=(bx*H,by*H)
    print(name,"switches",len(sw),"conflicts",len(conf),"kink levels",sc_u,flush=True)
    for pat in itertools.product((0,1),repeat=1+len(centres)):
        vb=pat[0]; us=pat[1:]
        sig=[None]*len(sw)
        for j,i in vidx.items(): sig[i]=vb
        for c,u0 in zip(cr,us):
            for m,i in c['u'].items(): sig[i]=u0^(m%2)
        D=np.zeros((2*len(sw),2))
        for i in range(len(sw)):
            s=sig[i]; D[2*i,s]=-dsz[i]*H/2; D[2*i+1,s]=dsz[i]*H/2
        for c,u0 in zip(cr,us):
            R=lib['core'][(u0,vb)]['roles']
            for mm in (-1,0,1,2): D[2*c['u'][mm]:2*c['u'][mm]+2]=R[('U',mm)]
            for dj,i in zip(range(-2,3),c['vc']): D[2*i:2*i+2]=R[('V',dj)]
        chk=qstar.check(A2,D,Y); cost=qstar.cost(D)
        exp=sum(Bd(s[2]) for s in sw)+len(centres)*lib['core'][(0,0)]['X']
        Q=np.exp(gluelib.snap(A2+D,1e-5)); t0=time.time(); w=gluelib.weak(Q,Y)
        print(name,pat,"cost-closed %.1e"%(cost-exp),"violations",chk['violations'],"weakly solvable:",w,"(%ds)"%(time.time()-t0),flush=True)
if __name__=="__main__":
    which=sys.argv[1]
    if which=="C3": run([0],"C3 single crossing (4U x 9V + neighbours)")
    if which=="C5": run([0,12],"C5 V track crossed by two U wires at levels 24 apart")
    if which=="C6": run([0,6],"C6 V track crossed by two U wires at levels 12 apart")
