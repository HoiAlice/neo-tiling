import sys, itertools, numpy as np
from multiprocessing import Pool
from edge import g
import cx2
from core import solve_dom
from loc8 import build_inst
from loc7 import sat_value, milp_credit
aW=3.75; Je=2*(np.exp((4-aW)*0.2/2)-1); c2=2*Je
h0,h2=0.02,0.04
def star(a=3.0,with_nbrs=True):
    sw=[(-2.5,-2.5,5,1+g,1.0)]                        # 0 centre (box centre (0,0))
    for sgn in (-1,1):                                # 1 NW, 2 SE attachments d=4 centres (sgn*a, -sgn*a)
        c=(sgn*a,-sgn*a); sw.append((c[0]-2,c[1]-2,4,1+g,1.0))
    sw.append((-1-2.5,-1-2.5,5,1+g+h0,1+h0))          # 3 SW
    sw.append((1-2.5,1-2.5,5,1+g-h2,1-h2))            # 4 NE
    if with_nbrs:
        for sgn in (-1,1):                            # 5 NW2, 6 SE2
            c=(2*sgn*a,-2*sgn*a); sw.append((c[0]-2,c[1]-2,4,1+g,1.0))
        sw.append((-2-2.5,-2-2.5,5,1+g+2*h0,1+2*h0))  # 7 SW2
        sw.append((2-2.5,2-2.5,5,1+g-2*h2,1-2*h2))    # 8 NE2
    return sw
# NOTE geometry: NW has sgn=-1 -> centre (-a,+a)
def star_rels(nb):
    r=[(0,3,'eq',Je),(0,4,'eq',Je),(0,1,'ne',Je),(0,2,'ne',Je)]
    if nb: r+=[(1,5,'ne',c2),(2,6,'ne',c2),(3,7,'eq',c2),(4,8,'eq',c2)]
    return r
def job(j):
    name,sw,rel=j
    S=sat_value(sw,rel,900); C=milp_credit(sw,rel,900); return name,S,C
def term_job(sg):
    sw,idx=G
    A,Y,conf,ks=cx2.setup(sw)
    r=solve_dom(A,Y,fixed=dict(zip([ks[i] for i in idx],sg)),conflicts=conf,time_limit=300)
    return sg,r[2]
G=None
def _init(b,i):
    global G
    G=(b,i)
if __name__=="__main__":
    which=sys.argv[1]
    if which=="star":
        jobs=[("star5",star(3.0,False),star_rels(False)),("star9",star(3.0,True),star_rels(True))]
        with Pool(2) as p: out=p.map(job,jobs)
        for n,S,C in out: print(n,"S=%.6f cert=%.6f margin=%.2e"%(S[0],C[0],C[0]-S[0]),S[2],C[2],flush=True)
    if which=="cross":
        sw=build_inst(aW); K=[2,3,4,5,6,19,20,21,22]; blk=[sw[i] for i in K]
        idx=[0,4,5,8]   # V_in=2, V_out=6, U_in=19, U_out=22 -> local indices
        G=(blk,idx)
        with Pool(8,initializer=_init,initargs=(blk,idx)) as p: res=dict(p.map(term_job,list(itertools.product((0,1),repeat=4))))
        mn=min(res.values())
        print("terminals (V_in,V_out,U_in,U_out); excess over min %.6f"%mn)
        for s,v in sorted(res.items()): print(s,round(v-mn,5),"Vbreak",int(s[0]!=s[1]),"Ubreak",int(s[2]==s[3]))
