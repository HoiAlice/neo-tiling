"""np_half.py -- interval-certified credit tables for windows containing a 0.5 V link (parity flip next to a corner).
Levels: bottom = 1 - 0.02*(s_c - 4), top = bottom + 0.01 (order-equivalent to the final rule: strictly decreasing in s_c, step >= 0.02 > g).
T1 corner: K=(0,0), arm along (+1,-1), V chain NE: V0 at K, V1 at K+(.5,.5), V2 at K+(1.5,1.5), ...
T4 corner (second corner of a track, reflected type, V0' shares the TOP corner of u0'): u0'=(0,0), arm along (+1,-1), V0' bottom (-1,-1), V1' (-1.5,-1.5), V2' (-2.5,-2.5), ..."""
import itertools, math, sys
from np_dual import *
from np_chain import run, JE
g=0.01
def lv(sc): return 1.0-0.02*(sc-4)
def sw(bx,by,d):
    b=lv(bx+by+d); return (float(bx),float(by),d,b+g,b)
def T1(kind):
    u={"u0":(0,0,4),"u1":(3,-3,4),"u2":(6,-6,4)}
    v={"V0":(0,0,5),"V1":(0.5,0.5,5),"V2":(1.5,1.5,5),"V3":(2.5,2.5,5)}
    return {**u,**v}
def T4():
    u={"u0":(0,0,4),"u1":(3,-3,4),"u2":(6,-6,4)}
    v={"V0":(-1,-1,5),"V1":(-1.5,-1.5,5),"V2":(-2.5,-2.5,5),"V3":(-3.5,-3.5,5)}
    return {**u,**v}
E,N='eq','ne'
def win(P,names,kinds,credits,label):
    sws=[sw(*P[n]) for n in names]
    return run(label,sws,kinds,credits)
if __name__=="__main__":
    out=[]
    for tag,P in (("T1",T1(None)),("T4",T4())):
        out.append(win(P,["V0","V1"],[E],[2],tag+" V pair V0-V1 (0.5 link)"))
        out.append(win(P,["V1","V2"],[E],[2],tag+" V pair V1-V2 (after the 0.5 link)"))
        out.append(win(P,["V0","V1","V2"],[E,E],[2,2],tag+" V triple V0,V1,V2"))
        out.append(win(P,["V0","V1","V2","V3"],[E,E,E],[2,2,2],tag+" V 4-chain V0..V3"))
        out.append(win(P,["V0","u0"],[E],[2],tag+" corner pair V0,u0"))
        out.append(win(P,["V1","V0","u0"],[E,E],[2,2],tag+" corner triple V1,V0,u0"))
        out.append(win(P,["V1","V0","u0","u1"],[E,E,N],[2,2,2],tag+" corner 4: V1,V0,u0,u1"))
        out.append(win(P,["V2","V1","V0","u0"],[E,E,E],[2,2,2],tag+" corner 4: V2,V1,V0,u0"))
        out.append(win(P,["V0","u0","u1","u2"],[E,N,N],[2,2,2],tag+" corner 4: V0,u0,u1,u2"))
    print("MIN margin over all windows (units of y... absolute cost):",min(out),"  J_e =",JE,flush=True)
