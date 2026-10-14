from k3 import *
import term, snapw
def build_relay_cp(n=4,armsteps=(3,3,3,3),sw_weak=(3,3.75,3)):
    P=sum(armsteps); K=(0.0,0.0)
    e,Bv,Av=corner_edge(K,(1,-1),n,armsteps,B0)
    sw=list(e)
    iu=len(sw); sw.append(vertex_sw(Bv[0],Bv[1],B0-SV*(n+1)))     # V-end vertex u
    ir=len(sw); sw.append(vertex_sw(Av[0],Av[1],B0))                # relay at arm end
    # pure U wire from relay centre along (1,-1)
    rc=(Av[0]+2.5,Av[1]+2.5); p=0
    for st in sw_weak[:-1]:
        p+=st; c=(rc[0]+p,rc[1]-p); sw.append((c[0]-2,c[1]-2,4)+lev(B0))
    p+=sw_weak[-1]; c=(rc[0]+p,rc[1]-p)
    iv=len(sw); sw.append(vertex_sw(c[0]-2.5,c[1]-2.5,B0))
    return sw,[iu,iv]
if __name__=="__main__":
    sw,idx=build_relay_cp()
    for i,s in enumerate(sw): print(i,tuple(round(float(x),3) for x in s))
    tb=term.term_table(sw,idx,procs=4); mn=min(tb.values())
    print({k:round(v-mn,5) for k,v in sorted(tb.items())},flush=True)
    sat=[k for k in tb if tb[k]-mn<0.02]
    print(sat, snapw.snapped_solv(sw,idx,sat)[0],flush=True)
