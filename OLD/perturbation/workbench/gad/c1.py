from bias import *
from multiprocessing import Pool
def job(a):
    name,sw,pairs=a; n=len(sw); tb=table(sw)
    c,e=fit(tb,n,pairs); return name,n,pairs,c,e,tb
if __name__=="__main__":
    G=(6,6);Gb=(6,7);Gc=(7,6)
    J=[]
    # (1) ferro NE triples, d=6, small steps, plus AF-path ferro
    for st in [(1,1),(2,2),(4,4),(7,7)]:
        sw=[(st[0]*i,st[1]*i)+G for i in range(3)]
        J.append((f"ferro NE step{st} n=3 gaps(6,6)",sw,None))
    J.append(("ferro via AF 2-path: (0,0),(-3,3),(-6,6) gap(6,6)",[(0,0)+G,(-3,3)+G,(-6,6)+G],None))
    J.append(("ferro via AF 2-path gap(4,4) offsets(-3,3)",[(0,0,4,4),(-3,3,4,4),(-6,6,4,4)],[(0,1),(1,2)]))
    # (2) mixed: one ferro pair + one AF pair
    J.append(("mixed: S0(0,0), S1(2,2) ferro, S2(-3,3) AF to S0, gap(6,6)",[(0,0)+G,(2,2)+G,(-3,3)+G],None))
    J.append(("mixed: S0(0,0), S1(4,4), S2(-3,3)",[(0,0)+G,(4,4)+G,(-3,3)+G],None))
    J.append(("mixed: S0(0,0), S1(2,2), S2(5,-3)",[(0,0)+G,(2,2)+G,(5,-3)+G],None))
    # (3) 4 switches: AF triangle + pendant (biased / not)
    tri=[(0,0)+G,(-2,3)+G,(-5,5)+G]
    for p4 in [(3,-3),(2,-4),(-7,7),(-8,8)]:
        for g in [G,Gb,Gc]:
            J.append((f"tri+pendant {p4} gap{g}",tri+[p4+g],None))
    with Pool(8) as p:
        for name,n,pairs,c,e,tb in p.map(job,J):
            np_=len(pairs) if pairs else n*(n-1)//2
            print(name,"\n   E0=%.4f h=%s J=%s resid=%.2e"%(c[0],np.round(c[1:1+n],4),np.round(c[1+n:],4),e))
