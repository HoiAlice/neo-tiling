import sys; sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction
def fr(Q): return [tuple(Fraction(float(v)).limit_denominator(10**9) for v in r) for r in Q]
def decomp(Q,y):
    """approximate decomposition y ~ sum m_S 1_S from the flow LP (float), S reachable candidates from flow paths (+boundary shares)"""
    P=fr(Q); yf=[Fraction(float(v)).limit_denominator(10**9) for v in y]
    G=planar.chain_graph(P); lp=planar.flow_lp(P,yf,False,G)
    if not lp.feasible: return None
    out=[]
    for m,path in planar.decompose_flow(G,lp.f):
        S=frozenset().union(*(G.arcs[k][2] for k in path)); B=frozenset().union(*(G.arcs[k][3] for k in path))
        out.append((float(m),S,B))
    return out,lp
def name(q): return ("s%d"%(q//2))+("t" if q%2==0 else "b")
if __name__=="__main__":
    d=np.load(sys.argv[1]); k=int(sys.argv[2]); y=d['y']; Q=d['Qs'][k]
    r=decomp(Q,y); print("feasible",r is not None)
    if r:
        out,lp=r; print("paths",len(out))
        for m,S,B in sorted(out,key=lambda x:-x[0]): print(round(m,5),"out",len(S),"bnd",len(B)," ".join(name(q) for q in sorted(S)))
