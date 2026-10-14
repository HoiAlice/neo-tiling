import sys, time, numpy as np
from k4weak import *
if __name__=="__main__":
    init(); pat=(0,0,1,1)
    u,c=glue_Q(pat); Q=np.exp(snap(u,1e-5)); Y=G["Y"]
    import planar
    from fractions import Fraction
    t0=time.time()
    Pf=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]
    g=planar.chain_graph(Pf); print("arcs",len(g.arcs),"nodes",len(g.nodes),"build s",round(time.time()-t0),flush=True)
    yf=[Fraction(float(v)).limit_denominator(10**9) for v in Y]
    r=planar.flow_lp(Pf,yf,graph=g); print("weak solvable at generator y:",r.feasible,"time",round(time.time()-t0),flush=True)
