import sys, time, pickle, numpy as np, itertools
from multiprocessing import Pool
from k4weak import *
import planar
from fractions import Fraction
def Qof(pat):
    u,c=glue_Q(pat); return np.exp(snap(u,1e-5))
def check(args):
    pat,y=args
    Q=Qof(pat); Pf=[tuple(Fraction(float(v)).limit_denominator(10**9) for v in row) for row in Q]
    yf=[Fraction(float(v)).limit_denominator(10**9) for v in y]
    return pat,planar.flow_lp(Pf,yf).feasible
if __name__=="__main__":
    init(); t0=time.time()
    pat0=(0,0,1,1); Q0=Qof(pat0)
    y=find_y([Q0],G["Y"],1e-6,100)
    print("single-pattern y-LP feasible:",y is not None,"time",round(time.time()-t0),flush=True)
    if y is not None:
        np.save("k4_y_0011.npy",y); print("max/min",y.max()/y.min(),flush=True)
        pats=[p for p in itertools.product((0,1),repeat=4) if sum(p)==2]
        with Pool(5,initializer=init) as p:
            for r in p.imap_unordered(check,[(q,y) for q in pats]): print(r,"time",round(time.time()-t0),flush=True)
