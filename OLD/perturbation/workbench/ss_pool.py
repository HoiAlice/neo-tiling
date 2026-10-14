# Pooled-block model: points with log-displacement targets a_i must be pooled into one of two hubs
# (x-block or y-block); block cost = min_m sum (e^{|a_i-m|}-1)   (isotonic/pooling optimum in exp metric).
import itertools, numpy as np
from scipy.optimize import minimize_scalar
def blk(v):
    if not v: return 0.0
    r=minimize_scalar(lambda m: sum(np.exp(abs(a-m))-1 for a in v),bounds=(min(v),max(v)),method='bounded',options={'xatol':1e-12})
    return r.fun
for a in [(0.1,0.2,0.3,0.4),(0.1,0.2,0.3,0.6),(0.05,0.1,0.15,0.2,0.25,0.35)]:
    n=len(a); res=[]
    for mask in range(2**n):
        J=[a[i] for i in range(n) if mask>>i&1]; K=[a[i] for i in range(n) if not mask>>i&1]
        res.append((blk(J)+blk(K),sum(J),sum(K),tuple(J)))
    res.sort()
    print("a=",a,"total",round(sum(a),3))
    for r in res[:3]+res[-2:]: print("  cost %.5f  sumJ %.3f sumK %.3f J=%s"%r)
