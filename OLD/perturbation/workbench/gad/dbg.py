import numpy as np, itertools
exec(open('ls4.py').read().split("grid=np.array")[0])
combo=sols[0]; print(combo)
inc=np.zeros((6,4))
for e,c in enumerate(combo): inc[e,c[2]]+=1; inc[e,c[1]]-=1
u_,s_,vt=np.linalg.svd(inc.T); print("sv",np.round(s_,3)); rank=np.sum(s_>1e-9); cyc=vt[rank:]; print(np.round(cyc,3))
print([sgn_s(c) for c in combo])
from collections import Counter
print(Counter(sum(1 for c in cm if c[0]=="pure") for cm in sols))
