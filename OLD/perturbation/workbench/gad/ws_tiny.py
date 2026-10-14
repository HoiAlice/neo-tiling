import sys; sys.path.insert(0,".")
import numpy as np
from core import weakly_solvable
d=np.load(sys.argv[1]); Qs=d['Qs']; Y=d['Y']
lv=sorted(set(np.round(Y,9))); rank=np.array([lv.index(round(v,9)) for v in Y])
print("levels",len(lv))
for name,eta in [("rank",rank.astype(float)),("handset",(Y-Y.min())/ (lv[1]-lv[0]) )]:
    for eps in [1e-1,1e-2,1e-3,1e-4,1e-5]:
        y=1+eps*eta/ (eta.max())
        print(name,eps,[weakly_solvable(Q,y) for Q in Qs],flush=True)
