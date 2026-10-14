import numpy as np, cx2, itertools
from loc3 import fixed_cost, B, J, chain
def block_min(sw,sg,w):
    A,Y,conf,ks=cx2.setup(sw); best=1e9
    free=[k for k in range(len(conf)) if k not in ks]
    for ch in itertools.product((0,1),repeat=len(free)):
        coord=[0]*len(conf)
        for k,s in zip(ks,sg): coord[k]=s
        for k,c in zip(free,ch): coord[k]=c
        best=min(best,fixed_cost(A,conf,coord,w=np.repeat(w,2)))
    return best
# P3 with bits 000: blocks {0,1} weights (1,.5), {1,2} weights (.5,1)
sw=chain(2)
m1=block_min(sw,(0,0),np.array([1,.5])); m2=block_min(sw,(0,0),np.array([.5,1]))
print("weighted blocks sum",m1+m2,"vs true 3B+2J",3*B+2*J,"vs 3B+J",3*B+J, "3B", 3*B)
