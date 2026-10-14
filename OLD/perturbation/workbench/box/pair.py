import numpy as np
def rho_pair(a,y):
    a=np.asarray(a,float);T=len(a);best=0.0
    for p in range(T):
        for q in range(T):
            if y[p]>y[q]:
                best=max(best,min(a[p,0]-a[q,0],a[p,1]-a[q,1])/2)
    return best
