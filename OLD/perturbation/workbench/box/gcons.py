"""Constructive: antitone Lipschitz g, IVT points on box diagonals. Returns u or None."""
import numpy as np
def g_construct(a,y,r,L=None):
    a=np.asarray(a,float);y=np.asarray(y,float);T=len(a)
    SW=a-r
    if L is None: L=1e6
    def g(z): return max(y[s]-L*max(0.0,(z-SW[s]).max()) for s in range(T))
    u=np.zeros((T,2))
    for t in range(T):
        lo,hi=0.0,1.0   # parameter along diagonal SW_t -> NE_t
        pt=lambda s: SW[t]+s*2*r*np.ones(2)
        if g(pt(0))<y[t]-1e-12 or g(pt(1))>y[t]+1e-12: return None
        for _ in range(200):
            m=(lo+hi)/2
            if g(pt(m))>=y[t]: lo=m
            else: hi=m
        # g nonincreasing: take s where g crosses y_t; use lo (g>=y)
        u[t]=pt(lo)
    return u
def dom_ok(u,y,tol=1e-9):
    T=len(u)
    for p in range(T):
        for q in range(T):
            if y[p]>y[q] and (u[p]<=u[q]+tol).sum()==0: return False
    return True
if __name__=="__main__":
    a=np.array([[3,2],[3,2],[2,3],[0,3],[1,3],[3,0],[1,1]],float);y=np.array([2,2,1,0,2,2,1],float)
    for r in [0.5,0.51,0.6,1.0]:
        u=g_construct(a,y,r); print(r,None if u is None else dom_ok(u,y))
        if u is not None and r==0.6: print(u)
