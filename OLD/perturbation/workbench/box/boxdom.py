"""BOXdom in closed form.  a = log-coordinates (T x 2), y levels.
d(s,t) = min_i (a[s,i]-a[t,i]).   BOXdom(a,y,r) <=> d(s,t) <= 2r for all y_s>y_t.
Canonical witness: u_t = a_t - r + tau_t*(1,1),  tau_t = clip(max_{s: y_s>y_t} d(s,t), 0, 2r)."""
import numpy as np
def dmat(a):
    return np.minimum(a[:,None,0]-a[None,:,0], a[:,None,1]-a[None,:,1])
def rho_dom(a,y):
    a=np.asarray(a,float);y=np.asarray(y,float);D=dmat(a); H=y[:,None]>y[None,:]
    return max(0.0,(D[H].max()/2) if H.any() else 0.0)
def canonical(a,y,r):
    a=np.asarray(a,float);y=np.asarray(y,float);D=dmat(a); H=y[:,None]>y[None,:]
    tau=np.zeros(len(a))
    for t in range(len(a)):
        m=H[:,t]
        if m.any(): tau[t]=min(2*r,max(0.0,D[m,t].max()))
    return a-r+tau[:,None]
def dom_free(u,y,tol=1e-9):
    T=len(u)
    return all((u[p]<=u[q]+tol).any() for p in range(T) for q in range(T) if y[p]>y[q])
