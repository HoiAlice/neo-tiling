"""Critical kappa values: where the combinatorial type of W_kappa (orders of coordinates, orientations of triples) changes."""
import itertools, numpy as np
from numpy.polynomial import polynomial as Pl
def critical_kappas(P):
    P=np.asarray(P,float);T=len(P);crit=set([1.0])
    for i in range(2):
        for s in range(T):
            for t in range(T):
                if s!=t:
                    k=np.sqrt(P[s,i]/P[t,i])   # P_s/k = P_t*k
                    if k>1: crit.add(float(k))
    # coordinate polynomials  kappa * coord : SW -> c ; NE -> c*kappa^2
    def X(pt,i):
        t,typ=pt; c=P[t,i]
        return np.array([c]) if typ==0 else np.array([0,0,c])
    pts=[(t,0) for t in range(T)]+[(t,1) for t in range(T)]
    for a,b,q in itertools.combinations(pts,3):
        xa,ya,xb,yb,xq,yq=X(a,0),X(a,1),X(b,0),X(b,1),X(q,0),X(q,1)
        poly=Pl.polysub(Pl.polymul(Pl.polysub(xb,xa),Pl.polysub(yq,ya)),Pl.polymul(Pl.polysub(yb,ya),Pl.polysub(xq,xa)))
        poly=np.trim_zeros(poly,'b')
        if len(poly)<=1: continue
        for z in np.roots(poly[::-1]):
            if abs(z.imag)<1e-9 and z.real>1: crit.add(float(z.real))
    return sorted(crit)
