"""concave_pair.py -- exact U-pair value for a nonconvex cost phi(|r|) nondecreasing, concave on [0,inf) (e.g. |r|^q, q<1) by vertex enumeration:
an optimum has every x_{t,c} in {a_{s,c}} (vertex of the piecewise-concave problem).  Compares the pair value with 2B, B = phi(delta)."""
import itertools, math, sys
import numpy as np
h = 1.0
def pair_value(phi, a, d=4):
    # points: t0,b0,t1,b1 ; U(0,0): b0=(0,0), t0=(d,d); U(a,-a): b1=(a,-a), t1=(a+d,-a+d)
    A = np.array([[d, d], [0, 0], [a + d, -a + d], [a, -a]], float) * h
    conf = [(0, 1), (0, 3), (2, 1), (2, 3)]
    best = (1e18, None); allopt = []
    cand = [A[:, c] for c in (0, 1)]
    vals = []
    for ix in itertools.product(range(4), repeat=4):
        for iy in itertools.product(range(4), repeat=4):
            X = np.array([[cand[0][ix[t]], cand[1][iy[t]]] for t in range(4)])
            ok = all(X[a_, 0] <= X[b_, 0] + 1e-12 or X[a_, 1] <= X[b_, 1] + 1e-12 for a_, b_ in conf)
            if ok:
                cost = float(np.sum(phi(np.abs(X - A))))
                vals.append((cost, ix, iy))
    vals.sort(key=lambda v: v[0])
    return vals
if __name__ == '__main__':
    for q in (0.5, 0.75):
        phi = lambda r, q=q: r ** q
        B = phi(4 * h)
        for a in (3.0, 3.75):
            v = pair_value(phi, a)
            m = v[0][0]
            opt = [x for x in v if x[0] < m + 1e-9]
            print("q=%.2f a=%.2f: pair min %.6f ; 2B(isolated, one point moves delta) = %.6f ; 2*2phi(delta/2) (convex-style) = %.6f ; #optimal vertices %d" % (q, a, m, 2 * B, 4 * phi(2 * h), len(opt)))
            for c, ix, iy in opt[:6]: print("    cost %.6f x-index %s y-index %s" % (c, ix, iy))
