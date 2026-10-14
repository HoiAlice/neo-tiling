"""Compatibility of a global trend eta=-c*(x+y) (log coords, x+y of the point) with the required order/ties of Y."""
import numpy as np, sys
def name(q): return ("s%d"%(q//2))+("t" if q%2==0 else "b")
for f in ["cprime_yfound.npz","ws_k3.npz"]:
    d=np.load(f); Y=d['Y']; A=np.log(d['Qs'][0]) if False else None
    A=np.load("cprime_Q_1010.npz")['A'] if f.startswith("cprime") else d['A']
    s=A.sum(1); n=len(Y)
    # point-level violations: y_a>y_b required but s_a > s_b (trend says a lower)
    worst=[];ties=[]
    for a in range(n):
        for b in range(n):
            if Y[a]>Y[b]+1e-9 and s[a]>s[b]: worst.append((s[a]-s[b],a,b))
            if a<b and abs(Y[a]-Y[b])<1e-9: ties.append((abs(s[a]-s[b]),a,b))
    worst.sort(reverse=True); ties.sort(reverse=True)
    print(f,"points",n,"order-violating pairs (y_a>y_b but x+y larger)",len(worst),"of",sum(1 for a in range(n) for b in range(n) if Y[a]>Y[b]+1e-9))
    print("  worst:",[(round(w,2),name(a),name(b),Y[a],Y[b]) for w,a,b in worst[:5]])
    print("  tie classes with spread in x+y: max",round(ties[0][0],2),name(ties[0][1]),name(ties[0][2]),"; ties with spread>0.01:",sum(1 for t in ties if t[0]>0.01),"of",len(ties))
    # switch-level (centre) trend
    c=(s[0::2]+s[1::2])/2; ysw=(Y[0::2]+Y[1::2])/2
    v=[(c[a]-c[b],a,b) for a in range(len(c)) for b in range(len(c)) if ysw[a]>ysw[b]+1e-9 and c[a]>c[b]]
    print("  switch-level violations",len(v),"worst",sorted(v,reverse=True)[:3])
