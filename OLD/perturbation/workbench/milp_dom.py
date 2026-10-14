import numpy as np, itertools
from pyscipopt import Model, quicksum
def rho_dom_L1(U, y, w=None, M=50.0):
    """U: log-coordinates (T,2); y levels; weights w; cost sum w*|du|. dominance relaxation (weak ties allowed)."""
    T=len(U); w=np.ones(T) if w is None else w
    m=Model(); m.hideOutput()
    u={(t,c):m.addVar(lb=-M,ub=M) for t in range(T) for c in range(2)}
    d={(t,c):m.addVar(lb=0) for t in range(T) for c in range(2)}
    for t in range(T):
        for c in range(2):
            m.addCons(d[t,c]>=u[t,c]-U[t,c]); m.addCons(d[t,c]>=U[t,c]-u[t,c])
    for t in range(T):
        for s in range(T):
            if y[t]>y[s]:
                sg=[m.addVar(vtype='B') for c in range(2)]
                m.addCons(sg[0]+sg[1]>=1)
                for c in range(2):
                    m.addCons(u[t,c]<=u[s,c]+2*M*(1-sg[c]))
    m.setObjective(quicksum(w[t]*d[t,c] for t in range(T) for c in range(2)))
    m.optimize()
    return m.getObjVal(), np.array([[m.getVal(u[t,c]) for c in range(2)] for t in range(T)])
def build(n, edges, K=10.0):
    # variables 0..n-1 level 1..n ; anchors n..2n-1 level 0 at v-(1,1)
    pos=np.zeros((2*n,2)); return None
if __name__=="__main__":
    # path v1<v2<v3, positions (0,0),(1,1),(2,2)?? edges only unit offsets -> (v3,v1) offset 2 also conflict
    def inst(V, K=10.0):
        n=len(V); U=[];y=[];w=[]
        for i,v in enumerate(V): U.append(v); y.append(10+i); w.append(1.0)
        for i,v in enumerate(V): U.append((v[0]-1,v[1]-1)); y.append(0); w.append(K)
        return np.array(U,float),np.array(y,float),np.array(w)
    # path-like: v1=(0,0), v2=(1,1) edge; v3 incomparable to v1 (far x below): v3=(1.0-3, 2)?? 
    for name,V in [("single",[(0,0)]),("edge",[(0,0),(1,1)]),
                   ("path3 (v3~v2 only)",[(0,0),(1,1),(-5,2)]),
                   ("chain3 triangle",[(0,0),(1,1),(2,2)]),
                   ("triangle unit",[(0,0),(1,1),(1.0,1.0)])]:
        U,y,w=inst(V); print(name, round(rho_dom_L1(U,y,w)[0],4))
