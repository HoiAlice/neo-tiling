"""Exact two-phase simplex (Fractions, Bland): min c.m s.t. sum m_k cols_k = y, m >= 0."""
from fractions import Fraction as Fr
def exact_lp(cols,y,c=None):
    n=len(y); K=len(cols); c=[Fr(1)]*K if c is None else [Fr(v) for v in c]
    T=[[Fr(cols[k][q]) for k in range(K)]+[Fr(1) if i==q else Fr(0) for i in range(n)]+[Fr(y[q])] for q in range(n)]
    for q in range(n):
        if T[q][-1]<0: T[q]=[-v for v in T[q]]
        T[q][K+q]=Fr(1)
    basis=[K+q for q in range(n)]
    def run(cost,allowed):
        while True:
            ent=next((j for j in allowed if cost[j]<0),None)
            if ent is None: return True
            rows=[(T[q][-1]/T[q][ent],basis[q],q) for q in range(n) if T[q][ent]>0]
            if not rows: return False
            r=min(rows)[2]; piv=T[r][ent]; T[r]=[v/piv for v in T[r]]
            for q in range(n):
                if q!=r and T[q][ent]!=0:
                    f=T[q][ent]; T[q]=[a-f*b for a,b in zip(T[q],T[r])]
            f=cost[ent]
            for j in range(len(cost)): cost[j]-=f*T[r][j]
            basis[r]=ent
    cost=[Fr(0)]*(K+n+1)
    for q in range(n): cost=[a-b for a,b in zip(cost,T[q])]
    for q in range(n): cost[K+q]=Fr(0)
    run(cost,range(K+n))
    if cost[-1]!=0: return None
    # phase 2
    cost=[c[j] if j<K else Fr(0) for j in range(K)]+[Fr(0)]*(n+1)
    for q in range(n):
        b=basis[q]
        if b<K and cost[b]!=0:
            f=cost[b]; cost=[a-f*v for a,v in zip(cost,T[q])]
    run(cost,range(K))
    sol=[(basis[q],T[q][-1]) for q in range(n) if basis[q]<K and T[q][-1]!=0]
    return sol
