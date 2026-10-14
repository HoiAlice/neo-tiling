"""Exact certificate, robust version of planar.certify: independent-support selection in rationals; verification by planar.is_reachable (exact) and exact sum."""
import sys; sys.path.insert(0,"/Users/olegoleg/Code/neo-tiling/poly-hardness")
import numpy as np, planar
from fractions import Fraction as Fr
from scipy.optimize import linprog
def Fq(x): return Fr(float(x))
def exact_simplex(cols,y):
    """Phase-1 simplex in exact rationals (Bland rule): find m>=0 with sum m_k cols_k = y."""
    n=len(y); K=len(cols)
    T=[[Fr(cols[k][q]) for k in range(K)]+[Fr(1) if i==q else Fr(0) for i in range(n)]+[Fr(y[q])] for q in range(n)]
    for q in range(n):
        if T[q][-1]<0: T[q]=[-v for v in T[q]]
        T[q][K+q]=Fr(1)
    basis=[K+q for q in range(n)]
    # objective: minimise sum of artificials -> reduced costs
    cost=[Fr(0)]*(K+n+1)
    for q in range(n): cost=[c-v for c,v in zip(cost,T[q])]
    for q in range(n): cost[K+q]=Fr(0)
    while True:
        ent=next((j for j in range(K+n) if cost[j]<0),None)
        if ent is None: break
        rows=[(T[q][-1]/T[q][ent],basis[q],q) for q in range(n) if T[q][ent]>0]
        if not rows: return None
        r=min(rows)[2]; piv=T[r][ent]; T[r]=[v/piv for v in T[r]]
        for q in range(n):
            if q!=r and T[q][ent]!=0:
                f=T[q][ent]; T[q]=[a-f*b for a,b in zip(T[q],T[r])]
        f=cost[ent]; cost=[a-f*b for a,b in zip(cost,T[r])]; basis[r]=ent
    if cost[-1]!=0: return None
    sol=[(basis[q],T[q][-1]) for q in range(n) if basis[q]<K and T[q][-1]!=0]
    return sol
def exact_solve(cols,y,minmass=False):
    if not minmass: return exact_simplex(cols,y)
    M=np.array(cols,float).T
    res=linprog(np.ones(len(cols)),A_eq=M,b_eq=[float(v) for v in y],bounds=[(0,None)]*len(cols),method="highs-ds")
    if res.status!=0: return None
    sup=[k for k in range(len(cols)) if res.x[k]>1e-12]
    sol=exact_simplex([cols[k] for k in sup],y)
    return None if sol is None else [(sup[k],m) for k,m in sol]
def exact_solve_old(cols,y):
    M=np.array(cols,float).T
    res=linprog(np.zeros(len(cols)),A_eq=M,b_eq=[float(v) for v in y],bounds=[(0,None)]*len(cols),method="highs-ds")
    if res.status!=0: return None
    sup=[k for k in range(len(cols)) if res.x[k]>1e-12]
    # exact independent subset of support columns (Gaussian elimination on column vectors)
    n=len(y); basis=[]; red=[]   # red: reduced vectors with pivot
    for k in sup:
        v=[Fr(c) for c in cols[k]]
        for (p,w) in red:
            if v[p]!=0:
                f=v[p]/w[p]; v=[a-f*b for a,b in zip(v,w)]
        p=next((i for i,a in enumerate(v) if a!=0),None)
        if p is not None: red.append((p,v)); basis.append(k)
    # solve B m = y exactly (least squares exact on independent columns)
    m_=len(basis); A=[[Fr(cols[k][q]) for k in basis] for q in range(n)]
    N=[[sum(A[q][i]*A[q][j] for q in range(n)) for j in range(m_)] for i in range(m_)]
    rhs=[sum(A[q][i]*y[q] for q in range(n)) for i in range(m_)]
    for i in range(m_):
        piv=next((r for r in range(i,m_) if N[r][i]!=0),None)
        if piv is None: return None
        N[i],N[piv],rhs[i],rhs[piv]=N[piv],N[i],rhs[piv],rhs[i]
        for r in range(m_):
            if r!=i and N[r][i]!=0:
                f=N[r][i]/N[i][i]; N[r]=[a-f*b for a,b in zip(N[r],N[i])]; rhs[r]-=f*rhs[i]
    sol=[rhs[i]/N[i][i] for i in range(m_)]
    if any(v<0 for v in sol): return None
    for q in range(n):
        if sum(A[q][i]*sol[i] for i in range(m_))!=y[q]: return None
    return [(basis[i],sol[i]) for i in range(m_) if sol[i]!=0]
def certify2(P,y,minmass=False):
    G=planar.chain_graph(P); lp=planar.flow_lp(P,y,False,G)
    if not lp.feasible: return None,"float LP infeasible"
    T=G.T; cand=set(); bl=np.zeros(T)
    for k,(_,_,_,bnd) in enumerate(G.arcs):
        for q in bnd: bl[q]+=lp.f[k]
    for _,path in planar.decompose_flow(G,lp.f):
        out=frozenset().union(*(G.arcs[k][2] for k in path)); bnd=frozenset().union(*(G.arcs[k][3] for k in path))
        cand.add(out)
        share=sorted((q for q in bnd if lp.g[q]>1e-12),key=lambda q:-lp.g[q]/bl[q])
        for j in range(1,len(share)+1): cand.add(out|frozenset(share[:j]))
        for q in bnd: cand.add(out|frozenset([q]))
    cand=[S for S in cand if planar.is_reachable(P,S,False)]
    cols=[tuple(1 if q in S else 0 for q in range(T)) for S in cand]
    sol=exact_solve(cols,y,minmass)
    if sol is None: return None,"exact solve failed (%d candidate sets)"%len(cand)
    return [(cand[k],m) for k,m in sol],"ok"
def check(P,y,cert):
    tot=[Fr(0)]*len(y)
    for S,m in cert:
        if m<0 or not planar.is_reachable(P,S,False): return False
        for q in S: tot[q]+=m
    return tot==list(y)
def exact_ok(Q,y):
    P=[(Fq(a),Fq(b)) for a,b in Q]; c,msg=certify2(P,y)
    return (c is not None and check(P,y,c)),msg
