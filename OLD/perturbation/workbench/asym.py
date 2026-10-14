import itertools
U=[(-4.5,4.5),(-1.5,1.5),(1.5,-1.5),(4.5,-4.5)]
Vb=[-2.5,-1.5,-0.5,0.5,1.5]
lv={-2:(1.15,1.10),-1:(1.10,1.05),0:(1.05,1.0),1:(.85,.80),2:(.65,.60)}
pts=[]  # (name,(x,y),level)
for j,(bx,by) in enumerate(U,1):
    pts.append((f"Ut{j}",(bx+4,by+4),1.05)); pts.append((f"Ub{j}",(bx,by),1.0))
for s in range(-2,3):
    b=s-0.5
    pts.append((f"Vt{s}",(b+5,b+5),lv[s][0])); pts.append((f"Vb{s}",(b,b),lv[s][1]))
pos={n:p for n,p,l in pts}; L={n:l for n,p,l in pts}
def tau(n):
    k,i=n[:2],n[2:]
    if k[0]=='U': return ('Ub' if k[1]=='t' else 'Ut')+str(5-int(i))
    return ('Vb' if k[1]=='t' else 'Vt')+str(-int(i))
# check geometry
for n in pos:
    t=tau(n); assert abs(pos[t][0]-(4-pos[n][0]))<1e-9 and abs(pos[t][1]-(4-pos[n][1]))<1e-9,(n,t)
C=set((a,b) for a in pos for b in pos if L[a]>L[b]+1e-9)
CP=set((tau(b),tau(a)) for (a,b) in C)
print(len(C),len(CP))
def rel(a,b): # a higher; violated at P if a >= b coordinatewise
    pa,pb=pos[a],pos[b]; return pa[0]>=pb[0] and pa[1]>=pb[1]
for name,S in (("C-CP",C-CP),("CP-C",CP-C)):
    print(name,len(S))
    for (a,b) in sorted(S):
        pa,pb=pos[a],pos[b]
        print(" ",a,b,pa,pb,L[a],L[b],"violatedAtP" if rel(a,b) else "")
