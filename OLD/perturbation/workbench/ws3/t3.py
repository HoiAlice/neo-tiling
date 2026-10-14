from common import *
sw=build("cp"); d=np.load("/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad/ws_snap_cp.npz"); Qs=list(d['Qs'])
y,gaps=kinked_y(sw,[4]); Q=Qs[0]
r=feasible(Q,y); print(r.feasible, [a for a in dir(r) if not a.startswith('_')])
rng=np.random.default_rng(0)
print("noise 1e-3:",feasible(Q,y+1e-3*rng.standard_normal(len(y))).feasible)
y2=y.copy(); y2[0]+=0.05; print("top0 up .05",feasible(Q,y2).feasible)
y3=y.copy(); y3[1]+=0.2; print("bot1 up .2",feasible(Q,y3).feasible)
# y with the wrong (no kink) rule
y4,_=kinked_y(sw,[4],rho=1.0); print("rho=1 (no kink)",feasible(Q,y4).feasible)
