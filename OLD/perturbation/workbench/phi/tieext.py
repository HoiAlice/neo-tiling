import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import phi_dual as pd, lib_u as L, glue_u as GU
pd.set_phi('sq', h=1.0); u = 2.5
for pat in [(0,1,0,0),(1,0,0,0),(0,1,1,1),(1,0,1,1)]:
    sw, bits, idx = GU.xwires(u, 3, 3, pat)
    # reproduce glued x
    blk = pd.Block(sw); h = pd.H; x = blk.A.copy(); inK = set(idx)
    xK, bK, _ = GU.kopt(u, pat)
    for k, s in enumerate(idx): x[2*s] = xK[2*k]; x[2*s+1] = xK[2*k+1]
    for s in range(len(sw)):
        if s in inK: continue
        dl = sw[s][2]*h; b = bits[s]; x[2*s][b] -= dl/2; x[2*s+1][b] += dl/2
    Kp = {p for s in idx for p in (2*s, 2*s+1)}
    co = [(c, i, j, round(abs(x[i][c]-x[j][c]),9)) for c in (0, 1) for i in Kp for j in range(blk.T) if j not in Kp and abs(x[i][c]-x[j][c]) < 1e-4]
    # nearest-but-not-equal gaps
    gaps = sorted(abs(x[i][c]-x[j][c]) for c in (0, 1) for i in Kp for j in range(blk.T) if j not in Kp and abs(x[i][c]-x[j][c]) >= 1e-4)[:3]
    print(pat, "coincidences K-vs-exterior:", co[:6], "(count %d)" % len(co), "smallest non-coincident gaps (h):", [round(g, 4) for g in gaps])
