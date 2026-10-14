import sys,os; sys.path.insert(0,".")
from ws_h import *
sw=list(sw3)
for h in (0.2,0.1,0.02):
    row=[]
    for gap in (0.01,0.002):
        for c2 in (0.05,0.08,0.12,0.2,0.4,0.8):
            Y=y_rule(sw,[4],[0.02,c2],gap,0.3)
            ok=sum(bool(weakly_solvable(np.exp(h*XI[p]),Y)) for p in PATS)
            row.append((gap,c2,ok))
    print("h",h,"single cprime G*: (gap,c2,#patterns weakly solvable of 16):",row,flush=True)
