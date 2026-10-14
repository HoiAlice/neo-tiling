import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import phi_dual as pd
sys.modules['np_dual'] = pd
sys.path.insert(0, '/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad')
from np_kplus import kplus, TERM
sw = kplus(); blk = pd.Block(sw)
for p in [(0,1,0,1,0,0,0,0),(0,1,0,1,0,0,1,1),(0,0,0,1,1,0,0,1)]:
    fixed = {blk.own[i]: b for i, b in zip(TERM, p)}
    t0=time.time(); lo,hi,_,st = pd.branch_and_bound(blk, fixed, tol=1e-7); print(p, lo, hi, st, time.time()-t0, flush=True)
