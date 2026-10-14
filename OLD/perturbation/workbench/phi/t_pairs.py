import sys, os, math, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import phi_dual as pd
sys.modules['np_dual'] = pd
sys.path.insert(0, '/Users/olegoleg/Code/neo-tiling/perturbation/workbench/gad')
from np_pair_exact import U
def pair_table(a):
    blk = pd.Block([U(0, 0), U(a, -a)])
    B2 = 2 * pd.B_closed(4)
    rows = {}
    for rt in itertools.product((0, 1), repeat=4):
        assign = dict(zip(range(4), rt))
        val, lam, x = pd.dual_float(blk, assign)
        rows[rt] = pd.dual_rigorous(blk, assign, lam) - B2
    return rows
if __name__ == '__main__':
    for name, p in [('pi', None), ('sq', None), ('cosh', None), ('pow', 1.5), ('pow', 3.0)]:
        pd.set_phi(name, h=pd.H, p=p)
        for a in (3.0, 3.75):
            r = pair_table(a)
            nat = r[(0, 0, 1, 0)]
            others = min(v for k, v in r.items() if k not in [(0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 1), (1, 0, 1, 1)])
            print(pd.PHI.name, a, "natural(equal bits) %.6f  closed 2phi(g/2)=%.6f  min other class %.6f" % (nat, 2*float(pd.PHI.f((4-a)*pd.H/2)), others))
