import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t_pairs import *
for h in (0.01, 0.05, 0.1, 0.1951606566777282, 0.5):
    pd.set_phi('pi', h=h)
    for a in (3.0, 3.99):
        r = pair_table(a); nat = r[(0, 0, 1, 0)]
        others = min(v for k, v in r.items() if k not in [(0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 1), (1, 0, 1, 1)])
        print("pi h %.4f a %.2f natural %.6g  min other class %.6g  ratio %.3f" % (h, a, nat, others, others/nat))
