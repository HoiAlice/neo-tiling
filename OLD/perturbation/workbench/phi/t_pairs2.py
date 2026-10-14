import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t_pairs import *
for name, p, h, a in [('sq', None, 0.2, 2.5), ('sq', None, 0.2, 3.75), ('pi', None, 1.0, 2.0), ('pi', None, 1.0, 3.9), ('pow', 3.0, 0.2, 1.75), ('pow', 3.0, 0.2, 3.9)]:
    pd.set_phi(name, h=h, p=p)
    r = pair_table(a)
    nat = r[(0, 0, 1, 0)]
    others = min(v for k, v in r.items() if k not in [(0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 1), (1, 0, 1, 1)])
    print(pd.PHI.name, "h", h, "a", a, "natural %.6g  closed %.6g  min other class %.6g  (other/natural %.2f)" % (nat, 2*float(pd.PHI.f((4-a)*pd.H/2)), others, others/nat))
