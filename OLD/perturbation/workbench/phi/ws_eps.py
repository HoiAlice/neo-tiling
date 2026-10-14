import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ws_g import *
import ws_k3g as K3
h = float(sys.argv[1]); pd.set_phi('sq', h=h)
u, att, aw = 2.5, 3.0, 3.75
sw3 = build_cp(u, att, aw); xs = {p: glued_x(sw3, u, p)[0] for p in itertools.product((0, 1), repeat=4)}
dm = [(a, b, d, 0, 0) for (a, b, d) in sw3]
y0 = y_pw(dm, 0.02, 0.08, 4); eta = (y0 - 1) / (y0.max() - 1)
for eps in (0.01, 0.1, 0.5):
    y = 1 + eps * eta
    ok = [bool(weakly_solvable(np.exp(x), y)) for x in xs.values()]
    print("cprime h=%g eps=%g ratio %.3f weakly solvable %d/16" % (h, eps, y.max() / y.min(), sum(ok)), flush=True)
