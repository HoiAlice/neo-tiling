"""Edge A with the corner at the NE end of the V wire (levels below the crossing U); edge B unchanged."""
from edge import *
import sys
h0c, h2c = 0.02, 0.04


def vlev(s, b=1.0):
    sh = -h0c * s if s < 0 else -h2c * s
    return (b + g + sh, b + sh)


def build(smax=8, weakE1=3.75):
    sw = []; ids = {}
    for s in range(-4, smax + 1):
        t, b = vlev(s); sw.append((s - 0.5, s - 0.5, 5, t, b))
    ids['v1'] = 0
    ytop, ybot = vlev(smax)
    ut = ybot                     # corner U top = V last bottom (mirror of the SW-end corner)
    ex, ey = smax - 0.5, smax - 0.5
    steps = [3, 3, weakE1, 3, 3]; p = 0
    sw.append((ex, ey, 4, ut, ut - g))
    for st in steps[:-1]:
        p += st; sw.append((ex + p, ey - p, 4, ut, ut - g))
    P = sum(steps)
    c = (ex + P + 2, ey - P + 2); sw.append((c[0] - 2.5, c[1] - 2.5, 5, ut, ut - g)); ids['v2'] = len(sw) - 1
    def vert(t): return (3 * t + 2 - 2.5, -3 * t + 2 - 2.5, 5, 1 + g, 1.0)
    def usw(t): return (3 * t, -3 * t, 4, 1 + g, 1.0)
    sw.append(vert(-5.75)); ids['A'] = len(sw) - 1
    for t in (-4.75, -3.5, -2.5, -1.5, -0.5, 0.5, 1.5, 2.5): sw.append(usw(t))
    sw.append(vert(3.5)); ids['B'] = len(sw) - 1
    return sw, [ids['v1'], ids['v2'], ids['A'], ids['B']]


if __name__ == "__main__":
    smax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    sw, idx = build(smax)
    for i, s in enumerate(sw): print(i, tuple(round(float(x), 3) for x in s))
    print("terminals", idx, flush=True)
    tb, mn = table(sw, idx, procs=4, verbose=False)
    for s, v in sorted(tb.items()):
        uns = (s[0] == s[1]) + (s[2] == s[3]); print(s, "unsat", uns, round(v - mn, 5), flush=True)
    sat = [s for s in tb if s[0] != s[1] and s[2] != s[3]]
    print(solv(sw, idx, sat), flush=True)
