"""Reduction STAB(G) membership -> weak solvability at fixed prices, d = 3.

Exactly the gadget of lean/StabGadget.lean (theorem mem_indicatorCone_iff_inStab_of_gabriel):
  lift(a)   = (a0, a1, -a0 - a1) + (1 + |a|^2) e           (rewards, |a0| + |a1| <= 1/8)
  heavy uv  = lift(mid) + |a_u - a_v|^2 (1/4 + gamma) e     (one per edge)
  marker z  = (1/4) e                                       (strictly below everything)
and every edge is Gabriel with margin gamma in (0, 1/2]:
  |a_w - mid|^2 >= |a_u - a_v|^2 / 4 + gamma  for all other rewards w.
With y_z = y_heavy = 1 and y_v = 1 - s_v, y is weakly solvable iff s in STAB(G).
"""

from __future__ import annotations

from fractions import Fraction as Fr


def sqn(a):
    return a[0] ** 2 + a[1] ** 2


def lift(a, extra=Fr(0)):
    h = 1 + sqn(a) + extra
    return (a[0] + h, a[1] + h, -a[0] - a[1] + h)


def mid(a, b):
    return ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)


def gabriel_margin(A, edges):
    """Largest gamma such that every edge is Gabriel with margin gamma (None if no edges)."""
    best = None
    for u, v in edges:
        m = mid(A[u], A[v])
        r2 = sqn((A[u][0] - A[v][0], A[u][1] - A[v][1])) / 4
        for w in range(len(A)):
            if w not in (u, v):
                val = sqn((A[w][0] - m[0], A[w][1] - m[1])) - r2
                best = val if best is None else min(best, val)
    return best


def normalize(drawing):
    """Scale an integer drawing into the box |a0| + |a1| <= 1/8 (centred)."""
    xs = [Fr(p[0]) for p in drawing]
    ys = [Fr(p[1]) for p in drawing]
    cx, cy = (max(xs) + min(xs)) / 2, (max(ys) + min(ys)) / 2
    r = max(abs(x - cx) + abs(y - cy) for x, y in zip(xs, ys)) or Fr(1)
    k = Fr(1, 8) / r
    return [((x - cx) * k, (y - cy) * k) for x, y in zip(xs, ys)]


def build(drawing, edges, gamma=None, strict=False):
    """Return (P, idx) with idx = {'z': 0, 'reward': [...], 'heavy': {(u, v): i}}.
    strict=True builds the gadget for solvability (reachable sets): heights
    |a_u - a_v|^2 (1/4 + gamma/2), so that the empty-disk witnesses become strict."""
    A = normalize(drawing)
    g = gabriel_margin(A, edges)
    assert g is None or g > 0, "an edge is not Gabriel"
    if gamma is None:
        gamma = min(g, Fr(1, 2)) if g is not None else Fr(1, 2)
    assert 0 < gamma <= Fr(1, 2) and (g is None or gamma <= g)
    P = [(Fr(1, 4),) * 3]
    idx = {"z": 0, "reward": [], "heavy": {}, "gamma": gamma}
    for a in A:
        idx["reward"].append(len(P))
        P.append(lift(a))
    for u, v in edges:
        l2 = sqn((A[u][0] - A[v][0], A[u][1] - A[v][1]))
        idx["heavy"][u, v] = len(P)
        P.append(lift(mid(A[u], A[v]), l2 * (Fr(1, 4) + (gamma / 2 if strict else gamma))))
    return P, idx
