"""Minimal price perturbation in the plane: an exact cutting-plane method for any cost.

Problem.  Prices P = (p_t) in R^2_{++}, outputs y >= 0, a separable cost
    c(Q) = sum_{t, i} f(r_t^i),   r = log(q/p) ("log" costs) or r = q/p ("lin" costs),
with f convex.  Find  rho_c(P, y) = min { c(Q) : y weakly solvable at Q }  (the minimum exists,
Lean `exists_min_cost`; the infimum over solvable Q is the same number by the closure theorem).
Costs provided: LOG_ABS = |log(q/p)|, PI = max(q/p, p/q) - 1, EPS = |q/p - 1|.

Method (the text, section 4).
* Cuts.  A cut is a finite set C of pairs (t, R), |R| <= 2, with the property: if y is weakly
  solvable at Q then some pair of C is blocked at Q (t is not strictly covered by R).  Cuts come
  from Farkas vectors w of the flow LP (planar.py): every S with w(S) < 0 must contain the t and
  miss the R of some pair of C (Lean `exists_isBlocked_of_cut`); pairs suffice in the plane
  (Lean `exists_pair_cover`).  Validity does not depend on the point where the cut was found.
* Master: min c(Q) subject to all cuts.  Its value is a lower bound on rho.  It is solved
  exactly by branch and bound: blocking by a pair has four forms (Lean `isBlocked_pair_iff`):
  t weakly left of both, weakly below both, or below a point of the segment in one of two
  orientations.  The first two are order constraints q_t^i <= q_r^i.  With order constraints
  only, the node problem splits by coordinate into two isotonic regressions (convex, solved as
  LPs with tangent minorants of f, exact for piecewise linear f).  The segment form
  q_t <= mu q_r + (1 - mu) q_s is relaxed by McCormick envelopes (and, in the log scale, by
  tangents of e^{z_t} and secants of e^{z_r}, e^{z_s}) and handled by spatial branching on the
  box of mu or of a coordinate of r, s: the one with the largest relaxation error, split at the
  LP value.  Pruning test "t is blocked at (lowest q_t, highest q_r, q_s) of the box" is exact
  (Lean `IsBlocked.mono`).  pi is used in the linear scale, where it is convex too.
* Separation: the flow LP at the master optimum Q* (polynomial).  If y is weakly solvable at Q*,
  Q* is optimal; else the Farkas vector gives a new cut, violated at Q*.
* Upper bound: the tilt of the notes (lem:tilt) moves Q* to rational prices where y is
  certified solvable exactly (planar.certify).  Before the first master: the hyperbola prices.
"""

from __future__ import annotations

import heapq
import math
import time
from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp

import planar

# ---------------------------------------------------------------- costs


@dataclass(frozen=True)
class Cost:
    """f(r) with r = log(q/p) (param "log") or r = q/p (param "lin"); f convex in r."""

    name: str
    param: str
    f: callable
    df: callable
    pieces: tuple = ()  # affine pieces (a, b), f = max(a r + b) when f is piecewise linear
    tangents: tuple = ()  # initial tangent points otherwise
    radius: callable = None  # f(r) <= c  =>  r in radius(c) (an interval)
    base: tuple = ()  # affine minorants always used (e.g. both one-sided slopes at a kink)


LOG_ABS = Cost("|log(q/p)|", "log", abs, lambda r: math.copysign(1.0, r) if r else 0.0,
               pieces=((1.0, 0.0), (-1.0, 0.0)), radius=lambda c: (-c, c))
# pi is convex in q as well; the linear scale makes the segment form linear for fixed mu
PI = Cost("max(q/p,p/q)-1", "lin", lambda r: max(r, 1 / r) - 1,
          lambda r: 1.0 if r > 1 else (-1 / r**2 if r < 1 else 0.0),
          tangents=(0.98, 0.95, 0.9, 0.8, 0.67, 0.5, 0.33, 0.2, 0.1),
          radius=lambda c: (1 / (1 + c), 1 + c),
          base=((1.0, -1.0), (-1.0, 1.0)))  # r - 1 (exact for r >= 1) and 1 - r at the kink
EPS = Cost("|q/p-1|", "lin", lambda r: abs(r - 1), lambda r: math.copysign(1.0, r - 1),
           pieces=((1.0, -1.0), (-1.0, 1.0)), radius=lambda c: (max(1 - c, 1e-6), 1 + c))
COSTS = {"log": LOG_ABS, "pi": PI, "eps": EPS}

# the master accepts blocking up to TOL (relative); the LPs must be more accurate than that
TOL = 1e-8
LP_OPTIONS = {"primal_feasibility_tolerance": 1e-10, "dual_feasibility_tolerance": 1e-10}


def lp(c, A, b, bounds):
    """HiGHS with tight tolerances; on an undecided status, again with the defaults.
    Returns the scipy result (status 0) or None if infeasible."""
    for options in (LP_OPTIONS, {}):
        res = linprog(c, A_ub=A, b_ub=b, bounds=bounds, method="highs", options=options)
        if res.status in (0, 2):
            return res if res.status == 0 else None
    raise RuntimeError(res.message)


def ratio(cost, q, p):
    return math.log(q / p) if cost.param == "log" else q / p


def cost_value(cost, P, Q):
    return sum(cost.f(ratio(cost, float(Q[t][i]), float(P[t][i])))
               for t in range(len(P)) for i in range(2))


# ---------------------------------------------------------------- blocking in the plane


def block_margin(Q, t, R):
    """max over xi = (th, 1 - th) of min_{r in R} <xi, q_r - q_t>, divided by X_t + Y_t.
    >= 0 iff t is blocked by R (Lean `isBlocked_two_iff`)."""
    if not R:
        return math.inf
    xt, yt = Q[t]
    lines = [(Q[r][0] - xt - (Q[r][1] - yt), Q[r][1] - yt) for r in R]  # slope, value at 0
    cand = {0.0, 1.0}
    for i in range(len(lines)):
        for j in range(i):
            (a1, b1), (a2, b2) = lines[i], lines[j]
            if a1 != a2:
                th = (b2 - b1) / (a1 - a2)
                if 0 < th < 1:
                    cand.add(th)
    best = max(min(a * th + b for a, b in lines) for th in cand)
    return best / (xt + yt)


def blocked(Q, t, R, tol):
    return block_margin(Q, t, R) >= -tol


# ---------------------------------------------------------------- master branch and bound


@dataclass
class Node:
    lb: float
    orders: tuple  # per coordinate: frozenset of (a, b) meaning q_a^i <= q_b^i
    lo: np.ndarray  # box in the node variable z (z = log q or q), shape (T, 2)
    hi: np.ndarray
    mixed: frozenset  # (t, r, s): q_t below a point of the segment q_r (upper left) - q_s
    mu: dict = field(default_factory=dict)  # (t, r, s) -> box (a, b) of the segment parameter
    z: np.ndarray = None

    def __lt__(self, other):
        return self.lb < other.lb


class Master:
    """min c(Q) subject to the cuts, exact up to `tol`, by branch and bound."""

    def __init__(self, P, cost, box_radius, tol=TOL):
        self.P = [(float(x), float(y)) for x, y in P]
        self.T = len(P)
        self.cost = cost
        self.tol = tol
        lo_r, hi_r = cost.radius(box_radius)
        lo = np.zeros((self.T, 2))
        hi = np.zeros((self.T, 2))
        for t in range(self.T):
            for i in range(2):
                p = self.P[t][i]
                if cost.param == "log":
                    lo[t, i], hi[t, i] = math.log(p) + lo_r, math.log(p) + hi_r
                else:
                    lo[t, i], hi[t, i] = p * lo_r, p * hi_r
        self.lo0, self.hi0 = lo, hi
        self.tangents = [[sorted(cost.tangents) for _ in range(2)] for _ in range(self.T)]
        self.cuts = []
        self.cache = {}
        self.exp_tangents = [[[] for _ in range(2)] for _ in range(self.T)]
        self.nodes = 0

    # node variable z <-> price q and ratio r
    def q_of(self, z):
        return np.exp(z) if self.cost.param == "log" else z

    def r_of(self, t, i, z):
        p = self.P[t][i]
        return z - math.log(p) if self.cost.param == "log" else z / p

    def add_tangent(self, t, i, r):
        pool = self.tangents[t][i]
        if all(abs(r - x) > 1e-7 * (1 + abs(r)) for x in pool):
            pool.append(r)
            pool.sort()

    def minorants(self, t, i, zlo=-math.inf, zhi=math.inf):
        """Affine minorants of the cost of variable (t, i) in z: theta >= a z + b.  For smooth
        costs: the tangents inside [zlo, zhi] and the nearest one beyond each end (the others
        are redundant on the box)."""
        p = self.P[t][i]
        if self.cost.pieces:
            pcs = self.cost.pieces
        else:
            pool = self.tangents[t][i]
            rlo, rhi = self.r_of(t, i, zlo), self.r_of(t, i, zhi)
            inside = [r for r in pool if rlo <= r <= rhi]
            below = [r for r in pool if r < rlo][-1:]
            above = [r for r in pool if r > rhi][:1]
            pcs = [(self.cost.df(r), self.cost.f(r) - self.cost.df(r) * r)
                   for r in below + inside + above] + list(self.cost.base)
        if self.cost.param == "log":  # r = z - log p
            return [(a, b - a * math.log(p)) for a, b in pcs]
        return [(a / p, b) for a, b in pcs]  # r = z / p

    def node_lp(self, node):
        """The convex relaxation of a node, one LP.
        Variables z_t^i (node variable), theta_t^i (cost epigraph).  Rows:
          theta >= affine minorants of the cost;  z_a^i <= z_b^i for the order constraints;
          for every required segment form (t, r, s) with parameter mu in [a, b], coordinatewise
          q_t <= mu q_r + (1 - mu) q_s, relaxed by McCormick envelopes of the two products and,
          for log costs (q = e^z), by tangents of e^{z_t} (q_t from below) and secants of
          e^{z_r}, e^{z_s} over the box (from above).
        The relaxation tends to the exact constraint as the boxes of mu and z shrink."""
        T = self.T
        nvar = [4 * T]  # z: index 2 t + i, theta: 2 T + 2 t + i
        bounds = [(node.lo[t, i], node.hi[t, i]) for t in range(T) for i in range(2)]
        bounds += [(0, None)] * (2 * T)
        rows, rhs = [], []

        def new(lo_, hi_):
            bounds.append((lo_, hi_))
            nvar[0] += 1
            return nvar[0] - 1

        def row(coefs, b):
            rows.append(coefs)
            rhs.append(b)

        Z = lambda t, i: 2 * t + i  # noqa: E731
        for i in range(2):
            for a, b in node.orders[i]:
                row({Z(a, i): 1.0, Z(b, i): -1.0}, 0.0)
            for t in range(T):
                for a, b in self.minorants(t, i, node.lo[t, i], node.hi[t, i]):
                    row({Z(t, i): a, 2 * T + Z(t, i): -1.0}, -b)
        log = self.cost.param == "log"
        aux = []  # per triple and coordinate: indices of mu, q_t, q_r, q_s, w1, w2
        for m in node.mixed:
            t, r, s = m
            ma, mb = node.mu.get(m, (0.0, 1.0))
            mu = new(ma, mb)
            for i in range(2):
                qv = {}
                for v in (t, r, s):
                    lo_, hi_ = node.lo[v, i], node.hi[v, i]
                    if not log:
                        qv[v] = (Z(v, i), lo_, hi_)
                        continue
                    k = new(math.exp(lo_), math.exp(hi_))
                    qv[v] = (k, math.exp(lo_), math.exp(hi_))
                    if v == t:  # q_t >= e^c (1 + z_t - c), tangents refined in `evaluate`
                        for c in [lo_, hi_] + [c for c in self.exp_tangents[t][i]
                                               if lo_ < c < hi_]:
                            row({Z(v, i): math.exp(c), k: -1.0}, math.exp(c) * (c - 1))
                    elif hi_ > lo_:  # q_v <= secant of e^z over [lo, hi]
                        sl = (math.exp(hi_) - math.exp(lo_)) / (hi_ - lo_)
                        row({k: 1.0, Z(v, i): -sl}, math.exp(lo_) - sl * lo_)
                kt, _, _ = qv[t]
                kr, rl, rh = qv[r]
                ks, sl_, sh = qv[s]
                w1 = new(0.0, None)  # w1 = mu q_r
                w2 = new(0.0, None)  # w2 = (1 - mu) q_s
                row({w1: 1.0, kr: -mb, mu: -rl}, -mb * rl)
                row({w1: 1.0, kr: -ma, mu: -rh}, -ma * rh)
                row({w2: 1.0, ks: -(1 - ma), mu: sl_}, ma * sl_)
                row({w2: 1.0, ks: -(1 - mb), mu: sh}, mb * sh)
                row({kt: 1.0, w1: -1.0, w2: -1.0}, 0.0)
                aux.append((m, i, mu, kt, kr, ks, w1, w2))
        A = np.zeros((len(rows), nvar[0]))
        for k, coefs in enumerate(rows):
            for j, v in coefs.items():
                A[k, j] += v
        c = np.zeros(nvar[0])
        c[2 * T:4 * T] = 1.0
        res = lp(c, A, np.array(rhs), bounds)
        if res is None:
            return None
        res.aux = aux
        return res

    def coord_lp(self, i, orders, lo, hi):
        """Without segment forms the node problem splits by coordinate: an isotonic regression
        in coordinate i.  Results are cached (children change one coordinate)."""
        key = (i, orders, tuple(lo), tuple(hi))
        if key in self.cache:
            return self.cache[key]
        T = self.T
        prev, stall = -math.inf, 0
        while True:
            rows, rhs = [], []
            for a, b in orders:
                row = np.zeros(2 * T)
                row[a], row[b] = 1.0, -1.0
                rows.append(row)
                rhs.append(0.0)
            for t in range(T):
                for a, b in self.minorants(t, i, lo[t], hi[t]):
                    row = np.zeros(2 * T)
                    row[t], row[T + t] = a, -1.0
                    rows.append(row)
                    rhs.append(-b)
            c = np.concatenate([np.zeros(T), np.ones(T)])
            bounds = [(lo[t], hi[t]) for t in range(T)] + [(0, None)] * T
            res = lp(c, np.array(rows), np.array(rhs), bounds)
            if res is None:
                out = None
                break
            z, theta = res.x[:T], res.x[T:]
            gap = [self.cost.f(self.r_of(t, i, z[t])) - theta[t] for t in range(T)]
            stall = stall + 1 if res.fun <= prev + 1e-12 else 0
            if self.cost.pieces or max(gap) <= 1e-7 or stall >= 5:
                out = (res.fun, z)
                break
            prev = res.fun
            for t in range(T):
                if gap[t] > 1e-8:
                    self.add_tangent(t, i, self.r_of(t, i, z[t]))
        self.cache[key] = out
        return out

    def evaluate(self, node):
        T = self.T
        if not node.mixed:
            out = [self.coord_lp(i, node.orders[i], node.lo[:, i], node.hi[:, i])
                   for i in range(2)]
            if out[0] is None or out[1] is None:
                return False
            node.lb = out[0][0] + out[1][0]
            node.z = np.stack([out[0][1], out[1][1]], axis=1)
            return True
        prev, stall = -math.inf, 0
        log = self.cost.param == "log"
        while True:
            res = self.node_lp(node)
            if res is None:
                return False
            x = res.x
            z = x[:2 * T].reshape(T, 2)
            theta = x[2 * T:4 * T].reshape(T, 2)
            gap = [(self.cost.f(self.r_of(t, i, z[t, i])) - theta[t, i], t, i)
                   for t in range(T) for i in range(2)]
            # tangents of e^{z_t} under q_t, refined like the cost tangents
            egap = [(math.exp(z[m[0], i]) - x[kt], m[0], i)
                    for m, i, _, kt, *_r in res.aux] if log else []
            # tangent minorants keep the bound valid; refine while it improves
            stall = stall + 1 if res.fun <= prev + 1e-12 else 0
            tight = ((self.cost.pieces or max(gap)[0] <= 1e-7)
                     and all(g <= 1e-9 * math.exp(z[t, i]) for g, t, i in egap))
            if tight or stall >= 5:
                node.lb, node.z = res.fun, z
                node.split = self.split_choice(node, x, z, res.aux)
                return True
            prev = res.fun
            for g, t, i in gap:
                if g > 1e-8:
                    self.add_tangent(t, i, self.r_of(t, i, z[t, i]))
            for g, t, i in egap:
                if g > 1e-9 * math.exp(z[t, i]):
                    self.exp_tangents[t][i].append(z[t, i])

    def split_choice(self, node, x, z, aux):
        """Per segment form, the box to split: mu or a coordinate of r or s, whichever carries
        the largest error of the relaxation at the LP solution (McCormick terms w - mu q and
        secants of e^z)."""
        log = self.cost.param == "log"
        best = {}
        for m, i, mu, kt, kr, ks, w1, w2 in aux:
            t, r, s = m
            ma, mb = node.mu.get(m, (0.0, 1.0))
            for v, kq, w, coef in ((r, kr, w1, x[mu]), (s, ks, w2, 1 - x[mu])):
                q_true = math.exp(z[v, i]) if log else z[v, i]
                err = x[w] - coef * q_true  # overestimate of the product
                lo_, hi_ = self.q_of(node.lo[v, i]), self.q_of(node.hi[v, i])
                rel_q = (hi_ - lo_) / hi_
                cand = ("mu", x[mu]) if mb - ma >= rel_q else ("z", v, i, z[v, i])
                if err > best.get(m, (0.0, None))[0]:
                    best[m] = (err, cand)
                if log:  # secant gap of e^{z_v}
                    sec = x[kq] - q_true
                    if coef * sec > best.get(m, (0.0, None))[0]:
                        best[m] = (coef * sec, ("z", v, i, z[v, i]))
        return {m: c for m, (_, c) in best.items()}

    def feasible_box(self, node):
        """Exact pruning: a required segment form needs t blocked by {r, s} at the corner of the
        box most favourable to blocking."""
        qlo, qhi = self.q_of(node.lo), self.q_of(node.hi)
        for t, r, s in node.mixed:
            Qx = {t: qlo[t], r: qhi[r], s: qhi[s]}
            if not blocked(Qx, t, (r, s), self.tol):
                return False
        return True

    def children(self, node, cut):
        """One child per form of blocking of each pair in the cut."""
        out = []

        def child(add0=(), add1=(), mixed=None):
            o0 = node.orders[0] | frozenset(add0)
            o1 = node.orders[1] | frozenset(add1)
            mx = node.mixed | ({mixed} if mixed else frozenset())
            return Node(node.lb, (o0, o1), node.lo.copy(), node.hi.copy(), frozenset(mx),
                        dict(node.mu), node.z)

        for t, R in cut:
            R = tuple(R)
            out.append(child(add0=[(t, r) for r in R]))  # weakly left of all of R
            out.append(child(add1=[(t, r) for r in R]))  # weakly below all of R
            if len(R) == 2:
                for r, s in (R, R[::-1]):  # r upper left, s lower right
                    out.append(child(add0=[(r, s), (t, s)], add1=[(s, r), (t, r)],
                                     mixed=(t, r, s)))
        return out

    def spatial_children(self, node, triple):
        """Split at its midpoint the box chosen by `split_choice` (mu or a coordinate of r, s);
        if the relaxation shows no error there, the widest of the seven boxes of the triple."""
        ma, mb = node.mu.get(triple, (0.0, 1.0))
        choice = getattr(node, "split", {}).get(triple)
        if choice is not None:
            best = None if choice[0] == "mu" else (choice[1], choice[2])
        else:
            best, width = None, mb - ma
            for v in triple:
                for i in range(2):
                    wdt = node.hi[v, i] - node.lo[v, i]
                    if self.cost.param == "lin":
                        wdt /= self.P[v][i]
                    if wdt > width:
                        best, width = (v, i), wdt
        a = Node(node.lb, node.orders, node.lo.copy(), node.hi.copy(), node.mixed,
                 dict(node.mu), node.z)
        b = Node(node.lb, node.orders, node.lo.copy(), node.hi.copy(), node.mixed,
                 dict(node.mu), node.z)
        def point(lo_, hi_, val):
            # split at the LP value (it becomes an end of both boxes, where the envelopes are
            # exact); near the ends of the box, at the midpoint
            w = hi_ - lo_
            if val is not None and lo_ + 0.05 * w < val < hi_ - 0.05 * w:
                return val
            return 0.5 * (lo_ + hi_)

        val = choice[-1] if choice is not None else None
        if best is None:
            mid = point(ma, mb, val)
            a.mu[triple], b.mu[triple] = (ma, mid), (mid, mb)
        else:
            v, i = best
            mid = point(node.lo[v, i], node.hi[v, i], val if choice is not None else None)
            a.hi[v, i] = mid
            b.lo[v, i] = mid
        return [a, b]

    def solve(self, time_limit=600.0, node_limit=10**6):
        """Returns (value, Q, exact): value is a valid lower bound; exact=False if a limit hit
        (then value is the best open bound)."""
        t0 = time.time()
        empty = (frozenset(), frozenset())
        root = Node(0.0, empty, self.lo0.copy(), self.hi0.copy(), frozenset())
        if not self.evaluate(root):
            raise RuntimeError("master infeasible: the box is too small")
        heap = [root]
        while heap:
            node = heapq.heappop(heap)
            self.nodes += 1
            if time.time() - t0 > time_limit or self.nodes > node_limit:
                return node.lb, self.q_of(node.z), False
            Q = self.q_of(node.z)
            # violation of a cut: how far its least violated pair is from being blocked
            viol = [min(-block_margin(Q, t, R) for t, R in cut) for cut in self.cuts]
            worst = max(range(len(viol)), key=viol.__getitem__, default=None)
            if worst is None or viol[worst] <= self.tol:
                return node.lb, Q, True  # best-first: the first feasible node is optimal
            bad = [m for m in node.mixed
                   if not blocked(Q, m[0], (m[1], m[2]), self.tol)]
            kids = (self.spatial_children(node, bad[0]) if bad else
                    self.children(node, self.cuts[worst]))
            for kid in kids:
                if self.feasible_box(kid) and self.evaluate(kid):
                    heapq.heappush(heap, kid)
        raise RuntimeError("master infeasible")


# ---------------------------------------------------------------- separation and cuts


def snap(Q, P, rel=1e-10):
    """Rational prices from floats.  Values of one coordinate closer than `rel` are merged, so
    that the ties produced by the isotonic regressions are exact, and a group containing an
    unmoved price (within `rel` of p) takes that exact price."""
    T = len(Q)
    out = [[None, None] for _ in range(T)]
    for i in range(2):
        order = sorted(range(T), key=lambda t: Q[t][i])
        group = [order[0]]
        for t in order[1:] + [None]:
            if t is not None and Q[t][i] - Q[group[-1]][i] <= rel * Q[t][i]:
                group.append(t)
                continue
            fixed = [P[s][i] for s in group if abs(Q[s][i] - P[s][i]) <= rel * P[s][i]]
            val = fixed[0] if fixed else Fraction(float(np.mean([Q[s][i] for s in group])))
            for s in group:
                out[s][i] = val
            group = [t]
    return [tuple(v) for v in out]


def strict_covers(Q, S, tol):
    """Pairs (t, R), t in S, R outside S, |R| <= 2, not blocked at Q, most violated first."""
    T = len(Q)
    rest = [s for s in range(T) if s not in S]
    found = []
    for t in S:
        for a in range(len(rest)):
            for b in range(a, len(rest)):
                R = (rest[a],) if a == b else (rest[a], rest[b])
                mg = block_margin(Q, t, R)
                if mg < -tol:
                    found.append((mg, t, R))
    found.sort()
    return [(t, R) for _, t, R in found]


def make_cut(Q, w, tol):
    """A cut C from a Farkas vector w: every S with w(S) < 0 contains t and misses R for some
    (t, R) in C.  Built greedily with a 0-1 program that looks for an S not yet hit."""
    T = len(Q)
    cut = []
    while True:
        A, lb_ = [], []
        for t, R in cut:  # x_t - sum_{r in R} x_r <= 0  (S not hit by (t, R))
            row = np.zeros(T)
            row[t] = 1.0
            for r in R:
                row[r] -= 1.0
            A.append(row)
            lb_.append(-np.inf)
        cons = [LinearConstraint(np.array(A), lb_, np.zeros(len(A)))] if A else []
        res = milp(c=np.asarray(w, dtype=float), constraints=cons, integrality=np.ones(T),
                   bounds=Bounds(0, 1))
        if res.status != 0 or res.fun > -1e-9:
            return cut
        S = {q for q in range(T) if res.x[q] > 0.5}
        covers = strict_covers(Q, S, tol)
        if not covers:  # S looks weakly reachable at Q: hit it with its least blocked pair
            rest = [s for s in range(T) if s not in S]
            pairs = [(block_margin(Q, t, (r, s)), t, (r, s)) for t in S
                     for r in rest for s in rest if r <= s]
            _, t, R = min(pairs)
            covers = [(t, tuple(sorted(set(R))))]
        cut.append(covers[0])


def tilt(Q, y, delta):
    """Lemma tilt of the notes: q_t + delta (sum_i exp(-q_t^i) - delta y_t) (1, 1), on prices
    normalized to max 1 per coordinate (rational output)."""
    sx = max(q[0] for q in Q)
    sy = max(q[1] for q in Q)
    d = Fraction(delta)
    out = []
    for (x, yv), yt in zip(Q, y):
        xn, yn = x / sx, yv / sy
        shift = d * (Fraction(math.exp(-float(xn)) + math.exp(-float(yn))) - d * Fraction(yt))
        out.append(((xn + shift) * sx, (yn + shift) * sy))
    return out


def hyperbola_point(P, cost):
    """q^1 = p^1, q^2 = kappa / p^1 with the best kappa (golden section on log kappa).  All sets
    are weakly reachable there (notes, lem:full), so y is weakly solvable."""
    P = planar.frac_points(P)
    logs = [math.log(x * yv) for x, yv in P]

    def val(lk):
        return sum(cost.f(ratio(cost, math.exp(lk) / float(x), float(yv))) for x, yv in P)

    a, b = min(logs), max(logs)
    g = (math.sqrt(5) - 1) / 2
    for _ in range(100):
        c, d = b - g * (b - a), a + g * (b - a)
        if val(c) <= val(d):
            b = d
        else:
            a = c
    kappa = Fraction(math.exp((a + b) / 2))
    return [(x, kappa / x) for x, _ in P]


# ---------------------------------------------------------------- the main loop


@dataclass
class Result:
    lower: float
    upper: float
    Q: list  # rational prices with an exact certificate
    certificate: list
    iterations: int
    cuts: int
    nodes: int
    seconds: float
    log: list = field(default_factory=list)


def solve(P, y, cost=LOG_ABS, tol=TOL, max_iter=500, time_limit=1800.0, verbose=False):
    t0 = time.time()
    P = planar.frac_points(P)
    y = [Fraction(v) for v in y]
    T = len(P)
    # upper bound from the hyperbola
    Qup = hyperbola_point(P, cost)
    cert = planar.certify(Qup, y)
    assert cert is not None
    upper = cost_value(cost, P, Qup)
    master = Master(P, cost, upper, tol)
    # dominance cuts: y_t > y_s  =>  t blocked by {s}
    for t in range(T):
        for s in range(T):
            if y[t] > y[s]:
                master.cuts.append([(t, (s,))])
    log = []
    lower = 0.0
    for it in range(1, max_iter + 1):
        left = time_limit - (time.time() - t0)
        lower, Qf, exact = master.solve(time_limit=max(left, 1.0))
        if not exact:
            break
        Qs = snap([tuple(q) for q in Qf], P)
        # Q* is optimal if y is weakly solvable there.  Floating point puts points that should
        # lie on a segment slightly off it, so first try the tilt of the notes with a small
        # delta and certify exactly.
        done = False
        for delta in (0, 1e-9, 1e-8, 1e-7, 1e-6, 1e-5):
            Qc = Qs if delta == 0 else tilt(Qs, y, delta)
            c = planar.certify(Qc, y)
            if c is not None:
                val = cost_value(cost, P, Qc)
                if val < upper:
                    upper, Qup, cert = val, Qc, c
                done = True
                break
        log.append((it, lower, upper, len(master.cuts), master.nodes))
        if verbose:
            print(f"it {it}: lower {lower:.7f} upper {upper:.7f} cuts {len(master.cuts)} "
                  f"nodes {master.nodes} {time.time() - t0:.1f}s", flush=True)
        if done:
            break
        # Separation.  The master accepts blocking up to `tol`; at Q* itself such near-blocked
        # pairs look strictly covering and would return an old cut.  The tilt resolves them,
        # so separate at slightly tilted points and take the first new cut.  (Any cut is valid;
        # the point only matters for progress.)
        cut = None
        for delta in (1e-7, 1e-6, 1e-5):
            Qt = tilt(Qs, y, delta)
            lp = planar.flow_lp(Qt, y)
            if lp.feasible:
                continue
            cand = make_cut([tuple(map(float, q)) for q in Qt], lp.w, tol)
            if cand and cand not in master.cuts:
                cut = cand
                break
        if cut is None:
            break  # no progress possible at this tolerance: report the gap
        master.cuts.append(cut)
    return Result(lower, upper, Qup, cert, it, len(master.cuts), master.nodes,
                  time.time() - t0, log)
