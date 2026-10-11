"""Covering cuts: rho(P, y) with a proved lower bound and an exact certificate.

Blocking. `t` is blocked by `R` at prices Q if some xi >= 0, xi != 0 has
<xi, q_r - q_t> >= 0 for all r in R, i.e. t does not strictly cover R. A *cut* is a
list C of pairs (t, R) with a refutation w: <w, y> < 0, and every S with
sum_{t in S} w_t < 0 contains the t and misses the R of some pair of C. If y is weakly
solvable at Q, some pair of every cut is blocked at Q (Lean: `exists_isBlocked_of_cut`).

Master. Minimize the total perturbation over the box a in [1/(1+D), 1+D] subject to
the cuts found so far. Every weakly solvable Q satisfies all cuts, so the master value
is a lower bound on rho (`le_minPert_of_relaxation`). Blocking by a single s is the
disjunction "q_t^i <= q_s^i for some i" (`isBlocked_singleton_iff`): binaries only.
Blocking by a larger R is the union of d linear "pure" cases q_t^i <= q_r^i for all
r in R (witness e_i) and the general case: a witness xi with sum xi = mixed (perspective
form) and bilinear terms xi * a, handled by SCIP's spatial branch and bound. The union
is exactly blocking; the pure cases let most branches avoid the bilinear terms.
Blocking is invariant under the normalization (`isBlocked_smul_iff`).

Start: dominance. If y_t > y_s, the single pair (t, {s}) is a cut with w = e_s - e_t
(`le_of_dominates`). On the real data these cuts alone usually give the optimum.

Separation. At the master optimum Q*, column generation decides whether y lies in the
cone of the weakly reachable spectra at Q* (pricing: a binary program over S with
lazily added coverings, each found by the covering LP). If yes, Q* is weakly solvable
and its value equals the lower bound: rho is found. If not, the duals give a refutation
w, and a greedy pass picks coverings of Q* that kill every S with w(S) < 0. This new
cut is violated by Q*, since a strictly covering t is not blocked. A cut violated by
the current optimum differs from every earlier cut, and there are finitely many cuts,
so the loop is finite. In floating point a repeated cut means a tolerance artifact:
status "stalled". The validity of a cut depends only on w, y and the pairs, and is
checked with integer w.

`certify` turns the floating optimum into exact rationals: ties within a tolerance are
snapped to one rational, witnesses are chosen exactly (coordinate vectors first), and
as a last resort the prices are tilted as in the closure theorem (notes, lem:tilt). The
answer is checked by `verify.verify`; its pi(P, Q) is an upper bound on rho.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass
from fractions import Fraction
from typing import TYPE_CHECKING

import numpy as np
from pyscipopt import Model, quicksum
from scipy.optimize import linprog

from .verify import Rational, exact_masses, verify

if TYPE_CHECKING:
    from collections.abc import Callable

    from .prep import Prepared, Problem
    from .verify import Verification

Pair = tuple[int, tuple[int, ...]]  # (t, R): t is to be blocked by R
COVER_TOL = 1e-8  # a covering LP margin above this counts as a strict covering
FEASTOL = 1e-9  # SCIP feasibility tolerance of the master
GAP = 1e-6  # relative gap of the master; its dual bound is the reported lower bound
GAP_LOOSE = 1e-4  # gap of the intermediate masters, tightened to GAP at the end
MASS_EPS = 1e-12
ZERO = 1e-9  # LP values below this count as zero
LAMBDA_SCALE = 10**6  # refutations are rounded to integers / LAMBDA_SCALE
SNAP_TOLS = (1e-9, 1e-8, 1e-7, 1e-6, 1e-5)
HALF = 0.5  # rounding threshold for binaries
SOLVED = ("optimal", "gaplimit")  # master statuses with a usable optimum


@dataclass(frozen=True)
class Cut:
    pairs: tuple[Pair, ...]
    w: tuple[int, ...]  # integer refutation: <w, y> < 0


@dataclass(frozen=True)
class CutSolution:
    status: str  # "optimal", "stalled", "time limit", "iteration limit"
    bound: float  # proved lower bound on rho (up to the solver tolerances)
    value: float  # value of the last master optimum
    seconds: float
    a: tuple[tuple[float, ...], ...]  # last master optimum, multipliers q = p * a
    spectra: tuple[tuple[frozenset[int], float], ...]  # at a, when "optimal"
    cuts: tuple[Cut, ...]
    iterations: int
    upper: float = math.inf  # best exactly certified upper bound on rho
    answer: Verification | None = None  # the certified answer behind `upper`


def covering(Q: list[list[float]], S: frozenset[int], t: int) -> tuple[int, ...] | None:
    """The support R of a strict covering of the complement of S by t, if any: the LP
    max eps s.t. sum_r w_r q_r + eps 1 <= q_t, w in the simplex on S^c. A basic
    optimum has at most d nonzero weights."""
    T, d = len(Q), len(Q[0])
    others = [s for s in range(T) if s not in S]
    if not others:
        return None
    n = len(others)
    c = np.zeros(n + 1)
    c[-1] = -1.0
    A = np.array([[Q[s][i] for s in others] + [1.0] for i in range(d)])
    res = linprog(
        c,
        A_ub=A,
        b_ub=np.array(Q[t]),
        A_eq=np.array([[1.0] * n + [0.0]]),
        b_eq=[1.0],
        bounds=[(0, None)] * n + [(None, None)],
        method="highs",
    )
    if res.status != 0 or res.x[-1] <= COVER_TOL:
        return None
    return tuple(sorted(others[j] for j in range(n) if res.x[j] > MASS_EPS))


class _Pricing:
    """max sum_t dual_t x_t over nonempty S = {x = 1} closed under known coverings:
    t in S implies R meets S."""

    def __init__(self, T: int) -> None:
        self.model = Model("pricing")
        self.model.hideOutput()
        self.x = [self.model.addVar(f"x_{t}", vtype="B") for t in range(T)]
        self.model.addCons(quicksum(self.x) >= 1)
        self.known: set[Pair] = set()

    def add(self, pair: Pair) -> None:
        if pair in self.known:
            return
        self.known.add(pair)
        self.model.freeTransform()
        t, R = pair
        self.model.addCons(self.x[t] <= quicksum(self.x[r] for r in R))

    def best(self, dual: np.ndarray) -> tuple[float, frozenset[int]]:
        model = self.model
        model.freeTransform()
        objective = quicksum(dual[t] * x for t, x in enumerate(self.x))
        model.setObjective(objective, "maximize")
        model.optimize()
        S = frozenset(t for t, x in enumerate(self.x) if model.getVal(x) > HALF)
        return model.getObjVal(), S


def separate(Q: list[list[float]], y: np.ndarray):
    """Column generation for y in cone{1_S : S weakly reachable at Q}.

    Returns ("yes", [(S, m_S)]) or ("no", w, coverings): w(S) >= 0 on every weakly
    reachable S (they are closed under the coverings found) and <w, y> < 0."""
    T = len(Q)
    pricing = _Pricing(T)
    cols = [frozenset([t]) for t in range(T)]
    cols = [S for S in cols if all(covering(Q, S, t) is None for t in S)]
    while True:
        n = len(cols)
        A = np.array([[1.0 if t in S else 0.0 for S in cols] for t in range(T)])
        A = A.reshape(T, n)
        res = linprog(
            np.concatenate([np.zeros(n), np.ones(T)]),
            A_eq=np.hstack([A, np.eye(T)]),
            b_eq=y,
            bounds=[(0, None)] * (n + T),
            method="highs",
        )
        if res.fun < ZERO:
            return "yes", [(S, v) for S, v in zip(cols, res.x[:n]) if v > MASS_EPS]
        dual = np.array(res.eqlin.marginals)
        while True:
            value, S = pricing.best(dual)
            if value <= ZERO:
                return "no", -dual, set(pricing.known)
            bad = next(
                ((t, R) for t in S if (R := covering(Q, S, t)) is not None), None
            )
            if bad is None:
                cols.append(S)
                break
            pricing.add(bad)


def _killing_pairs(
    Q: list[list[float]], w: tuple[int, ...], known: set[Pair]
) -> tuple[Pair, ...]:
    """Greedy: coverings of Q such that every S with w(S) < 0 contains the t and misses
    the R of one of them. Each round finds the most negative S that survives and adds a
    covering that kills it, preferring known ones with small R."""
    T = len(Q)
    model = Model("cut")
    model.hideOutput()
    x = [model.addVar(f"x_{t}", vtype="B") for t in range(T)]
    model.setObjective(quicksum(w[t] * x[t] for t in range(T)))
    pairs: list[Pair] = []
    while True:
        model.optimize()
        if model.getObjVal() > -HALF:  # integer w: the minimum is >= 0
            return tuple(pairs)
        S = frozenset(t for t in range(T) if model.getVal(x[t]) > HALF)
        cands = [(t, R) for t, R in known if t in S and not set(R) & S]
        if not cands:
            cands = [(t, R) for t in S if (R := covering(Q, S, t)) is not None]
        if not cands:
            raise RuntimeError("a weakly reachable S has w(S) < 0")
        pair = min(cands, key=lambda c: len(c[1]))
        pairs.append(pair)
        model.freeTransform()
        model.addCons(x[pair[0]] <= quicksum(x[r] for r in pair[1]))


class _Master:
    def __init__(self, prep: Prepared, D: float) -> None:
        T, d, P = prep.T, prep.d, prep.P
        self.P, self.T, self.d = P, T, d
        self.lo, self.hi = 1 / (1 + D), 1 + D
        m = self.model = Model("master")
        m.hideOutput()
        self.a = {
            (t, i): m.addVar(f"a_{t}_{i}", lb=self.lo, ub=self.hi)
            for t in range(T)
            for i in range(d)
        }
        g = {k: m.addVar(f"g_{k[0]}_{k[1]}", lb=0, ub=D) for k in self.a}
        for k, a in self.a.items():
            m.addCons(g[k] >= a - 1)
            m.addCons(g[k] >= 1 / a - 1)  # convex on a > 0
        m.setObjective(quicksum(g.values()), "minimize")
        self.blocked: dict[Pair, object] = {}

    def _diff(self, r: int, t: int, i: int):
        """q_r^i - q_t^i in the master variables."""
        return self.P[r][i] * self.a[r, i] - self.P[t][i] * self.a[t, i]

    def _blocked(self, pair: Pair):
        """A binary b with b = 1 => t blocked by R."""
        if pair in self.blocked:
            return self.blocked[pair]
        m, P, d = self.model, self.P, self.d
        t, R = pair
        k = len(self.blocked)
        b = m.addVar(f"b_{k}", vtype="B")
        if len(R) == 1:
            (s,) = R
            delta = [m.addVar(f"delta_{k}_{i}", vtype="B") for i in range(d)]
            m.addCons(quicksum(delta) >= b)
            for i in range(d):
                M = P[t][i] * self.hi - P[s][i] * self.lo
                m.addCons(self._diff(s, t, i) >= -M * (1 - delta[i]))
        else:
            # pure disjuncts, linear: q_t^i <= q_r^i for all r in R (witness e_i)
            pure = [m.addVar(f"pure_{k}_{i}", vtype="B") for i in range(d)]
            mixed = m.addVar(f"mixed_{k}", vtype="B")
            m.addCons(quicksum(pure) + mixed >= b)
            for i in range(d):
                for r in R:
                    M = P[t][i] * self.hi - P[r][i] * self.lo
                    m.addCons(self._diff(r, t, i) >= -M * (1 - pure[i]))
            # any witness, perspective form: sum xi = mixed, so mixed = 0 leaves 0 >= 0
            xi = [m.addVar(f"xi_{k}_{i}", lb=0, ub=1) for i in range(d)]
            m.addCons(quicksum(xi) == mixed)
            for r in R:
                m.addCons(quicksum(xi[i] * self._diff(r, t, i) for i in range(d)) >= 0)
        self.blocked[pair] = b
        return b

    def add(self, pairs: tuple[Pair, ...]) -> None:
        self.model.freeTransform()
        if len(pairs) == 1:
            self.model.chgVarLb(self._blocked(pairs[0]), 1)  # the pair must be blocked
        else:
            self.model.addCons(quicksum(self._blocked(p) for p in pairs) >= 1)

    def solve(self, time_limit: float | None, gap: float):
        m = self.model
        m.freeTransform()
        m.setParam("limits/gap", gap)
        m.setParam("numerics/feastol", FEASTOL)
        if time_limit is not None:
            m.setParam("limits/time", max(time_limit, 1.0))
        try:
            m.optimize()
        except Exception:  # SCIP aborts on unresolved LP troubles
            return "error", math.inf, 0.0, ()
        if m.getNSols() == 0:
            return m.getStatus(), math.inf, m.getDualbound(), ()
        a = tuple(
            tuple(m.getVal(self.a[t, i]) for i in range(self.d)) for t in range(self.T)
        )
        return m.getStatus(), m.getObjVal(), m.getDualbound(), a


def _integer_refutation(w: np.ndarray, y: tuple[Fraction, ...]) -> tuple[int, ...]:
    scale = LAMBDA_SCALE / max(np.max(np.abs(w)), 1e-300)
    wi = tuple(round(v * scale) for v in w)
    if sum(c * v for c, v in zip(wi, y)) >= 0:
        raise RuntimeError("rounded refutation lost <w, y> < 0")
    return wi


def solve_cuts(  # noqa: PLR0912, PLR0913, PLR0915
    prep: Prepared,
    *,
    time_limit: float | None = None,
    max_iterations: int = 500,
    D: float | None = None,
    verbose: bool = False,
    upper: Callable[[tuple], Verification | None] | None = None,
    incumbent: Verification | None = None,
    initial_cuts: tuple[Cut, ...] = (),
) -> CutSolution:
    """The covering-cut loop. `D` overrides the box of `prep` (any D >= rho works).
    `incumbent` is a certified answer known in advance and `initial_cuts` valid cuts
    found elsewhere (both e.g. from `cppdom.pure_cut_loop`).

    `upper` maps master multipliers to an exactly certified answer (for example
    `primal.upper_bound`); it is called at every master optimum, and the loop stops
    as soon as the best certified value is within the gap of the lower bound."""
    T, d, P = prep.T, prep.d, prep.P
    y = np.array(prep.y)
    y_exact = prep.problem.y
    master = _Master(prep, prep.D if D is None else D)
    cuts: list[Cut] = []
    for t in range(T):
        for s in range(T):
            if y_exact[t] > y_exact[s]:
                w = tuple(1 if r == s else -1 if r == t else 0 for r in range(T))
                cut = Cut(((t, (s,)),), w)
                cuts.append(cut)
                master.add(cut.pairs)
    for cut in initial_cuts:
        if cut not in cuts:
            cuts.append(cut)
            master.add(cut.pairs)
    t0 = time.perf_counter()
    bound, status, value, a, spectra = 0.0, "iteration limit", math.inf, (), ()
    best: Verification | None = incumbent
    iteration, gap = 0, GAP_LOOSE
    while iteration < max_iterations:
        iteration += 1
        left = None if time_limit is None else time_limit - (time.perf_counter() - t0)
        st, value, dual_bound, a = master.solve(left, gap)
        bound = max(bound, dual_bound)
        if st not in SOLVED:
            status = "time limit" if st == "timelimit" else f"master: {st}"
            break
        if upper is not None:
            check = upper(a)
            if check is not None and (
                best is None or check.total_pert < best.total_pert
            ):
                best = check
        Q = [[P[t][i] * a[t][i] for i in range(d)] for t in range(T)]
        answer = separate(Q, y)
        if verbose:
            ub = float(best.total_pert) if best is not None else math.inf
            print(
                f"iteration {iteration}: value {value:.10g} bound {bound:.10g} "
                f"upper {ub:.10g} -> {answer[0]}"
            )
        if best is not None and float(best.total_pert) - bound <= GAP * max(
            float(best.total_pert), 1.0
        ):
            status = "optimal"
            break
        if answer[0] == "yes":
            if value - bound <= GAP * max(abs(value), 1.0):
                status, spectra = "optimal", tuple(answer[1])
                break
            gap = GAP  # weakly solvable but the bound is loose: tighten and repeat
            continue
        w = _integer_refutation(answer[1], y_exact)
        pairs = _killing_pairs(Q, w, answer[2])
        if any(c.pairs == pairs for c in cuts):
            status = "stalled"
            break
        cuts.append(Cut(pairs, w))
        master.add(pairs)
        if verbose:
            print(f"  cut {pairs}")
    return CutSolution(
        status=status,
        bound=bound,
        value=value,
        seconds=time.perf_counter() - t0,
        a=a,
        spectra=spectra,
        cuts=tuple(cuts),
        iterations=iteration,
        upper=float(best.total_pert) if best is not None else math.inf,
        answer=best,
    )


# ---------------------------------------------------------------- exact certificate


def _snap(Q: list[list[float]], tol: float) -> list[list[Fraction]]:
    """Values of one coordinate within relative distance tol of their neighbour in
    sorted order get one common rational (their mean)."""
    T, d = len(Q), len(Q[0])
    out: list[list[Fraction]] = [[Fraction(0)] * d for _ in range(T)]
    for i in range(d):
        order = sorted(range(T), key=lambda t: Q[t][i])
        groups, cur = [], [order[0]]
        for t in order[1:]:
            if Q[t][i] - Q[cur[-1]][i] <= tol * abs(Q[t][i]):
                cur.append(t)
            else:
                groups.append(cur)
                cur = [t]
        groups.append(cur)
        for group in groups:
            mean = sum(Q[t][i] for t in group) / len(group)
            v = Fraction(mean).limit_denominator(10**12)
            for t in group:
                out[t][i] = v
    return out


def _margin(Q, S, t, xi) -> Fraction:
    """min over s not in S of <xi, q_s - q_t>, exactly."""
    T, d = len(Q), len(Q[0])
    values = (
        sum(xi[i] * (Q[s][i] - Q[t][i]) for i in range(d))
        for s in range(T)
        if s not in S
    )
    return min(values, default=Fraction(1))


def _float_witness(Q: list[list[float]], S: frozenset[int], t: int) -> np.ndarray:
    """max mu s.t. <xi, q_s - q_t> >= mu for s not in S, xi in the simplex."""
    T, d = len(Q), len(Q[0])
    rows = [
        [Q[t][i] - Q[s][i] for i in range(d)] + [1.0] for s in range(T) if s not in S
    ]
    rows = rows or [[0.0] * d + [1.0]]
    res = linprog(
        np.concatenate([np.zeros(d), [-1.0]]),
        A_ub=np.array(rows),
        b_ub=np.zeros(len(rows)),
        A_eq=np.array([[1.0] * d + [0.0]]),
        b_eq=[1.0],
        bounds=[(0, None)] * d + [(None, None)],
        method="highs",
    )
    return res.x[:d]


def _witness(Q, S, t) -> tuple[list[Fraction], Fraction]:
    """The best exact witness: coordinate vectors or roundings of the LP witness."""
    d = len(Q[0])
    cands = [[Fraction(int(i == j)) for j in range(d)] for i in range(d)]
    xf = _float_witness([[float(c) for c in row] for row in Q], S, t)
    for den in (10**3, 10**6, 10**9, 10**12):
        v = [max(Fraction(float(c)).limit_denominator(den), Fraction(0)) for c in xf]
        if sum(v) > 0:
            cands.append([c / sum(v) for c in v])
    best = max(cands, key=lambda xi: _margin(Q, S, t, xi))
    return best, _margin(Q, S, t, best)


def _tilt(Q, y, wit, family):
    """Closure theorem, lem:tilt: q_t - delta (sum_i ln q_t^i + delta y_t) e with the
    witnesses xi + delta / q_t. Tries growing delta until every witness is exact."""
    T, d = len(Q), len(Q[0])
    ymax = max(y) or 1
    for k in range(10, 2, -1):
        delta = Fraction(1, 10**k)
        Qd = []
        for t in range(T):
            log_sum = sum(math.log(float(c)) for c in Q[t])
            shift = delta * (
                Fraction(log_sum).limit_denominator(10**9)
                + delta * Fraction(y[t]) / Fraction(ymax)
            )
            Qd.append([c - shift for c in Q[t]])
        if any(c <= 0 for row in Qd for c in row):
            continue
        tilted = {}
        for (j, t), xi in wit.items():
            v = [xi[i] + delta / Q[t][i] for i in range(d)]
            v = [c / sum(v) for c in v]
            if _margin(Qd, family[j], t, v) < 0:
                break
            tilted[j, t] = v
        else:
            return Qd, tilted
    return None


def _certify_at(problem: Problem, prep: Prepared, Qf, tol: float):
    T, d = problem.T, problem.d
    Q = _snap(Qf, tol)
    Qs = [[float(c) for c in row] for row in Q]
    answer = separate(Qs, np.array([float(v) for v in problem.y]))
    if answer[0] != "yes":
        return None
    family = [S for S, _ in answer[1]]
    if exact_masses(family, problem.y)[1]:
        return None
    wit, worst = {}, Fraction(0)
    for k, S in enumerate(family):
        for t in S:
            wit[k, t], margin = _witness(Q, S, t)
            worst = min(worst, margin)
    if worst < 0:
        tilted = _tilt(Q, problem.y, wit, family)
        if tilted is None:
            return None
        Q, wit = tilted
    Pn = [[problem.P[t][i] * prep.scale[i] for i in range(d)] for t in range(T)]
    a = tuple(tuple(Q[t][i] / Pn[t][i] for i in range(d)) for t in range(T))
    witnesses = {}
    for key, xi in wit.items():  # back to the original coordinates
        v = [xi[i] * prep.scale[i] for i in range(d)]
        witnesses[key] = tuple(c / sum(v) for c in v)
    return verify(problem, Rational(a=a, spectra=tuple(family), witnesses=witnesses))


def certify(
    problem: Problem, prep: Prepared, solution: CutSolution
) -> Verification | None:
    """The exactly certified answer of the loop: the best upper bound found, or a
    certificate near the last master optimum."""
    if solution.answer is not None:
        return solution.answer
    return certify_point(problem, prep, solution.a)


def certify_point(problem: Problem, prep: Prepared, a) -> Verification | None:
    """The cheapest exactly certified rational answer near the multipliers a, over
    the snapping tolerances `SNAP_TOLS`; None if none passes `verify`."""
    T, d = problem.T, problem.d
    Qf = [[prep.P[t][i] * a[t][i] for i in range(d)] for t in range(T)]
    best = None
    for tol in SNAP_TOLS:
        check = _certify_at(problem, prep, Qf, tol)
        better = best is None or (check and check.total_pert < best.total_pert)
        if check is not None and check.certified and better:
            best = check
    return best
