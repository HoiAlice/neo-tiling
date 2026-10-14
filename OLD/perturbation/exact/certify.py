"""Exact rational certificates (pycddlib with GMP rationals, no tolerances).

A certificate of an upper bound is (Q, sets S_k, masses m_k, witnesses xi_{k,t}) with
Q >= 0, m >= 0, sum_k m_k 1_{S_k} = y and <xi_{k,t}, q_s - q_t> >= 0, xi_{k,t} >= 0,
xi_{k,t} != 0 for t in S_k, s outside S_k. `verify` checks it from scratch.
"""

from __future__ import annotations

from fractions import Fraction

import cdd
import cdd.gmp as g


def F(x) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(x)


def lp(c, A_ub=(), b_ub=(), A_eq=(), b_eq=(), sense="min"):
    """Exact LP over free variables: optimize c.x s.t. A_ub x <= b_ub, A_eq x = b_eq.

    Returns (status, value, x) with status in {'optimal', 'infeasible', 'unbounded'}.
    """
    n = len(c)
    rows = [[F(b)] + [-F(a) for a in row] for row, b in zip(A_ub, b_ub)]
    eq0 = len(rows)
    rows += [[F(b)] + [-F(a) for a in row] for row, b in zip(A_eq, b_eq)]
    if not rows:
        rows = [[Fraction(0)] + [Fraction(0)] * n]
    mat = g.matrix_from_array(rows, rep_type=cdd.RepType.INEQUALITY)
    mat.lin_set = frozenset(range(eq0, len(rows)))
    mat.obj_type = cdd.LPObjType.MIN if sense == "min" else cdd.LPObjType.MAX
    mat.obj_func = tuple([Fraction(0)] + [F(x) for x in c])
    prog = g.linprog_from_matrix(mat)
    g.linprog_solve(prog)
    st = prog.status
    if st == cdd.LPStatusType.OPTIMAL:
        return "optimal", prog.obj_value, list(prog.primal_solution)
    if st in (cdd.LPStatusType.INCONSISTENT, cdd.LPStatusType.STRUC_INCONSISTENT):
        return "infeasible", None, None
    if st in (cdd.LPStatusType.DUAL_INCONSISTENT, cdd.LPStatusType.STRUC_DUAL_INCONSISTENT):
        return "unbounded", None, None
    raise RuntimeError(f"cdd status {st}")


def weak_witness(Q, S: frozenset, t: int):
    """A weak witness of t for S at Q (xi >= 0, sum xi = 1), or None."""
    d = len(Q[0])
    out = [s for s in range(len(Q)) if s not in S]
    A_ub = [[-(F(Q[s][i]) - F(Q[t][i])) for i in range(d)] for s in out]
    A_ub += [[-Fraction(int(i == j)) for i in range(d)] for j in range(d)]
    b_ub = [Fraction(0)] * (len(out) + d)
    st, _, x = lp([Fraction(0)] * d, A_ub, b_ub, [[Fraction(1)] * d], [Fraction(1)])
    return x if st == "optimal" else None


def max_margin_witness(Q, S: frozenset, t: int):
    """argmax over the simplex of min_{s not in S} <xi, q_s - q_t> (exact LP)."""
    d = len(Q[0])
    out = [s for s in range(len(Q)) if s not in S]
    if not out:
        return [Fraction(1, d)] * d, Fraction(1)
    A_ub = [[-(F(Q[s][i]) - F(Q[t][i])) for i in range(d)] + [Fraction(1)] for s in out]
    A_ub += [[-Fraction(int(i == j)) for i in range(d)] + [Fraction(0)] for j in range(d)]
    st, tau, x = lp(
        [Fraction(0)] * d + [Fraction(1)],
        A_ub,
        [Fraction(0)] * len(A_ub),
        [[Fraction(1)] * d + [Fraction(0)]],
        [Fraction(1)],
        sense="max",
    )
    return x[:d], tau


def cone_masses(y, sets: list[frozenset]):
    """m >= 0 with sum_k m_k 1_{S_k} = y, or None."""
    K, T = len(sets), len(y)
    A_eq = [[Fraction(int(t in S)) for S in sets] for t in range(T)]
    A_ub = [[-Fraction(int(i == k)) for i in range(K)] for k in range(K)]
    st, _, m = lp([Fraction(0)] * K, A_ub, [Fraction(0)] * K, A_eq, [F(v) for v in y])
    return m if st == "optimal" else None


def pi1(P, Q) -> Fraction:
    return sum(
        abs(F(q) / F(p) - 1) for prow, qrow in zip(P, Q) for p, q in zip(prow, qrow)
    )


def weakly_solvable(Q, y, sets: list[frozenset]):
    """Exact check of weak solvability of y at Q using the given candidate sets.

    Keeps the weakly reachable ones; returns (masses, witnesses) or None.
    """
    good, wit = [], {}
    for S in sets:
        ws = {t: weak_witness(Q, S, t) for t in S}
        if all(w is not None for w in ws.values()):
            k = len(good)
            good.append(S)
            wit.update({(k, t): w for t, w in ws.items()})
    m = cone_masses(y, good) if good else None
    return None if m is None else (good, m, wit)


def best_prices(P, y, sets: list[frozenset], witness: dict):
    """Exact LP: min pi_1(P, Q) over Q >= 0 with the given sets and fixed witnesses.

    `witness[k, t]` is a rational point of the simplex. Always feasible (Q constant).
    Returns (value, Q).
    """
    T, d = len(P), len(P[0])
    nq = T * d
    n = 2 * nq  # q then e

    def qi(t, i):
        return t * d + i

    c = [Fraction(0)] * nq + [Fraction(1)] * nq
    A, b = [], []
    for t in range(T):
        for i in range(d):
            p = F(P[t][i])
            row = [Fraction(0)] * n
            row[qi(t, i)] = 1 / p
            row[nq + qi(t, i)] = Fraction(-1)
            A.append(row), b.append(Fraction(1))  # q/p - 1 <= e
            row = [Fraction(0)] * n
            row[qi(t, i)] = -1 / p
            row[nq + qi(t, i)] = Fraction(-1)
            A.append(row), b.append(Fraction(-1))  # 1 - q/p <= e
            row = [Fraction(0)] * n
            row[qi(t, i)] = Fraction(-1)
            A.append(row), b.append(Fraction(0))  # q >= 0
    for k, S in enumerate(sets):
        for t in S:
            xi = witness[k, t]
            for s in range(T):
                if s in S:
                    continue
                row = [Fraction(0)] * n
                for i in range(d):
                    row[qi(s, i)] -= F(xi[i])
                    row[qi(t, i)] += F(xi[i])
                A.append(row), b.append(Fraction(0))
    st, val, x = lp(c, A, b)
    assert st == "optimal", st
    Q = [[x[qi(t, i)] for i in range(d)] for t in range(T)]
    return val, Q


def verify(P, y, Q, sets, m, witness) -> Fraction:
    """Check an upper-bound certificate exactly; return pi_1(P, Q)."""
    T, d = len(P), len(P[0])
    assert all(F(q) >= 0 for row in Q for q in row), "Q >= 0"
    assert all(F(x) >= 0 for x in m), "m >= 0"
    for t in range(T):
        tot = sum((F(mk) for mk, S in zip(m, sets) if t in S), Fraction(0))
        assert tot == F(y[t]), f"cone: y_{t}"
    for k, S in enumerate(sets):
        for t in S:
            xi = [F(v) for v in witness[k, t]]
            assert all(v >= 0 for v in xi) and any(v > 0 for v in xi), "witness"
            for s in range(T):
                if s not in S:
                    gap = sum(xi[i] * (F(Q[s][i]) - F(Q[t][i])) for i in range(d))
                    assert gap >= 0, f"witness of {t} in S_{k} against {s}"
    return pi1(P, Q)
