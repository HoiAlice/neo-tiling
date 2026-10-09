"""Weak solvability at fixed prices (the case rho = 0), exactly certified both ways.

A spectrum S is weakly reachable at P iff every t in S has a weak witness: xi >= 0,
sum xi = 1, <xi, p_s - p_t> >= 0 for all s not in S. By LP duality no witness exists iff
t strictly covers the complement: sum_s w_s p_s < p_t coordinatewise for convex weights
w. y is weakly solvable iff y lies in the cone of the indicators of the weakly reachable
spectra; by Farkas, otherwise some lambda has sum_{t in S} lambda_t >= 0 on every weakly
reachable S and <lambda, y> < 0 (the refutations of the notes, chapter 4).

All LPs run in floating point; the objects they return (witnesses and masses, or strict
coverings and a refutation) are converted to rationals and checked exactly, so both
answers are certified. If a certificate fails the exact check the result is `None`.
Enumeration of spectra is exponential in T; use it for T up to about 16.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from fractions import Fraction
from typing import TYPE_CHECKING

import numpy as np
from scipy.optimize import linprog

from .verify import exact_masses

if TYPE_CHECKING:
    from .prep import Problem

MAX_T = 16
DENOMINATOR = 10**9
EPS = 1e-9

Spectrum = frozenset[int]
Vec = tuple[Fraction, ...]


def _frac(v: float) -> Fraction:
    return Fraction(float(v)).limit_denominator(DENOMINATOR)


def _spectra(T: int):
    for n in range(1, T + 1):
        for S in itertools.combinations(range(T), n):
            yield frozenset(S)


@dataclass(frozen=True)
class WeakSolvability:
    """`solvable` is None when neither certificate passed the exact check."""

    solvable: bool | None
    masses: dict[Spectrum, Fraction] = field(default_factory=dict)
    witnesses: dict[tuple[Spectrum, int], Vec] = field(default_factory=dict)
    coverings: dict[tuple[Spectrum, int], Vec] = field(default_factory=dict)
    refutation: Vec = ()
    reachable: tuple[Spectrum, ...] = ()


def witness_or_covering(
    problem: Problem, S: Spectrum, t: int
) -> tuple[str, Vec | None]:
    """An exact weak witness of t for S, or an exact strict covering of S^c by t.

    The LP  max eps  s.t.  sum_s w_s p_s + eps 1 <= p_t,  w in the simplex on S^c
    has value eps* > 0 iff t strictly covers; its dual is the witness when eps* <= 0."""
    P, d, T = problem.P, problem.d, problem.T
    others = [s for s in range(T) if s not in S]
    if not others:
        return "witness", tuple([Fraction(1)] + [Fraction(0)] * (d - 1))
    Pf = [[float(c) for c in p] for p in P]
    n = len(others)
    c = np.zeros(n + 1)
    c[-1] = -1.0  # maximize eps, the last variable
    A_ub = np.array([[Pf[s][i] for s in others] + [1.0] for i in range(d)])
    b_ub = np.array([Pf[t][i] for i in range(d)])
    res = linprog(
        c,
        A_ub=A_ub,
        b_ub=b_ub,
        A_eq=np.array([[1.0] * n + [0.0]]),
        b_eq=[1.0],
        bounds=[(0, None)] * n + [(None, None)],
        method="highs",
    )
    if res.status != 0:
        return "undecided", None
    if res.x[-1] > EPS:
        w = [_frac(v) for v in res.x[:-1]]
        total = sum(w)
        if total == 0:
            return "undecided", None
        w = [v / total for v in w]
        strict = all(
            sum(w[j] * P[s][i] for j, s in enumerate(others)) < P[t][i]
            for i in range(d)
        )
        return ("covering", tuple(w)) if strict else ("undecided", None)
    xi = [max(_frac(-v), Fraction(0)) for v in res.ineqlin.marginals]
    total = sum(xi)
    if total == 0:
        return "undecided", None
    xi = [v / total for v in xi]
    valid = all(sum(xi[i] * (P[s][i] - P[t][i]) for i in range(d)) >= 0 for s in others)
    return ("witness", tuple(xi)) if valid else ("undecided", None)


def weakly_reachable(problem: Problem):
    """Weakly reachable spectra with exact witnesses, and exact strict coverings for the
    others (a spectrum without either is treated as undecided and left out of both)."""
    witnesses, coverings, reachable, undecided = {}, {}, [], []
    for S in _spectra(problem.T):
        found = {}
        for t in S:
            kind, obj = witness_or_covering(problem, S, t)
            if kind != "witness":
                if kind == "covering":
                    coverings[S, t] = obj
                else:
                    undecided.append(S)
                found = None
                break
            found[t] = obj
        if found is not None:
            witnesses.update({(S, t): xi for t, xi in found.items()})
            reachable.append(S)
    return reachable, witnesses, coverings, undecided


def weakly_solvable(problem: Problem) -> WeakSolvability:  # noqa: PLR0911
    """Decide y in cone{1_S : S weakly reachable at P} with exact certificates."""
    if problem.T > MAX_T:
        raise ValueError(f"T = {problem.T} too large for enumeration")
    T = problem.T
    reachable, witnesses, coverings, undecided = weakly_reachable(problem)
    y = np.array([float(v) for v in problem.y])
    if not reachable:
        return WeakSolvability(bool(np.all(y == 0)))
    A = np.array([[1.0 if t in S else 0.0 for S in reachable] for t in range(T)])
    res = linprog(
        np.ones(len(reachable)),
        A_eq=A,
        b_eq=y,
        bounds=[(0, None)] * len(reachable),
        method="highs",
    )
    if res.status == 0:
        support = [S for S, v in zip(reachable, res.x) if v > EPS]
        masses, error = exact_masses(support, problem.y)
        if error == 0:
            return WeakSolvability(
                True, masses, witnesses, coverings, (), tuple(reachable)
            )
        return WeakSolvability(None, reachable=tuple(reachable))
    if undecided:
        return WeakSolvability(None, reachable=tuple(reachable))
    # refutation: min <lambda, y> with sum_{t in S} lambda_t >= 0 on reachable S
    res = linprog(
        y,
        A_ub=-A.T,
        b_ub=np.zeros(len(reachable)),
        bounds=[(-1, 1)] * T,
        method="highs",
    )
    if res.status != 0:
        return WeakSolvability(None, reachable=tuple(reachable))
    lam = tuple(_frac(v) for v in res.x)
    valid = sum(lam[t] * problem.y[t] for t in range(T)) < 0 and all(
        sum(lam[t] for t in S) >= 0 for S in reachable
    )
    if not valid:
        return WeakSolvability(None, reachable=tuple(reachable))
    return WeakSolvability(False, {}, witnesses, coverings, lam, tuple(reachable))
