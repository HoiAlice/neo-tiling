"""Exact verification of a solver answer (notes, remark on exact checking).

`rational` converts the floating-point answer to rationals with a given denominator, and
`verify` checks a rational answer exactly: for every spectrum S_k and every t in S_k
the weak witness condition xi >= 0, xi != 0, <xi, q_s - q_t> >= 0 for s not in S_k, the
masses from sum_k m_k 1_{S_k} = y, and the value pi(P, Q). A certified answer is a
weakly solvable price set, so pi(P, Q) is an upper bound on rho(P, y) (notes, lem:min).

The optimum lies on the boundary of solvability, so a naive conversion may break a
witness inequality by a tiny amount; the report lists the violated pairs with the exact
defect. Moving the answer to really solvable prices within the solver tolerances is a
separate task.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import TYPE_CHECKING

import sympy

if TYPE_CHECKING:
    from .model import Solution
    from .prep import Problem

Vec = tuple[Fraction, ...]


def pert(p: Fraction, q: Fraction) -> Fraction:
    return max(q / p, p / q) - 1


@dataclass
class Verification:
    Q: tuple[Vec, ...]  # exact prices in the original coordinates
    total_pert: Fraction
    masses: dict[frozenset[int], Fraction]
    witness_defects: list[tuple[int, int, int, Fraction]] = field(default_factory=list)
    mass_error: Fraction = Fraction(0)

    @property
    def certified(self) -> bool:
        return not self.witness_defects and self.mass_error == 0

    def __str__(self) -> str:
        lines = [f"pi(P, Q) = {self.total_pert} ~ {float(self.total_pert):.6g}"]
        for t, q in enumerate(self.Q):
            lines.append(f"  q_{t + 1} = ({', '.join(str(c) for c in q)})")
        for S, mass in self.masses.items():
            lines.append(f"  m{{{','.join(str(t + 1) for t in sorted(S))}}} = {mass}")
        if self.witness_defects:
            lines.append("  witness defects (k, t, s, <xi, q_s - q_t>):")
            lines.extend(
                f"    k={k + 1} t={t + 1} s={s + 1}: {float(v):.3g}"
                for k, t, s, v in self.witness_defects
            )
        if self.mass_error:
            lines.append(f"  mass equation residual: {float(self.mass_error):.3g}")
        lines.append("  certified" if self.certified else "  NOT certified")
        return "\n".join(lines)


@dataclass(frozen=True)
class Rational:
    """A solver answer converted to exact rationals: multipliers, spectra, witnesses."""

    a: tuple[Vec, ...]
    spectra: tuple[frozenset[int], ...]
    witnesses: dict[tuple[int, int], Vec]


def rational(solution: Solution, denominator: int) -> Rational:
    """Plain conversion of the floating-point answer with `limit_denominator`. Finding
    nearby prices that are really (weakly) solvable within the solver tolerances is a
    separate task and is deliberately not attempted here."""

    def conv(x: float) -> Fraction:
        return Fraction(x).limit_denominator(denominator)

    return Rational(
        a=tuple(tuple(conv(x) for x in row) for row in solution.a),
        spectra=tuple(S for S, _ in solution.spectra),
        witnesses={
            key: tuple(max(conv(x), Fraction(0)) for x in xi)
            for key, xi in solution.witnesses.items()
        },
    )


def verify(problem: Problem, answer: Rational) -> Verification:
    """Exact check of a rational answer; no rounding happens here."""
    T, d = problem.T, problem.d
    Q = tuple(
        tuple(problem.P[t][i] * answer.a[t][i] for i in range(d)) for t in range(T)
    )
    total = sum(pert(problem.P[t][i], Q[t][i]) for t in range(T) for i in range(d))
    defects = []
    for k, S in enumerate(answer.spectra):
        for t in S:
            xi = answer.witnesses.get((k, t))
            if xi is None or sum(xi) == 0:
                defects.append((k, t, t, Fraction(0)))
                continue
            for s in range(T):
                if s in S:
                    continue
                value = sum(xi[i] * (Q[s][i] - Q[t][i]) for i in range(d))
                if value < 0:
                    defects.append((k, t, s, value))
    masses, error = exact_masses(list(answer.spectra), problem.y)
    return Verification(Q, total, masses, defects, error)


def exact_masses(
    spectra: list[frozenset[int]], y: tuple[Fraction, ...]
) -> tuple[dict[frozenset[int], Fraction], Fraction]:
    """Solve sum_k m_k 1_{S_k} = y exactly (free parameters set to zero); the second
    value is the residual: the total negative mass, or |y| if there is no solution."""
    T = len(y)
    if not spectra:
        return {}, sum(abs(v) for v in y)
    A = sympy.Matrix([[1 if t in S else 0 for S in spectra] for t in range(T)])
    b = sympy.Matrix([sympy.Rational(v.numerator, v.denominator) for v in y])
    try:
        sol, params = A.gauss_jordan_solve(b)
    except ValueError:
        return {S: Fraction(0) for S in spectra}, sum(abs(v) for v in y)
    sol = sol.subs(dict.fromkeys(params, 0))
    masses = {S: Fraction(int(sol[k].p), int(sol[k].q)) for k, S in enumerate(spectra)}
    if any(v < 0 for v in masses.values()):
        residual = sum(abs(v) for v in masses.values() if v < 0)
        return masses, residual
    return masses, Fraction(0)
