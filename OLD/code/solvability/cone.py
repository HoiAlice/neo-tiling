"""Membership of y in cone{1_S : S reachable}, with an exact certificate (step 2).

The LP is solved in floating point to guess a basis (primal) or a vertex (dual); the
guess is re-solved and checked over Q.  If that fails, an exact rational simplex
decides.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from typing import TYPE_CHECKING, Union

import numpy as np
import sympy
from scipy.optimize import linprog
from sympy.solvers.simplex import InfeasibleLPError
from sympy.solvers.simplex import linprog as exact_linprog

from .geometry import solve_linear

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator, Sequence

    from .prices import Prices, Spectrum

_ZERO = 1e-9  # float LP values below this are treated as zero
_ACTIVE = 1e-7  # tolerance for active constraints of a float LP vertex


@dataclass(frozen=True)
class Decomposition:
    masses: dict[Spectrum, F]

    def vector(self, T: int) -> list[F]:
        return [
            sum((m for S, m in self.masses.items() if t in S), F(0)) for t in range(T)
        ]


@dataclass(frozen=True)
class Obstruction:
    coefficients: list[F]

    def value(self, y: Sequence[F]) -> F:
        return sum((c * v for c, v in zip(self.coefficients, y)), F(0))

    def nonnegative_on(self, spectra: Iterable[Spectrum]) -> bool:
        return all(sum((self.coefficients[t] for t in S), F(0)) >= 0 for S in spectra)

    def inequality(self) -> str:
        terms = list(enumerate(self.coefficients))
        lhs = " + ".join(f"{-c}*y_{t + 1}" for t, c in terms if c < 0) or "0"
        rhs = " + ".join(f"{c}*y_{t + 1}" for t, c in terms if c > 0) or "0"
        return f"{lhs} <= {rhs}"


Verdict = Union[Decomposition, Obstruction]


def _rational(v) -> F:
    v = sympy.Rational(v)
    return F(int(v.p), int(v.q))


def _sympy(v: F) -> sympy.Rational:
    return sympy.Rational(v.numerator, v.denominator)


class ConeOracle:
    def __init__(self, prices: Prices) -> None:
        self.T = prices.T
        self.spectra = [S for S in prices.reachable_spectra if S]
        self.incidence = np.array(
            [[1.0 if t in S else 0.0 for S in self.spectra] for t in range(self.T)]
        )

    def decide(self, y: Sequence[F]) -> Verdict:
        if any(v < 0 for v in y):
            raise ValueError("y must be nonnegative")
        for attempt in (
            self._primal_guess,
            self._dual_guess,
            self._primal_exact,
            self._dual_exact,
        ):
            verdict = attempt(y)
            if verdict is not None and self.verify(y, verdict):
                return verdict
        raise RuntimeError("could not decide exactly; please report this instance")

    def verify(self, y: Sequence[F], verdict: Verdict) -> bool:
        if isinstance(verdict, Decomposition):
            return all(
                S in self.spectra and m > 0 for S, m in verdict.masses.items()
            ) and verdict.vector(self.T) == list(y)
        return verdict.nonnegative_on(self.spectra) and verdict.value(y) < 0

    def _primal_guess(self, y: Sequence[F]) -> Decomposition | None:
        res = linprog(
            np.zeros(len(self.spectra)),
            A_eq=self.incidence,
            b_eq=[float(v) for v in y],
            bounds=(0, None),
            method="highs",
        )
        if res.status != 0:
            return None
        support = [j for j, v in enumerate(res.x) if v > _ZERO]
        rows = [
            [F(1) if t in self.spectra[j] else F(0) for j in support]
            for t in range(self.T)
        ]
        m = solve_linear(rows, list(y)) if support else []
        if m is None or any(v < 0 for v in m):
            return None
        return Decomposition({self.spectra[j]: v for j, v in zip(support, m) if v > 0})

    def _dual_guess(self, y: Sequence[F]) -> Obstruction | None:
        res = linprog(
            [float(v) for v in y],
            A_ub=-self.incidence.T,
            b_ub=np.zeros(len(self.spectra)),
            bounds=(-1, 1),
            method="highs",
        )
        if res.status != 0 or res.fun > -_ZERO:
            return None
        return next(
            (
                Obstruction(lam)
                for lam in self._rationalise(res.x)
                if self.verify(y, Obstruction(lam))
            ),
            None,
        )

    def _rationalise(self, lam: np.ndarray) -> Iterator[list[F]]:
        """Round to small denominators, then re-solve the active constraints."""
        for den in (1, 2, 3, 4, 6, 12, 60, 840):
            yield [F(round(v * den), den) for v in lam]
        rows, rhs = [], []
        for S in self.spectra:
            if abs(sum(lam[t] for t in S)) < _ACTIVE:
                rows.append([F(t in S) for t in range(self.T)])
                rhs.append(F(0))
        for t in range(self.T):
            if abs(abs(lam[t]) - 1) < _ACTIVE:
                rows.append([F(u == t) for u in range(self.T)])
                rhs.append(F(round(lam[t])))
        exact = solve_linear(rows, rhs) if rows else None
        if exact is not None:
            yield exact

    def _primal_exact(self, y: Sequence[F]) -> Decomposition | None:
        """Equalities as two inequality blocks: sympy wants A x <= b, x >= 0."""
        A = self.incidence.astype(int)
        b = [_sympy(v) for v in y]
        try:
            _, x = exact_linprog(
                sympy.zeros(1, len(self.spectra)),
                sympy.Matrix(np.vstack([A, -A]).tolist()),
                sympy.Matrix(b + [-v for v in b]),
            )
        except InfeasibleLPError:
            return None
        return Decomposition(
            {S: _rational(v) for S, v in zip(self.spectra, x) if v > 0}
        )

    def _dual_exact(self, y: Sequence[F]) -> Obstruction | None:
        """Shifted variables mu = lambda + 1 in [0, 2]: sympy assumes mu >= 0."""
        A = sympy.Matrix(
            np.vstack([-self.incidence.T, np.eye(self.T)]).astype(int).tolist()
        )
        b = sympy.Matrix([-len(S) for S in self.spectra] + [2] * self.T)
        _, mu = exact_linprog(sympy.Matrix([[_sympy(v) for v in y]]), A, b)
        return Obstruction([_rational(v) - 1 for v in mu])
