"""Preparation before the solver (notes, remark "Подготовка задачи").

1. Normalization: the problem is invariant under p^i_t -> lambda_i p^i_t with one
   lambda_i per coordinate; we scale so that max_t p^i_t = 1.
2. The bound D(kappa) = sum_t (max(kappa / (p^1_t p^2_t), p^1_t p^2_t / kappa) - 1),
   minimized over kappa (convex in log kappa, one pass over the sorted products).
3. The start point: q^2_t = kappa / p^1_t, singleton spectra, witnesses
   (1/q^1_t, 1/q^2_t, 0, ...).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction

Vec = tuple[Fraction, ...]
MIN_DIM = 2  # the hyperbola bound uses the first two coordinates


@dataclass(frozen=True)
class Problem:
    """Prices P (rows p_t) and outputs y, exact rationals."""

    P: tuple[Vec, ...]
    y: tuple[Fraction, ...]
    periods: tuple[str, ...] | None = None  # labels of t, e.g. years
    factors: tuple[str, ...] | None = None  # labels of i, e.g. input names

    def __post_init__(self) -> None:
        if not self.P or len(self.P) != len(self.y):
            raise ValueError("P and y must have the same positive length T")
        if self.periods is not None and len(self.periods) != len(self.P):
            raise ValueError("one period label per observation")
        if self.factors is not None and len(self.factors) != len(self.P[0]):
            raise ValueError("one factor label per coordinate")
        d = len(self.P[0])
        if d < MIN_DIM or any(len(p) != d for p in self.P):
            raise ValueError("all prices must have the same dimension d >= 2")
        if any(c <= 0 for p in self.P for c in p):
            raise ValueError("prices must be strictly positive")
        if any(v < 0 for v in self.y):
            raise ValueError("outputs must be nonnegative")

    @property
    def T(self) -> int:
        return len(self.P)

    @property
    def d(self) -> int:
        return len(self.P[0])

    @classmethod
    def parse(cls, prices: str, outputs: str) -> Problem:
        """'4,1;3,3;1,4' and '1,5,3'."""
        P = tuple(
            tuple(Fraction(c.strip()) for c in row.split(","))
            for row in prices.split(";")
        )
        y = tuple(Fraction(v.strip()) for v in outputs.split(","))
        return cls(P, y)


@dataclass(frozen=True)
class Prepared:
    """Normalized problem with the bound and the start point."""

    problem: Problem
    scale: tuple[Fraction, ...]  # lambda_i, normalized price = lambda_i * price
    P: tuple[tuple[float, ...], ...]  # normalized prices, floats for the solver
    y: tuple[float, ...]
    kappa: float
    D: float
    start_a: tuple[tuple[float, ...], ...]  # multipliers of the start point, a = q / p

    @property
    def T(self) -> int:
        return self.problem.T

    @property
    def d(self) -> int:
        return self.problem.d


def hyperbola_bound(products: list[float], kappa: float) -> float:
    return sum(max(kappa / pi, pi / kappa) - 1 for pi in products)


def best_kappa(products: list[float]) -> float:
    """Minimizer of D(kappa). D is convex in log kappa; between consecutive sorted
    products the stationary point is kappa_k = sqrt(sum_upper pi / sum_lower 1/pi), so
    the minimum is one of these points or a kink pi_(k)."""
    s = sorted(products)
    candidates = list(s)
    for k in range(1, len(s)):
        lower, upper = s[:k], s[k:]
        candidates.append(math.sqrt(sum(upper) / sum(1 / pi for pi in lower)))
    return min(candidates, key=lambda kappa: hyperbola_bound(s, kappa))


def prepare(problem: Problem, slack: float = 1e-6) -> Prepared:
    """Normalize, choose kappa, compute D = D(kappa) (1 + slack) and the start point."""
    scale = tuple(1 / max(p[i] for p in problem.P) for i in range(problem.d))
    P = tuple(tuple(float(c * s) for c, s in zip(p, scale)) for p in problem.P)
    products = [p[0] * p[1] for p in P]
    kappa = best_kappa(products)
    D = hyperbola_bound(products, kappa) * (1 + slack)
    start_a = tuple(
        tuple(kappa / (p[0] * p[1]) if i == 1 else 1.0 for i in range(problem.d))
        for p in P
    )
    return Prepared(
        problem=problem,
        scale=scale,
        P=P,
        y=tuple(float(v) for v in problem.y),
        kappa=kappa,
        D=D,
        start_a=start_a,
    )
