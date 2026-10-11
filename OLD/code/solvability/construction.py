"""A piecewise linear h with prescribed spectra at chosen points (step 3, "склейка")."""

from __future__ import annotations

import math
from dataclasses import dataclass, replace
from fractions import Fraction as F
from typing import TYPE_CHECKING

from .geometry import Vec, hadamard, ip
from .prices import fmt_spectrum

if TYPE_CHECKING:
    from collections.abc import Iterable

    from .prices import Prices, Spectrum


@dataclass(frozen=True)
class PiecewiseLinear:
    """h(x) = min_j <lines[j], x>, lines in Q^2_{>0}: strictly positive neoclassical."""

    lines: tuple[Vec, ...]

    def __post_init__(self) -> None:
        assert self.lines and all(a[0] > 0 and a[1] > 0 for a in self.lines)

    def __call__(self, x: Vec) -> F:
        return min(ip(a, x) for a in self.lines)

    def active(self, x: Vec) -> list[int]:
        value = self(x)
        return [j for j, a in enumerate(self.lines) if ip(a, x) == value]

    def spectrum_at(self, prices: Prices, x: Vec) -> Spectrum | None:
        """{t : h(p_t o x) < 1}, or None if x lies on a curve."""
        values = [self(hadamard(p, x)) for p in prices.points]
        return (
            None if 1 in values else frozenset(t for t, v in enumerate(values) if v < 1)
        )


@dataclass(frozen=True)
class Realization:
    """h with points x_i such that the spectrum of x_i is S_i."""

    h: PiecewiseLinear
    points: tuple[Vec, ...]
    spectra: tuple[Spectrum, ...]

    def with_function(self, h: PiecewiseLinear) -> Realization:
        return replace(self, h=h)

    def images(self, prices: Prices) -> list[Vec]:
        return [hadamard(p, x) for x in self.points for p in prices.points]

    def spectra_hold(self, prices: Prices) -> bool:
        return all(
            self.h.spectrum_at(prices, x) == S
            for x, S in zip(self.points, self.spectra)
        )

    def margin(self, prices: Prices) -> F:
        """min |h(p_t o x_i) - 1|: positive iff all spectra are strict."""
        return min((abs(self.h(z) - 1) for z in self.images(prices)), default=F(1))

    def ball_radius(self, prices: Prices) -> F:
        """Balls of this radius around the x_i lie in the open orthant and, for every
        q_t with |q_t - p_t|_inf <= price_radius, inside the chamber R_S of (h, Q).

        h is Lipschitz in the l1 norm with constant L = max xi, and
        |q o x - p o x_i|_1 <= |q|_inf |x - x_i|_1 + |q - p|_inf |x_i|_1.  With
        |q|_inf <= 2 max p and |x - x_i|_1 <= 2 rho, rho = margin / (8 L max p) makes
        the first term at most margin / 2.
        """
        lipschitz = (
            8 * max(max(a) for a in self.h.lines) * max(max(p) for p in prices.points)
        )
        inside_orthant = min((min(x) for x in self.points), default=F(1)) / 2
        return min(self.margin(prices) / lipschitz, inside_orthant)

    def price_radius(self, prices: Prices) -> F:
        """Prices q_t with |q_t - p_t|_inf <= eps stay positive, |q|_inf <= 2 max p, and
        the second term of ball_radius stays at most margin / 4, so every h(q_t o x),
        x in a ball, differs from h(p_t o x_i) by less than the margin."""
        lines = max(max(a) for a in self.h.lines)
        spread = max((x[0] + x[1] for x in self.points), default=F(1))
        return min(
            self.margin(prices) / (4 * lines * spread),
            min(min(p) for p in prices.points) / 2,
        )


class Patching:
    def __init__(self, prices: Prices) -> None:
        self.prices = prices

    def separating_line(self, S: Spectrum, t: int) -> Vec:
        """xi with <xi, p_t> < 1 < <xi, p_s> for s not in S: direction (sigma, 1)
        with sigma between the slope bounds of the prices left and right of p_t."""
        w = self.prices[t]
        outside = [self.prices[s] for s in range(self.prices.T) if s not in S]
        if not outside:
            return (1 / (2 * (w[0] + w[1])),) * 2
        lower = [F(0)] + [(w[1] - z[1]) / (z[0] - w[0]) for z in outside if z[0] > w[0]]
        upper = [(z[1] - w[1]) / (w[0] - z[0]) for z in outside if z[0] < w[0]]
        sigma = (max(lower) + min(upper)) / 2 if upper else max(lower) + 1
        direction = (sigma, F(1))
        scale = 2 / (ip(direction, w) + min(ip(direction, z) for z in outside))
        return (sigma * scale, scale)

    def realize(self, spectra: Iterable[Spectrum]) -> Realization:
        """One h with a point of spectrum S for every given reachable S ("склейка").

        Copy i sits at x_i = (a_i, 1/a_i), a_{i+1} = M a_i.  Its separating lines,
        transported by the same scaling, exceed 1 on every other copy once
        M min(xi^1 p^1, xi^2 p^2) > 1.  The empty spectrum needs no point.
        """
        spectra = list(dict.fromkeys(S for S in spectra if S))
        unreachable = [S for S in spectra if not self.prices.is_reachable(S)]
        if unreachable:
            raise ValueError(
                "not reachable: " + ", ".join(map(fmt_spectrum, unreachable))
            )
        if not spectra:
            return Realization(PiecewiseLinear(((F(1), F(1)),)), (), ())
        lines = [
            (i, self.separating_line(S, t)) for i, S in enumerate(spectra) for t in S
        ]
        threshold = max(
            1 / min(xi[0] * p[0], xi[1] * p[1])
            for _, xi in lines
            for p in self.prices.points
        )
        M = F(math.floor(threshold) + 2)
        realization = Realization(
            PiecewiseLinear(tuple((xi[0] / M**i, xi[1] * M**i) for i, xi in lines)),
            tuple((M**i, 1 / M**i) for i in range(len(spectra))),
            tuple(spectra),
        )
        assert realization.spectra_hold(self.prices), "patching failed"
        return realization
