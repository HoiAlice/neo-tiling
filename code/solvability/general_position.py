"""General position of (h, P) for piecewise linear h (step 4).

By the Lean theorem generalPosition_polyMin_of_triples it suffices to check two finite
conditions: NoSharedLine (at a common point of two curves different lines are active)
and GenericTriples (no three vectors xi_j o p_t are collinear, except three collinear
prices on one line).  h is replaced by chords of a strictly convex curve, refined only
where something fails, then perturbed on a grid (Schwartz-Zippel: success probability
>= 1/2 per round).
"""

from __future__ import annotations

import itertools
import math
import random
from dataclasses import dataclass
from fractions import Fraction as F
from typing import TYPE_CHECKING, Callable

from .construction import PiecewiseLinear, Realization
from .geometry import Vec, common_point, det, hadamard, line_through

if TYPE_CHECKING:
    from .prices import Prices


@dataclass
class Report:
    lines: int
    rounds: int
    grid: int


class GeneralPositioner:
    def __init__(self, prices: Prices, seed: int = 0) -> None:
        self.prices = prices
        self.rng = random.Random(seed)
        pairs = itertools.combinations(range(prices.T), 2)
        self.crossings = [
            (s, t, y)
            for s, t in pairs
            if (y := common_point(prices[s], prices[t])) is not None and min(y) >= 0
        ]

    def run(self, realization: Realization) -> tuple[Realization, Report]:
        return self.perturb(self.refine(realization))

    # -- conditions

    def _shared_line_points(self, a: Vec):
        """Images of the points where line a would carry the curves of both s and t."""
        for s, t, y in self.crossings:
            x = (y[0] / a[0], y[1] / a[1])
            yield hadamard(self.prices[s], x), hadamard(self.prices[t], x)

    def shared_line_violations(self, h: PiecewiseLinear) -> list[int]:
        return [
            j
            for j, a in enumerate(h.lines)
            if any(h(zs) == 1 and h(zt) == 1 for zs, zt in self._shared_line_points(a))
        ]

    def has_generic_triples(self, h: PiecewiseLinear) -> bool:
        P = self.prices
        labelled = [
            ((j, t), hadamard(a, P[t]))
            for j, a in enumerate(h.lines)
            for t in range(P.T)
        ]
        for i, ((j0, t0), a0) in enumerate(labelled):
            directions: dict[Vec, list[tuple[int, int]]] = {}
            for (j, t), a in labelled[i + 1 :]:
                d = (a[0] - a0[0], a[1] - a0[1])
                if d == (0, 0):
                    return False
                key = (F(1), d[1] / d[0]) if d[0] else (F(0), F(1))
                directions.setdefault(key, []).append((j, t))
            for group in directions.values():
                for (j1, t1), (j2, t2) in itertools.combinations(group, 2):
                    forced = (
                        j0 == j1 == j2
                        and det(
                            (P[t0][0] - P[t1][0], P[t0][1] - P[t1][1]),
                            (P[t0][0] - P[t2][0], P[t0][1] - P[t2][1]),
                        )
                        == 0
                    )
                    if not forced:
                        return False
        return True

    # -- refinement: chords of a strictly convex curve, bisected only where needed

    @staticmethod
    def _chords(H: Callable[[Vec], F], ratios: list[F]) -> PiecewiseLinear:
        """Polygon inscribed in {H = 1}, vertices on the axes and at (1, r)."""
        vertices = [(1 / H((F(1), F(0))), F(0))]
        vertices += [(1 / H((F(1), r)), r / H((F(1), r))) for r in ratios]
        vertices.append((F(0), 1 / H((F(0), F(1)))))
        return PiecewiseLinear(
            tuple(line_through(a, b) for a, b in zip(vertices, vertices[1:]))
        )

    @staticmethod
    def _split(ratios: list[F], j: int) -> F:
        """New node in chord j: geometric midpoint, or a step towards the axis."""
        if j == 0:
            return ratios[0] / 4
        if j == len(ratios):
            return ratios[-1] * 4
        lo, hi = ratios[j - 1], ratios[j]
        g = F(math.sqrt(lo * hi)).limit_denominator(10**12)
        return g if lo < g < hi else (lo + hi) / 2

    def refine(self, realization: Realization) -> Realization:
        P, h = self.prices, realization.h
        images = realization.images(P)

        def harmonic(z):
            return z[0] * z[1] / (z[0] + z[1])

        eps = (
            realization.margin(P) / (2 * max(map(harmonic, images)) + 1)
            if images
            else F(1, 4)
        )

        def H(z):
            return h(z) + eps * harmonic(z)

        ratios = sorted({z[1] / z[0] for z in images} or {F(1)})
        while True:
            g = self._chords(H, ratios)
            failing: set[int] = set(self.shared_line_violations(g))
            for x, S in zip(realization.points, realization.spectra):
                for t, p in enumerate(P.points):
                    z = hadamard(p, x)
                    if g(z) == 1 or (g(z) < 1) != (t in S):
                        failing.update(g.active(z))
            if not failing:
                return realization.with_function(g)
            ratios = sorted(set(ratios) | {self._split(ratios, j) for j in failing})

    # -- perturbation

    def _step(self, realization: Realization) -> F:
        """Grid step keeping strict spectra and NoSharedLine (Lipschitz bounds)."""
        P, h = self.prices, realization.h
        images = realization.images(P)
        xi_max, xi_min = max(max(a) for a in h.lines), min(min(a) for a in h.lines)
        bounds = [xi_min / 2]
        if images:
            bounds.append(
                realization.margin(P) / (2 * max(z[0] + z[1] for z in images))
            )
        for a in h.lines:
            for zs, zt in self._shared_line_points(a):
                slack = max(1 - h(zs), 1 - h(zt))
                spread = max(z[0] + z[1] for z in (zs, zt)) * (1 + 2 * xi_max / xi_min)
                bounds.append(slack / (2 * spread))
        return min(bounds)

    def perturb(self, realization: Realization) -> tuple[Realization, Report]:
        h = realization.h
        grid = max(2 * math.comb(len(h.lines) * self.prices.T, 3), 1)
        delta = self._step(realization) / grid
        for rounds in itertools.count(1):
            shifted = tuple(
                (
                    a[0] + delta * self.rng.randint(-grid, grid),
                    a[1] + delta * self.rng.randint(-grid, grid),
                )
                for a in h.lines
            )
            candidate = realization.with_function(PiecewiseLinear(shifted))
            if not candidate.spectra_hold(self.prices) or self.shared_line_violations(
                candidate.h
            ):
                delta /= 2  # excluded by the choice of delta; a safeguard only
            elif self.has_generic_triples(candidate.h):
                return candidate, Report(len(h.lines), rounds, grid)
        raise AssertionError("unreachable")
