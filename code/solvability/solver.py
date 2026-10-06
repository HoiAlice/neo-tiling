"""Deciding y and building h for a family of reachable spectra."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from typing import TYPE_CHECKING

from .cone import ConeOracle, Decomposition, Obstruction, Verdict
from .construction import Patching, Realization
from .general_position import GeneralPositioner, Report
from .prices import Prices, fmt_spectrum

if TYPE_CHECKING:
    from collections.abc import Iterable, Sequence

    from .prices import Spectrum


@dataclass
class Decision:
    prices: Prices
    y: list[F]
    verdict: Verdict

    @property
    def solvable(self) -> bool:
        return isinstance(self.verdict, Decomposition)

    def __str__(self) -> str:
        P = self.prices
        out = [f"T = {P.T}; reachable spectra: {len(P.reachable_spectra)} of {2**P.T}"]
        if P.coverings:
            out += ["coverings (p_t dominates a point of [p_s, p_r]):"]
            out += [f"  {c}" for c in P.describe_coverings()]
        if isinstance(self.verdict, Obstruction):
            lam = self.verdict
            out += [
                "NOT regularly solvable.  Obstruction (Farkas certificate):",
                f"  every solvable y satisfies  {lam.inequality()}",
                f"  here <lambda, y> = {lam.value(self.y)} < 0",
                f"  lambda = ({', '.join(map(str, lam.coefficients))})",
            ]
        else:
            out.append("Regularly solvable.  y = sum m_S 1_S:")
            out += [
                f"  {m} * 1_{fmt_spectrum(S)}" for S, m in self.verdict.masses.items()
            ]
        return "\n".join(out)


@dataclass
class Construction:
    """h with a point x_S of spectrum S for each prescribed S; masses, if given,
    turn the points into the measure sum_S m_S Uniform(ball(x_S, rho))."""

    prices: Prices
    realization: Realization
    report: Report | None = None
    masses: dict[Spectrum, F] | None = None

    def __str__(self) -> str:
        r = self.realization
        out = []
        if self.report is not None:
            out.append(
                "general position: NoSharedLine and GenericTriples verified "
                f"({self.report.lines} lines, "
                f"{self.report.rounds} perturbation round(s))"
            )
        out.append("h(x) = min_j (a_j x1 + b_j x2), (a_j, b_j):")
        out += [f"  ({a[0]}, {a[1]})" for a in r.h.lines]
        if r.points:
            rho = r.ball_radius(self.prices)
            out.append(f"points x_S of spectrum S (balls of radius {rho} stay in R_S):")
        for x, S in zip(r.points, r.spectra):
            mass = "" if self.masses is None else f", m = {self.masses[S]}"
            out.append(f"  S = {fmt_spectrum(S)}: x = ({x[0]}, {x[1]}){mass}")
        return "\n".join(out)


class Solver:
    def __init__(
        self, prices: Prices, *, general_position: bool = True, seed: int = 0
    ) -> None:
        self.prices = prices
        self.general_position = general_position
        self.seed = seed

    def decide(self, y: Sequence[F]) -> Decision:
        y = [F(v) for v in y]
        return Decision(self.prices, y, ConeOracle(self.prices).decide(y))

    def construct(
        self, spectra: Iterable[Spectrum], masses: dict[Spectrum, F] | None = None
    ) -> Construction:
        """The only place where h is built; ValueError for unreachable spectra."""
        realization = Patching(self.prices).realize(spectra)
        report = None
        if self.general_position:
            positioner = GeneralPositioner(self.prices, self.seed)
            realization, report = positioner.run(realization)
        return Construction(self.prices, realization, report, masses)
