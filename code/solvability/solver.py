"""The four steps put together, and a printable result."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from typing import TYPE_CHECKING

from .cone import ConeOracle, Decomposition, Obstruction, Verdict
from .construction import Patching, Realization
from .general_position import GeneralPositioner, Report
from .prices import Prices, fmt_spectrum

if TYPE_CHECKING:
    from collections.abc import Sequence


@dataclass
class Result:
    prices: Prices
    y: list[F]
    verdict: Verdict
    realization: Realization | None = None
    report: Report | None = None

    @property
    def solvable(self) -> bool:
        return isinstance(self.verdict, Decomposition)

    def __str__(self) -> str:
        P = self.prices
        out = [f"T = {P.T}; reachable spectra: {len(P.reachable_spectra)} of {2**P.T}"]
        if P.coverings:
            out += ["coverings (p_t dominates a point of [p_s, p_r]):"] + [
                f"  {c}" for c in P.describe_coverings()
            ]
        if isinstance(self.verdict, Obstruction):
            lam = self.verdict
            out += [
                "NOT regularly solvable.  Obstruction (Farkas certificate):",
                f"  every solvable y satisfies  {lam.inequality()}",
                f"  here <lambda, y> = {lam.value(self.y)} < 0",
                f"  lambda = ({', '.join(map(str, lam.coefficients))})",
            ]
            return "\n".join(out)
        out.append("Regularly solvable.  y = sum m_S 1_S:")
        out += [f"  {m} * 1_{fmt_spectrum(S)}" for S, m in self.verdict.masses.items()]
        if self.realization is None:
            return "\n".join(out)
        if self.report is not None:
            out.append(
                f"general position: NoSharedLine and GenericTriples verified "
                f"({self.report.lines} lines, "
                f"{self.report.rounds} perturbation round(s))"
            )
        out.append("h(x) = min_j (a_j x1 + b_j x2), (a_j, b_j):")
        out += [f"  ({a[0]}, {a[1]})" for a in self.realization.h.lines]
        if self.realization.points:
            out.append(
                f"mu = sum_i m_i Uniform(ball(x_i, {self.realization.ball_radius(P)})):"
            )
            out += [
                f"  x = ({x[0]}, {x[1]}), m = {m}, S(x) = {fmt_spectrum(S)}"
                for x, m, S in zip(
                    self.realization.points,
                    self.realization.masses,
                    self.realization.spectra,
                )
            ]
        return "\n".join(out)


class Solver:
    def __init__(
        self,
        prices: Prices,
        *,
        construct: bool = True,
        general_position: bool = True,
        seed: int = 0,
    ) -> None:
        self.prices = prices
        self.construct = construct
        self.general_position = general_position
        self.seed = seed

    def solve(self, y: Sequence[F]) -> Result:
        y = [F(v) for v in y]
        verdict = ConeOracle(self.prices).decide(y)
        result = Result(self.prices, y, verdict)
        if isinstance(verdict, Obstruction) or not self.construct:
            return result
        realization = Patching(self.prices).realize(verdict)
        if self.general_position:
            realization, result.report = GeneralPositioner(self.prices, self.seed).run(
                realization
            )
        result.realization = realization
        return result
