"""Reading a solution: which prices moved, in which periods, and by how much."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .model import Solution


def changes(
    solution: Solution,
    periods: list[str] | None = None,
    factors: list[str] | None = None,
) -> list[tuple[str, str, float, float]]:
    """(period, factor, multiplier a, perturbation pi) for every coordinate, sorted by
    the perturbation, largest first. The multipliers are invariant under the
    normalization, so they read directly as relative price changes."""
    rows = []
    for t, row in enumerate(solution.a):
        for i, a in enumerate(row):
            period = periods[t] if periods else str(t + 1)
            factor = factors[i] if factors else str(i + 1)
            rows.append((period, factor, a, max(a, 1 / a) - 1))
    rows.sort(key=lambda r: -r[3])
    return rows


def describe(
    solution: Solution,
    periods: list[str] | None = None,
    factors: list[str] | None = None,
    top: int = 15,
    threshold: float = 1e-4,
) -> str:
    rows = [r for r in changes(solution, periods, factors) if r[3] > threshold]
    lines = [
        f"status={solution.status}  value={solution.value:.6g}  "
        f"bound={solution.bound:.6g}  time={solution.seconds:.0f}s",
        f"{len(rows)} coordinates moved; the largest:",
    ]
    for period, factor, a, p in rows[:top]:
        sign = "+" if a > 1 else "-"
        lines.append(
            f"  {period:>6} {factor:<14} {sign}{100 * abs(a - 1):6.2f}%   pi={p:.4f}"
        )
    by_period: dict[str, float] = {}
    by_factor: dict[str, float] = {}
    for period, factor, _, p in rows:
        by_period[period] = by_period.get(period, 0.0) + p
        by_factor[factor] = by_factor.get(factor, 0.0) + p
    lines.append(
        "by period: "
        + ", ".join(
            f"{k}: {v:.3f}"
            for k, v in sorted(by_period.items(), key=lambda kv: -kv[1])[:top]
        )
    )
    lines.append(
        "by factor: "
        + ", ".join(
            f"{k}: {v:.3f}" for k, v in sorted(by_factor.items(), key=lambda kv: -kv[1])
        )
    )

    def label(S: frozenset[int]) -> str:
        return ",".join(periods[t] if periods else str(t + 1) for t in sorted(S))

    lines.append(
        "spectra: " + "; ".join(f"{{{label(S)}}}={m:.3g}" for S, m in solution.spectra)
    )
    return "\n".join(lines)
