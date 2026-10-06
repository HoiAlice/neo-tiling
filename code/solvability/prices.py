"""Prices, coverings and reachable spectra (step 1)."""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cached_property
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .geometry import Vec

Spectrum = frozenset[int]


def fmt_spectrum(S: Spectrum) -> str:
    return "{" + ",".join(str(t + 1) for t in sorted(S)) + "}"


@dataclass(frozen=True)
class Prices:
    points: tuple[Vec, ...]

    def __post_init__(self) -> None:
        if any(p[0] <= 0 or p[1] <= 0 for p in self.points):
            raise ValueError("prices must be strictly positive")
        for s, t in itertools.combinations(range(self.T), 2):
            if self[s][0] == self[t][0] or self[s][1] == self[t][1]:
                raise ValueError(f"prices {s + 1} and {t + 1} share a coordinate")

    @classmethod
    def parse(cls, text: str) -> Prices:
        return cls(
            tuple(
                tuple(F(c.strip()) for c in item.split(",")) for item in text.split(";")
            )
        )

    def __getitem__(self, t: int) -> Vec:
        return self.points[t]

    @property
    def T(self) -> int:
        return len(self.points)

    def covers(self, t: int, s: int, r: int) -> bool:
        """p_t >= mu p_s + (1 - mu) p_r for some mu in [0, 1]: two intervals meet."""
        lo, hi = F(0), F(1)
        for c in range(2):
            a, b = self[s][c] - self[r][c], self[t][c] - self[r][c]
            if a > 0:
                hi = min(hi, b / a)
            elif a < 0:
                lo = max(lo, b / a)
            elif b < 0:
                return False
        return lo <= hi

    @cached_property
    def coverings(self) -> list[tuple[int, int, int]]:
        """(t, s, r), s <= r, t covering {s, r}; triples implied by pairs dropped."""
        idx = range(self.T)
        pairs = [(t, s, s) for t in idx for s in idx if t != s and self.covers(t, s, s)]
        dominated = {(t, s) for t, s, _ in pairs}
        triples = [
            (t, s, r)
            for t in idx
            for s, r in itertools.combinations(idx, 2)
            if t not in (s, r)
            and (t, s) not in dominated
            and (t, r) not in dominated
            and self.covers(t, s, r)
        ]
        return pairs + triples

    def is_reachable(self, S: Spectrum) -> bool:
        return not any(
            t in S and s not in S and r not in S for t, s, r in self.coverings
        )

    @cached_property
    def reachable_spectra(self) -> list[Spectrum]:
        subsets = (
            frozenset(c)
            for k in range(self.T + 1)
            for c in itertools.combinations(range(self.T), k)
        )
        return [S for S in subsets if self.is_reachable(S)]

    def describe_coverings(self) -> list[str]:
        return [
            f"{t + 1} >= {s + 1}" if s == r else f"{t + 1} <= [{s + 1}, {r + 1}]"
            for t, s, r in self.coverings
        ]
