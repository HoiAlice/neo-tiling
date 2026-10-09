"""Real-data instances of the perturbation problem (see code/data/README.md).

Each period t is one observation: a price vector p_t of the inputs and the output y_t.

berndt_wood()               US manufacturing 1947-1971, inputs K, L, E, M (d=4, T=25)
euklems(geo, industry)      EU KLEMS 2023, inputs K, L, II (d = 3, T up to 27)
window(problem, start, n)   n consecutive periods, for tests of growing size
"""

from __future__ import annotations

import csv
import math
from fractions import Fraction
from pathlib import Path

from .prep import Problem

DATA = Path(__file__).resolve().parent.parent / "data"
DENOMINATOR = 10**9  # floats from the files are converted to exact rationals with this


def _frac(x: float) -> Fraction:
    return Fraction(x).limit_denominator(DENOMINATOR)


def berndt_wood() -> Problem:
    """Prices (PK, PL, PE, PM) and the gross output quantity QY, 1947-1971."""
    P, y, years = [], [], []
    for line in (DATA / "berndt_wood_klem.dat").read_text().splitlines():
        f = [float(v) for v in line.split()]
        if len(f) < 11:  # noqa: PLR2004 - YEAR QY PY QK PK QL PL QE PE QM PM ...
            continue
        P.append(tuple(_frac(f[i]) for i in (4, 6, 8, 10)))
        y.append(_frac(f[1]))
        years.append(str(int(f[0])))
    factors = ("capital", "labour", "energy", "materials")
    return Problem(tuple(P), tuple(y), tuple(years), factors)


def _value(text: str) -> float:
    """A file entry as a positive finite float, else nan (the files use NA, Inf and 0
    for missing values)."""
    try:
        v = float(text)
    except ValueError:
        return math.nan
    return v if math.isfinite(v) and v > 0 else math.nan


def _chain(cp: list[float], pyp: list[float], q: list[float]) -> list[float]:
    """Volume series: the file's `*_Q` where present, else chain-linked from
    previous-year prices, q_t = q_{t-1} pyp_t / cp_{t-1}, restarted at cp_t after a
    gap."""
    out = []
    for t in range(len(cp)):
        if not math.isnan(q[t]):
            out.append(q[t])
        elif t > 0 and not math.isnan(out[-1]) and not math.isnan(pyp[t]):
            out.append(out[-1] * pyp[t] / cp[t - 1])
        else:
            out.append(cp[t] if t == 0 or math.isnan(out[-1]) else math.nan)
    return out


def euklems(
    geo: str, industry: str = "C", years: tuple[int, int] = (1995, 2020)
) -> Problem:
    """Prices (capital, labour, intermediates) and gross output volume for one industry.

    capital price = (VA_CP - COMP) / Kq_GFCF, labour price = COMP / H_EMP,
    intermediates price = II_CP / II_Q, output = GO_Q (chain-linked when missing).
    Years with a missing entry are dropped; the result lists the years kept."""
    with (DATA / "euklems.csv").open(newline="") as f:
        rows = [
            {k: _value(v) for k, v in row.items() if k != "geo"}
            for row in csv.DictReader(f)
            if row["geo"] == geo and row["industry"] == industry
        ]
    rows.sort(key=lambda r: r["year"])
    rows = [r for r in rows if years[0] <= r["year"] <= years[1]]
    if not rows:
        raise ValueError(f"no rows for {geo}/{industry} in {years}")
    go_q = _chain(*([r[c] for r in rows] for c in ("GO_CP", "GO_PYP", "GO_Q")))
    ii_q = _chain(*([r[c] for r in rows] for c in ("II_CP", "II_PYP", "II_Q")))
    P, y, kept = [], [], []
    for r, go, ii in zip(rows, go_q, ii_q):
        pk = (r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"]
        pl = r["COMP"] / r["H_EMP"]
        pii = r["II_CP"] / ii
        if all(math.isfinite(v) and v > 0 for v in (pk, pl, pii, go)):
            P.append((_frac(pk), _frac(pl), _frac(pii)))
            y.append(_frac(go))
            kept.append(str(int(r["year"])))
    if len(P) < 2:  # noqa: PLR2004
        raise ValueError(f"too few complete observations for {geo}/{industry}")
    factors = ("capital", "labour", "intermediates")
    return Problem(tuple(P), tuple(y), tuple(kept), factors)


def select(problem: Problem, indices: tuple[int, ...]) -> Problem:
    """Keep only the coordinates `indices` of every price (e.g. two inputs, d = 2)."""
    P = tuple(tuple(p[i] for i in indices) for p in problem.P)
    factors = tuple(problem.factors[i] for i in indices) if problem.factors else None
    return Problem(P, problem.y, problem.periods, factors)


def window(problem: Problem, start: int, n: int) -> Problem:
    sl = slice(start, start + n)
    periods = problem.periods[sl] if problem.periods else None
    return Problem(problem.P[sl], problem.y[sl], periods, problem.factors)
