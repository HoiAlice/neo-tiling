"""Real-data instances: the data files of OLD/code/data (see OLD/code/data/README.md).

berndt_wood(inputs)        US manufacturing 1947-1971, inputs from K, L, E, M (T = 25)
euklems(geo, industry)     EU KLEMS 2023, inputs capital, labour, intermediates (d = 3)

Prices and outputs are converted to exact rationals with denominator <= 10^9, and every
price coordinate is scaled to max_t p^i_t = 1 (pi_1 is invariant under this scaling).
"""

from __future__ import annotations

import csv
import math
from fractions import Fraction
from pathlib import Path

DATA = Path(__file__).resolve().parents[2] / "OLD" / "code" / "data"
DENOMINATOR = 10**9


def _frac(x: float) -> Fraction:
    return Fraction(x).limit_denominator(DENOMINATOR)


def _normalize(P):
    d = len(P[0])
    top = [max(p[i] for p in P) for i in range(d)]
    return [[p[i] / top[i] for i in range(d)] for p in P]


def berndt_wood(inputs: str = "KLEM"):
    cols = {"K": 4, "L": 6, "E": 8, "M": 10}
    P, y = [], []
    for line in (DATA / "berndt_wood_klem.dat").read_text().splitlines():
        f = [float(v) for v in line.split()]
        if len(f) < 11:
            continue
        P.append([_frac(f[cols[c]]) for c in inputs])
        y.append(_frac(f[1]))
    return _normalize(P), y


def _value(text: str) -> float:
    try:
        v = float(text)
    except ValueError:
        return math.nan
    return v if math.isfinite(v) and v > 0 else math.nan


def _chain(cp, pyp, q):
    out = []
    for t in range(len(cp)):
        if not math.isnan(q[t]):
            out.append(q[t])
        elif t > 0 and not math.isnan(out[-1]) and not math.isnan(pyp[t]):
            out.append(out[-1] * pyp[t] / cp[t - 1])
        else:
            out.append(cp[t] if t == 0 or math.isnan(out[-1]) else math.nan)
    return out


def euklems(geo: str, industry: str = "C", years: tuple[int, int] = (1995, 2020)):
    with (DATA / "euklems.csv").open(newline="") as f:
        rows = [
            {k: _value(v) for k, v in row.items() if k not in ("geo", "industry")}
            for row in csv.DictReader(f)
            if row["geo"] == geo and row["industry"] == industry
        ]
    rows.sort(key=lambda r: r["year"])
    rows = [r for r in rows if years[0] <= r["year"] <= years[1]]
    go_q = _chain(*([r[c] for r in rows] for c in ("GO_CP", "GO_PYP", "GO_Q")))
    ii_q = _chain(*([r[c] for r in rows] for c in ("II_CP", "II_PYP", "II_Q")))
    P, y = [], []
    for r, go, ii in zip(rows, go_q, ii_q):
        pk = (r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"]
        pl = r["COMP"] / r["H_EMP"]
        pii = r["II_CP"] / ii
        if all(math.isfinite(v) and v > 0 for v in (pk, pl, pii, go)):
            P.append([_frac(pk), _frac(pl), _frac(pii)])
            y.append(_frac(go))
    return _normalize(P), y
