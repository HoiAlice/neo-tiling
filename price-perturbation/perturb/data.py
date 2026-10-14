"""Loaders for the data sets in ../data (see ../README.md, section Data).

All prices are exact Fractions.  A loader returns (P, y, years) unless stated otherwise.
"""

from __future__ import annotations

import csv
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "data"


def _us_rows():
    with open(DATA / "us_tot.csv") as f:
        rows = list(csv.DictReader(f))
    return [{k: F(x) for k, x in r.items()} for r in rows], [int(r["year"]) for r in rows]


def load_us_d2():
    """EU KLEMS 2023, US total economy, 1995-2020 (T = 26).  P_t = (K/II, L/II) after dividing K, L,
    II by their maxima over the years; y = GO_Q.  Returns (P, y, years)."""
    v, years = _us_rows()
    P3 = [((r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"], r["COMP"] / r["H_EMP"], r["II_CP"] / r["II_Q"])
          for r in v]
    mx = [max(p[i] for p in P3) for i in range(3)]
    P3 = [tuple(p[i] / mx[i] for i in range(3)) for p in P3]
    return [(p[0] / p[2], p[1] / p[2]) for p in P3], [r["GO_Q"] for r in v], years


def load_us_d3(T=None):
    """Same data at d = 3.  The nominal gross output GO_CP = VA_CP + II_CP gives the output price
    GO_CP / GO_Q; prices (K, L, II) / GO price, each divided by its maximum first.  Returns
    (P, y, years), truncated to the first T years if T is given."""
    v, years = _us_rows()
    P4 = [((r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"], r["COMP"] / r["H_EMP"], r["II_CP"] / r["II_Q"],
           (r["VA_CP"] + r["II_CP"]) / r["GO_Q"]) for r in v]
    mx = [max(p[i] for p in P4) for i in range(4)]
    P4 = [tuple(p[i] / mx[i] for i in range(4)) for p in P4]
    P = [(p[0] / p[3], p[1] / p[3], p[2] / p[3]) for p in P4]
    y = [r["GO_Q"] for r in v]
    return (P[:T], y[:T], years[:T]) if T else (P, y, years)


def load_bea(ind, d=2, T=40):
    """BEA-BLS industry `ind` (1..63), the last T years of 1963-2016.  d = 2: (pK/pII, pL/pII);
    d = 4: (pK, pLcol, pLn, pII) / pGO (needs the detail file); d = 7: five capital types and two
    labour types / pII.  y = GO_Q.  Returns (P, y, years)."""
    if d == 2:
        with open(DATA / "bea_klems_1963_2016.csv") as f:
            rows = [r for r in csv.DictReader(f) if int(r["indnum"]) == ind]
        rs = sorted(rows, key=lambda r: int(r["year"]))[-T:]
        P = [(F(r["pK"]) / F(r["pII"]), F(r["pL"]) / F(r["pII"])) for r in rs]
        return P, [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs]
    with open(DATA / "bea_klems_1963_2016.csv") as f:
        agg = {(r["indnum"], r["year"]): r for r in csv.DictReader(f)}
    det = defaultdict(list)
    with open(DATA / "bea_klems_detail_1963_2016.csv") as f:
        for r in csv.DictReader(f):
            det[r["indnum"]].append(r)
    rs = sorted(det[str(ind)], key=lambda r: int(r["year"]))[-T:]
    if d == 4:
        P = [tuple(F(x) / F(r["pGO"]) for x in
                   (agg[(r["indnum"], r["year"])]["pK"], r["pLcol"], r["pLn"], r["pII"])) for r in rs]
    elif d == 7:
        P = [tuple(F(r[c]) / F(r["pII"]) for c in
                   ("pKit", "pKsoft", "pKrd", "pKart", "pKoth", "pLcol", "pLn")) for r in rs]
    else:
        raise ValueError("d must be 2, 4 or 7")
    return P, [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs]


def load_berndt_wood():
    """Berndt-Wood (1975) US manufacturing KLEM, 1947-71 (T = 25), d = 4: (PK, PL, PE, PM) / PY,
    y = output quantity column.  Returns (P, y, years)."""
    with open(DATA / "berndt_wood_klem.dat") as f:
        rows = [list(map(F, l.split())) for l in f if l.strip()]
    P = [(r[4] / r[2], r[6] / r[2], r[8] / r[2], r[10] / r[2]) for r in rows]
    return P, [r[1] for r in rows], [int(r[0]) for r in rows]
