"""Data sets.  Every loader returns (P, y, years): P a list of price vectors, y the outputs (exact
Fractions), years the list of years.  Slices with unusable data return three empty lists.

Rounding policy (one for all loaders): the price vectors are rounded to the nearest rationals with
denominator <= 10^9 (`limit_denominator(10**9)`), far below the precision of the sources; equal values
stay equal.  Exact arithmetic on ratios of long decimals is needlessly slow.  Outputs y are exact.

us_d2()              d = 2: (K/II, L/II), EU KLEMS 2023 US total economy 1995-2020 (T = 26), y = GO_Q.
us_d3(T)             d = 3: (K, L, II) / GO price, same data.
bea(ind, d, T)       BEA-BLS industry `ind` (1..63), the last T years of 1963-2016 (T = None: all 54).
                     d = 2: (pK/pII, pL/pII); d = 4: (pK, pLcol, pLn, pII)/pGO; d = 7: five capital and
                     two labour types / pII; d = 8: those seven and pII, all / pGO.
va_model(geo, ind)   d = 2, value-added model: inputs K, L, output value added.  EU KLEMS 2023,
                     1995-2021, csv/euklems.csv (US, DE, FR, JP; 8 industries).
berndt_wood()        Berndt-Wood (1975) US manufacturing KLEM, 1947-71 (T = 25), d = 4.
"""

from __future__ import annotations

import csv
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

CSV = Path(__file__).resolve().parent / "csv"
K7 = ["pKit", "pKsoft", "pKrd", "pKart", "pKoth", "pLcol", "pLn"]


def _short(P):
    return [tuple(F(v).limit_denominator(10**9) for v in p) for p in P]


def _us_rows():
    with open(CSV / "us_tot.csv") as f:
        rows = list(csv.DictReader(f))
    return [{k: F(x) for k, x in r.items()} for r in rows], [int(r["year"]) for r in rows]


def us_d2():
    """EU KLEMS 2023, US total economy, 1995-2020 (T = 26).  P_t = (K/II, L/II) after dividing K, L,
    II by their maxima over the years; y = GO_Q."""
    v, years = _us_rows()
    P3 = [((r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"], r["COMP"] / r["H_EMP"], r["II_CP"] / r["II_Q"])
          for r in v]
    mx = [max(p[i] for p in P3) for i in range(3)]
    P3 = [tuple(p[i] / mx[i] for i in range(3)) for p in P3]
    return _short([(p[0] / p[2], p[1] / p[2]) for p in P3]), [r["GO_Q"] for r in v], years


def us_d3(T=None):
    """Same data at d = 3.  The nominal gross output GO_CP = VA_CP + II_CP gives the output price
    GO_CP / GO_Q; prices (K, L, II) / GO price, each divided by its maximum first.  Truncated to the
    first T years if T is given."""
    v, years = _us_rows()
    P4 = [((r["VA_CP"] - r["COMP"]) / r["Kq_GFCF"], r["COMP"] / r["H_EMP"], r["II_CP"] / r["II_Q"],
           (r["VA_CP"] + r["II_CP"]) / r["GO_Q"]) for r in v]
    mx = [max(p[i] for p in P4) for i in range(4)]
    P4 = [tuple(p[i] / mx[i] for i in range(4)) for p in P4]
    P = _short([(p[0] / p[3], p[1] / p[3], p[2] / p[3]) for p in P4])
    y = [r["GO_Q"] for r in v]
    return (P[:T], y[:T], years[:T]) if T else (P, y, years)


def bea(ind, d=2, T=None):
    """BEA-BLS industry `ind` (1..63), the last T years of 1963-2016 (T = None: all years)."""
    if d == 2:
        with open(CSV / "bea_klems_1963_2016.csv") as f:
            rows = [r for r in csv.DictReader(f) if int(r["indnum"]) == ind]
        rs = sorted(rows, key=lambda r: int(r["year"]))[-T:] if T else sorted(rows, key=lambda r: int(r["year"]))
        P = [(F(r["pK"]) / F(r["pII"]), F(r["pL"]) / F(r["pII"])) for r in rs]
        return _short(P), [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs]
    if d not in (4, 7, 8):
        raise ValueError("d must be 2, 4, 7 or 8")
    with open(CSV / "bea_klems_1963_2016.csv") as f:
        agg = {(r["indnum"], r["year"]): r for r in csv.DictReader(f)}
    det = defaultdict(list)
    with open(CSV / "bea_klems_detail_1963_2016.csv") as f:
        for r in csv.DictReader(f):
            det[r["indnum"]].append(r)
    rs = sorted(det[str(ind)], key=lambda r: int(r["year"]))
    rs = rs[-T:] if T else rs
    if d == 4:
        P = [tuple(F(x) / F(r["pGO"]) for x in
                   (agg[(r["indnum"], r["year"])]["pK"], r["pLcol"], r["pLn"], r["pII"])) for r in rs]
    elif d == 7:
        P = [tuple(F(r[c]) / F(r["pII"]) for c in K7) for r in rs]
    else:
        P = [tuple(F(r[c]) / F(r["pGO"]) for c in K7 + ["pII"]) for r in rs]
    return _short(P), [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs]


def _num(r, k):
    v = r[k]
    if v in ("", "NA", "nan", "Inf", "-Inf"):
        return None
    v = F(v)
    return v if v > 0 else None


def va_model(geo, ind):
    """VA = GO_CP - II_CP (the file's VA_CP is not equal to GO - II, so it is not used).
    p_K = (VA - COMP) / Kq_GFCF, p_L = COMP / H_EMP.  VA volume by double deflation, chain-linked:
    VA_PYP(t) = GO_PYP(t) - II_PYP(t), X_PYP(t) = X_CP(t-1) X_Q(t) / X_Q(t-1) when X_PYP is missing
    (exact for chain volumes), Q(t) = Q(t-1) VA_PYP(t) / VA(t-1), Q(0) = VA(0); p_VA = VA / Q.
    Prices (p_K, p_L) / p_VA, y = Q.  Slices with broken volume series (UK) return empty lists."""
    with open(CSV / "euklems.csv") as f:
        rows = sorted((r for r in csv.DictReader(f) if r["geo"] == geo and r["industry"] == ind),
                      key=lambda r: int(r["year"]))
    rows = [r for r in rows if all(_num(r, k) is not None
                                   for k in ("COMP", "H_EMP", "Kq_GFCF", "GO_CP", "II_CP"))]

    def pyp(k, x):
        v = _num(rows[k], x + "_PYP")
        if v is not None:
            return v
        a, b, c = _num(rows[k - 1], x + "_CP"), _num(rows[k], x + "_Q"), _num(rows[k - 1], x + "_Q")
        return None if None in (a, b, c) else a * b / c

    def va(r):
        return F(r["GO_CP"]) - F(r["II_CP"])

    P, y, years, q = [], [], [], None
    for k, r in enumerate(rows):
        if k > 0:
            go, ii = pyp(k, "GO"), pyp(k, "II")
            if go is None or ii is None or int(r["year"]) != int(rows[k - 1]["year"]) + 1:
                return [], [], []
        q = va(r) if k == 0 else q * (go - ii) / va(rows[k - 1])
        pk = (va(r) - F(r["COMP"])) / F(r["Kq_GFCF"])
        if pk <= 0 or q <= 0:
            return [], [], []
        pva = va(r) / q
        P.append((pk / pva, F(r["COMP"]) / F(r["H_EMP"]) / pva))
        y.append(q)
        years.append(int(r["year"]))
    return _short(P), y, years


def berndt_wood():
    """Berndt-Wood (1975) US manufacturing KLEM, 1947-71 (T = 25), d = 4: (PK, PL, PE, PM) / PY,
    y = output quantity column."""
    with open(CSV / "berndt_wood_klem.dat") as f:
        rows = [list(map(F, l.split())) for l in f if l.strip()]
    P = [(r[4] / r[2], r[6] / r[2], r[8] / r[2], r[10] / r[2]) for r in rows]
    return _short(P), [r[1] for r in rows], [int(r[0]) for r in rows]
