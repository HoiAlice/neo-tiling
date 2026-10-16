"""Data sets.  Prices are exact Fractions; a loader returns (P, y, years).

va_model(geo, ind)  d = 2: inputs K, L; output value added (the output price is kept as numeraire).
                    EU KLEMS 2023, 1995-2021, data/euklems.csv (US, DE, FR, JP; 8 industries).
us3()               d = 3: (K, L, II) / GO price, y = gross output.  EU KLEMS US total economy 1995-2020
                    (../price-perturbation/data/us_tot.csv).
bea8(ind)           d = 8: five capital types, two labour types, II, all / GO price, y = gross output.
                    BEA-BLS integrated industry accounts, 1977-2016 (../price-perturbation/data).
Prices are returned as the nearest rationals with denominator <= 10^9 (far below the precision of the
sources; equal values stay equal): exact arithmetic on ratios of long decimals is needlessly slow.
"""

from __future__ import annotations

import csv
from fractions import Fraction as F
from pathlib import Path

from perturb import data as ppdata

EUKLEMS = Path(__file__).resolve().parents[1] / "data" / "euklems.csv"
K8 = ["pKit", "pKsoft", "pKrd", "pKart", "pKoth", "pLcol", "pLn", "pII"]


def _short(P):
    return [tuple(F(v).limit_denominator(10**9) for v in p) for p in P]


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
    with open(EUKLEMS) as f:
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


def us3():
    P, y, years = ppdata.load_us_d3()
    return _short(P), y, years


def bea8(ind, T=40):
    with open(ppdata.DATA / "bea_klems_detail_1963_2016.csv") as f:
        rs = sorted((r for r in csv.DictReader(f) if int(r["indnum"]) == ind),
                    key=lambda r: int(r["year"]))[-T:]
    P = [tuple(F(r[c]) / F(r["pGO"]) for c in K8) for r in rs]
    return _short(P), [F(r["GO_Q"]) for r in rs], [int(r["year"]) for r in rs]
