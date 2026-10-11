"""Berndt-Wood US manufacturing 1947-1971 (read from ../code/data, not copied).

Inputs K, L, E, M with prices PK, PL, PE, PM; output QY.  A planar instance takes two inputs.
"""

from fractions import Fraction
from pathlib import Path

FILE = Path(__file__).resolve().parent.parent / "code" / "data" / "berndt_wood_klem.dat"
COLUMN = {"K": 4, "L": 6, "E": 8, "M": 10}  # YEAR QY PY QK PK QL PL QE PE QM PM
PAIRS = ("KL", "KE", "KM", "LE", "LM", "EM")


def berndt_wood(pair="KL"):
    """(P, y, years): prices of the two inputs, gross output, years (T = 25)."""
    P, y, years = [], [], []
    for line in FILE.read_text().splitlines():
        f = line.split()
        if len(f) < 11:
            continue
        P.append(tuple(Fraction(float(f[COLUMN[c]])).limit_denominator(10**9) for c in pair))
        y.append(Fraction(float(f[1])).limit_denominator(10**9))
        years.append(int(float(f[0])))
    return P, y, years


GEOS = ("DE", "FR", "JP", "UK", "US")
INDUSTRIES = ("C", "F", "G", "H", "J", "K", "M-N", "TOT")
KLEMS_PAIRS = ((0, 1), (0, 2), (1, 2))  # (capital, labour, intermediates)
KLEMS_NAMES = "KLI"


def euklems(geo, industry, pair):
    """A planar slice of EU KLEMS 2023 (loader of code/perturbation/datasets.py, read only):
    two of the prices (capital, labour, intermediates) and gross output."""
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "code"))
    from perturbation.datasets import euklems as load

    prob = load(geo, industry)
    return [tuple(p[i] for i in pair) for p in prob.P], list(prob.y), prob.periods
