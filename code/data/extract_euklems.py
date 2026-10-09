"""Extract the slices of EU KLEMS 2023 used by the tests into one small CSV.

Run once after downloading the raw files into code/data/raw/ (see README.md):

    python code/data/extract_euklems.py

Output: code/data/euklems.csv with one row per (geo, industry, year) and the columns
needed for the prices of capital, labour and intermediate inputs and the output volume.
"""

from __future__ import annotations

import csv
from pathlib import Path

HERE = Path(__file__).parent
RAW = HERE / "raw"
GEOS = ["UK", "US", "DE", "FR", "JP"]
INDUSTRIES = ["TOT", "C", "F", "G", "H", "J", "K", "M-N"]
NATIONAL = [
    "GO_CP",
    "GO_PYP",
    "GO_Q",
    "II_CP",
    "II_PYP",
    "II_Q",
    "VA_CP",
    "COMP",
    "H_EMP",
]
CAPITAL = ["K_GFCF", "Kq_GFCF"]


def load(name: str, columns: list[str]) -> dict[tuple[str, str, int], dict[str, str]]:
    out = {}
    with (RAW / name).open(newline="") as f:
        for row in csv.DictReader(f):
            key = (row["geo_code"], row["nace_r2_code"], int(row["year"]))
            if key[0] in GEOS and key[1] in INDUSTRIES:
                out[key] = {c: row[c] for c in columns}
    return out


def main() -> None:
    national = load("euklems_national_accounts.csv", NATIONAL)
    capital = load("euklems_capital_accounts.csv", CAPITAL)
    with (HERE / "euklems.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["geo", "industry", "year", *NATIONAL, *CAPITAL])
        for key in sorted(national):
            if key in capital:
                geo, industry, year = key
                row = {**national[key], **capital[key]}
                writer.writerow(
                    [geo, industry, year, *(row[c] for c in NATIONAL + CAPITAL)]
                )


if __name__ == "__main__":
    main()
