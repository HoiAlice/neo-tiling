"""Least l1 perturbation of prices for weak solvability (see ../README.md)."""

import sys
from pathlib import Path

# reuse the exact oracle, the flow oracle and the data loaders of price-perturbation/
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "price-perturbation"))
