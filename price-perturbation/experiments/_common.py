"""Shared setup for the experiment scripts: puts price-perturbation/ on sys.path (so that
`import perturb` works when a script is run from anywhere) and defines output folders."""

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "tex" / "figures"
RESULTS = Path(__file__).resolve().parent / "results"

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
