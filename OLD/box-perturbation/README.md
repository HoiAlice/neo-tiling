# Weak solvability in a price box at d = 2

Given boxes `Q_min <= Q <= Q_max` (bounds for each of the 2T prices) and outputs `y`, is there `Q`
in the box at which `y` is weakly solvable? The answer is one membership question in the cone of
weakly reachable sets of the 2T corners, and a solution, if any, can be taken on the diagonals of
the boxes. At d = 2 this is one flow LP of `poly-hardness/` (the weak-solvability oracle), so the
box problem is polynomial relative to it.

* `box-perturbation.tex` — the text (Russian).
* `lean/BoxPerturbation/` — `box_iff` (any d >= 2), no `sorry`, standard axioms only. Build:
  `lake build BoxPerturbation` from the repository root.

## Code

* `box.py` — `decide`, `witness` (rational Q in the box with an exact certificate), `refute`
  (exact Farkas vector, checked by the longest-path column oracle), `certify`, `in_box`. Uses
  `../poly-hardness/planar.py`. Interior point, no simplex.
* `example.py` — EU KLEMS, US, total economy, 1995-2020 (`data/us_tot.csv`): the least maximal
  log deviation of the 2T prices by bisection, both sides certified, `example.png`.
* `tests/test_box.py` — comparison with the definition on small instances, degenerate boxes.

From this folder:

```
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -m pytest -q -p no:cacheprovider tests
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python example.py
```
