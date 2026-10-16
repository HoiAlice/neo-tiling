# l1-perturbation

Exact algorithm for the least l_p perturbation of prices (1 <= p <= inf) that makes the outputs y
weakly solvable.  Every price of every year may move; the cost is ONE weighted l_p norm of the whole
vector of deviations, relative (q/p - 1) or logarithmic (ln q - ln p).  A MILP master problem
(HiGHS, free) and the exact box oracle of `../price-perturbation/perturb/exact_oracle.py` (reused, not
copied).  Results of the 2026-10-16 runs: [RESULTS.md](RESULTS.md).

```
l1pert/problem.py   metrics "rel" / "log", cost, box cost, rational corners, box query, Q from a certificate
l1pert/master.py    master MILP: half-widths, year signs, dominance, polyblock cuts, cover cuts, l_p objective
l1pert/solve.py     the loop: master -> query at v + delta 1 -> projection -> cover / polyblock cuts
l1pert/data.py      value-added model d = 2 (EU KLEMS, data/euklems.csv), US d = 3, BEA d = 8
lean/               L1Perturbation/Reduction.lean: the theorems the algorithm relies on, no sorry
tex/                l1-perturbation.tex: the chapter (Russian), figures/
tests/              tiny instances, independent brute-force checks
```

## Problem and results

Prices P (T points of R^d_{>0}), outputs y >= 0, weights c > 0.  Minimize C_p(Q) = ||c o dev(Q, P)||_p
over Q at which y is weakly solvable.

* Reduction (Lean `exists_weakSolvable_iff_boxFeasible_lp`, `_linf`, `_rel_lp`): equivalent to
  minimizing ||c o (alpha + beta)||_p over half-widths whose box passes ONE box query; the feasible
  half-widths form an up-closed set (`BoxFeasible.mono`): monotonic optimization.
* One-signedness (`exists_oneSigned_le`, `exists_lt_of_mixed_lp`): optimal prices move every year in
  one direction.
* Covers and dominance (`meets_of_conv_lt`, `le_of_lt`): a weakly reachable set containing t meets
  every A whose convex hull has a point strictly below t.
* NO certificate (`not_boxCone_of_certificate`): the oracle's Farkas vector and finite cover set
  prove NO at every box where those covers are present.  Hence cover cuts: some cover must disappear;
  linear and exact in the relative metric, piecewise-linear relaxation in the log metric.
* Algorithm: polyblock outer approximation (Tuy 2000; Tuy, Al-Khayyal, Thach 2005) with a MILP master
  and combinatorial Benders cuts (Codato, Fischetti 2006).  LB <= OPT_p <= UB at every step, UB = exact
  cost of a rational Q checked independently; for every eps > 0 it stops with UB - LB <= eps UB
  (packing bound `separated_bound`).  The step bound is exponential; NP-hard for d >= 3.
* Real data (p = 1, 2): 8 BEA slices with d = 8, T = 40 solved to optimality in 1-10 min, US d = 3 and
  the value-added slices d = 2 in seconds; BEA 6 and 31 open.

## Run

```
cd l1-perturbation
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -m pytest -q -p no:cacheprovider tests
```
Lean (not in the lakefile; nothing outside this folder is edited):
`lake env lean l1-perturbation/lean/L1Perturbation/Reduction.lean` from the repository root.

```python
import l1pert
from l1pert import data
from l1pert.problem import Problem
from l1pert.solve import solve
P, y, years = data.bea8(24)
res = solve(Problem(P, y, p=1, metric="rel"), eps=1e-4, time_limit=600)   # LB, UB, Q (rational), status
```
