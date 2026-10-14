# price-perturbation

Least perturbation of observed (normalised) prices that makes the outputs `y` weakly solvable: exact
radii, weighted and per-year / per-pair lexicographic profiles, Lean formalization, text with proofs.

**Coming back to write the paper? Start with [PAPER-NOTES.md](PAPER-NOTES.md)** (main insight,
decisions taken, what is proven where, how to reproduce every number, open questions).

## Layout

```
perturb/        Python package (run everything from this folder, interpreter ../.venv/bin/python)
  box.py          d = 2 BOX feasibility by one flow LP (copy of OLD/box-perturbation/box.py; needs poly-hardness/planar.py)
  proj.py         general d: distance, rational breakpoints, black-box oracles, exact least radius, certificates
  milp_oracle.py  PLACEHOLDER oracles: oracle_milp, oracle_cg (column generation) for d >= 3
  zono.py         weighted formulation (zonotope balls), least_wradius, wwitness, default_weights
  lexprofile.py   lexicographic profile of per-year radii
  pairs.py        lexicographic profile of per-pair half-widths a_{t,i}
  data.py         loaders: load_us_d2, load_us_d3, load_bea, load_berndt_wood
experiments/    example and benchmark scripts (us_*.py, bench_*.py, meet_check.py), results/ = benchmark logs
tests/          pytest suite (conftest.py puts the package on sys.path)
data/           input data (see Data)
tex/            price-perturbation.tex (Russian, proofs), figures/ (written by the examples), build/
lean/           PricePerturbation library (built from the repository root)
```

## Run

```
cd price-perturbation
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -m pytest -q -p no:cacheprovider tests    # several minutes
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python experiments/us_weighted.py                 # US data, writes tex/figures/example_zono.png
```

Examples (US data, write a png to `tex/figures/`): `us_box.py` (exact hexagonal rho*, `example.png`),
`us_weighted.py`, `us_rotating.py`, `us_profile.py` (about 3 minutes), `us_pairs.py`;
`us_d3_breakpoints.py [T]` prints breakpoint statistics at d = 3.
Benchmarks (long, run one at a time): `bench_d2_real.py`, `bench_d2_synthetic.py`, `bench_large_d.py`;
logs of the runs behind the numbers in the text are in `experiments/results/`.
`meet_check.py [seconds]`: experiment on the meet property of the feasible set of radii.

Lean: `lake build PricePerturbation` from the repository root (no `sorry`, standard axioms only; not
a default target).  `Support.lean` and `Box.lean` (namespace `NeoTiling.BoxPerturbation`) are copies
of `OLD/box-perturbation/lean`.

## Problem

Prices `p_t` in R^d_{++} (t in [T]) are normalised (d+1)-dimensional prices.  The distance of
normalised points is `dist(a, b) = min_s sum_i |u_i + s| + |s|`, `u = ln a - ln b`, i.e. the sum of
absolute deviations of `(u_1, .., u_d, 0)` from its median (for d = 2 the hexagonal norm
`max(|u1|, |u2|, |u1 - u2|)`).  Given outputs `y >= 0`, find `rho* = min_Q max_t dist(q_t, p_t)` over
all `Q` at which `y` is weakly solvable.

## Facts (d >= 2, `proj.py`)

1. The ball `{dist <= rho}` lies in the cube `|u_i| <= rho` and contains the diagonal.  By the box
   theorem, feasibility at radius `rho` <=> `BOX(p e^{-rho}, p e^{rho}, y)`; a solution lies on the
   diagonals `q_t = p_t e^{s_t}`, `|s_t| <= rho`.
2. Corners `(P/k, P k)`, `z = k^2 = e^{2 rho}`, `k` rational.
3. Every `(d+1)`-determinant of the vectors `(p_t, 1)`, `(z p_t, 1)`, `(e_i, 0)` equals
   `z^{b-1} (D0 z + D1)`, so all breakpoints are RATIONAL.  Between consecutive breakpoints the
   combinatorics is constant, feasibility is monotone in `z` and closed: `rho* = 0` or `rho* = (1/2)
   ln z_k` at a breakpoint (US data d = 2: 8310 breakpoints; d = 3, T = 26: 127160, 30 s).
4. Oracle = black box `oracle(W, lo, hi) -> bool | OracleAnswer`: exists `w` in the cone of weakly
   reachable sets of `W` with `lo <= w <= hi`.  Reference oracles: `oracle_brute` (any d, exact),
   `oracle_flow` (d = 2, box form; interior-point flow LP, certificates by `box.py`).
   `least_radius_exact` uses only the booleans: z = 1, then the last gap, then binary search over
   gaps, O(log #breakpoints) calls.
5. `witness` (YES, exact Q from columns + masses) and `refute` (NO, Farkas vector, global check
   delegated to a column oracle) work when the oracle supplies certificates.

## PLACEHOLDER oracles (`milp_oracle.py`)

`oracle_milp`: K = |W| sets (Caratheodory), binaries, McCormick, big-M witnesses; HiGHS.  `oracle_cg`:
column generation, LP master over weakly reachable sets, pricing = one-set MILP `price_milp` with each
witness row divided by its big-M (essential).  Both are temporary stand-ins; the pricing MILP with
exact geometry (lazy covering cuts) is the proper fix.  The no-good retry loop triggers at d = 7 and
2 of 4 BEA industries still fail (see `results/bench_large_d.log`).  Tests compare with
`oracle_brute` (d = 3, T <= 4) and `oracle_flow` (d = 2).

## Weighted formulation (`zono.py`)

Year `t` has penalties `kappa[t][i] > 0` for the `d` normalised prices and `kappa0[t] > 0` for the
normalising price.  With `u = ln q - ln p`:
`d_kappa(q_t, p_t) = min_s max(kappa0[t] |s|, max_i kappa[t][i] |u_i + s|)`.

1. The ball is the zonotope "log-box `[-rho/kappa_i, rho/kappa_i]` plus the diagonal segment of
   half-length `rho/kappa0`".  Its bounding box has half-widths `a_i = rho (1/kappa_i + 1/kappa0)`; the
   corners `+-a` and the path `theta -> theta v`, `v_i = 1/kappa_i + 1/kappa0`, lie in it.
2. Feasibility at `rho` <=> `BOX(L, U, y)`, `L = p exp(-a)`, `U = p exp(a)`: one oracle call
   (`least_wradius`).  Rounded rational corners: `inner=True` for YES, `inner=False` for NO,
   disagreement is reported as AMBIG (never happened).
3. A solution can be taken on the path `q_t = p_t exp(theta_t v_t)` (`wwitness`); cheaper prices
   (smaller kappa) move more.
4. With all weights 1 and d = 2 the ball is the hexagon scaled by 1/2.
5. The witness is certified up to float only (`Q` lies on boundaries), so `wwitness` checks BOX
   with corners `Q exp(-+1e-8)`.

`default_weights`: `kappa = base[name] * tau_t`, `base = {K: 1, L: 3, II: 3, GO: 4}`,
`tau_t = 0.5 + 0.5 (t - t0)/(T - 1)` (oldest year pays half): imputed capital rental price is the
cheapest to move, well-measured prices cost more, older deflators are less reliable.  US data
(T = 26, d = 2): rho* = 0.058072 with these weights, 0.044827 with equal weights (= 0.089654 / 2).

## Lexicographic profiles

Per-year (`lexprofile.profile`): year `t` has its own radius `r_t`; `R = {r : feasible(r)}` is closed
and upward closed (one oracle call per query with corners `p_t exp(-+r_t v_t)`).  The profile is the
lexicographic minimum of the decreasing rearrangement of `r` over `R`.  Stages: free years share a
common bound `rho` (bisection); `B` = minimum-cardinality set of years that must stay at `rho` (it
contains the individually blocking years `B0`; if the rest is jointly feasible `B = B0`, else
supersets of `B0` over ALL free years are searched by increasing size and the procedure branches over
all minimum choices); fix `B`, repeat.  Exact up to the bisection tolerance; a polynomial number of
oracle calls, O(T^2 log(1/eps)), without branching; exponential in the worst case otherwise.  The
meet property of `R` is false (counterexample and statistics in `experiments/meet_check.py`), yet the
lexicographic minimum was reached without branching in all but 1 of 427 random profiles.

Per-pair (`pairs.wall_profile`): the unit is a pair `(t, i)` with a symmetric half-width `a_{t,i}`,
no weights.  Same stages.  For d = 2 the candidates `B0` are searched among the pairs touched by an
exact witness only (an untouched pair can be lowered with the witness kept); the superset search
ranges over all free pairs.  No truncation: an exception is raised rather than a possibly
non-optimal result.  Same exactness and complexity statement.

US data (d = 2, T = 26, default weights): 24 stages, 1015 oracle calls, 190 s, no branching
(`us_profile.py`).

## Benchmarks (`zono.least_wradius`, final weights; logs in `experiments/results/`)

1. d = 2 real data (US T = 26, 10 BEA industries T = 40), flow LP vs column generation: all brackets
   agree to 2e-6, no AMBIG; per-case times from 3 s to 350 s (flow) and 10 s to 105 s (CG).
2. d = 2 synthetic (T = 20..60, 5 families, one call at rho = 0.05): decisions agree in all 25
   cases; CG is faster on convex instances (168 s vs 3.4 s at T = 60).
3. Large d, CG only, tol 1e-5: US d = 3, Berndt-Wood d = 4, BEA d = 4 and d = 7 (T = 40); 25 to 28
   oracle calls, up to 790 s; 3 of 4 BEA d = 7 industries fail with the no-good retry error.

## Data

* `data/us_tot.csv`: EU KLEMS 2023, US total economy, 1995-2020 (T = 26).  Prices K = (VA_CP -
  COMP) / Kq_GFCF, L = COMP / H_EMP, II = II_CP / II_Q, output `GO_Q`; d = 3 adds the output price
  `(VA_CP + II_CP) / GO_Q`.
* `data/bea_klems_1963_2016.csv`, `bea_klems_detail_1963_2016.csv`, `bea_klems_1947_2016.csv`:
  BEA-BLS integrated industry-level production account, research extension (Eldridge et al. 2020,
  public domain), 63 industries.  Built by `data/build_bea.py` from
  `KLEMS-Research-Tables-Underlying-Data_0.xlsx` (bea.gov): chained Tornqvist price aggregates
  `pK`, `pL`, `pII`, `pGO` and the detailed capital / labour types, output quantity `GO_Q`.
* `data/berndt_wood_klem.dat` (+ description `.txt`): Berndt-Wood KLEM data set, US manufacturing
  1947-71, courtesy Ernst R. Berndt.

## Lean

`lean/PricePerturbation/`: `Hex.lean` (`hex_iff_scale`, `hex_iff_corners`: d = 2 hexagon <=> box),
`Proj.lean` (`proj_iff_scale`, `proj_iff_corners` for every d), `LocalConstancy.lean` and
`Radius.lean` (`least_radius_breakpoint`: feasible radii are `[rho*, inf)` and `rho* = 0` or a
minor of the homogenized corners vanishes), `Shape.lean` (general distance, ball shape),
`Weighted.lean` (weighted distance, `wfeasible_iff_corners`, `wfeasible_iff_path`, `least_wradius_breakpoint`),
`Profile.lean` (per-year radii, closed upward-closed feasible set, Pareto-minimal element).
Not formalized: rationality of breakpoints, the algorithms and their complexity, certificates.
The text with all proofs: `tex/price-perturbation.tex` (Russian, self-contained modulo `latex/notes.tex`).
