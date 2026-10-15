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
  exact_oracle.py EXACT oracle for any d: column generation, pricing MILP with 0/1 cover cuts only,
                  geometry in rationals, exact YES/NO certificates (use this one for d >= 3)
  zono.py         weighted formulation (zonotope balls), least_wradius, wwitness, default_weights
  lexprofile.py   lexicographic profile of per-year radii
  pairs.py        lexicographic profile of per-pair half-widths a_{t,i}
  onesided.py     one-sided lexicographic profile: unique Q, no branching (see "One-sided profile")
  data.py         loaders: load_us_d2, load_us_d3, load_bea, load_berndt_wood
experiments/    example and benchmark scripts (us_*.py, bea_onesided.py, ratio_d3.py, aggregation.py,
                bench_*.py, meet_check.py), results/ = logs
tests/          pytest suite (conftest.py puts the package on sys.path)
data/           input data (see Data)
tex/            price-perturbation.tex (Russian, proofs), onesided.tex (one-sided profile, proofs),
                figures/ (written by the examples), build/
lean/           PricePerturbation library (built from the repository root)
```

## Run

```
cd price-perturbation
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python -m pytest -q -p no:cacheprovider tests    # 88 tests, ~3.5 minutes
PYTHONDONTWRITEBYTECODE=1 ../.venv/bin/python experiments/us_weighted.py                 # US data, writes tex/figures/example_zono.png
```

Examples (US data, write a png to `tex/figures/`): `us_box.py` (exact hexagonal rho*, `example.png`),
`us_weighted.py`, `us_rotating.py`, `us_profile.py` (about 3 minutes), `us_pairs.py`,
`us_onesided.py [years to drop]` (about 4 minutes, two runs without dropped years),
`us_onesided_d3.py` (25 minutes, exact oracle);
`us_d3_breakpoints.py [T]` prints breakpoint statistics at d = 3.
BEA: `bea_onesided.py [--exact] 15 49` (30-80 minutes per industry), `ratio_d3.py` (about 10 minutes),
`aggregation.py real|placebo ...` (about 3 minutes per case).
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
witness row divided by its big-M (essential).  Both are temporary stand-ins, SUPERSEDED by
`exact_oracle.oracle_exact` (exact-geometry pricing with lazy cover cuts, see below).  The no-good retry loop triggers at d = 7 and
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

## One-sided profile (`onesided.py`, text `tex/onesided.tex`, 2026-10-14/15)

Owner's requirements: perturb PRICES only (never the outputs y); polynomially many oracle calls
(approximation with linear convergence is fine); a regularization under which a solution always
exists and is unique; proven guarantees; rational prices; an oracle that is never wrong.

Units are the 2T half-axes of the paths: `theta_t in [-alpha_t, beta_t]`, `alpha, beta >= 0`;
feasibility of `(alpha, beta)` is one BOX query with corners `p_t exp(-alpha_t v_t)`,
`p_t exp(beta_t v_t)`.  The profile is the lexicographic minimum of the decreasing rearrangement of
`(alpha, beta)`.

Proved in `tex/onesided.tex` (idealized exact levels):
1. Never empty: aligning one coordinate of all q_t makes every set weakly reachable; this gives an
   explicit feasible level `rho_bar` (see "Unsolvability measure").
2. Pareto-minimal <=> every nonzero unit blocks; a blocking `beta_t` forces `theta_t = beta_t` for
   every feasible theta.  So for any Pareto-minimal `(alpha, beta)` (in particular the profile) theta,
   hence Q, is UNIQUE ON THE PATHS, and each year has at most one nonzero half-axis.  Off the paths:
   no solution lies strictly inside the final boxes (each moved year touches a face through its far
   corner); other points of those faces (same distance) are not excluded.
3. Algorithm: stages as in `lexprofile`, WITHOUT the minimum-cardinality search; a tie (B0 not jointly
   lowerable) is broken by a fixed priority order, then a tightening pass.  No ties -> the output is
   the profile and it is unique; ties -> Pareto-minimal (Q still unique).  At most 2T stages,
   `O(T^2 + T log(rho_bar/eps))` queries, linear convergence.  Blocking units are found by splitting
   (a group that goes down jointly has none); stage queries ask the inner box only (`outer=False`).
4. The sorted `|theta_t|` equals the sorted symmetric profile of `lexprofile`: the one-sided profile
   keeps the magnitudes and fixes the signs.
5. Rational solution (`rational_solution`): from an exact YES certificate at the final rational box,
   the corner-theorem construction along the price-LINEAR segment `L_t + theta (U_t - L_t)` gives a
   rational Q in the balls with an exact certificate (the segment stays in the ball since
   `d/da ln(1 + theta(e^a - 1)) <= 1`).  First tried: far corners rounded inwards.

Why not other metrics: the feasible theta set is not a lattice (`oracle_brute`, d = 2, T = 4: 685 of
611635 pairs violate max/min closure, 2333 of 727900 with diagonal paths); minimizing a separable sum
over an abstract monotone set given by a membership oracle needs exponentially many queries
(construction in the text).

Checks: 85 random instances (d = 2 flow / brute, d = 3 brute, also equal penalties): no ties, all
checks pass, the answer does not depend on the priority order.  Tests: `tests/test_onesided.py`
(including a synthetic tie and the linear-path construction).

## Exact oracle (`exact_oracle.py`, text `tex/onesided.tex`, section "Точный оракул")

Why `oracle_cg` fails: its pricing MILP checks witnesses <xi, W_s - W_t> >= 0 in floats; the profile
drives the points to degenerate configurations (near breakpoints, a coordinate nearly shared), the
solver accepts non-reachable sets and the no-good loop never ends (US d = 3 profile died at stage 15
even with 300 retries).  Fix: S is weakly reachable iff no convex combination of <= d + 1 points
outside S is strictly below a point of S (Caratheodory).  Each such (t, A) is the 0/1 cut
`x_t <= sum_{s in A} x_s`; the pricing MILP has only these cuts (lazy), every cut and every accepted S
is verified in rationals (cut: exact LP on |A| points; S: float witness rounded to rationals and
checked exactly, full rational LP as a fallback).  Exact finish: rational cone LP over the columns,
YES -> exact masses, else exact Farkas lam and one more pricing with INTEGER weights (an improving set
has value >= 1, so the solver tolerance cannot hide it).  `mip_rel_gap = 0` (HiGHS default 1e-4 could
also stop the placeholder CG early).  Cuts of the last call are passed as hints to the next one
(re-verified exactly).  Checked: = oracle_brute on 210 queries (d = 3, T = 3, 4; d = 2, T = 4), every
NO certificate verified on all reachable sets; = oracle_flow on 105 queries (d = 2, T = 10, 20).
Speed: ~4x slower than flow at d = 2; BEA 49 (T = 40) ~2 s per call.  Tests: `tests/test_exact_oracle.py`.
Use `oracle_exact` for d >= 3 (and for plain queries lo = hi = y); `oracle_cg` is superseded.

## Unsolvability measure

`rho* <= rho_bar = min_i min_c max_t |ln c - ln p_t^i| / v_t^i`: the cost of aligning one coordinate
(explicit, no oracle).  `rho*/rho_bar` in [0, 1]: 0 = weakly solvable, 1 = no better than the trivial
explanation.  Computed by `experiments/ratio_d3.py` (function `rho_bar`).  The one-sided profile
collapsed onto a hyperplane p_i = const exactly where rho* = rho_bar (observation, 4 cases).

## One-sided profile: results

| data | rho* | rho*/rho_bar | stages / calls / time | picture |
|---|---|---|---|---|
| US d = 2 (`us_onesided.py`) | 0.0581 | 1.00 | 25 / 671 / 2 min | collapse onto p_K/p_II ~ 0.93 |
| US d = 2 without 2008, 2020 (`us_onesided.py 2008 2020`) | 0.0392 | | 23 / 1464 / 6 min | same collapse, same signs |
| BEA 15 d = 2 (`bea_onesided.py 15`) | 0.2527 | 1.00 | 39 / 1208 / 31 min | collapse onto p_L/p_II ~ 0.224, 8 years off |
| BEA 49 d = 2 (`bea_onesided.py --exact 49`) | 0.0223 | 0.05 | 23 / 699 / 78 min | no collapse, 9 of 40 years unmoved |
| US d = 3 (`us_onesided_d3.py`, exact oracle) | 0.0362 | 0.80 | 24 / 663 / 25 min | no collapse |

Details.  US d = 2: no ties, `|theta_t|` equal to the symmetric profile in all 26 years; signs
1995-2014 up except 1996, 2015-2020 down; extreme pair 2008 (+) / 2020 (-).  Without 2008 and 2020
(weights of the full data) the extreme pair is 2011 / 2019: the conflict is a time trend, not the
crisis years.  BEA 15: signs in blocks.  BEA 49: signs alternate without a trend; BEA 15 and 49 agree
in sign in 15 of the 30 years moved in both (no common year effect).  US d = 3: extreme pair 2002 (+)
/ 2018 (-), 2020 not moved, signs 1995-2004 up, from 2005 mostly down; std ln(K/GO) 0.046 -> 0.027,
ln(II/GO) 0.025 -> 0.015, ln(L/GO) unchanged; singular values of centred ln Q 0.63, 0.15, 0.048 (ln P:
0.70, 0.21, 0.107); the rational corner solution is weakly solvable EXACTLY (certificate of 26 sets).
The collapsed coordinate (d = 2) is the one with the smallest std(ln p_i) / v_i (US: K, BEA 15: L).

Files: figures `tex/figures/example_onesided.png`, `example_onesided_no2008_no2020.png`,
`example_onesided_bea.png` (BEA 15, 49; drawn by `bea_onesided.py --plot` from
`experiments/results/onesided_bea.jsonl`), `example_onesided_d3.png` (drawn from the logged theta of
the US d = 3 run; `us_onesided_d3.py` prints but does not draw).  Interactive 3D view of US d = 3:
https://claude.ai/artifact/SVBCU1xb4cK17hiDN3gJto (private).  The US d = 2 call count is the fast
variant (splitting, inner box only); the first run without these took 1671 calls, same answer.

## Dimensions and aggregation (2026-10-15)

Raw BEA prices per industry-year: 5 capital types, 2 labour types, II, output price GO; y = GO_Q always.
d = 2 (`load_bea(d=2)`): K, L aggregated (chained Tornqvist, `build_bea.py`) / II, the output price
DROPPED.  d = 7 (`load_bea(d=7)`, old benchmark): 5 K types, 2 L types / II, output price DROPPED, so
it is not the full problem.  Full problem: d = 8, all 8 / GO.  d = 3 (`ratio_d3.py`): K, L, II / GO.
At fixed prices, dropping a coordinate (same numeraire) only shrinks the reachable family (a witness
with a zero there works in the full problem), so more coordinates mechanically weaken the test.

rho* (exact oracle) by version, rho*/rho_bar in brackets:

| BEA | d=2 /II | d=3 /GO | d=8 /GO | placebo d=8 (2 seeds) |
|---|---|---|---|---|
| 15 Motor vehicles | 0.253 (1.00) | 0.099 (0.81) | 0.0057 (0.05) | 0.093, 0.076 |
| 24 Petroleum | 0.473 (0.92) | 0.157 (0.75) | 0.018 (0.09) | 0.137, 0.117 |
| 1 Farms | 0.229 (0.44) | 0.241 (0.68) | 0.038 (0.11) | 0.180, 0.202 |
| 6 Utilities | 0.199 (0.86) | 0.053 (0.36) | 0.043 (0.34) | |
| 12 Machinery | 0.039 (0.16) | 0.051 (0.63) | 0.033 (0.41) | |
| 27 Wholesale | 0.054 (0.34) | 0.072 (0.93) | 0.024 (0.13) | |
| 31 Water transp. | 0.045 (0.09) | 0.130 (0.42) | 0.036 (0.18) | |
| 46 Rental | 0.020 (0.12) | 0.016 (0.19) | 0.0025 (0.03) | |
| 49 Prof. services | 0.022 (0.05) | 0.013 (0.15) | 0.0098 (0.11) | |
| 63 State and local | 0.153 (0.84) | 0 | 0 | |

d = 3 equals d = 4 (labour split) to 5 digits for 12, 24, 46 and d = 8 equals d = 4 for 6.  Placebo
(deviations of each type from its aggregate permuted over years, `aggregation.py placebo`) lowers rho*
only by 5-25 %, real detail by 5-17 times: the drop is NOT mechanical, the aggregate indices lose
information the model uses.  No d >= 3 case is degenerate (rho* = rho_bar).  Logs:
`results/ratio_d3.log`, `results/aggregation.log` (the d = 8 and placebo numbers come from scratch
versions of `aggregation.py` with the same logic; the script itself was not rerun).  rho* at d = 2 in
the table is from `results/bench_d2_real.log` (flow oracle), d = 3 and d = 8 from the exact oracle.

## Open questions (one-sided profile)

1. Off-path solutions on the faces through the far corner: exclude, or refine the units to one-sided
   errors of single prices (t, i, +-) (one BOX query still, but uniqueness no longer follows).
2. Genericity: no ties for almost all penalties (levels are roots of exponential sums).
3. Error bound across stages at finite bisection tolerance.
4. Is the collapse <=> rho* = rho_bar a theorem?
5. Lean: blocking / Pareto / uniqueness lemmas, the link with the symmetric profile, the cover-cut
   lemma; `wfeasible_iff_path` needs asymmetric intervals.
6. Aggregation: placebo on more industries and seeds; the full 63 industries at d = 8.

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
