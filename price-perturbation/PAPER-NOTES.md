# Paper notes: least price perturbation for weak solvability

State as of 2026-10-14. Read this first when assembling the paper draft. The full text with
proofs is `tex/price-perturbation.tex` (Russian). Everything below points into this folder.

## 1. The question

Prices are (d+1)-tuples known up to a common factor, normalized by price 0, giving points
p_t in R^d_{++}; outputs y in R^T_+. If y is not weakly solvable at P (criterion from
`latex/notes.tex`: y in cone{1_S : S weakly reachable}), find the least correction of the prices
that makes it weakly solvable.

## 2. Main structural insight (lead with this in the paper)

**Everything reduces to the box problem.** "Is there Q with L_t <= q_t <= U_t at which y is
weakly solvable" is ONE oracle query on the 2T corners (L_t, U_t) (box theorem, reproved in the
tex, Lean `BoxPerturbation.box_iff`, any d >= 2). A perturbation region R_t around p_t that
contains the lower and upper corners of its bounding box and a monotone path between them is
equivalent to that box. The metric only chooses the box sizes:

- equal-weight hexagon (sum of log deviations of the d+1 prices modulo scale) — same rho* and same
  solutions as the plain box (US data: 0.0897 both);
- weighted max metric d_kappa (chosen formulation, below) — zonotope = box + diagonal segment,
  bounding-box half-widths rho (1/kappa^i_t + 1/kappa^0_t);
- per-year radii, per-(resource, year) radii — same box theorem with other box sizes.

Dichotomy: regions containing their bounding-box corners (≡ box, everything exact, d = 2
polynomial) vs regions that do not (e.g. the weighted SUM metric with lambda^0 > min lambda^i,
or a rhombus): genuinely 2T-dimensional, no exact method. The sum version was REJECTED by the
author on modelling grounds — do not include it.

Suggested paper structure: (1) box theorem as the core; (2) breakpoints and the least radius;
(3) complexity; (4) profiles (lexicographic refinement); (5) the metric as a modelling layer
(where the box sizes come from, the remark on price 0); (6) computations.

## 3. Chosen formulation (modelling layer)

Penalty kappa^i_t > 0 for each price i = 0..d and year t (larger = measured more precisely).
d_kappa(a, b) = min_s max(kappa^0 |s|, max_i kappa^i |u_i + s|), u = ln a - ln b: weighted l_inf
distance of the tuples modulo the common scale. Price i is known up to relative error rho/kappa^i.
Remark in the tex: where price 0 comes from — an error in the normalizing price shifts the
normalized point along the diagonal; an equal error in all other prices does the same; the
metric picks the cheaper explanation.

Solution form (theorem (A)<=>(B)<=>(C)): one parameter per year, q_t = p_t exp(theta_t v_t),
|theta_t| <= rho, v_t = 1/kappa_t + 1/kappa^0_t. The direction is fixed by the weights (parallel
across years iff kappa_t = base * tau_t; rotating weights give rotating steps, see
`tex/figures/example_rot.png`). The problem is T-dimensional, not 2T: proven, not a choice.

## 4. Results and where they are proven

Lean library `PricePerturbation` (`lake build PricePerturbation`, no sorry, standard axioms):

| statement | Lean |
|---|---|
| ball shape (zonotope) | `wdist_le_iff`, `mem_wbox_of_wdist`, `wdist_wpath_le` |
| reduction to corners / to the path | `wfeasible_iff_corners`, `wfeasible_iff_path`, general `path_of_corners` |
| least radius exists, is a breakpoint | `least_wradius_breakpoint` (with `eventually_exists_sign_eq`, `eventually_isWeakReachable_of`, `witness_iff_homogeneous`) |
| per-year radii, R closed and up-closed, Pareto-minimal vectors exist | `rfeasible_iff_corners`, `rfeasible_iff_path`, `RFeasible.mono`, `isClosed_setOf_rfeasible`, `exists_minimal_rfeasible` |
| (unweighted special cases, kept as helpers) | `proj_iff_*`, `hex_iff_*`, `least_radius_breakpoint`, `least_radius_rational`, `projDist_le_iff_mem_convexHull` |

Paper-only (tex), not formalized: rationality of breakpoints for equal weights in the weighted
setting; the complexity theorem; the profile procedures; certificates in code.

Complexity (tex theorem "сложность", fixed d): (a) equal weights: exact rho* with O(d log T)
oracle calls, independent of the bit length L (breakpoints z = -D1/D0 rational, enumerate
C(2T+d, d+1) minors); (b) arbitrary rational weights: bisection with safe rounding, bracket of
width eps in poly(L) + O(log 1/eps) calls (bound rho_bar from the exponential sums; rounding
error eta = 2^{1-k}/min v). d = 2: oracle = flow LP, so (a) polynomial, (b) weakly polynomial.

## 5. Profiles (beyond the min-max)

- Per year (`perturb/lexprofile.py`, tex section "Профиль поправок") and per (resource, year)
  pair without weights (`perturb/pairs.py`, the author's preferred variant: "minimize via the box,
  fix only the pairs that hit the constraint").
- The set R of feasible radius vectors has NO least element (meet property false, trivially:
  correct year 1 or year 2, not neither). Lexicographic minimum of the sorted vector is the
  canonical choice; the staged procedure is exact (up to tolerance): candidate set from
  individually blocking units, joint test, superset search with branching if needed.
  Polynomial calls without branching, exponential worst case. In practice branching never
  occurred on real data (1 of 427 tiny random instances, a tolerance effect).
- US, per year (weights): 24 stages, 1015 calls, all years move, min radius 0.0027.
  US, per pair (no weights): rho* = 0.0897, 33 stages, 976 calls, 16 of 52 pairs untouched,
  moves mostly in K/II only.
- Observation (not a theorem): profile solutions line up on a near-vertical line
  p_K/p_II ≈ const — equal first coordinates make every set weakly reachable (witness e_1), and
  K is the cheapest to move. TODO in tex: check/generalize.

## 5a. Answers to questions that came up (keep for the discussion section)

- Why only scaling / one parameter per year: proven (box corners dominate any point of the box for
  both monotone properties: being separable, being covered); not a modelling restriction.
- Data cannot distinguish "error in the normalizing price" from "the same error in all other
  prices" (same normalized point); the metric picks the cheaper explanation.
- Many years sit at the vertices of their zonotopes in the plain witness only because the
  construction takes the largest feasible theta; profiles remove this artefact.
- Lexicographic minimum: the sorted vector is unique; which unit gets which radius may not be;
  branching is needed only for "either this or that" situations (no least element of R).

## 6. Oracle and computations

- d = 2: flow LP on the chain graph (`poly-hardness/`) — needed for the polynomiality theorem
  and for an exact NO certificate (one longest path); computations use column generation
  (`perturb/milp_oracle.py: oracle_cg`): LP master over weakly reachable sets, pricing = one-set
  MILP with big-M witnesses, each witness row DIVIDED BY M_st (essential). Flow LP = compact form,
  CG = path form (Dantzig–Wolfe).
- The no-good retry loop in `price_milp` is a workaround (triggers at d = 7, 3 of 4 BEA
  industries still fail) — NOT part of the method. Proper fix (TODO): exact-geometry pricing with
  lazy covering cuts x_t <= sum_{s in A} x_s, |A| <= d+1 (finite witness lists for d = 2).
- Numbers in the tex (weighted formulation): d = 2 real data (US + 10 BEA industries), synthetic
  families A–E, large d (US d=3, Berndt–Wood d=4, BEA d=4, BEA d=7) — scripts and logs in
  `experiments/` and `experiments/results/`. CG faster than flow in 7/11 real cases and in all
  synthetic families from T = 30; flow wins only on small/easy instances. Only synthetic: hand
  picked families, no example found where flow wins at large T.
- Earlier unweighted benchmarks (63 BEA industries T = 40, T up to 70) are superseded; numbers
  are in git history of the tex / chat only.

## 7. Open questions

1. Exact pricing for large d (lazy covering cuts) — d = 7 fails today.
2. Is lexicographic profile computable with polynomially many calls in the worst case, or is
   branching unavoidable on some instance?
3. The near-vertical-line phenomenon of profiles: theorem?
4. Weighted sum metric with lambda^0 > min lambda^i (2T-dimensional): rejected, but its
   complexity is open if ever needed.
5. Lean: rationality of breakpoints in the weighted equal-weights case; the complexity theorem
   is out of Mathlib's reach.

## 8. Reproducing numbers and figures

All from `price-perturbation/` (Python `../.venv/bin/python`, `PYTHONDONTWRITEBYTECODE=1`):

| item | script | output |
|---|---|---|
| box at common radius, US d=2 (rho* = 0.0897 exact, 8310 breakpoints) | `experiments/us_box.py` | `tex/figures/example.png` |
| weighted US example and equal weights | `experiments/us_weighted.py` | `tex/figures/example_zono.png` |
| rotating weights | `experiments/us_rotating.py` | `tex/figures/example_rot.png` |
| per-year lexicographic profile | `experiments/us_profile.py` | `tex/figures/example_profile.png` |
| per-pair profile (no weights) | `experiments/us_pairs.py` | `tex/figures/example_pairs.png` |
| meet-property counterexamples | `experiments/meet_check.py` | stdout |
| tables of the tex (weighted) | `experiments/bench_d2_real.py`, `bench_d2_synthetic.py`, `bench_large_d.py` | `experiments/results/*.log` |

Tests: `../.venv/bin/python -m pytest -q -p no:cacheprovider tests` (74 tests, ~3 min). Lean:
`lake build PricePerturbation` from the repo root. Run solvers one at a time (the laptop
crashed with parallel solver runs before).

## 9. Data

- `data/us_tot.csv`: EU KLEMS 2023, US total economy 1995–2020.
- `data/bea_klems_*.csv`: BEA–BLS integrated industry-level production account, research
  extension 1947–2016 (Eldridge et al. 2020, public domain), built by `data/build_bea.py` from
  `KLEMS-Research-Tables-Underlying-Data_0.xlsx` (bea.gov): Tornqvist aggregates for K and L,
  detailed prices for d = 7.
- `data/berndt_wood_klem.*`: Berndt–Wood KLEM, US manufacturing 1947–1971 (Berndt 1991 diskette).
