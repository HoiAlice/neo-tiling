# Night report 2026-10-09/10: certified minimal perturbation

Delete after reading. Scratch logs and scripts are in the session scratchpad (`REPORT.md`,
`LITERATURE.md`, `table.md`). Chapter 6 and the new section «Алгоритмическая
постановка» moved to `latex/perturbation.tex`. It is not compiled by me; it refers to
chapters 1–5 via `xr` and `build/notes.aux`, so build `notes.tex` first.

## 1. The method and its status

**Covering-cut algorithm** (`perturbation/cuts.py`, CLI `perturb.py --cuts`). A
Gomory-like cutting-plane scheme on the finite reformulation (notes, thm:reduction).

* Master: minimize π(P, Q) over the box, subject to cuts "one of the pairs (t, R) in C is
  blocked". Start: the dominance cuts y_t > y_s ⇒ ∃ i q_t^i ≤ q_s^i.
  - Blocking by one point is a choice of coordinate.
  - Blocking by a pair is d linear "pure" options or a general witness with bilinear terms.
  - The master is a MINLP solved by SCIP. Its dual bound is the lower bound.
* Separation at the master point Q*: column generation for y ∈ cone{1_S : S weakly
  reachable at Q*}.
  - If yes, Q* is optimal.
  - If no, the Farkas refutation w gives the killing coverings, i.e. a new cut.
* Validity: every cut holds at every weakly solvable Q, so the master value ≤ ρ. Proved in
  Lean.
* Finiteness: a new cut is violated at Q* while all old cuts hold there, and the number
  of cuts is finite. Proved on paper (notes, thm:finite), not in Lean. With ε-exact
  masters this gives an interval of width ε.
* Upper bound (`perturbation/primal.py`): every master point is repaired to weakly
  solvable prices.
  - Fix a family F and witnesses; the problem is then convex and always feasible.
    Alternate it with max-margin witnesses.
  - Certify in exact rationals (`verify.verify`).
  - `strict_point` tilts the result (lem:tilt) to *strictly* solvable prices. The strict
    margins are checked exactly; the extra cost is about 1e-8.
* Lower bound on SCIP trust: SCIP's dual bound is not an independently checkable
  certificate.

**Solver-free dominance relaxation** (`code/cpp/dominance.cpp`, `make -C code/cpp`,
wrapper `perturbation/cppdom.py`).

* ρ_dom = min over the coordinate choices σ of a sum of d isotonic regressions (notes,
  thm:split).
* Branch and bound over σ. The node problems are exact isotonic regressions with loss π:
  threshold splitting with min cuts (Hochbaum–Queyranne threshold theorem).
* Validated against SCIP: 60/60 random instances agree.
* Where y is weakly solvable at the found point, the exact check gives ρ = ρ_dom. Then ρ
  is certified with no MINLP at all: isotonic regressions plus min cuts for the lower
  bound, an LP plus exact rationals for the upper bound.

**Complexity** (notes, thm:hard; Lean `minPert_setCover`).

* Reduction from SET COVER: ρ = ρ_dom = δ·k*.
* Hence computing ρ is NP-hard when d is part of the input, and (1−ε) ln n approximation
  is as hard as for set cover.
* The value identity is fully proved in Lean. The reduction to complexity classes is on
  paper.
* Checked numerically on 8 random set covers.

## 2. Results (full series only)

51 full series: BW with every subset of ≥ 2 inputs (T = 25), and EU KLEMS for 5
countries × 8 industries (T = 22–26, d = 3).

**Summary**

* 45 are certified by the cut loop, with relative gap ≤ 1.1e-6.
* 42 of them are also certified solver-free by the C++ dominance B&B, in 0.01–42 s.
* ρ = ρ_dom on those 42. On UK K, US G and FR G, ρ > ρ_dom.

**Open (6).** Upper bounds come from the best of repair and the pure cut loop (§1b).

| series | lower | upper (exact) | gap | upper from |
|---|---|---|---|---|
| FR J | 0.19613 | 0.19697 | 0.4% | repair |
| US F | 4.2695 | 4.2868 | 0.4% | pure cut loop (295 s) |
| JP G | 0.13705 | 0.13907 | 1.5% | pure cut loop (30 s) |
| UK J | 2.3136 | 2.3852 | 3.0% | pure cut loop (17 s) |
| UK M-N | 0.76247 | 0.96769 | 21% | repair; the pure loop did not finish in 30 min. Lower bound: the dual bound of the master with all covering cuts y_t ≤ y(R), \|R\| ≤ d (time limit 30 min) |
| JP J | 0.13553 | 0.33449 | 60% | repair; the pure loop did not finish in 30 min |

Longer runs continue (`scratchpad/night/`, `scratchpad/seeded/`). The seeded runs are
the exact loop started with the pure loop's incumbent and cuts.

### 1b. Pure cut loop: fast certified upper bounds without a nonconvex solver

`cppdom.pure_cut_loop` runs the cut loop with pair blocking restricted to one coordinate
(q_t^i ≤ q_r^i for all r ∈ R).

* Every master is a disjunction of isotonic constraints, solved by the C++ B&B (the
  input now accepts general clauses).
* It is a restriction, so its values are not lower bounds. But the loop ends at weakly
  solvable prices, which are certified exactly. The finiteness argument is the same.
* On UK K and US G it found the exact optimum in 15 s and 26 s; the exact loop needed
  205 s and 1213 s.
* On the triangle it gives about 1.4641 > 2/5, because the optimum there needs a mixed
  witness.
* Its cuts are valid for the exact problem (Farkas). `solve_cuts(..., incumbent=...,
  initial_cuts=...)` takes them, and the CLI runs the pure loop first.

**Old reference numbers**

* BW K,L 1947–50: the "certified 0.0703" was stale. The old exact model and the new
  method both give 0.0676458.
* BW K,L 1947–56: 0.6743228 (old best 0.6748).
* BW KLEM 1947–52: 0.1465855, now certified.

Full table (lower bound = cut loop, upper bound = exact; "solver-free" = also certified
by the C++ path):

| series | T, d | ρ_dom (C++) | C++ time | ρ: lower | ρ: upper (exact) | status |
|---|---|---|---|---|---|---|
| BW EM | 25, 2 | 1.5109552 | 0.34 s | 1.5109546 | 1.5109552 | certified (also solver-free) |
| BW KE | 25, 2 | 1.5109552 | 0.49 s | 1.5109548 | 1.5109552 | certified (also solver-free) |
| BW KEM | 25, 3 | 1.5109552 | 0.96 s | 1.5109552 | 1.5109555 | certified (also solver-free) |
| BW KL | 25, 2 | 3.9593578 | 1.21 s | 3.9593578 | 3.9593578 | certified (also solver-free) |
| BW KLE | 25, 3 | 1.5109552 | 0.25 s | 1.5109551 | 1.5109552 | certified (also solver-free) |
| BW KLEM | 25, 4 | 1.5109552 | 1.13 s | 1.5109552 | 1.5109552 | certified (also solver-free) |
| BW KLM | 25, 3 | 2.3623635 | 1.03 s | 2.3623634 | 2.3623635 | certified (also solver-free) |
| BW KM | 25, 2 | 2.3623635 | 0.82 s | 2.3623635 | 2.3623635 | certified (also solver-free) |
| BW LE | 25, 2 | 1.5109552 | 0.43 s | 1.5109543 | 1.5109552 | certified (also solver-free) |
| BW LEM | 25, 3 | 1.5109552 | 0.38 s | 1.5109550 | 1.5109553 | certified (also solver-free) |
| BW LM | 25, 2 | 2.3623635 | 0.17 s | 2.3623635 | 2.3623635 | certified (also solver-free) |
| DE:C | 26, 3 | 2.2451787 | 2.26 s | 2.2451786 | 2.2451787 | certified (also solver-free) |
| DE:F | 26, 3 | 1.9308827 | 5.31 s | 1.9308827 | 1.9308827 | certified (also solver-free) |
| DE:G | 26, 3 | 1.9346128 | 0.97 s | 1.9346112 | 1.9346128 | certified (also solver-free) |
| DE:H | 26, 3 | 2.7305763 | 42.17 s | 2.7305762 | 2.7305762 | certified (also solver-free) |
| DE:J | 26, 3 | 0.2017923 | 0.06 s | 0.2017921 | 0.2017923 | certified (also solver-free) |
| DE:K | 26, 3 | 0.0717037 | 0.02 s | 0.0717036 | 0.0717037 | certified (also solver-free) |
| DE:M-N | 26, 3 | 0.6231376 | 0.16 s | 0.6231375 | 0.6231376 | certified (also solver-free) |
| DE:TOT | 26, 3 | 1.9183143 | 5.02 s | 1.9183142 | 1.9183143 | certified (also solver-free) |
| FR:C | 26, 3 | 1.3172398 | 2.89 s | 1.3172398 | 1.3172398 | certified (also solver-free) |
| FR:F | 26, 3 | 3.2302671 | 3.32 s | 3.2302641 | 3.2302671 | certified (also solver-free) |
| FR:G | 26, 3 | 0.8862383 | 1.26 s | 0.8862521 | 0.8862521 | certified |
| FR:H | 26, 3 | 3.4873378 | 5.96 s | 3.4873378 | 3.4873378 | certified (also solver-free) |
| FR:J | 26, 3 | 0.1960380 | 0.31 s | 0.1961341 | 0.1970087 | open, gap 0.4% |
| FR:K | 26, 3 | 0.7215238 | 0.61 s | 0.7215238 | 0.7215238 | certified (also solver-free) |
| FR:M-N | 26, 3 | 1.5130446 | 14.15 s | 1.5130446 | 1.5130446 | certified (also solver-free) |
| FR:TOT | 26, 3 | 2.6744680 | 5.99 s | 2.6744680 | 2.6744680 | certified (also solver-free) |
| JP:C | 26, 3 | 0.4248692 | 0.87 s | 0.4248692 | 0.4248692 | certified (also solver-free) |
| JP:F | 26, 3 | 0.7924055 | 1.08 s | 0.7924055 | 0.7924055 | certified (also solver-free) |
| JP:G | 26, 3 | 0.1345806 | 0.14 s | 0.1370484 | 0.2358828 | open, gap 41.9% |
| JP:H | 26, 3 | 0.2961565 | 0.47 s | 0.2961562 | 0.2961565 | certified (also solver-free) |
| JP:J | 26, 3 | 0.1354368 | 0.21 s | 0.1355326 | 0.3702086 | open, gap 63.4% |
| JP:K | 26, 3 | 0.4872363 | 6.98 s | 0.4872363 | 0.4872363 | certified (also solver-free) |
| JP:M-N | 26, 3 | 0.1976309 | 0.68 s | 0.1976308 | 0.1976309 | certified (also solver-free) |
| JP:TOT | 26, 3 | 0.3071890 | 0.67 s | 0.3071889 | 0.3071890 | certified (also solver-free) |
| UK:C | 22, 3 | 0.8049211 | 0.11 s | 0.8049208 | 0.8049211 | certified (also solver-free) |
| UK:F | 22, 3 | 2.1371598 | 4.43 s | 2.1371598 | 2.1371598 | certified (also solver-free) |
| UK:G | 22, 3 | 0.4092370 | 0.26 s | 0.4092367 | 0.4092370 | certified (also solver-free) |
| UK:H | 22, 3 | 1.0636745 | 0.08 s | 1.0636745 | 1.0636745 | certified (also solver-free) |
| UK:J | 22, 3 | 2.1878072 | 0.47 s | 2.3135796 | 2.6303805 | open, gap 12.0% |
| UK:K | 22, 3 | 4.8098638 | 1.53 s | 4.9863905 | 4.9863905 | certified |
| UK:M-N | 22, 3 | 0.7486023 | 0.77 s | 0.7494860 | 0.9676864 | open, gap 22.5% |
| UK:TOT | 22, 3 | 0.2194605 | 0.01 s | 0.2194605 | 0.2194605 | certified (also solver-free) |
| US:C | 26, 3 | 3.8072925 | 23.3 s | 3.8072924 | 3.8072925 | certified (also solver-free) |
| US:F | 26, 3 | 4.2505345 | 30.88 s | 4.2694646 | 4.6806466 | open, gap 8.8% |
| US:G | 26, 3 | 2.9878516 | 1.38 s | 3.1751065 | 3.1751066 | certified |
| US:H | 26, 3 | 4.7324298 | 10.55 s | 4.7324270 | 4.7324298 | certified (also solver-free) |
| US:J | 26, 3 | 1.9766498 | 0.48 s | 1.9766496 | 1.9766498 | certified (also solver-free) |
| US:K | 26, 3 | 3.2835566 | 1.36 s | 3.2835566 | 3.2835566 | certified (also solver-free) |
| US:M-N | 26, 3 | 2.7560449 | 8.88 s | 2.7560449 | 2.7560449 | certified (also solver-free) |
| US:TOT | 26, 3 | 4.4719609 | 37.19 s | 4.4719609 | 4.4719609 | certified (also solver-free) |

## 3. Hypotheses tested

* **thm:split** (fixed σ ⇒ d independent isotonic regressions): the value matches ρ_dom on
  all 51 series.
* **H1** "the relaxation optimum breaks every dominance in one coordinate": false. It
  holds on 24/51, and on every BW series.
* **H2** "ρ = ρ_dom": holds on 42/51. It fails on UK K, US G, FR G and the 6 open series.
* **H3** "no strict pair coverings at the ρ_dom optimum" (sufficient for equality):
  explains only 24 of the 42.
* **H4** "the obstructions are pairwise y_t > y_r + y_s": false. These inequalities hold
  almost everywhere, including where ρ > ρ_dom. The obstructions are collective, like
  example 2 of «Критерий разрешимости».
* **Reduction**: 8/8 random set covers give ρ = δ·k*.
* **Tilt**: strict solvability is verified exactly with δ = 1e-9 on the tested series.

Engineering findings, kept short:

* Kept:
  - pure linear disjuncts for pair blocking, which make the master 2.5–4× faster;
  - master gap 1e-4 in intermediate iterations and 1e-6 at the end;
  - the repair upper bound.
* Rejected:
  - Gurobi: the free license limits any quadratic/bilinear model to 200 variables, so the
    exact master is impossible;
  - a master without 0-1 (continuous witnesses): much weaker;
  - a pool master with explicit spectra, and refutation blocks: too slow;
  - deep multi-clause cuts, time-capped masters, box shrinking, two-coordinate pair
    witnesses: no gain;
  - weight disjunctions: valid but converge slowly.

## 4. Lean (0 sorry; `lake build` passes)

* `NeoTiling/Cuts.lean`:
  - `IsBlocked`, `exists_isBlocked_of_cut`, `isBlocked_singleton_iff`, `le_of_dominates`;
  - `isBlocked_smul_iff`, `le_minPert_of_relaxation`, `IsBlocked.exists_le_sum`;
  - `IsWeakReachable.isBlocked`, `exists_weakReachable_sum_neg`;
  - `card_le_of_cut_sequence`: the combinatorial core of finiteness. The cuts are
    pairwise distinct, so there are at most as many steps as cuts.
* `NeoTiling/Hardness.lean`:
  - `cover_bound` (the fractional-cover inequality);
  - `hardness_lower`, `hardness_upper`;
  - `minPert_setCover`: ρ = kδ on the set-cover prices. `hardness_upper` needs `1 ≤ d`,
    because it is false for d = 0.
* Not formalized:
  - the link from `card_le_of_cut_sequence` to the actual algorithm;
  - thm:split, which is elementary;
  - the complexity-class wrapper of thm:hard.

## 5. Literature (details in scratchpad `LITERATURE.md`, verification level marked)

* Closest: Shananin 1999 (Матем. моделирование 11(9)) and Agaltsov–Molchanov–Shananin
  (arXiv:1702.03576, J. Geom. Anal. 2018). They give the cone-of-spectra criterion for a
  **fixed** h, plus a CES/one-parameter case in d = 2. There is no free h, no stability or
  closure, and no price perturbation.
* Afriat/Varian/Hanoch–Rothschild: finite characterizations for single-agent data.
* Cherchye–De Rock–Smeulders–Spieksma 2014: NP-hardness of goodness-of-fit. Their measures
  drop observations or scale budgets, not prices.
* Hochbaum–Queyranne 2003 (convex cost closure) and Picard 1976 (max closure).
* Codato–Fischetti 2006 and Hooker–Ottosson 2003: Benders-type cuts.
* What seems new:
  - free-h realizability via finite spectra;
  - stability/closure;
  - minimal price perturbation as a finite problem with an exact cutting-plane method;
  - the dominance relaxation as a disjunctive isotonic regression and its NP-hardness.
  Absence in the literature is not proven.

## 6. Open

* Complexity for fixed d, in particular d = 2.
* Complexity of the separation (weak solvability at fixed prices with pair coverings).
* Conditions for ρ = ρ_dom.
* Stronger cuts: each cut is now one disjunction over 20–36 pairs.
* A solver-free path beyond the dominance relaxation: the mixed pair-blocking case is
  nonconvex.
* Finiteness in Lean.
* Process slips: I edited project files a few times with shell commands (`sed -i` on
  `cuts.py`, appends to `tests/test_cuts.py`) instead of the Edit tool. The resulting
  content is correct.
