# HANDOFF — read this first (written 2026-10-16 before a context reset)

Owner's goal: ONE journal-quality chapter (level of Mathematics of Operations Research) on an EXACT
algorithm for the least l_p perturbation of prices in log space that makes outputs y weakly solvable,
built on the box oracle (= polynomially many calls of the weak-solvability oracle; a MILP inside the
oracle is fine and unavoidable — NP-hardness for d >= 3).  Chat in Russian, code/Lean/comments in
English.  Edit only inside `l1-perturbation/` (lakefile is NOT edited; Lean checked with
`lake env lean l1-perturbation/lean/L1Perturbation/Reduction.lean`).  Run solvers one at a time.

## Owner's requirements (verbatim intent)
1. The algorithm provably approaches the optimum (LB -> OPT, UB -> OPT).
2. It never crashes because of oracle errors; it ALWAYS returns a weakly solvable point (certified) and
   a lower bound with a certificate.
3. Even "at the limit of precision" the bounds stay close; a computational tolerance parameter as in
   normal solvers.
4. NO crutches (no repair heuristics, targeted lifts, ad-hoc grids, SCIP master, retries).  Find the
   fundamental cause of every failure.  Minimal code in the folder.  Cite literature, do as it is done
   there where possible.
5. Test/illustrate ONLY on non-degenerate data (memory: feedback-nondegenerate-examples).  Show
   pictures as clickable file links.  Don't waste the owner's time: think before running, no
   multi-hour blind runs.

## STATE 2026-10-16 morning (overrides everything below)
Algorithm = Tuy's polyblock QA with a MILP master + combinatorial Benders cuts from the oracle's NO
certificate (covers).  Key pieces, all in code (solve.py, master.py, problem.py):
* metric flag: "log" (ln q - ln p) or "rel" (q/p - 1, Varian / Demuynck–Rehbeck price error).  In "rel"
  the corners p(1 -+ z) are linear => cover rows exact for fixed mu; "log" uses PWL (16 segments,
  incremental binaries) over e^z on the left, tangents on the right.
* cover cuts: NO certificate (lam, C) of exact_oracle (C read from eo._HINTS + strict dominances),
  deletion filter to a minimal C' with lam(S) >= 0 on sets respecting C' (0/1 MILP), cut "some cover of
  C' absent" with the certificate's mu.  Lean: `not_boxCone_of_certificate`.
* delta-query at v + delta 1, delta = eps UB / (4 ||c||): optimum lies on ties, the float master point
  only approximately; this box covers the tie.  THIS was the fix that made real data converge.
* projection along 1 from v (Tuy 2000 p.479), at most proj_steps queries; polyblock cut on minimal
  years at the infeasible end (needed only for the finiteness proof).
* UB in the loop = box cost ||c o max(alpha, beta)|| (valid by the reduction theorem); Q constructed
  and exactly verified ONCE at the end from the best box (exact rational verification is expensive).
* corners rounded to short rationals with RELATIVE precision 1e-12 (`_short`); zero half-width keeps
  p exactly; data prices limit_denominator(1e9) in data.py.  (Absolute rounding broke tiny BEA prices.)
* relative gap: stop when UB - LB <= eps UB; master mip_rel_gap = max(eps/4, gap/4).
Results: tiny hard instances rel p=1,2,inf converge (seconds to minutes); BEA d=8 slices solved to
optimality in 1-6 min (rel, p=1) — see experiments log in the tex computations section.
Lean (Reduction.lean, 671 lines, no sorry): + relDev, exists_weakSolvable_iff_boxFeasible_rel(_lp),
not_boxCone_of_certificate.  Tex rewritten (algorithm + literature); computations section to fill.

## BRIEF CHANGE 2026-10-16 (after the reset) — overrides the section below
Owner: per year NOT one scalar but d parameters — every price may move (the per-price model, as in
the code).  Goal unchanged: an EXACT algorithm, built on the literature, for the closest prices (l_p
in log space) making y weakly solvable.  The numeraire section below is kept only as a remark.
Decided method for the per-price model: MONOTONIC OPTIMIZATION (Tuy 2000 SIAM J. Optim. 11(2);
Rubinov–Tuy–Mays 2001 Optimization 49; Tuy–Al-Khayyal–Thach 2005 "Monotonic optimization: branch
and cut methods"): minimize an increasing cost over the up-closed set H = {z : box of z passes the
box query}.  The master MILP = polyblock outer approximation (plus valid dominance / sign rows).
Polyblock step = cut at an UPPER BOUNDARY point of the complement (Tuy: projection of the vertex on
the boundary of H); we take a maximal infeasible point on the conflict years: coordinates that can be
raised to zmax are dropped from the cut, the rest raised together by bisection.  Cut point >= old
lift point, so the old termination proof stays valid.  Absence of covers is NOT convex here (and
"present" is not convex either: bilinear lambda * e^beta), so OA does not apply.

### Literature check 2026-10-16 (PDFs in ../references/, read in full by agents)
* Our algorithm = Algorithm QA of Tuy–Al-Khayyal–Thach 2005 (§4.4, pp.54-55; copolyblock, min over
  conormal H) in the case WITHOUT normal constraints: incumbent always feasible, finite eps-stop
  (their Remark 2.4).  MILP master = argmin over proper vertices (Prop 4.2', Prop 3(ii) of tuy2006).
  Projection along v = e from the vertex is Tuy 2000 p.479 implementation issue 3 (rho^v_H), its
  convergence p.476 note 5.  Our finite bound (packing, tau-separated master points) is elementary and
  stronger than their subsequence convergence (Thm 2 of Tuy 2000).
* Up-closed H is automatically robust (= cl int H), so Tuy 2005 / SIT "essential" machinery is NOT
  needed; LB <= OPT is exact (cuts at exact infeasible points).  Cite Tuy 2005 only for the critique of
  eps-relaxation.
* Reduction cut (Prop 2.4) is useless here: checked, all a'_i = 0 (any single coordinate may be 0 if
  the others are at zmax).
* Conflict = combinatorial Benders cut (Codato–Fischetti 2006 eq. 7/21, greedy deletion filter §1);
  Fischetti–Salvagnin–Zanette 2010: minimality of the conflict is the main speed lever -> we filter
  years, then coordinates (coordinate leaves if NO persists with it at zmax).
* Dimension: the texts say polyblock methods work for n <~ 10 and slow near the optimum for n >~ 5
  (shallow cuts); largest test n = 100 with LP bounds.  Our n = 2dT = 16..24 already slow for p = 1, 2;
  p = inf converges.  Honest statement for the chapter.
* 15-min run, T=4 d=2 p=1 seed 3 (n=16): LB 0.388, UB 0.857, 108 cuts; iteration time grows from
  ~0.2 s to ~170 s — the MASTER MILP is the bottleneck (polyblock vertex explosion moved into the
  MILP), oracle calls are cheap at T=4.  Literature remedies not yet tried: single-tree lazy cuts
  (Codato–Fischetti), restart / cut purge (Tuy 2000 p.476).
* breckner2001.pdf in references is an unrelated paper (stochastic Navier–Stokes), not Rubinov–Tuy–Mays.

## (SUPERSEDED) DIRECTION DECIDED IN THE LAST DISCUSSION (owner: "молоти в этом направлении")
Literature (see below) perturbs ONE SCALAR PER OBSERVATION (Afriat / Varian efficiency, expenditure
error).  Our analog: error of the numeraire price of year t:  q_t = p_t * exp(theta_t)  (all
normalized prices of year t move together).  Cost: l_p of (c_t theta_t)_t, 1 <= p <= inf.
* max-type (p = inf) <-> Afriat index: exact by breakpoints + bisection (already done in
  ../price-perturbation: box radius, `proj.least_radius_exact`); cite Cherchye et al. Algorithm 1.
* sum-type (p < inf) <-> Varian index: expected NP-hard (+ inapproximable) by a reduction from
  INDEPENDENT SET as in Cherchye–De Rock–Smeulders–Spieksma.  TODO: prove for our model (theorem).
* KEY NEW LEMMA (to prove, then Lean): in this model the ABSENCE of a cover is CONVEX in theta.
  Cover (t, A) present  <=>  exists lam in simplex(A): sum_s lam_s e^{theta_s} p_s < e^{theta_t} p_t.
  Substitute mu_s = lam_s e^{theta_s - theta_t}:  present <=> max_{mu in M} sum_s mu_s e^{theta_t - theta_s} > 1,
  M = {mu >= 0 : sum_s mu_s p_s <= p_t}  (a fixed polytope from the data; strictness handled: the sup
  over the open set equals the max over M and is not attained inside when = 1).
  So  ABSENT <=> sum_s mu^k_s e^{theta_t - theta_s} <= 1 for every vertex mu^k of M  (log-sum-exp,
  convex).  |A| = 1 (dominance): linear, theta_t - theta_s <= min_i ln(p_s^i / p_t^i).
  With the box theorem the same holds for corners p_t e^{-alpha_t}, p_t e^{beta_t} (one scalar per corner).
* Exact algorithm (all standard, cite): combinatorial Benders (Codato–Fischetti 2006; conflicts =
  minimal infeasible subsets of years, explained by covers via the oracle's Farkas vector) + master =
  CONVEX MINLP solved exactly by outer approximation (Duran–Grossmann 1986, Fletcher–Leyffer 1994):
  tangent cuts of the convex absence constraints are GLOBALLY valid, no piecewise-linear grids.
  Finite: finitely many covers / cut sets; OA converges for convex MINLP.
* The per-price model (each price its own l_p deviation) is NOT convex in this sense (checked
  numerically: violations) -> keep as remark/extension; for it only the box/polyblock theory holds.

## Literature (read, with what to cite)
* Cherchye, De Rock, Smeulders, Spieksma, "Goodness of fit measures for revealed preference tests:
  complexity results and algorithms" (ACM TEAC; comsoc 2012 version
  https://comsoc-community.org/assets/proceedings/comsoc-2012/Cherchye.pdf): AI polynomial (sort
  critical values p_i q_j, bisection with GARP test; HARP via minimum cycle mean), VI NP-hard,
  HI no rho-approximation; reductions from independent set.  Text extracted:
  scratchpad lit/cherchye.txt (may be gone).
* Demuynck & Rehbeck, "Computing revealed preference goodness-of-fit measures with integer
  programming", Economic Theory 76(4) 2023 (WP https://dipot.ulb.ac.be/dspace/bitstream/2013/359107/3/040.pdf):
  GARP as MILP (u_t, binaries U_tv, (IP-1)-(IP-4)); Section 5 "average price error" = l1 price
  perturbation for GARP solved by ONE MILP (IP-15..19) — possible because GARP is LINEAR in prices
  (quantities are data).  Our rationalizability is bilinear (latent witnesses) and NP-hard for d>=3,
  so their single-MILP trick does not transfer; the oracle decomposition is the analog.
* Dean & Martin, "Measuring rationality with the minimum cost of revealed preference violations",
  REStat 98(3) 2016 (supp. https://www.columbia.edu/~md3405/Working_Paper_11_Supp.pdf): enumerate all
  cycles (Johnson's algorithm) + minimum set cover by IP; NP-hard (Shiozawa 2015, Econ. Bulletin).
* Varian (1985) J. Econometrics 30: minimal perturbation of data — computationally intensive.
* Kuosmanen, Post, Scholtes (2007): productive efficiency with errors-in-variables, L-inf statistic
  (= our box).
* Tuy, monotonic optimization (normal sets, polyblocks, branch-reduce-bound; SIAM J. Optim 2000):
  framework for the per-price model (minimize increasing function over an up-closed oracle set).
* Codato & Fischetti, Combinatorial Benders' cuts, Oper. Res. 54(4) 2006.

## Current state of the folder (minimal prototype, per-price model)
* `l1pert/problem.py` (cost, rational boxes, `verified` = independent exact check of the oracle's
  certificate, `solution_from_box` returns None instead of raising, `trivial` = aligned coordinate,
  feasible by the nonemptiness lemma, no oracle), `master.py` (MILP: half-widths, year signs,
  dominance with exact big-M, box cuts, l_p objective: p=1 linear, p=inf s>=cx, 1<p<inf tangents of
  (c x/UB)^p scaled by UB), `solve.py` (master -> inner rational box query -> lift = rational box
  B_out(z)*kappa, kappa >= e^tau; NO -> minimal conflicting years Y -> cut on Y coordinates; NO on Y
  certified by `proj.oracle_brute` when 2|Y| <= 12), `data.py` (va_model d=2 from data/euklems.csv,
  us3, bea8).  Oracle: `../price-perturbation/perturb/exact_oracle.py: oracle_exact` (reused).
* Lean `lean/L1Perturbation/Reduction.lean`, no sorry, standard axioms: reduction to boxes (general,
  `_lp`, `_linf`), `BoxFeasible.mono`, one-signedness (`exists_oneSigned(_le)`,
  `exists_lt_of_mixed_lp`), dominance/cover necessity (`le_sum_of_conv_lt`, `le_of_lt`,
  `meets_of_conv_lt`), `BoxFeasible.restrict` (deleting years), `separated_bound` (packing).
* tex `tex/l1-perturbation.tex` (Russian): describes the per-price box-cut algorithm; computations
  section is a TODO.  Must be REWRITTEN for the new direction.
* tests `tests/test_l1pert.py` (tiny instances, brute-force checks) — not all pass in time.

## Lessons / fundamental causes found (keep in the paper's numerical section)
* Optimal solutions lie ON degeneracies (coordinate ties, 3 points collinear); weak solvability is
  decided there by exact equalities.  Any float master + rounding flips answers.  => all decisions on
  RATIONAL boxes; the master only proposes.
* Lift: the cost bound must use |u| <= max(alpha, beta) (point of the box), NOT alpha + beta, else the
  gap-halving proof fails by a factor 2 (tex currently says alpha+beta: fix).  The master point is
  one-signed, so max = sum there.
* Cut depth: a cut from a box only tau larger than the master point raises LB by ~gap/(2n) -> stall
  even at T = 4.  Use the deepest valid cut (maximal infeasible box on Y = projection to the boundary,
  as in monotonic optimization) — this is the standard reduction step, not a crutch.
* Box/polyblock cuts approximate a curved boundary by staircases: (1/eps)^{dim-1}; inherent to the
  per-price model.  The per-year scalar model removes this (convex absence => OA).
* Oracle errors: YES is exact (all sets/masses verified rationally); NO is exact iff its final integer
  pricing MILP (integer weights) is solved correctly and last_stats["integer_weights"] is True.
  False NO only harms LB/optimality, never feasibility of the returned Q.
* Inner loops must be bounded and every iteration must make progress (gap halving or a separated
  cut) — else report status, never hang.
* Big-M only in the master: year signs (= true bounds, fine), dominance (now exact M), box cuts
  (threshold as coefficient, safe).  Integrality tolerance * M can fake a tie: master output is a hint.
* Flow LP (poly-hardness) is SLOWER than the exact CG oracle at T = 40 (2-14 s vs 0.8-3 s): not used.

## Data (non-degenerate)
Value-added model d = 2 (EU KLEMS, `data.va_model(geo, ind)`, output price kept): 32 slices, 7
degenerate (OPT = C_bar).  Good tests: US M-N (OPT/C_bar 0.16, easy), JP M-N (needs cuts, solved),
FR M-N and JP F (hard: certified bounds only so far).  US d = 3, BEA d = 8 (8 of 10 easy).
Do NOT use US d = 2 (K,L)/II or BEA d = 2 (aggregated, output price dropped: degenerate).

## Next steps (in order)
1. Prove the convex-absence lemma (tex + Lean via /prove) and the per-year reduction (box theorem on
   paths already in ../price-perturbation: `rfeasible_iff_path`, `onesided`).
2. Rewrite master/solve for the per-year model: variables theta (or alpha_t, beta_t per year),
   dominance linear, cover-absence constraints convex with lazy OA tangent cuts, conflicts from the
   box oracle explained by covers (re-add a small `explain` using exact_oracle.CoverCuts/price_exact),
   certified NO on small conflicts by enumeration, rational boxes for every decision.
3. Prove NP-hardness of the sum version (independent-set reduction in the style of Cherchye et al.).
4. Tests on tiny instances vs brute force; computations on the non-degenerate data; rewrite tex as
   the chapter with citations; README.
