# Price perturbation at d = 2: a polynomial box algorithm and NP-hardness of additive costs

Status date: 2026-10-12. Detailed proofs, scripts and logs are in `perturbation/workbench/`; this report is self-contained at the level of statements and proof structure and cites those files for the full arguments and certificates.

## 0. Setting and summary

**Data.** Prices `P ∈ Q^{T×2}_{>0}` (point `t` has prices `P_{t,1}, P_{t,2}`), levels `y ∈ Q^T_{≥0}`.
**Weak solvability.** `WeakSolvable Q y` is the closure notion of `NeoTiling/Closure.lean`; by `weakSolvable_iff` (d ≥ 2, Q ≥ 0, y ≥ 0) it is equivalent to `y ∈ cone{1_S : S weakly reachable at Q}`, where `S` is weakly reachable iff every `t ∈ S` has `ξ ≥ 0, ξ ≠ 0` with `ξ·(Q_s − Q_t) ≥ 0` for all `s ∉ S`. Equivalently: no `Q_t`, `t ∈ S`, lies in the interior of `conv{Q_s : s ∉ S} + R²_{≥0}`.
**Perturbation problems.** For per-coordinate costs `φ_{t,i}` (unimodal, minimal at `P_{t,i}`):

    PERT[φ](P, y, θ):  ∃ Q > 0 with WeakSolvable Q y and Σ_{t,i} φ_{t,i}(Q_{t,i}) ≤ θ.

The reference cost is `π(p,q) = max(q/p, p/q) − 1 = e^{|ln q − ln p|} − 1` (`perturbation/lean/Perturbation/Decision.lean`: `pert`, `totalPert`, `Decide`).

**Results (d = 2).**

| Cost class (additive, unimodal per coordinate) | Complexity | Status |
|---|---|---|
| `φ_{t,i} ∈ {0, ∞}` (an arbitrary closed box `[L, U]`; also any max-type distance `max_{t,i} φ_{t,i}` via its sublevel boxes) | **polynomial**: one exact flow LP on the 2T box corners, rational witness | **proved** (Part I), independently reviewed |
| `φ = π` (fixed, finite, convex in `ln q`) | **NP-hard** (reduction from MAX-CUT, max degree 3) | lower-bound direction proved (modulo finite certified computations); upper-bound direction proved except one lemma on weak solvability of the glued optimum, see §II.6 |
| `φ` given in the input (any finite unimodal) | NP-hard | as for `π` (contains it) |
| fixed `φ(ln q − ln p)`, `φ` even, convex, `C²`, `φ(0) = φ'(0) = 0 < φ''(0)` (e.g. `r²`, `cosh r − 1`) | NP-hard for small grid step | lower bound proved for `r²` (all `h`) and the class (`h ≤ h_0(φ)`); upper bound conditional on the same weak-solvability lemma and on porting the layout to the retuned geometry |
| `φ(r) = |r|` (L1 in logarithms) | open | the construction provably degenerates (all gadget couplings vanish) |

The dividing line is therefore not "convex vs non-convex" but "independent tolerances vs a shared budget": with `φ ∈ {0, ∞}` every price is constrained separately and the problem is a single LP; with a finite strictly convex `φ` the sum couples the conflicts and encodes MAX-CUT. This mirrors revealed-preference goodness-of-fit indices (Afriat's uniform index is polynomial, Varian's additive index is NP-hard).

---

# Part I. Arbitrary box at d = 2 is polynomial

Full write-up: `workbench/box/BOX-FINAL.md` (supersedes `BOX.md`, `BOX-THEOREM.md`); independent referee report `workbench/box/REVIEW.md`.

## I.1 Statements

Data: rational `L ≤ U` in `R^{T×2}_{>0}` (zero-width coordinates and `L = U` allowed), rational `y ≥ 0`.
`BOX(L, U, y)`: `∃ Q` with `L ≤ Q ≤ U` and `WeakSolvable Q y`.
Corner configuration `W = (L_1, …, L_T, U_1, …, U_T)` (2T planar points, duplicates allowed); `C(W)` = cone of indicators of weakly reachable subsets of `W`.

**Theorem 1 (exact characterisation).** `BOX(L,U,y)` ⇔ there is `w ∈ C(W)` with `w(L_t) ≥ y_t ≥ w(U_t)` for all `t`.

**Theorem 2 (complexity).** The right-hand side is a linear feasibility problem with `O(T³)` variables, `O(T²)` rows, coefficients in `{0, ±1}`, right-hand sides `0` and `y_t`. Hence BOX is decided exactly in time polynomial in `T` and the bit length of `(L, U, y)` (ellipsoid / interior point with rounding).

**Theorem 3 (rational witness).** If BOX holds, an explicit rational `Q ∈ [L, U]` with `y` weakly solvable at `Q` is computed from an LP solution; each `Q_t = L_t + s*_t (U_t − L_t)` with `s*_t` a ratio of integers of at most `24b` bits (`b` = input bit length per entry).

**Theorem 4 (dominance only, any dimension d).** `∃ Q ∈ [L,U]` with no strict domination of a lower-level point by a higher-level one ⇔ for all `y_s > y_t` some coordinate has `L_{s,i} ≤ U_{t,i}`. Explicit witness, `O(dT²)`.

**Theorem 5 (bottleneck perturbation).** For boxes `[P/κ, κP]` (or any monotone continuous family), the minimal feasible `κ*` is attained and is one of `O(T³)` explicit algebraic numbers (roots of polynomials of degree ≤ 4 in κ); it is found by sorting them and `O(log T)` exact LPs. In particular `ρ_∞(P, y) := min_Q max_{t,i} π(P_{t,i}, Q_{t,i})` subject to weak solvability is computable in polynomial time.

## I.2 Proof structure

* **Inputs.** (F1) `weakSolvable_iff` (`NeoTiling/Closure.lean`). (F2) `PolyHardness.mem_indicatorCone_iff_flow` (`poly-hardness/lean/PolyHardness/FlowLP.lean`): cone membership for an arbitrary planar point set (no positivity, injectivity or general-position hypothesis) ⇔ a flow on the chain graph of the points. (F3) `cube_mem_span` (same file).
* **Lemma 1.** For `K = conv(…) + R²_{≥0}` and an arbitrary point `v`: `v ∉ int K` ⇔ a supporting `ξ ≥ 0, ξ ≠ 0` exists; `v ∉ K` gives strict separation.
* **(⇒)** From a decomposition `y = Σ λ_k 1_{S_k}` at `Q`, the corner sets `{L_t ∉ int K_k} ∪ {U_t ∉ K_k}` are weakly reachable in `W` and their combination satisfies the corner inequalities (uses only `L ≤ Q ≤ U` and that `K_k`, `int K_k` are up-sets).
* **(⇐)** On each segment `z_t(s) = L_t + s(U_t − L_t)` the functions `hi_t(s) = Σ m_k [z_t(s) ∉ int K_k]` (usc, nonincreasing) and `lo_t(s) = Σ m_k [z_t(s) ∉ K_k]` (lsc, nonincreasing) bracket `y_t` at `s* = max{s : hi_t(s) ≥ y_t}`. Every set between `R_min,k` and `R_max,k` is weakly reachable at `Q`, and `cube_mem_span` + `weakSolvable_iff` finish. No genericity, no enlargement, no compactness.
* **Algorithm.** Chain graph of the 2T corners (exact order and cross-product tests), LP of Theorem 2, path decomposition of the flow, witness `s*_t` as a maximum over facet exit parameters `λ°_k`.

## I.3 Verification

* Exact rational arithmetic throughout (exact simplex, exact reachability tests).
* 1120 random degenerate instances (zero widths, duplicates, collinear corners): 846 true with certified rational witnesses in the closed box (846/846), 274 false with no weakly solvable `Q` found by exhaustive quarter-grid search (0 violations).
* Fixed prices (`L = U`): 450/450 agree with the known fixed-price test.
* Critical families at the critical value ±10⁻⁹: 12/12 give (true, false, true).
* Theorem 4: 3000 instances in `d = 2…4`, 0 failures; 400 against brute force, 0 mismatches.
* Theorem 5: 59/59 instances with the transition exactly at one critical value.
* **Independent referee** (`box/REVIEW.md`): "correct with minor fixes"; Lean citations checked (hypotheses as claimed); 450 further instances with own generator and brute force, 0 counterexamples; all four minor fixes applied.

## I.4 Remarks

* At `d = 3` the full box problem is NP-hard: at `L = U` it is fixed-price weak solvability, NP-hard by the reduction in `np-hardness/` (3-colouring). So `d = 2` is the polynomial boundary (padding to `d > 3` not checked).
* Lean: the statement `box_iff` is written in `BOX-FINAL.md §7`; all inputs (F1)–(F3) exist and are proved; `box_iff` itself is not yet formalised.

---

# Part II. Additive costs: NP-hardness

Full write-ups: `workbench/NP-HARDNESS.md` (assembled proof and status; written before the generator was finished), `workbench/CROSSING-GADGET.md` (gadgets and layout, UPDATE 1–15), `workbench/WEAK-SOLV.md` (weak solvability, §1–17), `workbench/phi/PHI-CLASS.md` (the class of costs), `workbench/LOCALITY.md`, `workbench/CROSSING-PROOF.md`.

## II.1 Statement

**Theorem (target).** MAX-CUT on graphs of maximum degree 3 is polynomial-time reducible to `PERT[π]` at `d = 2`: from `(G, k)` one builds rational `(P, y, θ)` with

    G has a cut of size ≥ k  ⇔  ρ(P, y) ≤ θ,   ρ(P,y) := min_{Q: WeakSolvable Q y} Σ π(P_{t,i}, Q_{t,i}).

Precisely: `ρ(P,y) = S0 + J_e·(|E| − maxcut(G))` with explicit constants `S0` and `J_e = 2(√(21/20) − 1) = 0.04939`, and `θ = S0 + J_e(|E| − k) + J_e/2`.

## II.2 Gadgets

Grid: log-prices on `(1/4)Z` with step `h = 4 ln(21/20)`; a point at grid coordinate `m/4` has rational price `(21/20)^m`. Rotated coordinates `s = x + y`, `t = y − x`.

* **Switch.** Two points, top = bottom + `(d, d)`, level of top = level of bottom + gap. The higher-level top dominates the lower bottom, so a feasible `Q` must close the gap in one coordinate. Both choices cost exactly `B(d) = 2(e^{dh/2} − 1)` (Lemma 1, convexity): this choice is the **bit**.
* **U wire** (switches on an anti-diagonal, constant `s`): antiferromagnetic. Strong link (step 3) costs `E_S = 2(ρ² − 1) = 0.205` when violated, weak link (step 3.75) costs `J_e` (Prop. P, closed forms).
* **V wire** (diagonal, constant `t`): ferromagnetic, break cost ≥ 0.0858.
* **Corner, vertex star (degree ≤ 4), relay** (degree-2 star), **half-step V link** (flips the parity of a V chain).
* **Crossing core** (4 U × 5 V switches): a U wire crosses a V wire with all four terminal phases of exactly equal cost. Proof by symmetry alone: swap `x↔y` and the point reflection `q → c/q` with level reversal map the conflict set onto itself (finite check: 133 = 133 conflicts), so the energies of all bit patterns are permuted (CP Thm 1, Prop. X). Breaking either wire costs ≥ 0.0858 > J_e.

## II.3 Layout and levels

* **Explicit scheme** (`gad/scheme2.py`, CROSSING-GADGET UPDATE 10–14). Vertices are V buses on `t = 0`; every edge is an NW arm, a corner, a V track at its own height `t = T_e`, a corner and an arm. All crossings are U×V and aligned by construction. One weak link per edge in the middle of an arm tail. The odd number of antiferro links per edge is enforced by the arm step counts. The generator is polynomial: K_3 / K_4 / K_{3,3} have about 10³–10⁴ switches. A structural parity obstruction (every crossing would be misaligned) is removed by half-step V links at track ends.
* **Levels.** `y` depends on the switch centre: `y_bottom = F(s_c)`, `y_top = y_bottom + gap`, with `F` decreasing, a kink at every arm level, the slope multiplied by `ρ_F = 11` at each kink and the gap equal to 0.1 × the local slope. All numbers stay rational with `O(|E|)` bits. The conflict set equals that of a simple surrogate order, so every dominance computation uses small numbers.

## II.4 Lower bound: `ρ ≥ S0 + J_e(|E| − maxcut)` — proved modulo finite certificates

1. **Lemma 0.** Weak solvability implies that no higher-level point strictly dominates a lower one, so `ρ ≥ ρ_dom` (by hand).
2. **Lemma B (block relaxation).** Dropping conflicts between blocks lowers the minimum, and the cost splits over blocks (by hand).
3. **Lemma T (tilings).** Explicit construction: every wire stretch of any length is covered by two shifted tilings into blocks of ≤ 4 switches, with the weak link inside a block of both (by hand; machine-checked for r ≤ 60).
4. **Library certificates.** Every block type that occurs has `min cost ≥ ΣB + credit·(#violated relations)`. Credits are `2J_e` per strong relation and `J_e` per weak or core relation. Tight comparisons are closed forms proved by hand (Lemma 1, Prop. P, Lemma M). All other comparisons are interval-arithmetic branch-and-bound lower bounds with margins ≥ 0.0012, and ≥ 0.0335 for all but one strong step. The crossing core also has an exact rational Farkas certificate (Fractions only). For the canonical generator there are 13 plain block types plus the star and crossing cores; all are certified.
5. **Lemma C.** Two tilings, average credit ≥ `J_e` per relation, and an odd number of antiferro relations per edge give `cost ≥ S0 + J_e·#{edges with equal end bits}` (by hand).
6. **Audit.** On generated K_3, K_4, K_{3,3}, cube (256 patterns) and Petersen (1024 patterns) the inequality holds with slack exactly 0 and is never violated.

Status: a proof, with the block certificates as finite computer certificates (interval arithmetic; exact rational for the crossing core).

## II.5 Upper bound: an explicit feasible point — proved modulo weak solvability

1. **Glued point `Q*(σ)`.** For a cut `σ`: every switch sits at its isolated optimum; the crossing cores and the weak links of uncut edges sit at their stored optima. **Lemma G:** its cost is exactly `S0 + J_e·#uncut(σ)`.
2. **Feasibility for dominance.** Lemma R covers points of different clusters: displacement ≤ 0.6272, which gives a spacing of 6.5 grid steps, guaranteed by the scheme. Inside clusters: library feasibility.
3. **Exact audit of all conflict pairs.** 0 violations on K_3, K_4 and K_{3,3} (all patterns; up to 9.8·10⁷ conflicts per pattern) and on sampled patterns of the cube and Petersen graphs (up to 2.8·10⁸ conflicts per pattern). Cost deviation from the closed form ≤ 3.5·10⁻¹⁰. Snapping merges only structural ties: every merged pair is below 10⁻⁹ and none lies in [10⁻⁹, 10⁻⁴).
4. **Weak solvability of `Q*(σ)`, local part — certified.** Every window of radius R = 13 or R = 24 around every switch, for every local bit pattern, is weakly solvable under the level rule: 522/522 and 922/922 exact rational certificates. The window type list is mechanically complete for the scheme: it is derived from the generator's code paths, and one witness layout realises all types.
5. **Weak solvability, global part — see §II.6.**

Once weak solvability of `Q*(σ*)` holds for a maximum cut `σ*`, the closure lemma gives `ρ ≤ cost(Q*(σ*)) = S0 + J_e(|E| − maxcut)`, which matches §II.4 and proves the theorem.

## II.6 The remaining lemma

**Proved:**
* Lifting theorem (WEAK-SOLV §14): ordered clusters with local certificates against their higher context give a global cone decomposition.
* Far-field lemma (§16): beyond the window, the outside points only matter through two frontier constants per point; moderate witnesses are safe against all of them.
* Level-separation condition (§16): explicit, cheap, and necessary. Window certificates alone are **not** sufficient, and there is an explicit counterexample.

*Also proved (WEAK-SOLV §17):*
* **T-picture.** `y` is weakly solvable iff `M − y = Σ_j m_j 1[Q ∈ K_j]` for convex up-sets `K_j` (up to boundary ties).
* **Proposition H.** If a switch's own pair is tight in `x` at `Q*`, every reachable set that separates its top from its bottom contains the whole open half-plane `{x < x_top}`.

**Consequences of Proposition H:**
* Every certificate contains, for every switch, sets with a global half-plane "shadow".
* Window certificates with moderate witnesses cannot exist.
* Moving `Q*` slightly off the tie to restore moderate witnesses would need a window radius growing like `log N`.

**Open: the global accounting statement (c′).** A base `b` and, for every switch, separating sets of mass at least its gap can be chosen so that `M − y` is exactly a sum of convex up-set indicators. Evidence so far:
* exact rational whole-instance certificates on every instance small enough to compute: two interleaved crossing copies, 40/40 patterns at each of three separations; the 25-switch instance; K_3;
* the necessary condition "forced gap mass" holds with a large margin;
* no proof and no local-check formulation is known.

This is the only missing step of the NP-hardness proof. A new attempt (constructive global certificate: explicit gap sets plus a ridge-sum remainder, with the freedom to choose `y`) is in progress in `workbench/ws2/`.

## II.7 Other cost functions (`workbench/phi/PHI-CLASS.md`)

* **What does not depend on φ.** Lemma 0, all combinatorics (conflict sets, tilings, parity, layout), the crossing symmetry (needs `φ` even and the same in both coordinates), and Prop. Iso: for strictly convex `φ` the zero-excess / positive-excess pattern of every block is independent of `φ`.
* **What depends on φ.** Closed forms `B = 2φ(δ/2)`, `J(a) = 2φ((4−a)h/2)`, and `E_S ≥ 4J_e` for every convex `φ`. The crossing core is the only gadget calibrated to `π`. For `φ = r²` the library is re-tuned (strong step 5/2), and all interval certificates pass. Since `r²` is homogeneous, the step `h` does not matter.
* **Theorem S (lower bound).** Let `φ` be even, convex, `C²`, with `φ(0) = φ'(0) = 0 < φ''(0)`. Then for `h ≤ h_0(φ)` all library inequalities hold by a continuity lemma (`φ(hr)/(ch²) = r²(1 ± θ)`). Hence `ρ ≥ S0 + J_e(|E| − maxcut)`.
* **Theorem S-UB.** For `h ≤ h_1(φ)` the glued point keeps the `r²` routing and tie structure. The upper bound is then conditional on weak solvability and on porting the layout generator to the re-tuned geometry, which has not been done.
* **`φ = |r|`.** Every pair has all four bit patterns at exactly `2B` (by hand). Every block of the library is constant (LP), so the reduction outputs a constant. The complexity of the L1-log version is open.
* **Non-convex unimodal `φ` (`|r|^q, q < 1`).** Lemma 1 fails; the antiferro pair survives with a tunable gap. Open.

## II.8 Status table

| Ingredient | Kind |
|---|---|
| Part I, Theorems 1–5 | proved by hand on formal inputs (F1)–(F3); exact numerical validation; referee-checked |
| Lemma 0, Lemma 1, Prop. P (natural class), Lemma M, Lemma T, Lemma C, Lemma G, Lemma R, crossing degeneracy | proved by hand |
| Block library (13 plain types, stars, crossing core, half-step links, mirrored orientations) | finite computer certificates (interval arithmetic; crossing core exact rational) |
| Layout scheme: polynomial, conditions L1–L8, rule R, conflict-free glued point | constructive generator, conditions argued from the code; exhaustive audits on 5 graphs |
| Window weak-solvability certificates (every switch, R = 13, 24) | exact rational certificates, mechanically complete list |
| Global weak solvability (statement (c′), WEAK-SOLV §17) | **open**; exact whole-instance certificates on every computable instance; local certification provably impossible (Prop. H) |
| Lean | decision problem formalised (`Decision.lean`); box and hardness statements not yet formalised |

## II.9 Files

* `workbench/box/`: `BOX-FINAL.md`, `REVIEW.md`, `exactbox.py` (exact decision and witness), tests `t_fin*.py`.
* `workbench/NP-HARDNESS.md`, `CROSSING-GADGET.md`, `WEAK-SOLV.md`, `LOCALITY.md`, `CROSSING-PROOF.md`, `P-GAP.md`, `phi/PHI-CLASS.md`.
* `workbench/gad/`: gadget library and certificates (`np_*.py`), generator (`scheme2.py`), audits (`audit2.py`, `qstar.py`), window certificates (`exactcertW*.py`), weak-solvability tools (`ws_*.py`).
