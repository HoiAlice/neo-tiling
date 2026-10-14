# BOX (bottleneck / uniform-tolerance perturbation) at d = 2 is POLYNOMIAL

Verdict: **polynomial**, for the dominance relaxation (closed form, O(T^2)) and for the full weak-solvability problem (one flow LP of size O(T^3) per test, O(log T) tests, rho_inf is a root of an explicit quartic from an O(T^3) list). Both parts are proved for ALL P (no general-position assumption, see Section 6) and checked numerically (Section 5). Theorem 1 holds in every dimension d; full BOX is NP-hard for d >= 3 (Section 8).

Notation. kappa = 1+e. BOX(P,y,e) means: exists Q with Q_ti in [P_ti/kappa, kappa P_ti] and y weakly solvable at Q. Box of t: SW_t = P_t/kappa, NE_t = kappa P_t (corners, Q-space). In logs a = log P, r = log kappa, the box is a + [-r,r]^2. d(s,t) := min_i (a_{s,i} - a_{t,i}).

## 1. BOXdom: closed form

**Theorem 1.** BOXdom(P,y,r) holds iff d(s,t) <= 2r for every pair with y_s > y_t. Hence
rho_dom = (1/2) max(0, max_{y_s>y_t} d(s,t)), i.e. (1+e_dom)^2 = max over pairs y_s>y_t of min_i P_{s,i}/P_{t,i} (and >= 1).
The same r is attained (closed condition, ties allowed) by the explicit witness

  u_t = a_t - r(1,1) + tau_t (1,1),   tau_t = clip( max_{s: y_s>y_t} d(s,t), 0, 2r ).

Proof. Necessity: u_s,i <= u_t,i for some i forces a_{s,i} - a_{t,i} <= 2r. Sufficiency: u_t lies on the diagonal of its box. Take y_s > y_t and let i attain d(s,t), so d(s,t) <= 2r. Put tau_s = clip(d(p,s)) for the maximizing p (tau_s = 0 if none). If tau_s = 0 then tau_t >= clip(d(s,t)) >= d(s,t) (d(s,t) <= 2r) and u_{s,i} - u_{t,i} = d(s,t) - tau_t <= 0. If tau_s = d(p,s) < 2r (p heavier than s, hence than t): d(p,t) >= d(p,s) + d(s,t) (min of sums >= sum of mins), and d(p,t) <= 2r by the pair condition for (p,t), so tau_t >= d(p,t) >= tau_s + d(s,t) and u_{s,i} - u_{t,i} = d(s,t) + tau_s - tau_t <= 0. If d(p,s) >= 2r then tau_s = 2r and tau_t >= min(2r, d(p,t)) = d(p,t) >= 2r + d(s,t) (since d(p,t) <= 2r), same conclusion. QED

Two levels (heavy to SW corner, light to NE corner) is the special case tau in {0,2r}.

Conceptual reason (the "IVT lemma"): dominance-free means y is the restriction of an antitone function g (weakly decreasing in both coordinates; nested down-sets / staircases). A continuous antitone g exists with g(u_t) = y_t, u_t in box_t, iff g(SW_t) >= y_t >= g(NE_t) for all t (intermediate value theorem along the diagonal of the box). That is an interpolation condition on the 2T corner points only, and an antitone function with lower bounds y_s at SW_s and upper bounds y_t at NE_t exists iff there is no pair with SW_s >= NE_t (both coords) and y_s > y_t. This is exactly the pair condition. A uniform box is connected, so there is no budget coupling between conflicts. (In the additive version the budget couples them; that is where hardness lives.)

Remarks. (a) The 2-SAT relaxation (colour per conflict, clauses from 3-chains) is NOT needed and is not exact in general, irrelevant now. (b) The MILP "min r" of exact.py is unreliable in HiGHS (returned 1.0 instead of 0.5 on an example); decision-MILP (rfix) is fine and was used. (c) Nested staircase structure of rho_dom for the additive cost (HARD-RHO-D2.md A5) collapses for the bottleneck cost.

## 2. Full BOX: reduction to one flow LP

Let W_kappa = {SW_t} u {NE_t} (2T points of R^2_{>0}) and C(W) the weakly-solvable cone of W (planar.py flow LP).

**Theorem 2.** For every P (no genericity) and every kappa: (i) BOX(P,y,kappa) implies LP(kappa') for every kappa' > kappa, where
LP(kappa): exists w in C(W_kappa) with w(SW_t) >= y_t >= w(NE_t) for all t (an LP at d = 2: flow LP with one-sided residuals on the y-rows).
(ii) LP(kappa) implies BOX(P,y,kappa'') for every kappa'' > kappa.
Since the set of feasible Q is compact and weak solvability is closed in Q, BOX(kappa) <=> LP(kappa') for all kappa' > kappa, and rho_inf = inf{kappa : LP(kappa)} - 1 (LP and BOX are monotone in kappa).
The two proofs below are dimension-free; only the LP (flow LP) is specific to d = 2.

Proof (i). Let S_k be weakly reachable at Q with y = sum lam_k 1_{S_k}; put K_k = conv{Q_s : s not in S_k} + R^2_+ (closed convex up-set, K_k = empty if S_k is everything). For t in S_k, Q_t is not in int K_k. Define w = sum lam_k 1[z not in K_k] on W_kappa'. Each {z in W : z not in K_k} is weakly reachable in W (conv of the remaining points + R^2_+ lies in K_k). Now SW'_t < Q_t strictly in both coordinates: if t in S_k then SW'_t not in K_k (else Q_t in int K_k), so w(SW'_t) >= y_t; if t not in S_k then NE'_t > Q_t strictly gives NE'_t in int K_k, so the term of k vanishes in w(NE'_t) while y_t gets 0 from k too, hence w(NE'_t) <= y_t. QED
Proof (ii) (all P). Flow decomposition of the LP solution (plus the boundary parts g, as planar.certify) gives weakly reachable sets S_k of W_kappa with masses m_k >= 0 and sum_k m_k 1_{S_k}(SW_t) >= y_t >= sum_k m_k 1_{S_k}(NE_t). Let K_k = conv(W\S_k) + R^2_+ (K_k = empty if S_k = everything, then theta_k = 1), s_k(z) = min{s : z + s(1,1) in K_k}; s_k is convex and finite, hence continuous, and K up-set gives: z + s(1,1) in K iff s >= s_k(z). Weak reachability of S_k means: no point of S_k is in int K_k, i.e. s_k >= 0 on S_k; points of W\S_k lie in K_k, s_k <= 0 there. The corners SW''_t, NE''_t of the bigger box (kappa'' > kappa) are strictly SW of SW_t and strictly NE of NE_t. Hence s_k(SW''_t) > 0 if SW_t in S_k, and s_k(NE''_t) < 0 if NE_t not in S_k (else the point would be in the interior of K_k, resp. SW_t in int K_k). Choose delta > 0 below all these finitely many positive margins and put theta_k = clip(s_k/delta, 0, 1) = integral over u in [0,1] of 1[z not in K_k - u delta (1,1)]: continuous, antitone, an average of indicators of complements of translated convex up-sets. phi = sum m_k theta_k is continuous with phi(SW''_t) >= sum m_k 1_{S_k}(SW_t) >= y_t and phi(NE''_t) <= y_t (by the margins). The IVT on the diagonal of the bigger box gives Q_t with phi(Q_t) = y_t. Finally y = phi(Q) is a positive combination of the indicators of the sets {t : Q_t not in K_k - u delta(1,1)}, each weakly reachable at Q (conv of the remaining points + R^2_+ lies in the translated up-set, which misses Q_t; supporting functional xi >= 0, xi != 0), so y is in the weak cone and weakly solvable (weakSolvable_iff). Compactness/closedness gives kappa'' = kappa. QED
(For generic P one can take kappa'' = kappa directly, which is what construct.py does; construct2.py implements the degenerate version with kappa'' > kappa.)

Consequence: Theorem 1 is the special case where weak reachability is replaced by dominance (blockers of size 1).

Canonical position question (Task 2). The dominance-optimal Q (Theorem 1) does NOT make y weakly solvable in general: the triangle P = [[4,1],[3,3],[1,4]], y = [1,5,3] has rho_dom = 0 but kappa* = sqrt(6/5) = 1.0954 (e = 9.5%): (3,3) lies above the segment through (4,1),(1,4) and y_t = 5 > 1 + 3, so the heavy point must go to SW and the two lights to NE, 6/kappa <= 5 kappa. Covers do matter: on random instances kappa* > kappa_dom in 28 of 160 (17.5%). The cover conditions are not resolved "inside the dominance witness"; they are resolved by the LP, i.e. by the same corner/IVT principle with weak reachability in place of dominance.

## 3. rho_inf: finitely many critical values (Task 3)

The chain graph of W_kappa (Out/Bnd sets, arcs) depends only on: the coordinate orders of the 2T corner points (changes at kappa^2 = P_{s,i}/P_{t,i}) and the orientation of every triple of corners (sign of cross(a,b,q), kappa^2 * cross is a polynomial of degree <= 4 in kappa). So there are at most 2*C(T,2) + 4*C(2T,3) = O(T^3) critical values; between two consecutive ones the LP is the same LP, so feasibility is constant, and by monotonicity + closedness rho_inf is a critical value (kappa^* is a root of a quartic; in logs for the pair formula it is the explicit sqrt in Theorem 1). Algorithm: compute the critical set (crit.py), sort, binary search with exact-rational chain graph + LP: O(log T) LPs, each O(T^3) variables. Observed: kappa* (30-step bisection) lies in the critical set up to 1e-7 in 28/28 tests (|crit| about 50 for T=5). Timing: one LP 0.01 s (T=5), 0.06 s (T=10), 0.12 s (T=15), 1.4 s (T=20).

## 4. Scope

* Theorem 1 and Theorem 2 are proved for all P, y >= 0, uniform box (Section 7: per-point and per-coordinate boxes too). Nothing about the additive (sum) version.
* The only d = 2 ingredient is the LP: cone membership of W with one-sided bounds is a flow LP at d = 2 and NP-hard at d >= 3 (Section 8).

## 5. Numerical validation (all scripts in this folder; python = project .venv)

| Check | Script | Result |
|---|---|---|
| Thm 1 closed form vs exact decision MILP, at r = rho_dom (feasible) and r - 1e-4 (infeasible) | t_dom.py | 401 instances (T 3..12, 2..7 levels; families random grid, anti-diagonal, nested staircases, near-diagonal, real; plus the triangle): 0 disagreements |
| Thm 1 canonical witness u_t at exactly r = rho_dom is dominance-free (tol 1e-9) and in the box | t_dom.py | 401/401 |
| Same with the g-construction (IVT) at pair bound + 1e-4 | cmp2.py | 300/300 |
| Thm 2 (ii): explicit Q from LP solution (flow decomposition, theta_k, IVT bisection) at kappa*(1+0.1%) / (1+0.02%), exact-rational flow_lp residual of the constructed Q | construct.py | 174/174: in box, residual 0 (T = 3..6) |
| Thm 2: random search for Q (corners + random + level-monotone) finds a weakly solvable Q at kappa*(1+0.5%) | t_suf.py, t_suf2.py | 83/87, 59/59, 54/59 found; every miss is found at margin <= 5% (search limitation, the explicit construction above has no misses) |
| Thm 2 (i): below kappa* no Q found (random search at kappa*(1-1%/2%)) | t_suf*.py | 0 found (one hit was an artifact: kappa*(1-0.5%) < 1) |
| Thm 2 (i) necessity: Q random, y = positive combination of reachable sets, P = perturbation of Q inside radius r0; LP kappa* <= exp(r0) | t_nec.py | 60/60 |
| Critical values | t_crit.py | 28/28 |
| Degenerate P: integer grids (ties in coordinates, collinear corners), LP at kappa*(1+1e-4), explicit Q in the box of kappa*(1+2e-3), exact-rational flow_lp residual | construct2.py | 96/96 (grids 4, 5, 6; T 3..6): in box, residual 0 |
| Per-coordinate boxes, dominance: closed form lam = max_pairs min_i (a_si-a_ti)/(w_si+w_ti), diagonal witness vs decision MILP | weighted.py | 300/300 |
| Per-coordinate boxes, full: explicit Q at lam*(1+1e-3) | t_weighted.py | 26/26 |

Files: construct2.py, weighted.py, t_weighted.py, exact.py (decision/optimisation MILP), twosat.py (relaxation, not needed), pair.py, boxdom.py (Theorem 1 + witness), gcons.py (g-construction), lp_box.py (the LP of Thm 2, kappa_lp bisection), construct.py (explicit Q), crit.py (critical values), t_*.py, cmp*.py (tests), *.out (logs).

## 6. Degenerate P (closed)

Handled by the proof of Theorem 2 (ii) itself: the margins come from the strictly bigger box, not from general position. Part (i) never used genericity. The only remaining step is closedness: {Q in box_kappa : y weakly solvable at Q} is closed (WeakSolvable is a closure) and compact, and decreases in kappa, so the intersection over kappa'' > kappa is nonempty. The semicontinuity direction that matters: weak reachability of S is a closed condition in the points (limits of reachable sets are weakly reachable), which is why we pass to a bigger box instead of perturbing P (perturbing P would need lower semicontinuity of the cone, which is false). Numerically verified on 96 integer-grid instances (construct2.py).

## 7. Per-point / per-coordinate tolerances

Box of t: [P_ti/kappa_ti, kappa_ti P_ti], rectangle with corners SW_t, NE_t. Everything above goes through verbatim (the IVT runs along the diagonal of the rectangle; part (i), (ii) use only SW''_t < SW_t, NE''_t > NE_t strictly, obtained by scaling all kappa_ti up). W_points takes a (T,2) array.
Theorem 1': BOXdom holds iff for every y_s > y_t some i has SW_{s,i} <= NE_{t,i}, i.e. a_{s,i} - a_{t,i} <= r_{s,i} + r_{t,i}. With r_ti = lam w_ti the minimal scale is lam = max over y_s>y_t of min_i (a_si - a_ti)/(w_si + w_ti). The witness is the monotone path point u_t = SW_t + tau_t (NE_t - SW_t), tau_t = clip(max_{s: y_s>y_t} min_i (SW_{s,i}-SW_{t,i})/(NE_{t,i}-SW_{t,i}), 0, 1). (It coincides with Theorem 1 for equal radii.) Verified 300/300 (weighted.py) and full version 26/26 (t_weighted.py). Minimizing a weighted max e is the same bisection in lam.

## 8. Dimension

* Theorem 1 does not use d = 2: d(s,t) = min over all coordinates i in [d], same proof (the inequality d(p,t) >= d(p,s) + d(s,t) holds for min over any index set), same IVT lemma. So BOXdom is O(d T^2) in every dimension.
* Full BOX at kappa = 1 (e = 0) is exactly "y weakly solvable at P". That is NP-hard at d = 3: /Users/olegoleg/Code/neo-tiling/np-hardness/README.md states a Karp reduction from graph 3-colouring to neoclassical solvability and to weak solvability at fixed rational prices in R^3_{++} (Lean: NPHardness, Main.lean weakSolvable_iff_colorable). Hence BOX(P,y,e) (with e part of the input, e = 0 allowed) is NP-hard for d = 3, and for d >= 3 by the same statement if the construction is padded (only d = 3 is stated in that folder; I did not check padding). In NP for rational data at d = 3? Not claimed here. At d = 2: polynomial (this note). So d = 2 is exactly the boundary, and e > 0 does not make it easier at d = 3 only in the trivial sense that e = 0 is a special case; the decision "rho_inf <= e" is NP-hard for fixed e = 0.
* Theorem 2 (the reduction BOX <-> cone membership of the 2T corner points with one-sided bounds) is dimension-free; the LP is replaced by the cone-membership problem for 2T points in R^d.

## 9. Lean-friendly statements (not formalized; names from NeoTiling and perturbation/lean/Perturbation/Decision.lean)

Conventions: `open NeoTiling Perturbation`; `P Q : Fin T → Fin d → ℝ`, `y : Fin T → ℝ`, `e : ℝ`, `0 ≤ e`, `∀ t, P t ∈ orthant d`.

```lean
/-- pert (π) as a box. -/
theorem pert_le_iff {p q e : ℝ} (hp : 0 < p) (hq : 0 < q) (he : 0 ≤ e) :
    pert p q ≤ e ↔ p / (1 + e) ≤ q ∧ q ≤ p * (1 + e)

/-- no strict dominance from higher to lower level (the dominance relaxation). -/
def NoDom (Q : Fin T → Fin d → ℝ) (y : Fin T → ℝ) : Prop :=
  ∀ s t, y t < y s → ∃ i, Q s i ≤ Q t i

def BoxDom (P) (y) (e : ℝ) : Prop :=
  ∃ Q, (∀ t, Q t ∈ orthant d) ∧ (∀ t i, pert (P t i) (Q t i) ≤ e) ∧ NoDom Q y

def Box (P) (y) (e : ℝ) : Prop :=   -- d = 2 or any d >= 2 for weakSolvable_iff
  ∃ Q, (∀ t, Q t ∈ orthant d) ∧ (∀ t i, pert (P t i) (Q t i) ≤ e) ∧ WeakSolvable Q y

/-- Theorem 1 (any d). -/
theorem boxDom_iff (hP : ∀ t, P t ∈ orthant d) (he : 0 ≤ e) :
    BoxDom P y e ↔ ∀ s t, y t < y s → ∃ i, P s i ≤ (1 + e) ^ 2 * P t i
```
Explicit witness for `←`: `Q t i = P t i / (1 + e) * exp (τ t)` with `τ t = min (2 * log (1 + e)) (max 0 (sup over s with y t < y s of log (min_j P s j / P t j)))` (same coordinate shift for all i); the key inequality is `min_i (a_pi - a_ti) ≥ min_i (a_pi - a_si) + min_i (a_si - a_ti)`.

Theorem 2 (index `Fin (T + T)`: first block the SW corners, second the NE corners):
```lean
/-- corner configuration -/
noncomputable def corners (P : Fin T → Fin d → ℝ) (e : ℝ) : Fin (T + T) → Fin d → ℝ :=
  Fin.append (fun t i => P t i / (1 + e)) (fun t i => P t i * (1 + e))

/-- LP(e): one-sided cone membership on the 2T corners. -/
def CornerFeasible (P) (y) (e : ℝ) : Prop :=
  ∃ w ∈ indicatorCone (weakReachableSpectra (corners P e)),
    (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)

/-- Theorem 2 (2 ≤ d, P positive, y ≥ 0): BOX is the limit of the corner problem from above. -/
theorem box_iff (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) (hy : ∀ t, 0 ≤ y t) (he : 0 ≤ e) :
    Box P y e ↔ ∀ e' > e, CornerFeasible P y e'
```
Proof pieces as separate statements: `Box P y e → CornerFeasible P y e'` (e' > e), `CornerFeasible P y e → Box P y e'` (e' > e), `isCompact`/closedness: `Box P y e ↔ ∀ e' > e, Box P y e'` (compact boxes, `WeakSolvable` is `P ∈ closure ...`, so `{Q | WeakSolvable Q y}` is closed).
The two-sided analytic lemma used in `CornerFeasible → Box`: for a closed convex up-set `K ⊆ ℝ^d` with `K ≠ ∅`, `s_K z = sInf {s | z + s • 1 ∈ K}` is continuous and `z + s • 1 ∈ K ↔ s_K z ≤ s`.
Weighted version: replace `e` by `κ : Fin T → Fin d → ℝ`, `1 ≤ κ`, boxes `Icc (P t i / κ t i) (P t i * κ t i)`; `boxDom_iff` becomes `∀ s t, y t < y s → ∃ i, P s i / κ s i ≤ P t i * κ t i`.
