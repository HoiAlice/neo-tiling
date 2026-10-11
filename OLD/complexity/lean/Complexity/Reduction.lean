import Complexity.Column
import Complexity.Grid
import Complexity.Stab

/-!
# The reduction from planar independent set (Section 3)

Input: a graph with edges `{eu k, ev k}` and an orthogonal grid drawing `D` of it. Output: the
prices `D.redPrices` of the gadget on the subdivision `G''` of Lemma 3.3 (marker, a reward at
every node, a heavy point above every edge of `G''`), in dimension `3`, or in any `d ≥ 3` via
`dupCoord`. All prices are rational (`redPrices_rat`).

* `reduction_neoSolvable`, `reduction_weak`: for `s ≤ 1` the output vector `D.redOutput s` is
  neoclassically (weakly) solvable iff `s ∈ STAB(G'')`.
* `exists_indep_red_iff`: `α(G'') = α(G) + ∑ₖ D.c k`, so an oracle for `STAB(G'')`
  computes `α(G)` (through the cited GLS theorems, see `Complexity.Stab`).
* `reduction_col`: the column problem at `D.redPrices` with weights `D.redWeight` and bound
  `D.redBound k` has a solution iff `G` has an independent set of size `≥ k` (Karp).
* `reduction_*_dim`: the same in every dimension `d ≥ 3`.

Not formalized here: the existence of grid drawings in polynomial area, the NP-completeness of
independent set in planar graphs of maximum degree `3`, the theorems of Grötschel, Lovász and
Schrijver, and polynomial running time (Mathlib has no complexity classes).
-/

namespace NeoTiling.Complexity

open Finset

variable {n m : ℕ} {eu ev : Fin m → Fin n}

namespace GridDrawing

variable (D : GridDrawing eu ev)

/-- Number of nodes of `G''`. -/
noncomputable def redN : ℕ := Fintype.card (D.Vert)

/-- Number of edges of `G''`. -/
noncomputable def redM : ℕ := Fintype.card (D.Edge)

/-- Numbering of the nodes. -/
noncomputable def vEq : D.Vert ≃ Fin D.redN := Fintype.equivFin _

/-- Numbering of the edges. -/
noncomputable def eEq : D.Edge ≃ Fin D.redM := Fintype.equivFin _

/-- Number of prices: the marker, the rewards and the heavy points. -/
noncomputable def redT : ℕ := Fintype.card (Option (Fin D.redN ⊕ Fin D.redM))

/-- Numbering of the prices: `none` is the marker, `inl v` a reward, `inr k` a heavy point. -/
noncomputable def idx : Option (Fin D.redN ⊕ Fin D.redM) ≃ Fin D.redT := Fintype.equivFin _

/-- First endpoint of edge `k` of `G''`. -/
noncomputable def redEu (k : Fin D.redM) : Fin D.redN :=
  D.vEq (pathU eu ev _ (D.eEq.symm k))

/-- Second endpoint of edge `k` of `G''`. -/
noncomputable def redEv (k : Fin D.redM) : Fin D.redN :=
  D.vEq (pathV eu ev _ (D.eEq.symm k))

/-- The planar point of node `v` of `G''` (in the box `1/8`). -/
noncomputable def redA (v : Fin D.redN) : Fin 2 → ℝ := D.spoint (D.vEq.symm v)

/-- The height of the heavy point of edge `k`, valid for both modes. -/
noncomputable def redEta (k : Fin D.redM) : ℝ :=
  sqn (D.redA (D.redEu k) - D.redA (D.redEv k)) * (1 / 4 + D.gamma / 2)

/-- The prices of the gadget. -/
noncomputable def redPrices (t : Fin D.redT) : Fin 3 → ℝ :=
  match D.idx.symm t with
  | none => (1 / 4 : ℝ) • one3
  | some (.inl v) => lift (D.redA v)
  | some (.inr k) => lift (mid (D.redA (D.redEu k)) (D.redA (D.redEv k))) + D.redEta k • one3

/-- The output vector: `1` at the marker and the heavy points, `1 - s v` at the reward `v`. -/
noncomputable def redOutput (s : Fin D.redN → ℝ) (t : Fin D.redT) : ℝ :=
  match D.idx.symm t with
  | none => 1
  | some (.inl v) => 1 - s v
  | some (.inr _) => 1

/-- The column weights: `0` at the marker, `-1` at rewards, `redN + 1` at heavy points. -/
noncomputable def redWeight (t : Fin D.redT) : ℤ :=
  match D.idx.symm t with
  | none => 0
  | some (.inl _) => -1
  | some (.inr _) => D.redN + 1

/-- The column bound for an independent set of size `k` in `G`. -/
noncomputable def redBound (k : ℕ) : ℤ :=
  (D.redN + 1) * D.redM - D.redN + (k + ∑ e, D.c e : ℕ)

/-- `G''` has no loops. -/
theorem redEu_ne_redEv (k : Fin D.redM) : D.redEu k ≠ D.redEv k := fun h =>
  D.pathU_ne_pathV _ (D.vEq.injective h)

/-- **The gadget.** The hypotheses of `mem_indicatorCone_iff_inStabB_of_gabriel` and
`exists_col_iff_exists_indep` for the marker `idx none`, the rewards `idx (inl v)` at the points
`redA v` and the heavy points `idx (inr k)` at the heights `redEta k`, in both modes `b`. -/
private theorem gadget :
    Function.Injective (fun v => D.idx (some (.inl v))) ∧
    Function.Injective (fun k => D.idx (some (.inr k))) ∧
    (∀ v, D.idx (some (.inl v)) ≠ D.idx none) ∧ (∀ k, D.idx (some (.inr k)) ≠ D.idx none) ∧
    (∀ v k, D.idx (some (.inl v)) ≠ D.idx (some (.inr k))) ∧
    (∀ t, t = D.idx none ∨ (∃ v, t = D.idx (some (.inl v))) ∨ ∃ k, t = D.idx (some (.inr k))) ∧
    (∀ i, 0 < D.redPrices (D.idx none) i) ∧
    (∀ t, t ≠ D.idx none → ∀ i, D.redPrices (D.idx none) i < D.redPrices t i) ∧
    (∀ v, D.redPrices (D.idx (some (.inl v))) = lift (D.redA v)) ∧
    (∀ k, D.redPrices (D.idx (some (.inr k))) =
      lift (mid (D.redA (D.redEu k)) (D.redA (D.redEv k))) + D.redEta k • one3) ∧
    (∀ v, |D.redA v 0| + |D.redA v 1| ≤ 1 / 8) ∧
    (∀ v w, v ≠ w → 0 < sqn (D.redA w - D.redA v)) ∧
    (∀ k, D.redA (D.redEu k) ≠ D.redA (D.redEv k)) ∧
    (∀ k, ∀ w, w ≠ D.redEu k → w ≠ D.redEv k →
      sqn (D.redA (D.redEu k) - D.redA (D.redEv k)) / 4 + D.gamma ≤
        sqn (D.redA w - mid (D.redA (D.redEu k)) (D.redA (D.redEv k)))) ∧
    (∀ k, sqn (D.redA (D.redEu k) - D.redA (D.redEv k)) / 4 < D.redEta k) ∧
    (∀ b k, Ok b (sqn (D.redA (D.redEu k) - D.redA (D.redEv k)) * (1 / 4 + D.gamma) -
      D.redEta k)) := by
  have hγ := D.gamma_pos
  have ha (v) : |D.redA v 0| + |D.redA v 1| ≤ 1 / 8 := D.spoint_box _
  -- distinct nodes are at positive distance
  have hsep (v w : Fin D.redN) (h : v ≠ w) : 0 < sqn (D.redA w - D.redA v) := by
    have : D.redA w - D.redA v ≠ 0 := sub_ne_zero.2 fun e =>
      h (D.vEq.symm.injective (D.spoint_injective e)).symm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 this
    unfold sqn; fin_cases i <;> simp at hi ⊢ <;> positivity
  have hpos (k) := hsep _ _ (D.redEu_ne_redEv k).symm
  -- in the box `1/8` every coordinate of the lift is at least `7/8`
  have hlift (x : Fin 2 → ℝ) (hx : |x 0| + |x 1| ≤ 1 / 8) (i) : 7 / 8 ≤ lift x i := by
    fin_cases i <;> simp [lift, one3, sqn] <;>
      nlinarith [neg_abs_le (x 0), neg_abs_le (x 1), le_abs_self (x 0), le_abs_self (x 1)]
  have hmid (v w) : |mid (D.redA v) (D.redA w) 0| + |mid (D.redA v) (D.redA w) 1| ≤ 1 / 8 := by
    simp only [mid, abs_div, abs_two]
    linarith [abs_add_le (D.redA v 0) (D.redA w 0), abs_add_le (D.redA v 1) (D.redA w 1),
      ha v, ha w]
  have hη (k) : 0 ≤ D.redEta k := mul_nonneg (hpos k).le (by linarith)
  refine ⟨fun v w h => by simpa using h, fun k l h => by simpa using h, by simp, by simp,
    by simp, fun t => ?_, fun i => by simp [redPrices, one3], fun t ht i => ?_, fun v => by
    simp [redPrices], fun k => by simp [redPrices], ha, hsep,
    fun k h => by simpa [h, sqn] using hpos k, fun k w h1 h2 => ?_,
    fun k => by have := hpos k; unfold redEta; nlinarith, fun b k => Ok.of_pos ?_⟩
  · obtain ⟨_ | v | k, rfl⟩ := D.idx.surjective t <;> simp
  · obtain ⟨_ | v | k, rfl⟩ := D.idx.surjective t
    · exact absurd rfl ht
    · simp [redPrices, one3]; linarith [hlift _ (ha v) i]
    · simp [redPrices, one3]; linarith [hlift _ (hmid (D.redEu k) (D.redEv k)) i, hη k]
  · simpa [redA, redEu, redEv] using D.spoint_gabriel (D.eEq.symm k) (D.vEq.symm w)
      (fun e => h1 (D.vEq.symm_apply_eq.1 e)) (fun e => h2 (D.vEq.symm_apply_eq.1 e))
  · have := hpos k; unfold redEta; nlinarith

/-- All prices are rational. -/
theorem redPrices_rat (t : Fin D.redT) (i : Fin 3) : ∃ q : ℚ, D.redPrices t i = q := by
  -- the rationals form a subfield `F` of `ℝ`; the node coordinates and `scale` lie in it
  let F := (algebraMap ℚ ℝ).fieldRange
  suffices D.redPrices t i ∈ F by obtain ⟨q, hq⟩ := this; exact ⟨q, hq.symm⟩
  have hs : D.scale ∈ F := by
    unfold scale bound
    simp only [← Int.cast_abs]
    exact div_mem (one_mem F) (mul_mem (ofNat_mem F 16) (add_mem (sum_mem fun x _ =>
      add_mem (intCast_mem F _) (intCast_mem F _)) (one_mem F)))
  have hA (v j) : D.redA v j ∈ F := by
    fin_cases j <;> exact mul_mem hs (intCast_mem F _)
  obtain ⟨_ | v | k, rfl⟩ := D.idx.surjective t <;>
    fin_cases i <;> simp [redPrices, lift, one3, sqn, mid, redEta, gamma, Matrix.vecHead,
      Matrix.vecTail] <;>
    repeat' first
      | exact hA _ _ | exact hs | exact one_mem F | exact ofNat_mem F _
      | apply add_mem | apply sub_mem | apply mul_mem | apply div_mem | apply neg_mem
      | apply inv_mem

/-- The prices are positive. -/
theorem redPrices_pos (t : Fin D.redT) (i : Fin 3) : 0 < D.redPrices t i := by
  obtain ⟨-, -, -, -, -, -, h0, hz, -⟩ := D.gadget
  by_cases ht : t = D.idx none
  · exact ht ▸ h0 i
  · exact (h0 i).trans (hz t ht i)

/-- **`α(G'') = α(G) + ∑ₖ D.c k`.** -/
theorem exists_indep_red_iff (k : ℕ) :
    (∃ I : Finset (Fin n), Indep eu ev I ∧ k ≤ I.card) ↔
      ∃ J : Finset (Fin D.redN), Indep D.redEu D.redEv J ∧ k + ∑ e, D.c e ≤ J.card := by
  rw [exists_indep_subdivision_iff eu ev D.c k]
  constructor
  · rintro ⟨J, hJ, hk⟩
    refine ⟨J.map D.vEq.toEmbedding, fun e => ?_, by simpa using hk⟩
    simpa [redEu, redEv] using hJ (D.eEq.symm e)
  · rintro ⟨J, hJ, hk⟩
    refine ⟨J.map D.vEq.symm.toEmbedding, fun e => ?_, by simpa using hk⟩
    simpa [redEu, redEv] using hJ (D.eEq e)

/-- **Neoclassical solvability encodes `STAB(G'')`.** -/
theorem reduction_neoSolvable (s : Fin D.redN → ℝ) (hs : ∀ v, s v ≤ 1) :
    NeoSolvable D.redPrices (D.redOutput s) ↔ InStab D.redEu D.redEv s := by
  obtain ⟨hr, -, hzr, hzh, hrh, hall, -, hz, hPr, hPh, ha, hsep, hne, hgab, hη, hηγ⟩ := D.gadget
  have hy (t) : 0 ≤ D.redOutput s t := by
    obtain ⟨_ | v | k, rfl⟩ := D.idx.surjective t <;> simp [redOutput, hs]
  rw [neoSolvable_iff_mem_indicatorCone (by norm_num) (fun t i => D.redPrices_pos t i) hy]
  exact mem_indicatorCone_iff_inStabB_of_gabriel (b := true) D.gamma_pos D.gamma_le hr hzr hzh
    hrh hall hz hPr hPh ha (fun v w h => Ok.of_pos (hsep v w h)) hne hgab hη (hηγ true) _ s
    (by simp [redOutput]) (by simp [redOutput]) (by simp [redOutput])

/-- **Weak solvability encodes `STAB(G'')`.** -/
theorem reduction_weak (s : Fin D.redN → ℝ) :
    D.redOutput s ∈ indicatorCone (weakReachableSpectra D.redPrices) ↔
      InStab D.redEu D.redEv s := by
  obtain ⟨hr, -, hzr, hzh, hrh, hall, -, hz, hPr, hPh, ha, hsep, hne, hgab, hη, hηγ⟩ := D.gadget
  exact mem_indicatorCone_iff_inStabB_of_gabriel (b := false) D.gamma_pos D.gamma_le hr hzr hzh
    hrh hall hz hPr hPh ha (fun v w h => Ok.of_pos (hsep v w h)) hne hgab hη (hηγ false) _ s
    (by simp [redOutput]) (by simp [redOutput]) (by simp [redOutput])

/-- **The column problem encodes independent set in `G` (Karp).** -/
theorem reduction_col (b : Bool) (k : ℕ) :
    (∃ S : Finset (Fin D.redT), IsReachableB b D.redPrices S ∧
        D.redBound k ≤ ∑ t ∈ S, D.redWeight t) ↔
      ∃ I : Finset (Fin n), Indep eu ev I ∧ k ≤ I.card := by
  obtain ⟨hr, hh, hzr, hzh, hrh, hall, -, hz, hPr, hPh, ha, hsep, hne, hgab, hη, hηγ⟩ := D.gadget
  exact (exists_col_iff_exists_indep D.gamma_pos D.gamma_le hr hh hzr hzh hrh hall hz hPr hPh ha
    (fun v w h => Ok.of_pos (hsep v w h)) hne hgab hη (hηγ b) D.redWeight (by simp [redWeight])
    (by simp [redWeight]) (by simp [redWeight]) _).trans (D.exists_indep_red_iff k).symm

/-- Neoclassical solvability in dimension `d ≥ 3`. -/
theorem reduction_neoSolvable_dim {d : ℕ} (hd : 3 ≤ d) (s : Fin D.redN → ℝ)
    (hs : ∀ v, s v ≤ 1) :
    NeoSolvable (dupCoord d (by norm_num) D.redPrices) (D.redOutput s) ↔
      InStab D.redEu D.redEv s := by
  have hy (t) : 0 ≤ D.redOutput s t := by
    obtain ⟨_ | v | k, rfl⟩ := D.idx.surjective t <;> simp [redOutput, hs]
  have hP (t) : dupCoord d (by norm_num) D.redPrices t ∈ orthant d := fun i => by
    unfold dupCoord; split_ifs <;> exact D.redPrices_pos _ _
  have hS : reachableSpectra (dupCoord d (by norm_num) D.redPrices) =
      reachableSpectra D.redPrices :=
    Set.ext fun S => isReachableB_dupCoord (b := true) (by norm_num) hd _ S
  rw [neoSolvable_iff_mem_indicatorCone (by omega) hP hy, hS, ← D.reduction_neoSolvable s hs,
    neoSolvable_iff_mem_indicatorCone (by norm_num) (fun t i => D.redPrices_pos t i) hy]

/-- Weak solvability in dimension `d ≥ 3`. -/
theorem reduction_weak_dim {d : ℕ} (hd : 3 ≤ d) (s : Fin D.redN → ℝ) :
    D.redOutput s ∈ indicatorCone (weakReachableSpectra (dupCoord d (by norm_num) D.redPrices)) ↔
      InStab D.redEu D.redEv s := by
  have hS : weakReachableSpectra (dupCoord d (by norm_num) D.redPrices) =
      weakReachableSpectra D.redPrices :=
    Set.ext fun S => isReachableB_dupCoord (b := false) (by norm_num) hd _ S
  rw [hS, D.reduction_weak s]

/-- The column problem in dimension `d ≥ 3`. -/
theorem reduction_col_dim {d : ℕ} (hd : 3 ≤ d) (b : Bool) (k : ℕ) :
    (∃ S : Finset (Fin D.redT), IsReachableB b (dupCoord d (by norm_num) D.redPrices) S ∧
        D.redBound k ≤ ∑ t ∈ S, D.redWeight t) ↔
      ∃ I : Finset (Fin n), Indep eu ev I ∧ k ≤ I.card := by
  simp only [isReachableB_dupCoord (by norm_num : 0 < 3) hd]
  exact D.reduction_col b k

end GridDrawing

end NeoTiling.Complexity
