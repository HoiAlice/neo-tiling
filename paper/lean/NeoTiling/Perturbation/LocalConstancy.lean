import Mathlib

/-!
# Persistence of sign patterns

A family of vectors `v ρ j ∈ ℝⁿ` depends continuously on a parameter `ρ`. Suppose every
`n × n` determinant of the family that vanishes at `ρ₀` vanishes for all `ρ`. Then every sign
pattern `j ↦ sign (η₀ ⬝ᵥ v ρ₀ j)` realised by a linear functional at `ρ₀` is still realised near
`ρ₀` (`eventually_exists_sign_eq`).
-/

namespace NeoTiling.PricePerturbation

open Filter Topology Matrix

variable {n : ℕ}

/-- If `x` is a combination of the rows `M k`, `k ∈ K`, then replacing a row outside `K` by `x`
gives a singular matrix. -/
theorem det_updateRow_eq_zero_of_mem_span {M : Matrix (Fin n) (Fin n) ℝ} {K : Set (Fin n)}
    {x : Fin n → ℝ} (hx : x ∈ Submodule.span ℝ ((fun k => M k) '' K)) {k : Fin n} (hk : k ∉ K) :
    (M.updateRow k x).det = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    exact Matrix.det_zero_of_row_eq hik (by simp [Matrix.updateRow_ne hik])
  | zero => exact Matrix.det_eq_zero_of_row_eq_zero k (by simp)
  | add x y _ _ hx hy => rw [Matrix.det_updateRow_add, hx, hy, add_zero]
  | smul a x _ hx => rw [Matrix.det_updateRow_smul, hx, mul_zero]

/-- Cramer's rule: if `M` is nonsingular and replacing any row outside `K` by `x` gives a
singular matrix, then `x` is a combination of the rows `M k`, `k ∈ K`. -/
theorem mem_span_of_det_updateRow_eq_zero {M : Matrix (Fin n) (Fin n) ℝ} {K : Set (Fin n)}
    {x : Fin n → ℝ} (hM : M.det ≠ 0) (h : ∀ k ∉ K, (M.updateRow k x).det = 0) :
    x ∈ Submodule.span ℝ ((fun k => M k) '' K) := by
  have hc : ∀ k, (cramer Mᵀ x) k = (M.updateRow k x).det := fun k => cramer_transpose_apply M x k
  have h1 : Mᵀ *ᵥ cramer Mᵀ x = M.det • x := by
    rw [mulVec_cramer]; simp
  have hx : x = ∑ k, ((M.det)⁻¹ * cramer Mᵀ x k) • M k := by
    have : x = (M.det)⁻¹ • (Mᵀ *ᵥ cramer Mᵀ x) := by
      rw [h1, smul_smul, inv_mul_cancel₀ hM, one_smul]
    conv_lhs => rw [this, Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
    simp [Finset.smul_sum, smul_smul]
  rw [hx]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ K
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · rw [hc, h k hk]; simp

/-- A spanning family contains a basis `u ∘ I` whose members from `Z` span all of `u '' Z`
(extend a maximal independent subfamily of `u '' Z` to a basis). -/
theorem exists_index_basis {J : Type*} (u : J → Fin n → ℝ)
    (hu : Submodule.span ℝ (Set.range u) = ⊤) (Z : Set J) :
    ∃ I : Fin n → J, (Matrix.of fun k => u (I k)).det ≠ 0 ∧
      ∀ j ∈ Z, u j ∈ Submodule.span ℝ ((fun k => u (I k)) '' {k | I k ∈ Z}) := by
  classical
  obtain ⟨B, hBZ, -, hZB, hBli⟩ := exists_linearIndepOn_extension (K := ℝ) (v := u)
    (linearIndepOn_empty ℝ u) (Set.empty_subset Z)
  obtain ⟨C, -, hBC, hUC, hCli⟩ := exists_linearIndepOn_extension (K := ℝ) (v := u) hBli
    (Set.subset_univ B)
  have hspan : Submodule.span ℝ (Set.range (fun c : C => u c)) = ⊤ := by
    rw [eq_top_iff, ← hu, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := hUC ⟨j, Set.mem_univ j, rfl⟩
    simpa [Set.image_eq_range] using this
  have hli : LinearIndependent ℝ (fun c : C => u c) := hCli
  let bas := Module.Basis.mk hli hspan.ge
  haveI : Finite C := hli.finite
  have hcard : Nat.card C = n := by
    rw [← Module.finrank_eq_nat_card_basis bas]; simp
  let e := (Finite.equivFinOfCardEq hcard).symm
  refine ⟨fun k => (e k).1, ?_, ?_⟩
  · have h1 : LinearIndependent ℝ (fun k => u (e k).1) := hli.comp e e.injective
    have := Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of fun k => u (e k).1) |>.mp h1
    exact (Matrix.isUnit_iff_isUnit_det _).mp this |>.ne_zero
  · intro j hj
    refine Submodule.span_mono ?_ (hZB ⟨j, hj, rfl⟩)
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨e.symm ⟨b, hBC hb⟩, ?_, by simp⟩
    simpa using hBZ hb

/-- **Sign patterns persist.** Let `v ρ j ∈ ℝⁿ` (`j` in a finite `J`) be continuous in `ρ`, let
`v ρ₀` span `ℝⁿ`, and let every determinant `det (v ρ (I k))_k` vanishing at `ρ₀` vanish for all
`ρ`. Then for every `η₀`, near `ρ₀` some `η` has `sign (η ⬝ᵥ v ρ j) = sign (η₀ ⬝ᵥ v ρ₀ j)` for
all `j`.

Proof. Let `Z` be the indices with `η₀ ⬝ᵥ v ρ₀ j = 0` and pick a basis `M ρ₀ = (v ρ₀ (I k))_k`
through a maximal independent subfamily of `Z` (`exists_index_basis`); let `K = {k | I k ∈ Z}`
and `g k = η₀ ⬝ᵥ v ρ₀ (I k)`. Near `ρ₀` the matrix `M ρ` stays nonsingular; put
`η ρ = (M ρ)⁻¹ *ᵥ g`, continuous with `η ρ₀ = η₀`. For `j ∉ Z` the value `η ρ ⬝ᵥ v ρ j` tends
to `η₀ ⬝ᵥ v ρ₀ j ≠ 0`, so its sign persists. For `j ∈ Z` and `k ∉ K`, replacing row `k` of
`M ρ₀` by `v ρ₀ j` is singular (`det_updateRow_eq_zero_of_mem_span`), hence singular for all
`ρ` by hypothesis, so `v ρ j` lies in the span of the rows in `K` (Cramer), on which `η ρ`
vanishes. -/
theorem eventually_exists_sign_eq {J : Type*} [Finite J] (v : ℝ → J → Fin n → ℝ)
    (hv : ∀ j, Continuous fun ρ => v ρ j) {ρ₀ : ℝ}
    (hspan : Submodule.span ℝ (Set.range (v ρ₀)) = ⊤)
    (H : ∀ I : Fin n → J, (Matrix.of fun k => v ρ₀ (I k)).det = 0 →
      ∀ ρ, (Matrix.of fun k => v ρ (I k)).det = 0)
    (η₀ : Fin n → ℝ) :
    ∀ᶠ ρ in 𝓝 ρ₀, ∃ η : Fin n → ℝ,
      ∀ j, SignType.sign (η ⬝ᵥ v ρ j) = SignType.sign (η₀ ⬝ᵥ v ρ₀ j) := by
  classical
  obtain ⟨I, hdet, hZ⟩ := exists_index_basis (v ρ₀) hspan {j | η₀ ⬝ᵥ v ρ₀ j = 0}
  set M : ℝ → Matrix (Fin n) (Fin n) ℝ := fun ρ => Matrix.of fun k => v ρ (I k) with hM
  have hMc : Continuous M :=
    continuous_pi fun k => continuous_pi fun i => (continuous_apply i).comp (hv (I k))
  have hdc : Continuous fun ρ => (M ρ).det := hMc.matrix_det
  have hdne : ∀ᶠ ρ in 𝓝 ρ₀, (M ρ).det ≠ 0 := hdc.continuousAt.eventually_ne hdet
  set g : Fin n → ℝ := fun k => η₀ ⬝ᵥ v ρ₀ (I k) with hg
  have hgM : M ρ₀ *ᵥ η₀ = g := by
    ext k; simp [hM, hg, Matrix.mulVec, dotProduct_comm]
  -- `η ρ = (M ρ)⁻¹ *ᵥ g`, written with the adjugate to make continuity at `ρ₀` easy
  let η : ℝ → Fin n → ℝ := fun ρ => ((M ρ).det)⁻¹ • ((M ρ).adjugate *ᵥ g)
  have hηc : ContinuousAt η ρ₀ :=
    (hdc.continuousAt.inv₀ hdet).smul
      (hMc.matrix_adjugate.matrix_mulVec continuous_const).continuousAt
  have hη0 : η ρ₀ = η₀ := by
    simp only [η]
    rw [← hgM, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hdet, one_smul]
  have hηM : ∀ ρ, (M ρ).det ≠ 0 → M ρ *ᵥ η ρ = g := by
    intro ρ hρ
    simp only [η]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hρ, one_smul]
  have hlim : ∀ j, Tendsto (fun ρ => η ρ ⬝ᵥ v ρ j) (𝓝 ρ₀) (𝓝 (η₀ ⬝ᵥ v ρ₀ j)) := by
    intro j
    have : ContinuousAt (fun ρ => η ρ ⬝ᵥ v ρ j) ρ₀ := by
      unfold dotProduct
      exact tendsto_finset_sum _ fun i _ => ((continuous_apply i).continuousAt.comp hηc).mul
        ((continuous_apply i).comp (hv j)).continuousAt
    simpa [hη0] using this.tendsto
  have hall : ∀ j, ∀ᶠ ρ in 𝓝 ρ₀, (M ρ).det ≠ 0 →
      SignType.sign (η ρ ⬝ᵥ v ρ j) = SignType.sign (η₀ ⬝ᵥ v ρ₀ j) := by
    intro j
    by_cases hj : η₀ ⬝ᵥ v ρ₀ j = 0
    · -- `v ρ j` stays in the span of the rows from `Z`, on which `η ρ` vanishes
      refine Eventually.of_forall fun ρ hρ => ?_
      rw [hj, sign_zero]
      have hspan' : v ρ j ∈
          Submodule.span ℝ ((fun k => M ρ k) '' {k | I k ∈ {j | η₀ ⬝ᵥ v ρ₀ j = 0}}) := by
        refine mem_span_of_det_updateRow_eq_zero hρ fun k hk => ?_
        have h0 : ((M ρ₀).updateRow k (v ρ₀ j)).det = 0 :=
          det_updateRow_eq_zero_of_mem_span (hZ j hj) hk
        have e : ∀ ρ, (M ρ).updateRow k (v ρ j) =
            Matrix.of fun k' => v ρ (Function.update I k j k') := by
          intro ρ; ext k' i
          by_cases h : k' = k
          · subst h; simp [hM]
          · simp [hM, Matrix.updateRow_ne h, Function.update_of_ne h]
        rw [e] at h0 ⊢
        exact H _ h0 ρ
      have hker : ∀ x ∈ Submodule.span ℝ
          ((fun k => M ρ k) '' {k | I k ∈ {j | η₀ ⬝ᵥ v ρ₀ j = 0}}), η ρ ⬝ᵥ x = 0 := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, hk, rfl⟩ := hx
          have hk' : g k = 0 := hk
          simpa [Matrix.mulVec, hk', dotProduct_comm, hM] using congrFun (hηM ρ hρ) k
        | zero => simp
        | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
        | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
      rw [hker _ hspan', sign_zero]
    · -- a nonzero limit keeps its sign
      rcases lt_or_gt_of_ne hj with h | h
      · filter_upwards [(hlim j).eventually (gt_mem_nhds h)] with ρ hρ _
        rw [sign_neg hρ, sign_neg h]
      · filter_upwards [(hlim j).eventually (lt_mem_nhds h)] with ρ hρ _
        rw [sign_pos hρ, sign_pos h]
  filter_upwards [hdne, Filter.eventually_all.2 hall] with ρ h1 h2
  exact ⟨η ρ, fun j => h2 j h1⟩

end NeoTiling.PricePerturbation
