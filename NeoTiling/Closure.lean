import NeoTiling.Solvability

/-!
# Weakly reachable spectra and the closure of the solvable prices

An index `t` *strictly covers* a set `R` (`StrictCovers`) if `p_t` strictly dominates, in every
coordinate, a convex combination of the prices `p_r`, `r ∈ R`. A set `S` is *weakly reachable*
(`IsWeakReachable`) if every `t ∈ S` has a normalized witness `ζ ≥ 0`, `∑ ζ = 1`, with
`⟨ζ, p_s - p_t⟩ ≥ 0` for all `s ∉ S`.

Main results:

* `IsReachable.isWeakReachable`: reachable spectra are weakly reachable.
* `isWeakReachable_iff`: `S` is weakly reachable iff no `t ∈ S` strictly covers `Sᶜ`.
* `isReachable_shiftPrices`: for pairwise distinct prices, the shift
  `p ↦ p - δ (∑ᵢ log pᵢ) 1` makes every weakly reachable spectrum reachable for small `δ > 0`.
* `mem_closure_of_weakReachable_of_injective`: for pairwise distinct prices, `y` in the cone of
  the weakly reachable spectra of `P` makes `P` a limit of prices at which `y` is solvable.
* `mem_closure_split_step`: one coincidence of prices can be removed by an arbitrarily small move
  that keeps `y` in the cone of the weakly reachable spectra (after rematching the spectra).
* `mem_closure_of_weakReachable`: the same as above for arbitrary positive `P` (induction on the
  number of coincident pairs of prices, `defect`).
* `weakReachable_of_mem_closure`: the converse.
-/

open Set Filter Topology

namespace NeoTiling

variable {d T : ℕ} {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

/-- `t` strictly covers `R`: `∑_r w_r p_r < p_t` in every coordinate for convex weights `w`
supported on `R`. -/
def StrictCovers (P : Fin T → Fin d → ℝ) (t : Fin T) (R : Finset (Fin T)) : Prop :=
  ∃ w : Fin T → ℝ, (∀ r, 0 ≤ w r) ∧ (∀ r ∉ R, w r = 0) ∧ ∑ r, w r = 1 ∧
    ∀ i, (∑ r, w r • P r) i < P t i

/-- `S` is weakly reachable: every `t ∈ S` has a normalized witness `ζ ≥ 0`, `∑ ζ = 1`, with
`⟨ζ, p_s - p_t⟩ ≥ 0` for all `s ∉ S`. -/
def IsWeakReachable (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∃ ζ : Fin d → ℝ, (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧ ∀ s ∉ S, 0 ≤ ζ ⬝ᵥ (P s - P t)

/-- The weakly reachable spectra. -/
def weakReachableSpectra (P : Fin T → Fin d → ℝ) : Set (Finset (Fin T)) :=
  {S | IsWeakReachable P S}

/-- Reachable spectra are weakly reachable (normalize the witness; if `Sᶜ = ∅` any `ζ` works). -/
theorem IsReachable.isWeakReachable (hd : 1 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    {S : Finset (Fin T)} (hS : IsReachable P S) : IsWeakReachable P S := by
  intro t ht
  obtain ⟨ξ, hξ, hs⟩ := (isReachable_iff_exists_witness hP).1 hS t ht
  have hξ' : ∀ i, 0 ≤ ξ i := fun i => hξ i
  by_cases hσ : ∑ i, ξ i = 0
  · have h0 : ∀ i ∈ Finset.univ, ξ i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hξ' i)).1 hσ
    refine ⟨Pi.single ⟨0, by omega⟩ 1, ?_, ?_, ?_⟩
    · intro i
      by_cases h : i = ⟨0, by omega⟩
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · simp
    · intro s hs'
      have := hs s hs'
      have hz : ξ = 0 := funext fun i => h0 i (Finset.mem_univ _)
      simp [hz] at this
      linarith
  · have hpos : 0 < ∑ i, ξ i := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hξ' i) (Ne.symm hσ)
    refine ⟨(∑ i, ξ i)⁻¹ • ξ, ?_, ?_, ?_⟩
    · intro i; simpa using mul_nonneg (inv_nonneg.2 hpos.le) (hξ' i)
    · simp [← Finset.mul_sum, hσ]
    · intro s hs'
      rw [smul_dotProduct]
      exact mul_nonneg (inv_nonneg.2 hpos.le) (by have := hs s hs'; simp at this ⊢; linarith)

/-- A weak witness excludes strict covering: `0 ≤ ∑_s w_s ⟨ζ, p_s - p_t⟩ = ⟨ζ, ∑ w p - p_t⟩ < 0`. -/
theorem not_strictCovers_of_isWeakReachable {S : Finset (Fin T)} (hS : IsWeakReachable P S)
    {t : Fin T} (ht : t ∈ S) : ¬ StrictCovers P t Sᶜ := by
  rintro ⟨w, hw0, hwS, hw1, hlt⟩
  obtain ⟨ζ, hζ0, hζ1, hζ⟩ := hS t ht
  have ha : 0 ≤ ∑ r, w r * (ζ ⬝ᵥ (P r - P t)) := by
    refine Finset.sum_nonneg fun r _ => ?_
    by_cases hr : r ∈ S
    · simp [hwS r (by simpa using hr)]
    · exact mul_nonneg (hw0 r) (hζ r hr)
  have hb : ∑ r, w r * (ζ ⬝ᵥ (P r - P t)) = ζ ⬝ᵥ ((∑ r, w r • P r) - P t) := by
    simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  have hc : ζ ⬝ᵥ ((∑ r, w r • P r) - P t) < 0 := by
    obtain ⟨j, hj⟩ : ∃ j, 0 < ζ j := by
      by_contra h
      push_neg at h
      have : ∑ i, ζ i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    unfold dotProduct
    have hv : ∀ i, ((∑ r, w r • P r) - P t) i < 0 := fun i => by
      simpa using sub_neg.2 (hlt i)
    calc ζ ⬝ᵥ ((∑ r, w r • P r) - P t) = ∑ i, ζ i * ((∑ r, w r • P r) - P t) i := rfl
      _ < ∑ i : Fin d, (0 : ℝ) :=
        Finset.sum_lt_sum (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hζ0 i) (hv i).le)
          ⟨j, Finset.mem_univ _, mul_neg_of_pos_of_neg hj (hv j)⟩
      _ = 0 := by simp
  linarith

/-- **Approximate witnesses.** If `t ∈ S` does not strictly cover `Sᶜ`, then for every
`0 < ε < min_i (p_t)_i` some `ζ` in the standard simplex has `⟨ζ, p_s - p_t⟩ ≥ -ε` for `s ∉ S`.
Replace every price of `S` by `p_t - ε 1`; then `S` is reachable (a covering would be a strict
covering at `P`), and the witness of `isReachable_iff_exists_witness` at `t`, normalized, works. -/
theorem exists_approx_witness (hd : 1 ≤ d) (hP : ∀ t, P t ∈ orthant d) {S : Finset (Fin T)}
    {t : Fin T} (ht : t ∈ S) (hcov : ∀ t' ∈ S, ¬ StrictCovers P t' Sᶜ) {ε : ℝ} (hε : 0 < ε)
    (hεt : ∀ i, ε < P t i) :
    ∃ ζ ∈ stdSimplex ℝ (Fin d), ∀ s ∉ S, -ε ≤ ζ ⬝ᵥ (P s - P t) := by
  classical
  let P' : Fin T → Fin d → ℝ := fun r i => if r ∈ S then P t i - ε else P r i
  have hP' : ∀ r, P' r ∈ orthant d := by
    intro r i
    by_cases hr : r ∈ S
    · simp only [P', if_pos hr]; linarith [hεt i]
    · simp only [P', if_neg hr]; exact hP r i
  have hR : IsReachable P' S := by
    intro t' ht' ⟨w, hw0, hwS, hw1, hle⟩
    apply hcov t ht
    refine ⟨w, hw0, hwS, hw1, fun i => ?_⟩
    have hsum : ∑ r, w r • P' r = ∑ r, w r • P r := by
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : r ∈ S
      · have : w r = 0 := hwS r (by simpa using hr)
        simp [this]
      · congr 1; funext j; simp [P', hr]
    have h1 := hle i
    rw [hsum] at h1
    have h2 : P' t' i = P t i - ε := by simp [P', ht']
    rw [h2] at h1
    linarith
  obtain ⟨ξ, hξ, hξs⟩ := (isReachable_iff_exists_witness hP').1 hR t ht
  have hξ0 : ∀ i, 0 ≤ ξ i := fun i => hξ i
  have key : ∀ s ∉ S, 1 ≤ ξ ⬝ᵥ (P s - P t) + ε * ∑ i, ξ i := by
    intro s hs
    have h := hξs s hs
    have e : P' s - P' t = (P s - P t) + ε • (1 : Fin d → ℝ) := by
      funext j; simp [P', hs, ht]; ring
    rw [e, dotProduct_add, dotProduct_smul] at h
    simpa [dotProduct] using h
  have hσ : 0 ≤ ∑ i, ξ i := Finset.sum_nonneg fun i _ => hξ0 i
  rcases hσ.eq_or_lt with h0 | hpos
  · refine ⟨Pi.single ⟨0, by omega⟩ 1, ⟨fun x => ?_, by simp⟩, fun s hs => ?_⟩
    · rw [Pi.single_apply]; split_ifs <;> norm_num
    · have := key s hs
      have hz : ξ = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hξ0 i).1 h0.symm i (Finset.mem_univ _)
      subst hz
      simp at this
      linarith
  · refine ⟨(∑ i, ξ i)⁻¹ • ξ, ⟨fun x => ?_, ?_⟩, fun s hs => ?_⟩
    · simpa using mul_nonneg (inv_nonneg.2 hσ) (hξ0 x)
    · simp [← Finset.mul_sum, hpos.ne']
    · have := key s hs
      rw [smul_dotProduct, smul_eq_mul]
      have : (∑ i, ξ i)⁻¹ * 1 ≤ (∑ i, ξ i)⁻¹ * (ξ ⬝ᵥ (P s - P t) + ε * ∑ i, ξ i) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 hσ)
      have e : (∑ i, ξ i)⁻¹ * (ξ ⬝ᵥ (P s - P t) + ε * ∑ i, ξ i)
          = (∑ i, ξ i)⁻¹ * (ξ ⬝ᵥ (P s - P t)) + ε := by
        field_simp
      have : 0 < (∑ i, ξ i)⁻¹ := inv_pos.2 hpos
      linarith

/-- Weak reachability means no `t ∈ S` strictly covers `Sᶜ`. `←`: a cluster point of the
approximate witnesses of `exists_approx_witness` as `ε → 0` in the compact simplex. -/
theorem isWeakReachable_iff (hd : 1 ≤ d) (hP : ∀ t, P t ∈ orthant d) {S : Finset (Fin T)} :
    IsWeakReachable P S ↔ ∀ t ∈ S, ¬ StrictCovers P t Sᶜ := by
  refine ⟨fun hS t ht => not_strictCovers_of_isWeakReachable hS ht, fun hcov t ht => ?_⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨ε₀, hε₀, hεt⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ i, ε₀ < P t i := by
    refine ⟨(Finset.univ.inf' Finset.univ_nonempty (P t)) / 2, ?_, fun i => ?_⟩
    · have := (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun i _ => hP t i)
      linarith
    · have := Finset.inf'_le (P t) (Finset.mem_univ i)
      have h0 := (Finset.lt_inf'_iff Finset.univ_nonempty (a := (0:ℝ))).2 (fun i _ => hP t i)
      linarith
  have hε : ∀ n : ℕ, 0 < ε₀ / (n + 1) := fun n => by positivity
  have hεle : ∀ n : ℕ, ε₀ / (n + 1) ≤ ε₀ := fun n =>
    div_le_self hε₀.le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  choose ζ hζ hζs using fun n : ℕ =>
    exists_approx_witness hd hP ht hcov (hε n) (fun i => lt_of_le_of_lt (hεle n) (hεt i))
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (isCompact_stdSimplex (Fin d)).tendsto_subseq hζ
  have hεlim : Filter.Tendsto (fun n : ℕ => -(ε₀ / ((φ n : ℕ) + 1) : ℝ)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ε₀ / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat ε₀ |>.comp (Filter.tendsto_add_atTop_nat 1) |>.congr
        (fun n => by simp)
    simpa using (h1.comp hφ.tendsto_atTop).neg
  refine ⟨z, hz.1, hz.2, fun s hs => ?_⟩
  have hc : Filter.Tendsto (fun n => ζ (φ n) ⬝ᵥ (P s - P t)) Filter.atTop
      (nhds (z ⬝ᵥ (P s - P t))) :=
    ((continuous_id.dotProduct continuous_const).tendsto z).comp hlim
  exact le_of_tendsto_of_tendsto' hεlim hc (fun n => hζs (φ n) s hs)

/-! ### Pairwise distinct prices -/

/-- The shifted prices `q_t = p_t - δ (∑ᵢ log (p_t)ᵢ) 1`. -/
noncomputable def shiftPrices (P : Fin T → Fin d → ℝ) (δ : ℝ) : Fin T → Fin d → ℝ :=
  fun t i => P t i - δ * ∑ j, Real.log (P t j)

/-- **Strict concavity of `∑ log`.** For distinct positive `a ≠ b`,
`∑ᵢ (log aᵢ + (bᵢ - aᵢ) / aᵢ - log bᵢ) > 0`: each term is `x - 1 - log x ≥ 0` with
`x = bᵢ / aᵢ`, strictly for `x ≠ 1`. -/
theorem sum_log_bregman_pos {a b : Fin d → ℝ} (ha : a ∈ orthant d) (hb : b ∈ orthant d)
    (hab : a ≠ b) :
    0 < ∑ i, (Real.log (a i) + (b i - a i) / a i - Real.log (b i)) := by
  have hpos : ∀ i, 0 < a i ∧ 0 < b i := fun i => ⟨ha i, hb i⟩
  have key : ∀ i, Real.log (a i) + (b i - a i) / a i - Real.log (b i)
      = (b i / a i - 1) - Real.log (b i / a i) := by
    intro i
    obtain ⟨h1, h2⟩ := hpos i
    rw [Real.log_div h2.ne' h1.ne']
    field_simp
    ring
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · rw [key]
    have := Real.log_le_sub_one_of_pos (div_pos (hpos i).2 (hpos i).1)
    linarith
  · rw [key]
    have h1 := (hpos j).1
    have h2 := (hpos j).2
    have hne : b j / a j ≠ 1 := by
      intro h; apply hj; rw [div_eq_one_iff_eq h1.ne'] at h; exact h.symm
    have := Real.log_lt_sub_one_of_pos (div_pos h2 h1) hne
    linarith

/-- A nonnegative `ξ` with `⟨ξ, q_s - q_t⟩ > 0` for all `s ∉ S` excludes covering:
`0 < ∑_s w_s ⟨ξ, q_s - q_t⟩ = ⟨ξ, ∑ w q - q_t⟩ ≤ 0`. -/
theorem not_covers_of_pos {Q : Fin T → Fin d → ℝ} {S : Finset (Fin T)} {t : Fin T}
    {ξ : Fin d → ℝ} (hξ : 0 ≤ ξ) (h : ∀ s ∉ S, 0 < ξ ⬝ᵥ (Q s - Q t)) : ¬ Covers Q t Sᶜ := by
  rintro ⟨w, hw0, hwS, hw1, hle⟩
  have h1 := dotProduct_le_dotProduct_of_nonneg_left hle hξ
  have h2 : ξ ⬝ᵥ ∑ r, w r • Q r = ∑ r, w r * (ξ ⬝ᵥ Q r) := by
    simp [dotProduct_sum, dotProduct_smul]
  have h3 : ∑ r, w r * (ξ ⬝ᵥ (Q r - Q t)) = ∑ r, w r * (ξ ⬝ᵥ Q r) - ξ ⬝ᵥ Q t := by
    have : ∑ r, w r * (ξ ⬝ᵥ (Q r - Q t)) = ∑ r, w r * (ξ ⬝ᵥ Q r) - ∑ r, w r * (ξ ⬝ᵥ Q t) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by rw [dotProduct_sub]; ring
    rw [this, ← Finset.sum_mul, hw1, one_mul]
  have hpos : 0 < ∑ r, w r * (ξ ⬝ᵥ (Q r - Q t)) := by
    obtain ⟨r, hr⟩ : ∃ r, 0 < w r := by
      by_contra hcon
      push_neg at hcon
      have : ∑ r, w r = 0 := Finset.sum_eq_zero fun r _ => le_antisymm (hcon r) (hw0 r)
      linarith
    have hrS : r ∉ S := fun hr' => by
      have := hwS r (by simpa using hr'); linarith
    refine Finset.sum_pos' (fun s _ => ?_) ⟨r, Finset.mem_univ _, mul_pos hr (h r hrS)⟩
    by_cases hs : s ∈ S
    · simp [hwS s (by simpa using hs)]
    · exact mul_nonneg (hw0 s) (h s hs).le
  rw [h3] at hpos
  rw [h2] at h1
  linarith

/-- **The shift makes weak witnesses strict.** Let `p_s ≠ p_t`, `ζ ≥ 0`, `∑ ζ = 1`,
`⟨ζ, p_s - p_t⟩ ≥ 0`, and `g = (1/(p_t)ᵢ)ᵢ`. Then for small `δ > 0`,
`⟨ζ + δ g, q_s - q_t⟩ > 0` with `q = shiftPrices P δ`: the expression equals
`A + δ K - δ² L` with `A = ⟨ζ, p_s - p_t⟩ ≥ 0`, `K = ∑ᵢ (log (p_t)ᵢ + ((p_s)ᵢ - (p_t)ᵢ)/(p_t)ᵢ
- log (p_s)ᵢ) > 0` (`sum_log_bregman_pos`) and some constant `L`. -/
theorem eventually_shift_witness_pos (hP : ∀ t, P t ∈ orthant d) {s t : Fin T}
    (hst : P s ≠ P t) {ζ : Fin d → ℝ} (hζ : ∑ i, ζ i = 1) (hA : 0 ≤ ζ ⬝ᵥ (P s - P t)) :
    ∀ᶠ δ in 𝓝[>] 0, 0 < (ζ + δ • fun i => (P t i)⁻¹) ⬝ᵥ
      (shiftPrices P δ s - shiftPrices P δ t) := by
  have hK := sum_log_bregman_pos (hP t) (hP s) (Ne.symm hst)
  set F : Fin T → ℝ := fun r => ∑ j, Real.log (P r j) with hF
  set K := ∑ i, (Real.log (P t i) + (P s i - P t i) / P t i - Real.log (P s i)) with hKdef
  set L := (F s - F t) * ∑ i, (P t i)⁻¹ with hL
  have hKe : K = ∑ i, (P t i)⁻¹ * (P s i - P t i) - (F s - F t) := by
    simp only [hKdef, hF, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [div_eq_inv_mul]
    ring
  have key : ∀ δ : ℝ, (ζ + δ • fun i => (P t i)⁻¹) ⬝ᵥ (shiftPrices P δ s - shiftPrices P δ t)
      = ζ ⬝ᵥ (P s - P t) + δ * K - δ ^ 2 * L := by
    intro δ
    have e : shiftPrices P δ s - shiftPrices P δ t = (P s - P t) - (δ * (F s - F t)) • (1 : Fin d → ℝ) := by
      ext i; simp [shiftPrices, hF]; ring
    rw [e]
    simp only [add_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
    have h1 : ζ ⬝ᵥ (1 : Fin d → ℝ) = 1 := by simp [dotProduct, hζ]
    have h2 : (fun i => (P t i)⁻¹) ⬝ᵥ (1 : Fin d → ℝ) = ∑ i, (P t i)⁻¹ := by simp [dotProduct]
    have h3 : (fun i => (P t i)⁻¹) ⬝ᵥ P s - (fun i => (P t i)⁻¹) ⬝ᵥ P t
        = ∑ i, (P t i)⁻¹ * (P s i - P t i) := by
      simp only [dotProduct, ← Finset.sum_sub_distrib, mul_sub]
    rw [h1, h2, hKe, hL]
    simp only [smul_eq_mul]
    linear_combination δ * h3
  have hm : Set.Ioo (0 : ℝ) (K / (|L| + 1)) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (div_pos hK (by positivity))
  filter_upwards [hm] with δ hδ
  obtain ⟨h0, h1⟩ := hδ
  rw [key]
  have h2 : δ * (|L| + 1) < K := by rwa [lt_div_iff₀ (by positivity)] at h1
  have := le_abs_self L
  have := neg_abs_le L
  have h4 : δ * δ * |L| ≤ δ * K := by nlinarith [abs_nonneg L]
  nlinarith [mul_pos h0 h0, mul_nonneg (mul_pos h0 h0).le (abs_nonneg L)]

/-- For pairwise distinct prices, every weakly reachable spectrum is reachable at
`shiftPrices P δ` for small `δ > 0`: for `t ∈ S` use `ζ + δ g` of
`eventually_shift_witness_pos` (finitely many `s ∉ S`) and `not_covers_of_pos`. -/
theorem isReachable_shiftPrices (hP : ∀ t, P t ∈ orthant d) (hinj : Function.Injective P)
    {S : Finset (Fin T)} (hS : IsWeakReachable P S) :
    ∀ᶠ δ in 𝓝[>] 0, IsReachable (shiftPrices P δ) S := by
  have hall : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ t, t ∈ S → ¬ Covers (shiftPrices P δ) t Sᶜ := by
    rw [Filter.eventually_all]
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨ζ, hζ0, hζ1, hζ⟩ := hS t ht
      have hs : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ s, s ∉ S → 0 < (ζ + δ • fun i => (P t i)⁻¹) ⬝ᵥ
          (shiftPrices P δ s - shiftPrices P δ t) := by
        rw [Filter.eventually_all]
        intro s
        by_cases hsS : s ∈ S
        · exact Filter.Eventually.of_forall fun _ h => absurd hsS h
        · have hst : P s ≠ P t := fun h => hsS (by rw [hinj h]; exact ht)
          filter_upwards [eventually_shift_witness_pos hP hst hζ1 (hζ s hsS)] with δ hδ _ using hδ
      filter_upwards [hs, self_mem_nhdsWithin] with δ h hδ _
      refine not_covers_of_pos (fun i => ?_) h
      have : 0 < δ := hδ
      have := hζ0 i
      have := hP t i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      positivity
    · exact Filter.Eventually.of_forall fun _ h => absurd h ht
  exact hall

/-- `shiftPrices P δ → P` as `δ → 0`, and the shifted prices are eventually positive. -/
theorem tendsto_shiftPrices (hP : ∀ t, P t ∈ orthant d) :
    Tendsto (shiftPrices P) (𝓝[>] 0) (𝓝 P) ∧
      ∀ᶠ δ in 𝓝[>] 0, ∀ t, shiftPrices P δ t ∈ orthant d := by
  have hc : Continuous (shiftPrices (d := d) P) := by
    unfold shiftPrices
    exact continuous_pi fun t => continuous_pi fun i => by fun_prop
  have h0 : shiftPrices P 0 = P := by
    funext t i; simp [shiftPrices]
  have ht : Tendsto (shiftPrices P) (𝓝 0) (𝓝 P) := by
    simpa [h0] using hc.tendsto 0
  have ht' := ht.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  refine ⟨ht', ?_⟩
  have : ∀ᶠ Q in 𝓝 P, ∀ t, Q t ∈ orthant d :=
    eventually_all.2 fun t => ((continuous_apply t).tendsto P).eventually
      (isOpen_orthant.mem_nhds (hP t))
  exact ht'.eventually this

/-- **Closure, pairwise distinct prices.** If `P` is injective and `y` lies in the cone of the
weakly reachable spectra of `P`, then `P` is a limit of prices at which `y` is solvable: at
`shiftPrices P δ` all weakly reachable spectra of `P` are reachable (`isReachable_shiftPrices`,
finitely many `S`), so `neoSolvable_iff_mem_indicatorCone` applies. -/
theorem mem_closure_of_weakReachable_of_injective (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (hinj : Function.Injective P) (hy : ∀ t, 0 ≤ y t)
    (h : y ∈ indicatorCone (weakReachableSpectra P)) :
    P ∈ closure {Q : Fin T → Fin d → ℝ | NeoSolvable Q y} := by
  obtain ⟨hlim, horth⟩ := tendsto_shiftPrices hP
  have key : ∀ᶠ δ in 𝓝[>] (0:ℝ), weakReachableSpectra P ⊆ reachableSpectra (shiftPrices P δ) := by
    have : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ S : Finset (Fin T),
        S ∈ weakReachableSpectra P → IsReachable (shiftPrices P δ) S :=
      Filter.eventually_all.2 fun S => by
        by_cases hS : IsWeakReachable P S
        · exact (isReachable_shiftPrices hP hinj hS).mono fun δ h _ => h
        · exact Filter.Eventually.of_forall fun δ hS' => absurd hS' hS
    exact this.mono fun δ h S hS => h S hS
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [key, horth] with δ hsub hQ
  exact (neoSolvable_iff_mem_indicatorCone hd hQ hy).2 (Submodule.span_mono (Set.image_mono hsub) h)

/-! ### Repeated prices: detaching one index from its cluster -/

/-- The number of ordered pairs of distinct indices with equal prices. -/
noncomputable def defect (P : Fin T → Fin d → ℝ) : ℕ :=
  (Finset.univ.filter fun ts : Fin T × Fin T => ts.1 ≠ ts.2 ∧ P ts.1 = P ts.2).card

/-- **Threshold.** Masses `c ≥ 0` with values `θ`, and demands `D₁ + D₂ = ∑ c`: some `β`
has `D₁ ≤ c{θ ≤ β}` and `D₂ ≤ c{θ ≥ β}`. Take `β` minimal among the values `θ u` with
`c{θ ≤ θ u} ≥ D₁`; then `c{θ < β} < D₁` unless empty. -/
theorem exists_threshold {ι : Type*} [Fintype ι] (θ c : ι → ℝ) {D₁ D₂ : ℝ} (h1 : 0 ≤ D₁) (h2 : 0 ≤ D₂) (hD : D₁ + D₂ = ∑ u, c u) :
    ∃ β : ℝ, D₁ ≤ ∑ u ∈ Finset.univ.filter (fun u => θ u ≤ β), c u ∧
      D₂ ≤ ∑ u ∈ Finset.univ.filter (fun u => β ≤ θ u), c u := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨0, ?_, ?_⟩ <;> simp_all <;> linarith
  set G := Finset.univ.filter (fun u => D₁ ≤ ∑ x ∈ Finset.univ.filter (fun x => θ x ≤ θ u), c x)
    with hG
  have hGne : G.Nonempty := by
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ θ Finset.univ_nonempty
    refine ⟨m, ?_⟩
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
    have : Finset.univ.filter (fun x => θ x ≤ θ m) = Finset.univ :=
      Finset.filter_true_of_mem (fun x _ => hm x (Finset.mem_univ x))
    rw [this]; linarith
  obtain ⟨u₀, hu₀, hmin⟩ := Finset.exists_min_image G θ hGne
  have hu₀' : D₁ ≤ ∑ x ∈ Finset.univ.filter (fun x => θ x ≤ θ u₀), c x := by
    simpa [hG] using hu₀
  have hlt : ∑ x ∈ Finset.univ.filter (fun x => θ x < θ u₀), c x ≤ D₁ := by
    by_cases he : (Finset.univ.filter (fun x => θ x < θ u₀)).Nonempty
    · obtain ⟨u', hu', hmax⟩ := Finset.exists_max_image _ θ he
      have hu'lt : θ u' < θ u₀ := by simpa using hu'
      have heq : Finset.univ.filter (fun x => θ x ≤ θ u') = Finset.univ.filter (fun x => θ x < θ u₀) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; linarith
        · intro h; exact hmax x (by simpa using h)
      have hnot : u' ∉ G := by
        intro hg
        have := hmin u' hg
        linarith
      simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
      rw [heq] at hnot
      exact hnot.le
    · rw [Finset.not_nonempty_iff_eq_empty] at he
      rw [he]; simpa using h1
  refine ⟨θ u₀, hu₀', ?_⟩
  have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => θ x < θ u₀) c
  simp only [not_lt] at this
  linarith

/-- **Splitting masses.** If `L ∪ R` is everything, `D₁ ≤ c(L)`, `D₂ ≤ c(R)`, `D₁ + D₂ = ∑ c`,
then `c = c₁ + c₂` with `c₁, c₂ ≥ 0` supported on `L`, `R`, of totals `D₁`, `D₂`. -/
theorem exists_split {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ u, 0 ≤ c u) (L R : Finset ι)
    (hLR : ∀ u, u ∈ L ∨ u ∈ R) {D₁ D₂ : ℝ}
    (hD : D₁ + D₂ = ∑ u, c u) (hL : D₁ ≤ ∑ u ∈ L, c u) (hR : D₂ ≤ ∑ u ∈ R, c u) :
    ∃ c₁ c₂ : ι → ℝ, (∀ u, 0 ≤ c₁ u) ∧ (∀ u, 0 ≤ c₂ u) ∧ (∀ u, c u = c₁ u + c₂ u) ∧
      (∀ u ∉ L, c₁ u = 0) ∧ (∀ u ∉ R, c₂ u = 0) ∧ ∑ u, c₁ u = D₁ ∧ ∑ u, c₂ u = D₂ := by
  classical
  set A := ∑ u ∈ L.filter (fun u => u ∉ R), c u with hA
  set B := ∑ u ∈ L.filter (fun u => u ∈ R), c u with hB
  have hAB : A + B = ∑ u ∈ L, c u := by
    rw [hA, hB, add_comm]; exact Finset.sum_filter_add_sum_filter_not L _ c
  have hAR : A + ∑ u ∈ R, c u = ∑ u, c u := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => u ∈ R) c
    have e1 : Finset.univ.filter (fun u => u ∈ R) = R := by ext u; simp
    have e2 : Finset.univ.filter (fun u => u ∉ R) = L.filter (fun u => u ∉ R) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨(hLR u).resolve_right h, h⟩
      · exact fun h => h.2
    rw [e1, e2] at h; rw [← h, hA, add_comm]
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun u _ => hc u
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun u _ => hc u
  have hi : A ≤ D₁ := by linarith
  have hii : D₁ - A ≤ B := by linarith
  set ϑ := (D₁ - A) / B with hϑ
  have hϑ0 : 0 ≤ ϑ := div_nonneg (by linarith) hB0
  have hϑ1 : ϑ ≤ 1 := by
    rcases hB0.eq_or_lt with h | h
    · rw [hϑ, ← h]; simp
    · rw [hϑ, div_le_one h]; exact hii
  have hϑB : ϑ * B = D₁ - A := by
    rcases hB0.eq_or_lt with h | h
    · rw [← h]; simp; linarith
    · rw [hϑ]; field_simp
  refine ⟨fun u => if u ∈ L then (if u ∈ R then ϑ * c u else c u) else 0,
    fun u => c u - (if u ∈ L then (if u ∈ R then ϑ * c u else c u) else 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    have := hc u
    dsimp only
    split_ifs <;> positivity
  · intro u
    have := hc u
    dsimp only
    split_ifs <;> nlinarith
  · intro u; ring
  · intro u hu; simp [hu]
  · intro u hu
    have := (hLR u).resolve_right hu
    simp [this, hu]
  · have key : ∑ u : ι, (if u ∈ L then (if u ∈ R then ϑ * c u else c u) else 0)
        = A + ϑ * B := by
      rw [hA, hB, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h2 : u ∈ R <;> simp [h2]
    rw [key, hϑB]; ring
  · rw [Finset.sum_sub_distrib]
    have key : ∑ u : ι, (if u ∈ L then (if u ∈ R then ϑ * c u else c u) else 0)
        = A + ϑ * B := by
      rw [hA, hB, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h2 : u ∈ R <;> simp [h2]
    rw [key, hϑB]; linarith

/-- **Rematching.** Let `C` be the cluster of `t0` (indices with price `p_{t0}`). If `u` is weakly
reachable, meets `C` and misses a point of `C`, then `(u \ C) ∪ (w ∩ C)` is weakly reachable. For
`t ∈ u \ C` use the witness of `t` for `u` (a point of `C` outside `S'` is compared like the point
of `C \ u`); for `t ∈ w ∩ C` use the witness of some `t₁ ∈ u ∩ C` for `u`. -/
theorem isWeakReachable_rematch {t0 : Fin T} {u w : Finset (Fin T)}
    (hu : IsWeakReachable P u) (hu1 : ∃ t ∈ u, P t = P t0) (hu2 : ∃ s ∉ u, P s = P t0) :
    IsWeakReachable P
      (u \ Finset.univ.filter (fun s => P s = P t0) ∪
        w ∩ Finset.univ.filter (fun s => P s = P t0)) := by
  intro t ht
  have hm : ∀ x, x ∈ (u \ Finset.univ.filter (fun s => P s = P t0) ∪
        w ∩ Finset.univ.filter (fun s => P s = P t0)) ↔
      (x ∈ u ∧ P x ≠ P t0) ∨ (x ∈ w ∧ P x = P t0) := by
    intro x; simp [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter]
  rw [hm] at ht
  by_cases hc : P t = P t0
  · have hw : t ∈ w ∧ P t = P t0 := by
      rcases ht with h | h
      · exact absurd hc h.2
      · exact h
    obtain ⟨t₁, ht₁, hp₁⟩ := hu1
    obtain ⟨ζ, h0, h1, hζ⟩ := hu t₁ ht₁
    refine ⟨ζ, h0, h1, fun s hs => ?_⟩
    rw [hm] at hs
    push_neg at hs
    by_cases hsc : P s = P t0
    · rw [hsc, ← hc]; simp
    · have hsu : s ∉ u := fun h => hsc (hs.1 h)
      have hpt : P t = P t₁ := hc.trans hp₁.symm
      rw [hpt]; exact hζ s hsu
  · have htu : t ∈ u := by
      rcases ht with h | h
      · exact h.1
      · exact absurd h.2 hc
    obtain ⟨ζ, h0, h1, hζ⟩ := hu t htu
    obtain ⟨s', hs'u, hs'p⟩ := hu2
    refine ⟨ζ, h0, h1, fun s hs => ?_⟩
    rw [hm] at hs
    push_neg at hs
    by_cases hsc : P s = P t0
    · have := hζ s' hs'u
      rwa [hs'p, ← hsc] at this
    · exact hζ s (fun h => hsc (hs.1 h))

/-- Uniform margin from strict positivity over finitely many `(S, t, s)`. -/
theorem exists_uniform_margin (Q : Fin T → Fin d → ℝ)
    (h : ∀ S : Finset (Fin T), IsWeakReachable P S → ∀ t ∈ S, ∃ ζ : Fin d → ℝ,
        (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧ ∀ s ∉ S, P s ≠ P t → 0 < ζ ⬝ᵥ (Q s - Q t)) :
    ∃ μ > 0, ∀ S : Finset (Fin T), IsWeakReachable P S → ∀ t ∈ S, ∃ ζ : Fin d → ℝ,
        (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧ ∀ s ∉ S, P s ≠ P t → μ ≤ ζ ⬝ᵥ (Q s - Q t) := by
  classical
  have h' : ∀ S : Finset (Fin T), ∀ t : Fin T, ∃ ζ : Fin d → ℝ, IsWeakReachable P S → t ∈ S →
      ((∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧ ∀ s ∉ S, P s ≠ P t → 0 < ζ ⬝ᵥ (Q s - Q t)) := by
    intro S t
    by_cases hc : IsWeakReachable P S ∧ t ∈ S
    · obtain ⟨ζ, hζ⟩ := h S hc.1 t hc.2
      exact ⟨ζ, fun _ _ => hζ⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose ζ hζ using h'
  let F : Finset (Finset (Fin T) × Fin T × Fin T) := Finset.univ.filter
    (fun k => IsWeakReachable P k.1 ∧ k.2.1 ∈ k.1 ∧ k.2.2 ∉ k.1 ∧ P k.2.2 ≠ P k.2.1)
  let f : Finset (Fin T) × Fin T × Fin T → ℝ := fun k => ζ k.1 k.2.1 ⬝ᵥ (Q k.2.2 - Q k.2.1)
  have hpos : ∀ k ∈ F, 0 < f k := by
    intro k hk
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact (hζ k.1 k.2.1 hk.1 hk.2.1).2.2 k.2.2 hk.2.2.1 hk.2.2.2
  by_cases hF : F.Nonempty
  · refine ⟨F.inf' hF f, (Finset.lt_inf'_iff hF).2 hpos, ?_⟩
    intro S hS t ht
    refine ⟨ζ S t, (hζ S t hS ht).1, (hζ S t hS ht).2.1, fun s hs hst => ?_⟩
    exact Finset.inf'_le f (b := (S, t, s)) (by simp [F, hS, ht, hs, hst])
  · refine ⟨1, one_pos, ?_⟩
    intro S hS t ht
    refine ⟨ζ S t, (hζ S t hS ht).1, (hζ S t hS ht).2.1, fun s hs hst => ?_⟩
    exact absurd ⟨(S, t, s), by simp [F, hS, ht, hs, hst]⟩ hF

/-- **Good shifts.** For small `δ > 0`, `Q = shiftPrices P δ` is positive, keeps distinct prices
distinct, and has a uniform margin `μ > 0`: every `t ∈ S ∈ W(P)` has a simplex witness `ζ` with
`⟨ζ, q_s - q_t⟩ ≥ μ` for all `s ∉ S` with `p_s ≠ p_t`. Use `eventually_shift_witness_pos`,
normalize `(ζ + δ g) / (1 + δ ∑ g)`, and take the minimum over the finitely many `(S, t, s)`. -/
theorem eventually_shift_good (hP : ∀ t, P t ∈ orthant d) :
    ∀ᶠ δ in 𝓝[>] 0, (∀ t, shiftPrices P δ t ∈ orthant d) ∧
      (∀ a b, P a ≠ P b → shiftPrices P δ a ≠ shiftPrices P δ b) ∧
      ∃ μ > 0, ∀ S : Finset (Fin T), IsWeakReachable P S → ∀ t ∈ S, ∃ ζ : Fin d → ℝ,
        (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧
          ∀ s ∉ S, P s ≠ P t → μ ≤ ζ ⬝ᵥ (shiftPrices P δ s - shiftPrices P δ t) := by
  have h1 := (tendsto_shiftPrices hP).2
  have h2 : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ a b, P a ≠ P b → shiftPrices P δ a ≠ shiftPrices P δ b := by
    rw [Filter.eventually_all]; intro a
    rw [Filter.eventually_all]; intro b
    by_cases hab : P a = P b
    · exact Filter.Eventually.of_forall fun _ h => absurd hab h
    · have ho : {Q : Fin T → Fin d → ℝ | Q a ≠ Q b} ∈ 𝓝 P :=
        (isOpen_ne_fun (continuous_apply a) (continuous_apply b)).mem_nhds hab
      filter_upwards [(tendsto_shiftPrices hP).1 ho] with δ hδ _ using hδ
  have h3 : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ S : Finset (Fin T), IsWeakReachable P S → ∀ t ∈ S,
      ∃ ζ : Fin d → ℝ, (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧
        ∀ s ∉ S, P s ≠ P t → 0 < ζ ⬝ᵥ (shiftPrices P δ s - shiftPrices P δ t) := by
    rw [Filter.eventually_all]; intro S
    by_cases hS : IsWeakReachable P S
    · have key : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ t, t ∈ S →
          ∃ ζ : Fin d → ℝ, (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧
            ∀ s ∉ S, P s ≠ P t → 0 < ζ ⬝ᵥ (shiftPrices P δ s - shiftPrices P δ t) := by
        rw [Filter.eventually_all]; intro t
        by_cases ht : t ∈ S
        · obtain ⟨ζ₀, hζ0, hζ1, hζ⟩ := hS t ht
          have hs : ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ s, s ∉ S → P s ≠ P t →
              0 < (ζ₀ + δ • fun i => (P t i)⁻¹) ⬝ᵥ (shiftPrices P δ s - shiftPrices P δ t) := by
            rw [Filter.eventually_all]; intro s
            by_cases hsS : s ∈ S
            · exact Filter.Eventually.of_forall fun _ h => absurd hsS h
            · by_cases hst : P s = P t
              · exact Filter.Eventually.of_forall fun _ _ h => absurd hst h
              · filter_upwards [eventually_shift_witness_pos hP hst hζ1 (hζ s hsS)] with δ hδ _ _
                exact hδ
          filter_upwards [hs, self_mem_nhdsWithin] with δ hδs hδ _
          have hδ' : 0 < δ := hδ
          have hg : ∀ i, 0 < (P t i)⁻¹ := fun i => inv_pos.2 (hP t i)
          have hG : 0 ≤ ∑ i, (P t i)⁻¹ := Finset.sum_nonneg fun i _ => (hg i).le
          have hc : 0 < (1 + δ * ∑ i, (P t i)⁻¹)⁻¹ := inv_pos.2 (by positivity)
          refine ⟨(1 + δ * ∑ i, (P t i)⁻¹)⁻¹ • (ζ₀ + δ • fun i => (P t i)⁻¹), fun i => ?_, ?_, ?_⟩
          · have := hζ0 i
            have := hg i
            simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
            positivity
          · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, ← Finset.mul_sum,
              Finset.sum_add_distrib, hζ1, ← Finset.mul_sum]
            exact inv_mul_cancel₀ (by positivity)
          · intro s hs hst
            rw [smul_dotProduct]
            exact mul_pos hc (hδs s hs hst)
        · exact Filter.Eventually.of_forall fun _ h => absurd h ht
      filter_upwards [key] with δ h _ using h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hS
  filter_upwards [h1, h2, h3] with δ a b c
  exact ⟨a, b, exists_uniform_margin _ c⟩

/-- A simplex vector pairs with `v` by at most `∑ |vᵢ|`. -/
theorem abs_dotProduct_le {ζ v : Fin d → ℝ} (hζ0 : ∀ i, 0 ≤ ζ i) (hζ1 : ∑ i, ζ i = 1) :
    |ζ ⬝ᵥ v| ≤ ∑ i, |v i| := by
  have hle : ∀ i, ζ i ≤ 1 := fun i => hζ1 ▸ Finset.single_le_sum (fun j _ => hζ0 j) (Finset.mem_univ i)
  calc |ζ ⬝ᵥ v| = |∑ i, ζ i * v i| := rfl
    _ ≤ ∑ i, |ζ i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hζ0 i)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hle i)

/-- **Moving `t0`, generic index.** Let `P' = Q` with `q_{t0}` moved to `q_{t0} + η v`, and `ζ` a
simplex witness for `t` at `Q` with margin `μ` against distinct prices (`Q` constant on clusters).
If `t ≠ t0` and either `t0 ∈ S` or `p_t ≠ p_{t0}`, and `η ∑ |vᵢ| < μ`, then `ζ` is a weak witness
for `t` at `P'`. -/
theorem update_witness_of_ne {Q : Fin T → Fin d → ℝ} {S : Finset (Fin T)} {t t0 : Fin T}
    {ζ v : Fin d → ℝ} {μ η : ℝ} (hsame : ∀ a b, P a = P b → Q a = Q b)
    (hζ0 : ∀ i, 0 ≤ ζ i) (hζ1 : ∑ i, ζ i = 1)
    (hζ : ∀ s ∉ S, P s ≠ P t → μ ≤ ζ ⬝ᵥ (Q s - Q t)) (ht : t ≠ t0)
    (hcase : t0 ∈ S ∨ P t ≠ P t0) (hη : 0 ≤ η) (hημ : η * ∑ i, |v i| < μ) :
    ∀ s ∉ S, 0 ≤ ζ ⬝ᵥ (Function.update Q t0 (Q t0 + η • v) s -
      Function.update Q t0 (Q t0 + η • v) t) := by
  intro s hs
  have hsum : 0 ≤ η * ∑ i, |v i| := mul_nonneg hη (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hab := abs_dotProduct_le (v := v) hζ0 hζ1
  have hlow : -(η * ∑ i, |v i|) ≤ η * (ζ ⬝ᵥ v) := by
    have h1 := neg_abs_le (ζ ⬝ᵥ v)
    nlinarith
  rw [Function.update_of_ne ht]
  by_cases hs0 : s = t0
  · subst hs0
    rw [Function.update_self]
    have hne : P t ≠ P s := by
      rcases hcase with h | h
      · exact absurd h hs
      · exact h
    have := hζ s hs hne.symm
    have e : ζ ⬝ᵥ (Q s + η • v - Q t) = ζ ⬝ᵥ (Q s - Q t) + η * (ζ ⬝ᵥ v) := by
      rw [show Q s + η • v - Q t = (Q s - Q t) + η • v by abel, dotProduct_add, dotProduct_smul,
        smul_eq_mul]
    rw [e]; linarith
  · rw [Function.update_of_ne hs0]
    by_cases hst : P s = P t
    · rw [hsame s t hst, sub_self, dotProduct_zero]
    · have := hζ s hs hst
      linarith

/-- **Moving `t0`, the index `t0` itself**, when no `s ∉ S` shares its price. -/
theorem update_witness_self {Q : Fin T → Fin d → ℝ} {S : Finset (Fin T)} {t0 : Fin T}
    {ζ v : Fin d → ℝ} {μ η : ℝ} (hζ0 : ∀ i, 0 ≤ ζ i) (hζ1 : ∑ i, ζ i = 1)
    (hζ : ∀ s ∉ S, P s ≠ P t0 → μ ≤ ζ ⬝ᵥ (Q s - Q t0)) (hS : ∀ s ∉ S, P s ≠ P t0)
    (hη : 0 ≤ η) (hημ : η * ∑ i, |v i| < μ) :
    ∀ s ∉ S, 0 ≤ ζ ⬝ᵥ (Function.update Q t0 (Q t0 + η • v) s -
      Function.update Q t0 (Q t0 + η • v) t0) := by
  intro s hs
  have hne : s ≠ t0 := fun h => hS s hs (h ▸ rfl)
  rw [Function.update_self, Function.update_of_ne hne, dotProduct_sub, dotProduct_add,
    dotProduct_smul]
  have h1 := hζ s hs (hS s hs)
  have h2 := abs_dotProduct_le hζ0 hζ1 (v := v)
  have h3 : η * (ζ ⬝ᵥ v) ≤ η * ∑ i, |v i| :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hη
  rw [dotProduct_sub] at h1
  simp only [smul_eq_mul]
  linarith

/-- **Moving `t0`, cluster indices via a borrowed witness.** `ζ` is a margin witness at `q_{t0}`
against `u` (`⟨ζ, q_s - q_{t0}⟩ ≥ μ ≥ 0` for `s ∉ u` off the cluster). For `t ∈ S'` in the cluster
of `t0`, where every `s ∉ S'` off the cluster is outside `u`: if `t = t0` and `⟨ζ, v⟩ ≤ 0`, or
`t ≠ t0` and (`t0 ∈ S'` or `⟨ζ, v⟩ ≥ 0`), then `ζ` is a weak witness for `t` at `P'`. -/
theorem update_witness_cluster {Q : Fin T → Fin d → ℝ} {u S' : Finset (Fin T)} {t t0 : Fin T}
    {ζ v : Fin d → ℝ} {μ η : ℝ} (hsame : ∀ a b, P a = P b → Q a = Q b) (hμ : 0 ≤ μ)
    (hζ : ∀ s ∉ u, P s ≠ P t0 → μ ≤ ζ ⬝ᵥ (Q s - Q t0))
    (hsub : ∀ s ∉ S', P s ≠ P t0 → s ∉ u) (htC : P t = P t0)
    (hv0 : t = t0 → ζ ⬝ᵥ v ≤ 0) (hv1 : t ≠ t0 → t0 ∉ S' → 0 ≤ ζ ⬝ᵥ v) (hη : 0 ≤ η) :
    ∀ s ∉ S', 0 ≤ ζ ⬝ᵥ (Function.update Q t0 (Q t0 + η • v) s -
      Function.update Q t0 (Q t0 + η • v) t) := by
  intro s hs
  have hQt : Q t = Q t0 := hsame t t0 htC
  have key : ∀ s, s ≠ t0 → s ∉ S' → 0 ≤ ζ ⬝ᵥ (Q s - Q t0) := by
    intro s hs0 hs
    by_cases h : P s = P t0
    · rw [hsame s t0 h, sub_self, dotProduct_zero]
    · exact hμ.trans (hζ s (hsub s hs h) h)
  by_cases htt : t = t0
  · subst htt
    have h0 := hv0 rfl
    by_cases hst : s = t
    · subst hst; simp
    · rw [Function.update_of_ne hst, Function.update_self, dotProduct_sub, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
      have := key s hst hs
      rw [dotProduct_sub] at this
      nlinarith [mul_nonneg hη (neg_nonneg.mpr h0)]
  · rw [Function.update_of_ne htt, hQt]
    by_cases hst : s = t0
    · subst hst
      have := hv1 htt hs
      rw [Function.update_self, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith [mul_nonneg hη this]
    · rw [Function.update_of_ne hst]
      exact key s hst hs

/-- **Hypotheses of one detaching step**, on the shifted prices `Q`: `Q` is constant on clusters,
keeps distinct prices distinct, and has the uniform margin `μ` of `eventually_shift_good`. -/
def StepData (P Q : Fin T → Fin d → ℝ) (μ : ℝ) : Prop :=
  (∀ a b, P a = P b → Q a = Q b) ∧ (∀ a b, P a ≠ P b → Q a ≠ Q b) ∧ 0 < μ ∧
    ∀ S : Finset (Fin T), IsWeakReachable P S → ∀ t ∈ S, ∃ ζ : Fin d → ℝ,
      (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧ ∀ s ∉ S, P s ≠ P t → μ ≤ ζ ⬝ᵥ (Q s - Q t)

/-- **Spectra off the split.** A weakly reachable `S` that misses the cluster of `t0`, or
contains it, stays weakly reachable after moving `t0` (`update_witness_of_ne`,
`update_witness_self`). -/
theorem isWeakReachable_update_of_outer {Q : Fin T → Fin d → ℝ} {μ η : ℝ} {t0 : Fin T}
    {v : Fin d → ℝ} (hQ : StepData P Q μ) {S : Finset (Fin T)} (hS : IsWeakReachable P S)
    (hout : (∀ t ∈ S, P t ≠ P t0) ∨ ∀ s ∉ S, P s ≠ P t0) (hη : 0 ≤ η)
    (hημ : η * ∑ i, |v i| < μ) :
    IsWeakReachable (Function.update Q t0 (Q t0 + η • v)) S := by
  obtain ⟨hsame, hdist, hμ, hmarg⟩ := hQ
  intro t ht
  obtain ⟨ζ, hζ0, hζ1, hζ⟩ := hmarg S hS t ht
  refine ⟨ζ, hζ0, hζ1, ?_⟩
  by_cases htt : t = t0
  · subst htt
    have hS' : ∀ s ∉ S, P s ≠ P t := by
      rcases hout with h | h
      · exact absurd rfl (h t ht)
      · exact h
    exact update_witness_self hζ0 hζ1 hζ hS' hη hημ
  · have hcase : t0 ∈ S ∨ P t ≠ P t0 := by
      rcases hout with h | h
      · exact Or.inr (h t ht)
      · by_contra hc
        push_neg at hc
        exact h t0 hc.1 rfl
    exact update_witness_of_ne hsame hζ0 hζ1 hζ htt hcase hη hημ

/-- **Rematched spectra after the move.** Let `u` meet and miss the cluster `C` of `t0`, `t₁ ∈ u`
with `p_{t₁} = p_{t0}`, and `ζ` the margin witness of `t₁` for `u`. If `⟨ζ, v⟩ ≤ 0` when
`t0 ∈ w` and `⟨ζ, v⟩ ≥ 0` when `t0 ∉ w`, then `(u \ C) ∪ (w ∩ C)` is weakly reachable after
moving `t0`: indices off `C` use their own margin witnesses (`isWeakReachable_rematch`,
`update_witness_of_ne`), indices of `C` borrow `ζ` (`update_witness_cluster`). -/
theorem isWeakReachable_update_rematch {Q : Fin T → Fin d → ℝ} {μ η : ℝ} {t0 t₁ : Fin T}
    {v ζ : Fin d → ℝ} (hQ : StepData P Q μ) {u w : Finset (Fin T)} (hu : IsWeakReachable P u)
    (ht₁ : t₁ ∈ u) (ht₁C : P t₁ = P t0) (hu2 : ∃ s ∉ u, P s = P t0)
    (hζ0 : ∀ i, 0 ≤ ζ i) (hζ1 : ∑ i, ζ i = 1)
    (hζ : ∀ s ∉ u, P s ≠ P t₁ → μ ≤ ζ ⬝ᵥ (Q s - Q t₁))
    (hv0 : t0 ∈ w → ζ ⬝ᵥ v ≤ 0) (hv1 : t0 ∉ w → 0 ≤ ζ ⬝ᵥ v) (hη : 0 ≤ η)
    (hημ : η * ∑ i, |v i| < μ) :
    IsWeakReachable (Function.update Q t0 (Q t0 + η • v))
      (u \ Finset.univ.filter (fun s => P s = P t0) ∪
        w ∩ Finset.univ.filter (fun s => P s = P t0)) := by
  obtain ⟨hsame, hdist, hμ, hmarg⟩ := hQ
  have hm : ∀ x, x ∈ (u \ Finset.univ.filter (fun s => P s = P t0) ∪
        w ∩ Finset.univ.filter (fun s => P s = P t0)) ↔
      (x ∈ u ∧ P x ≠ P t0) ∨ (x ∈ w ∧ P x = P t0) := by
    intro x; simp [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter]
  have hS' := isWeakReachable_rematch (w := w) hu ⟨t₁, ht₁, ht₁C⟩ hu2
  intro t ht
  by_cases hPt : P t = P t0
  · have hζ'' : ∀ s ∉ u, P s ≠ P t0 → μ ≤ ζ ⬝ᵥ (Q s - Q t0) := by
      intro s hs hne
      have := hζ s hs (ht₁C ▸ hne)
      rwa [hsame t₁ t0 ht₁C] at this
    refine ⟨ζ, hζ0, hζ1, update_witness_cluster hsame hμ.le hζ'' ?_ hPt ?_ ?_ hη⟩
    · intro s hs hne hsu
      exact hs ((hm s).2 (Or.inl ⟨hsu, hne⟩))
    · intro h
      subst h
      apply hv0
      rcases (hm t).1 ht with h | h
      · exact absurd hPt h.2
      · exact h.1
    · intro _ h0
      apply hv1
      intro hw
      exact h0 ((hm t0).2 (Or.inr ⟨hw, rfl⟩))
  · have htt : t ≠ t0 := fun h => hPt (h ▸ rfl)
    obtain ⟨ζ', h0, h1, hζ'⟩ := hmarg _ hS' t ht
    exact ⟨ζ', h0, h1, update_witness_of_ne hsame h0 h1 hζ' htt (Or.inr hPt) hη hημ⟩

/-- **Rematching identity.** With `∑_U m₁ = D = ∑_I m` and nonnegative masses,
`∑_{u,w} (m₁ u · m w / D) 1_{(u\C) ∪ (w∩C)} = ∑_u m₁ u 1_{u\C} + ∑_w m w 1_{w∩C}`. -/
theorem sum_rematch (C : Finset (Fin T)) (U I : Finset (Finset (Fin T)))
    (m₁ m : Finset (Fin T) → ℝ) (h1 : ∀ u ∈ U, 0 ≤ m₁ u) (h2 : ∀ w ∈ I, 0 ≤ m w) {D : ℝ}
    (hU : ∑ u ∈ U, m₁ u = D) (hI : ∑ w ∈ I, m w = D) :
    ∑ u ∈ U, ∑ w ∈ I, (m₁ u * m w / D) • ((u \ C ∪ w ∩ C : Finset (Fin T)) : Set (Fin T)).indicator 1
      = ∑ u ∈ U, m₁ u • ((u \ C : Finset (Fin T)) : Set (Fin T)).indicator (1 : Fin T → ℝ)
        + ∑ w ∈ I, m w • ((w ∩ C : Finset (Fin T)) : Set (Fin T)).indicator 1 := by
  classical
  have key : ∀ u w : Finset (Fin T), ((u \ C ∪ w ∩ C : Finset (Fin T)) : Set (Fin T)).indicator (1 : Fin T → ℝ)
      = ((u \ C : Finset (Fin T)) : Set (Fin T)).indicator 1 + ((w ∩ C : Finset (Fin T)) : Set (Fin T)).indicator 1 := by
    intro u w
    ext x
    by_cases h1 : x ∈ C <;> by_cases h2 : x ∈ u <;> by_cases h3 : x ∈ w <;>
      simp [Set.indicator, h1, h2, h3]
  by_cases hD : D = 0
  · subst hD
    have hu : ∀ u ∈ U, m₁ u = 0 := (Finset.sum_eq_zero_iff_of_nonneg h1).1 hU
    have hw : ∀ w ∈ I, m w = 0 := (Finset.sum_eq_zero_iff_of_nonneg h2).1 hI
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero (s := U), Finset.sum_eq_zero (s := I)]
    · simp
    · intro w hw'; simp [hw w hw']
    · intro u hu'; simp [hu u hu']
    · intro u hu'; simp [hu u hu']
  · simp_rw [key, smul_add, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      rw [← Finset.sum_div, ← Finset.mul_sum, hI]
      field_simp
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      rw [← Finset.sum_div]
      simp_rw [mul_comm (m₁ _) (m w)]
      rw [← Finset.mul_sum, hU]
      field_simp

/-- A nonnegative multiple of an indicator lies in the indicator cone when the set is in `A`
(or the multiple is zero). -/
theorem smul_indicator_mem_indicatorCone {T : ℕ} {A : Set (Finset (Fin T))} {a : ℝ}
    {S : Finset (Fin T)} (ha : 0 ≤ a) (hS : a ≠ 0 → S ∈ A) :
    a • ((S : Set (Fin T)).indicator (1 : Fin T → ℝ)) ∈ indicatorCone A := by
  by_cases h0 : a = 0
  · rw [h0, zero_smul]; exact Submodule.zero_mem _
  · exact PointedCone.smul_mem _ ha (PointedCone.subset_span ⟨S, hS h0, rfl⟩)


/-- **One detaching step, cone level.** Under `StepData P Q μ`, for `d ≥ 2` there is `v ≠ 0` such
that for `0 < η` with `η ∑ |vᵢ| < μ`, `y` stays in the weak cone after moving `q_{t0}` to
`q_{t0} + η v`. Write `y = ∑ m_S 1_S`; let `U` be the spectra meeting and missing the cluster `C`,
`I`/`J` those containing / not containing `t0`, `D₁ = m(I)`, `D₂ = m(J)`. For `u ∈ U` take
`t₁ ∈ u ∩ C`, its margin witness `ζ_u` and `θ_u = ⟨ζ_u, a⟩`, `a = (0, 1, …, d-1)`.
`exists_threshold` gives `β`, `v = a - β 1`, `exists_split` gives `m = m₁ + m₂` on `U` with `m₁`
on `{θ ≤ β}` of total `D₁`, `m₂` on `{θ ≥ β}` of total `D₂`. Then
`y = ∑_{S ∉ U} m_S 1_S + ∑_{u, w ∈ I} (m₁ u m w / D₁) 1_{(u\C)∪(w∩C)} + ∑_{u, w ∈ J} (m₂ u m w / D₂) 1_{(u\C)∪(w∩C)}`
(`sum_rematch` twice), and every spectrum with nonzero coefficient is weakly reachable after the
move (`isWeakReachable_update_of_outer`, `isWeakReachable_update_rematch`). -/
theorem exists_update_step (hd : 2 ≤ d) {Q : Fin T → Fin d → ℝ} {μ : ℝ} (hQ : StepData P Q μ)
    (h : y ∈ indicatorCone (weakReachableSpectra P)) (t0 : Fin T) :
    ∃ v : Fin d → ℝ, v ≠ 0 ∧ ∀ η : ℝ, 0 < η → η * ∑ i, |v i| < μ →
      y ∈ indicatorCone (weakReachableSpectra (Function.update Q t0 (Q t0 + η • v))) := by
  classical
  obtain ⟨-, -, hμ, hmarg⟩ := id hQ
  obtain ⟨m, hm0, hmA, -, hy⟩ := exists_coef_of_mem_indicatorCone h
  set C := Finset.univ.filter (fun s => P s = P t0) with hC
  let sp : Finset (Fin T) → Prop := fun S => (∃ t ∈ S, P t = P t0) ∧ (∃ s ∉ S, P s = P t0)
  have hch : ∀ S, ∃ (t₁ : Fin T) (ζ : Fin d → ℝ), IsWeakReachable P S → sp S →
      t₁ ∈ S ∧ P t₁ = P t0 ∧ (∀ i, 0 ≤ ζ i) ∧ ∑ i, ζ i = 1 ∧
      ∀ s ∉ S, P s ≠ P t₁ → μ ≤ ζ ⬝ᵥ (Q s - Q t₁) := by
    intro S
    by_cases hS : IsWeakReachable P S ∧ sp S
    · obtain ⟨t₁, ht₁, hp⟩ := hS.2.1
      obtain ⟨ζ, h0, h1, hz⟩ := hmarg S hS.1 t₁ ht₁
      exact ⟨t₁, ζ, fun _ _ => ⟨ht₁, hp, h0, h1, hz⟩⟩
    · exact ⟨t0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hS⟩
  choose t₁ ζ hζ using hch
  let a : Fin d → ℝ := fun i => ((i : ℕ) : ℝ)
  let θ : Finset (Fin T) → ℝ := fun S => ζ S ⬝ᵥ a
  let c : Finset (Fin T) → ℝ := fun S => if sp S then m S else 0
  have hc0 : ∀ S, 0 ≤ c S := fun S => by
    simp only [c]; split_ifs
    exacts [hm0 S, le_rfl]
  let I := Finset.univ.filter (fun S => sp S ∧ t0 ∈ S)
  let J := Finset.univ.filter (fun S => sp S ∧ t0 ∉ S)
  have hD1 : 0 ≤ ∑ w ∈ I, m w := Finset.sum_nonneg fun w _ => hm0 w
  have hD2 : 0 ≤ ∑ w ∈ J, m w := Finset.sum_nonneg fun w _ => hm0 w
  have hD : ∑ w ∈ I, m w + ∑ w ∈ J, m w = ∑ S, c S := by
    simp only [I, J, c, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases h1 : sp S <;> by_cases h2 : t0 ∈ S <;> simp [h1, h2]
  obtain ⟨β, hβ1, hβ2⟩ := exists_threshold θ c hD1 hD2 hD
  obtain ⟨c₁, c₂, hc₁0, hc₂0, hcc, hc₁L, hc₂R, hc₁s, hc₂s⟩ := exists_split c hc0
    (Finset.univ.filter (fun u => θ u ≤ β)) (Finset.univ.filter (fun u => β ≤ θ u))
    (fun u => by rcases le_total (θ u) β with h | h <;> simp [h]) hD hβ1 hβ2
  let v : Fin d → ℝ := fun i => ((i : ℕ) : ℝ) - β
  have hv : v ≠ 0 := by
    intro hv0
    have e0 := congrFun hv0 ⟨0, by omega⟩
    have e1 := congrFun hv0 ⟨1, by omega⟩
    simp [v] at e0 e1
    linarith
  have hkey : ∀ z : Fin d → ℝ, ∑ i, z i = 1 → z ⬝ᵥ v = z ⬝ᵥ a - β := by
    intro z hz
    simp only [dotProduct, v, a, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hz, one_mul]
  refine ⟨v, hv, fun η hη hημ => ?_⟩
  have r1 := sum_rematch C Finset.univ I c₁ m (fun u _ => hc₁0 u) (fun w _ => hm0 w) hc₁s rfl
  have r2 := sum_rematch C Finset.univ J c₂ m (fun u _ => hc₂0 u) (fun w _ => hm0 w) hc₂s rfl
  have hrep : y = ∑ S, (if sp S then 0 else m S) • (S : Set (Fin T)).indicator (1 : Fin T → ℝ)
      + ∑ u, ∑ w ∈ I, (c₁ u * m w / ∑ w ∈ I, m w) •
          ((u \ C ∪ w ∩ C : Finset (Fin T)) : Set (Fin T)).indicator 1
      + ∑ u, ∑ w ∈ J, (c₂ u * m w / ∑ w ∈ J, m w) •
          ((u \ C ∪ w ∩ C : Finset (Fin T)) : Set (Fin T)).indicator 1 := by
    rw [r1, r2, hy]
    ext x
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, I, J,
      Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    have h12 := hcc S
    simp only [c] at h12
    by_cases h1 : sp S <;> by_cases h2 : t0 ∈ S <;> by_cases h3 : x ∈ S <;> by_cases h4 : x ∈ C <;>
      simp [h1, h2, h3, h4, Set.indicator] at h12 ⊢ <;> linarith
  have hpos : ∀ u, c₁ u ≠ 0 ∨ c₂ u ≠ 0 → sp u ∧ m u ≠ 0 := by
    intro u hu
    have h12 := hcc u
    have hcu : c u ≠ 0 := by
      rcases hu with hu | hu
      · have := hc₂0 u; have := lt_of_le_of_ne (hc₁0 u) (Ne.symm hu); intro h0; linarith
      · have := hc₁0 u; have := lt_of_le_of_ne (hc₂0 u) (Ne.symm hu); intro h0; linarith
    by_cases hs : sp u
    · simp only [c, hs, if_true] at hcu
      exact ⟨hs, hcu⟩
    · simp only [c, hs, if_false] at hcu
      exact absurd rfl hcu
  rw [hrep]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun S _ => ?_)
    (Submodule.sum_mem _ fun u _ => Submodule.sum_mem _ fun w hw => ?_))
    (Submodule.sum_mem _ fun u _ => Submodule.sum_mem _ fun w hw => ?_)
  · refine smul_indicator_mem_indicatorCone (by split_ifs; exacts [le_rfl, hm0 S]) fun hne => ?_
    by_cases hs : sp S
    · simp [hs] at hne
    · simp only [hs, if_false] at hne
      have hout : (∀ t ∈ S, P t ≠ P t0) ∨ ∀ s ∉ S, P s ≠ P t0 := by
        rcases not_and_or.1 hs with hs | hs
        · exact Or.inl fun t ht hp => hs ⟨t, ht, hp⟩
        · exact Or.inr fun s hs' hp => hs ⟨s, hs', hp⟩
      exact isWeakReachable_update_of_outer hQ (hmA S hne) hout hη.le hημ
  · refine smul_indicator_mem_indicatorCone (div_nonneg (mul_nonneg (hc₁0 u) (hm0 w)) hD1)
      fun hne => ?_
    have hc1 : c₁ u ≠ 0 := by rintro h0; simp [h0] at hne
    obtain ⟨hsp, hmu⟩ := hpos u (Or.inl hc1)
    have hθ : θ u ≤ β := by
      by_contra hθ; exact hc1 (hc₁L u (by simpa using hθ))
    have htw : t0 ∈ w := (Finset.mem_filter.1 hw).2.2
    obtain ⟨ht₁, ht₁C, h0, h1, hz⟩ := hζ u (hmA u hmu) hsp
    exact isWeakReachable_update_rematch hQ (hmA u hmu) ht₁ ht₁C hsp.2 h0 h1 hz
      (fun _ => by rw [hkey _ h1]; linarith) (fun h => absurd htw h) hη.le hημ
  · refine smul_indicator_mem_indicatorCone (div_nonneg (mul_nonneg (hc₂0 u) (hm0 w)) hD2)
      fun hne => ?_
    have hc2 : c₂ u ≠ 0 := by rintro h0; simp [h0] at hne
    obtain ⟨hsp, hmu⟩ := hpos u (Or.inr hc2)
    have hθ : β ≤ θ u := by
      by_contra hθ; exact hc2 (hc₂R u (by simpa using hθ))
    have htw : t0 ∉ w := (Finset.mem_filter.1 hw).2.2
    obtain ⟨ht₁, ht₁C, h0, h1, hz⟩ := hζ u (hmA u hmu) hsp
    exact isWeakReachable_update_rematch hQ (hmA u hmu) ht₁ ht₁C hsp.2 h0 h1 hz
      (fun h => absurd h htw) (fun _ => by rw [hkey _ h1]; linarith) hη.le hημ

/-- **The defect drops.** If `Q` keeps distinct prices of `P` distinct, `p_{t0} = p_{s0}` with
`s0 ≠ t0`, and the new value `x` differs from every `q_b`, `b ≠ t0`, then
`defect (update Q t0 x) < defect P`: equal pairs of the new prices are equal pairs of `P`, and
`(t0, s0)` is lost. -/
theorem defect_update_lt {Q : Fin T → Fin d → ℝ} {t0 s0 : Fin T} {x : Fin d → ℝ}
    (hdist : ∀ a b, P a ≠ P b → Q a ≠ Q b) (hne : t0 ≠ s0) (heq : P t0 = P s0)
    (hx : ∀ b, b ≠ t0 → x ≠ Q b) : defect (Function.update Q t0 x) < defect P := by
  classical
  unfold defect
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(t0, s0), ?_, ?_⟩
    · simp [hne, heq]
    · have h1 : Function.update Q t0 x s0 = Q s0 := Function.update_of_ne hne.symm _ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_self, h1]
      intro h
      exact hx s0 hne.symm h.2
  · intro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    obtain ⟨hab1, hab2⟩ := hab
    refine ⟨hab1, ?_⟩
    by_cases ha : a = t0
    · subst ha
      rw [Function.update_self, Function.update_of_ne (Ne.symm hab1)] at hab2
      exact absurd hab2 (hx b (Ne.symm hab1))
    by_cases hb : b = t0
    · subst hb
      rw [Function.update_self, Function.update_of_ne ha] at hab2
      exact absurd hab2.symm (hx a ha)
    rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab2
    by_contra hc
    exact hdist a b hc hab2

/-- **One detaching step, closure level.** If `p_{t0} = p_{s0}`, `t0 ≠ s0`, then `P` is a limit of
positive prices with smaller defect at which `y` is still in the weak cone: shift
(`eventually_shift_good`, `tendsto_shiftPrices`), then move `t0` by `η v` (`exists_update_step`)
with `η` small so that the new price avoids all others (`defect_update_lt`), stays positive and
close. -/
theorem mem_closure_split_step (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (h : y ∈ indicatorCone (weakReachableSpectra P)) {t0 s0 : Fin T} (hne : t0 ≠ s0)
    (heq : P t0 = P s0) :
    P ∈ closure {Q : Fin T → Fin d → ℝ | (∀ t, Q t ∈ orthant d) ∧ defect Q < defect P ∧
      y ∈ indicatorCone (weakReachableSpectra Q)} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have h1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), dist (shiftPrices P δ) P < ε / 2 :=
    Metric.tendsto_nhds.1 (tendsto_shiftPrices hP).1 _ (by positivity)
  obtain ⟨δ, hδd, hQpos, hdist, μ, hμ, hmarg⟩ := (h1.and (eventually_shift_good hP)).exists
  set Q := shiftPrices P δ with hQdef
  have hsame : ∀ a b, P a = P b → Q a = Q b := by
    intro a b hab
    funext i
    simp only [hQdef, shiftPrices, hab]
  have hQ : StepData P Q μ := ⟨hsame, hdist, hμ, hmarg⟩
  obtain ⟨v, hv, hstep⟩ := exists_update_step hd hQ h t0
  set f : ℝ → Fin T → Fin d → ℝ := fun η => Function.update Q t0 (Q t0 + η • v) with hf
  have hfc : Continuous f := by
    refine continuous_const.update t0 ?_
    fun_prop
  have hf0 : f 0 = Q := by simp [hf]
  have hft : Filter.Tendsto f (𝓝[>] 0) (𝓝 Q) := by
    rw [← hf0]; exact (hfc.tendsto 0).mono_left nhdsWithin_le_nhds
  have ea : ∀ᶠ η in 𝓝[>] (0:ℝ), ∀ t, f η t ∈ orthant d :=
    Filter.eventually_all.2 fun t =>
      ((continuous_apply t).tendsto Q |>.comp hft).eventually (isOpen_orthant.mem_nhds (hQpos t))
  have eb : ∀ᶠ η in 𝓝[>] (0:ℝ), dist (f η) Q < ε / 2 :=
    Metric.tendsto_nhds.1 hft _ (by positivity)
  have ec : ∀ᶠ η in 𝓝[>] (0:ℝ), ∀ b, b ≠ t0 → Q t0 + η • v ≠ Q b := by
    refine Filter.eventually_all.2 fun b => ?_
    by_cases hb : b = t0
    · exact Filter.Eventually.of_forall fun _ h => absurd hb h
    by_cases hPb : P b = P t0
    · filter_upwards [self_mem_nhdsWithin] with η hη _
      rw [hsame b t0 hPb]
      intro he
      exact smul_ne_zero (ne_of_gt hη) hv (add_eq_left.1 he)
    · have hne : Q t0 ≠ Q b := hdist _ _ (Ne.symm hPb)
      have hc : Continuous fun η : ℝ => Q t0 + η • v := by fun_prop
      have ht : Filter.Tendsto (fun η : ℝ => Q t0 + η • v) (𝓝[>] 0) (𝓝 (Q t0)) := by
        have := hc.tendsto 0
        simp only [zero_smul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      filter_upwards [ht.eventually (isOpen_ne.mem_nhds hne)] with η hη _ using hη
  have ee : ∀ᶠ η in 𝓝[>] (0:ℝ), η * ∑ i, |v i| < μ := by
    have hc : Continuous fun η : ℝ => η * ∑ i, |v i| := by fun_prop
    have ht : Filter.Tendsto (fun η : ℝ => η * ∑ i, |v i|) (𝓝[>] 0) (𝓝 0) := by
      have := hc.tendsto 0
      simp only [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact ht.eventually (Iio_mem_nhds hμ)
  have ed : ∀ᶠ η in 𝓝[>] (0:ℝ), 0 < η := self_mem_nhdsWithin
  obtain ⟨η, ha, hb, hc, hη, he⟩ :=
    (ea.and (eb.and (ec.and (ed.and ee)))).exists
  refine ⟨f η, ⟨ha, ?_, hstep η hη he⟩, ?_⟩
  · exact defect_update_lt hdist hne heq hc
  · calc dist P (f η) ≤ dist P Q + dist Q (f η) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm P Q, dist_comm Q (f η)]; linarith

/-- **Closure of the solvable prices.** For `d ≥ 2`, if `y` lies in the cone of the weakly
reachable spectra of `P`, then `P` is a limit of price sets at which `y` is solvable.

Proof: induction on the number of coincident pairs of prices (`defect`). Without coincidences,
`mem_closure_of_weakReachable_of_injective`: the shift `p ↦ p - δ (∑ log pᵢ) 1` makes every weakly
reachable spectrum reachable. Otherwise detach one index `t0` from its cluster
(`mem_closure_split_step`): after the shift, move `q_{t0}` by `η v` with `v = a - β 1`, and rematch
the cluster parts `S ∩ C` of the spectra that split the cluster so that those containing `t0` get
witnesses with `⟨ζ, v⟩ ≤ 0` and the others `⟨ζ, v⟩ ≥ 0` (a threshold `β` on `⟨ζ, a⟩`). This
keeps `y` in the weak cone and lowers the defect. Note that a fixed representation of `y` need not
become reachable as a whole, so the rematching is needed. -/
theorem mem_closure_of_weakReachable (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (hy : ∀ t, 0 ≤ y t) (h : y ∈ indicatorCone (weakReachableSpectra P)) :
    P ∈ closure {Q : Fin T → Fin d → ℝ | NeoSolvable Q y} := by
  induction' hn : defect P using Nat.strong_induction_on with n ih generalizing P
  by_cases hinj : Function.Injective P
  · exact mem_closure_of_weakReachable_of_injective hd hP hinj hy h
  · obtain ⟨t0, s0, heq, hne⟩ : ∃ t0 s0, P t0 = P s0 ∧ t0 ≠ s0 := by
      by_contra hc; push_neg at hc; exact hinj fun a b hab => hc a b hab
    have := mem_closure_split_step hd hP h hne heq
    rw [← closure_closure]
    refine closure_mono ?_ this
    rintro Q ⟨hQ, hlt, hyQ⟩
    exact ih _ (hn ▸ hlt) hQ hyQ rfl

/-- **Reachable spectra near `P` are weakly reachable at `P`.** If `S` is not weakly reachable,
some `t ∈ S` strictly covers `Sᶜ` with weights `w` (`isWeakReachable_iff`); the strict
inequalities `(∑ w q)ᵢ < (q_t)ᵢ` persist for `Q` near `P`, so `t` covers `Sᶜ` at `Q`. -/
theorem eventually_reachableSpectra_subset_weak (hd : 1 ≤ d) (hP : ∀ t, P t ∈ orthant d) :
    ∀ᶠ Q in 𝓝 P, reachableSpectra Q ⊆ weakReachableSpectra P := by
  have key : ∀ S : Finset (Fin T), ∀ᶠ Q in 𝓝 P, IsReachable Q S → IsWeakReachable P S := by
    intro S
    by_cases hS : IsWeakReachable P S
    · exact Filter.Eventually.of_forall fun _ _ => hS
    · obtain ⟨t, ht, hc⟩ := by
        have := (isWeakReachable_iff hd hP).not.1 hS
        push_neg at this; exact this
      obtain ⟨w, hw0, hwS, hw1, hlt⟩ := hc
      have : ∀ᶠ Q in 𝓝 P, ∀ i, (∑ r, w r • Q r) i < Q t i := by
        refine Filter.eventually_all.2 fun i => ?_
        have hc : Continuous fun Q : Fin T → Fin d → ℝ => (∑ r, w r • Q r) i := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          fun_prop
        exact (hc.tendsto P).eventually_lt ((by fun_prop : Continuous fun Q : Fin T → Fin d → ℝ => Q t i).tendsto P) (hlt i)
      filter_upwards [this] with Q hQ hR
      exact absurd ⟨w, hw0, hwS, hw1, fun i => (hQ i).le⟩ (hR t ht)
  filter_upwards [Filter.eventually_all_finset (Finset.univ : Finset (Finset (Fin T))) |>.2 fun S _ => key S] with Q hQ S hS
  exact hQ S (Finset.mem_univ _) hS

/-- **Converse.** If `P` is a limit of prices at which `y` is solvable, then `y` lies in the cone
of the weakly reachable spectra of `P`: near `P` the prices are positive, `y` lies in the cone of
`Sp(Q)` (`neoSolvable_iff_mem_indicatorCone`), and `Sp(Q) ⊆ W(P)`
(`eventually_reachableSpectra_subset_weak`). -/
theorem weakReachable_of_mem_closure (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (hy : ∀ t, 0 ≤ y t) (h : P ∈ closure {Q : Fin T → Fin d → ℝ | NeoSolvable Q y}) :
    y ∈ indicatorCone (weakReachableSpectra P) := by
  have hU : {Q : Fin T → Fin d → ℝ | (∀ t, Q t ∈ orthant d) ∧
      reachableSpectra Q ⊆ weakReachableSpectra P} ∈ 𝓝 P := by
    have h1 := eventually_reachableSpectra_subset_weak (by omega) hP
    have h2 : ∀ᶠ Q in 𝓝 P, ∀ t, Q t ∈ orthant d :=
      Filter.eventually_all.2 fun t =>
        ((continuous_apply t).tendsto P).eventually (isOpen_orthant.mem_nhds (hP t))
    exact (h2.and h1)
  obtain ⟨Q, ⟨hQ, hsub⟩, hQy⟩ := mem_closure_iff_nhds.1 h _ hU
  exact Submodule.span_mono (Set.image_mono hsub)
    ((neoSolvable_iff_mem_indicatorCone hd hQ hy).1 hQy)

end NeoTiling
