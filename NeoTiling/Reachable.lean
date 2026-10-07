import NeoTiling.Spectrum

/-!
# Reachable spectra

An index `t` *covers* a set `R` (`Covers`) if `p_t` dominates a convex combination of the prices
`p_r`, `r ∈ R`. A set `S` is a *reachable spectrum* (`IsReachable`) if no `t ∈ S` covers `Sᶜ`;
`Sp(P)` is `reachableSpectra P`.

Main results:

* `IsNeoclassical.spectrum_subset_reachableSpectra`: `Sp(h, P) ⊆ Sp(P)` for every neoclassical
  `h` (Jensen's inequality and monotonicity).
* `Covers.exists_card_le`: a covering by `R` can be reduced to a covering by at most `d` indices
  of `R` (Carathéodory).
* `isReachable_iff`: reachability is a finite test over sets of at most `d` indices.
-/

open Set

namespace NeoTiling

variable {d T : ℕ}

/-- `t` covers `R`: `∑_r w_r p_r ≤ p_t` for some convex weights `w` supported on `R`. -/
def Covers (P : Fin T → Fin d → ℝ) (t : Fin T) (R : Finset (Fin T)) : Prop :=
  ∃ w : Fin T → ℝ, (∀ r, 0 ≤ w r) ∧ (∀ r ∉ R, w r = 0) ∧ ∑ r, w r = 1 ∧ ∑ r, w r • P r ≤ P t

/-- `S` is a reachable spectrum: no `t ∈ S` covers the complement `Sᶜ`. -/
def IsReachable (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ¬ Covers P t Sᶜ

/-- The reachable spectra `Sp(P)`. -/
def reachableSpectra (P : Fin T → Fin d → ℝ) : Set (Finset (Fin T)) :=
  {S | IsReachable P S}

variable {P : Fin T → Fin d → ℝ}

/-- **`Sp(h, P) ⊆ Sp(P)`.** Let `x` be a strict point of `S`, `t ∈ S`, and let `w` cover
`Sᶜ`. Then `h (p_r * x) > 1` for `r ∉ S`, and by monotonicity and Jensen
`1 > h (p_t * x) ≥ h (∑ w_r (p_r * x)) ≥ ∑ w_r h (p_r * x) ≥ 1`. -/
theorem IsNeoclassical.spectrum_subset_reachableSpectra {h : (Fin d → ℝ) → ℝ}
    (hh : IsNeoclassical h) (hP : ∀ t, P t ∈ orthant d) : spectrum h P ⊆ reachableSpectra P := by
  rintro S ⟨x, hxo, hlt, hgt⟩ t ht ⟨w, hw0, hwS, hw1, hwP⟩
  have hx0 : 0 ≤ x := orthant_subset_Ici hxo
  have hu (r) : 0 ≤ P r * x := orthant_subset_Ici (mul_mem_orthant (hP r) hxo)
  have hr (r) : w r ≤ w r * h (P r * x) := by
    by_cases hr : r ∈ S
    · simp [hwS r (by simpa using hr)]
    · simpa using mul_le_mul_of_nonneg_left (hgt r hr).le (hw0 r)
  have hJ := hh.concaveOn.le_map_sum (t := Finset.univ) (w := w) (p := fun r => P r * x)
    (fun r _ => hw0 r) hw1 fun r _ => hu r
  have hsum : ∑ r, w r • (P r * x) = (∑ r, w r • P r) * x := by
    rw [Finset.sum_mul]; simp_rw [smul_mul_assoc]
  have hM := hh.mono (Finset.sum_nonneg fun r _ => smul_nonneg (hw0 r) (hu r))
    (hsum ▸ mul_le_mul_of_nonneg_right hwP hx0)
  have := hlt t ht
  simp only [smul_eq_mul] at hJ
  linarith [Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hr r]

/-- Covering is monotone in `R`. -/
theorem Covers.mono {t : Fin T} {R R' : Finset (Fin T)} (hc : Covers P t R) (hR : R ⊆ R') :
    Covers P t R' := by
  obtain ⟨w, hw0, hwR, hw1, hwP⟩ := hc
  exact ⟨w, hw0, fun r hr => hwR r (mt (@hR r) hr), hw1, hwP⟩

/-- **Carathéodory.** If `t` covers `R`, it covers a subset of `R` with at most `d` elements.
Induction on `|R|`: for `|R| > d` the `|R| + 1 > d + 1` vectors `(1, 0)` and `(p_r, 1)` in
`ℝᵈ × ℝ` are linearly dependent; moving the weights along the dependence until one of them
vanishes keeps a covering and removes an index. -/
theorem Covers.exists_card_le (hd : 0 < d) {t : Fin T} {R : Finset (Fin T)}
    (hc : Covers P t R) : ∃ R' ⊆ R, R'.card ≤ d ∧ Covers P t R' := by
  classical
  induction R using Finset.strongInductionOn with | _ R ih =>
  by_cases hR : R.card ≤ d
  · exact ⟨R, subset_rfl, hR, hc⟩
  obtain ⟨w, hw0, hwR, hw1, hwP⟩ := hc
  -- a relation `g₀ (1, 0) + ∑ g_r (p_r, 1) = 0` with `g₀ ≤ 0`
  let v (i : Option R) : (Fin d → ℝ) × ℝ := i.elim (1, 0) fun r => (P r, 1)
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 fun h : LinearIndependent ℝ v =>
    by have := h.fintype_card_le_finrank; simp at this; omega
  wlog hg0 : g none ≤ 0 generalizing g
  · exact this (-g) (by simp [hg]) (by simpa using hi) (by simp; linarith)
  let μ (r : Fin T) : ℝ := if h : r ∈ R then g (some ⟨r, h⟩) else 0
  have hμR (r) (hr : r ∉ R) : μ r = 0 := by simp [μ, hr]
  have hsum (F : Fin T → (Fin d → ℝ) × ℝ) : ∑ r, μ r • F r = ∑ x : R, g (some x) • F x := by
    rw [← Finset.sum_subset R.subset_univ fun r _ hr => by simp [hμR r hr], ← Finset.sum_coe_sort]
    simp [μ]
  simp only [v, Fintype.sum_option, Option.elim, ← hsum fun r => (P r, 1)] at hg
  have hμ1 : ∑ r, μ r = 0 := by simpa [Prod.snd_sum] using congrArg Prod.snd hg
  have hμP : ∑ r, μ r • P r = -g none • 1 := by
    have := congrArg Prod.fst hg
    simp [Prod.fst_sum] at this
    linear_combination (norm := module) this
  -- some coefficient of the relation is positive
  have hpos : ∃ r, 0 < μ r := by
    by_contra! h
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos fun r _ => h r).1 hμ1
    have : g none = 0 := by simpa [h0] using congrFun hμP ⟨0, hd⟩
    rcases i with _ | ⟨r, hr⟩
    · exact hi this
    · exact hi (by simpa [μ, hr] using h0 r (Finset.mem_univ _))
  -- move the weights along the relation until the first one vanishes
  obtain ⟨r₀, hr₀, hmin⟩ := (Finset.univ.filter (0 < μ ·)).exists_min_image (fun r => w r / μ r)
    (by simpa [Finset.filter_nonempty_iff] using hpos)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₀ hmin
  have hr₀R : r₀ ∈ R := by by_contra h; simp [hμR r₀ h] at hr₀
  set θ := w r₀ / μ r₀
  have hθ : 0 ≤ θ := div_nonneg (hw0 _) hr₀.le
  refine (ih _ (Finset.erase_ssubset hr₀R)
    ⟨fun r => w r - θ * μ r, fun r => ?_, fun r hr => ?_, ?_, ?_⟩).imp
    fun R' ⟨h1, h2⟩ => ⟨h1.trans (Finset.erase_subset _ _), h2⟩
  · rcases lt_or_ge 0 (μ r) with h | h
    · have := hmin r h; rw [le_div_iff₀ h] at this; linarith
    · nlinarith [hw0 r]
  · by_cases h : r = r₀
    · subst h; simp [θ, div_mul_cancel₀ _ hr₀.ne']
    · have : r ∉ R := fun h' => hr (Finset.mem_erase.2 ⟨h, h'⟩)
      simp [hwR r this, hμR r this]
  · simp [Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, hμ1]
  · have : ∑ r, (w r - θ * μ r) • P r = ∑ r, w r • P r - (θ * -g none) • 1 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμP]
    rw [this]
    exact (sub_le_self _ (smul_nonneg (mul_nonneg hθ (by linarith)) zero_le_one)).trans hwP

/-- **Finite test of reachability.** `S` is reachable iff no `t ∈ S` covers a set of at most `d`
indices outside `S`. -/
theorem isReachable_iff (hd : 0 < d) {S : Finset (Fin T)} :
    IsReachable P S ↔ ∀ t ∈ S, ∀ R ⊆ Sᶜ, R.card ≤ d → ¬ Covers P t R := by
  refine ⟨fun hS t ht R hR _ hc => hS t ht (hc.mono hR), fun H t ht hc => ?_⟩
  obtain ⟨R, hR, hcard, hc'⟩ := hc.exists_card_le hd
  exact H t ht R hR hcard hc'

end NeoTiling
