import NeoTiling.Spectrum

/-!
# Reachable spectra

An index `t` *covers* a set `R` (`Covers`) if `p_t` dominates a convex combination of the prices
`p_r`, `r ∈ R`. A set `S` is a *reachable spectrum* (`IsReachable`) if no `t ∈ S` covers `Sᶜ`;
`Sp(P)` is `reachableSpectra P`.

Main results:

* `IsNeoclassical.spectrum_subset_reachableSpectra`: `Sp(h, P) ⊆ Sp(P)` for every neoclassical
  `h` (Jensen's inequality and monotonicity).
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

end NeoTiling
