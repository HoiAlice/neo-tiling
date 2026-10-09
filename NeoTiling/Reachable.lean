import NeoTiling.Spectrum

/-!
# Reachable spectra

A set `S` is a *reachable spectrum* (`IsReachable`) if every `t ∈ S` has a witness: a nonzero
`ξ ≥ 0` with `⟨ξ, p_s - p_t⟩ > 0` for all `s ∉ S`. `Sp(P)` is `reachableSpectra P`.

Main results:

* `IsNeoclassical.spectrum_subset_reachableSpectra`: `Sp(h, P) ⊆ Sp(P)` for every neoclassical
  `h` and `d ≥ 1` (separation; Jensen's inequality and monotonicity).
-/

open Set

namespace NeoTiling

variable {d T : ℕ}

/-- `S` is a reachable spectrum: every `t ∈ S` has a nonzero `ξ ≥ 0` with `⟨ξ, p_s - p_t⟩ > 0`
for all `s ∉ S`. -/
def IsReachable (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∉ S, 0 < ξ ⬝ᵥ (P s - P t)

/-- The reachable spectra `Sp(P)`. -/
def reachableSpectra (P : Fin T → Fin d → ℝ) : Set (Finset (Fin T)) :=
  {S | IsReachable P S}

variable {P : Fin T → Fin d → ℝ}

open Pointwise in
/-- **`Sp(h, P) ⊆ Sp(P)`.** Let `x` be a strict point of `S` and `t ∈ S`. On the closed convex
set `C = conv {p_s * x | s ∉ S} + ℝᵈ₊` monotonicity and Jensen give `h ≥ 1`, while
`h (p_t * x) < 1`. A functional `f` with `f (p_t * x) < u < f (C)` is nonnegative on `ℝᵈ₊`, and
`ξᵢ = f (eᵢ) xᵢ` is the witness, since `⟨ξ, p⟩ = f (p * x)`. For `S = univ` any `eᵢ` works. -/
theorem IsNeoclassical.spectrum_subset_reachableSpectra {h : (Fin d → ℝ) → ℝ}
    (hh : IsNeoclassical h) (hd : 1 ≤ d) (hP : ∀ t, P t ∈ orthant d) :
    spectrum h P ⊆ reachableSpectra P := by
  rintro S ⟨x, hxo, hlt, hgt⟩ t ht
  by_cases hS : ∀ s, s ∈ S
  · exact ⟨Pi.single ⟨0, hd⟩ 1, fun i => by rw [Pi.single_apply]; positivity,
      fun h0 => by simpa using congrFun h0 ⟨0, hd⟩, fun s hs => (hs (hS s)).elim⟩
  push_neg at hS
  obtain ⟨s₀, hs₀⟩ := hS
  have hx0 : 0 ≤ x := orthant_subset_Ici hxo
  have hu (r) : 0 ≤ P r * x := orthant_subset_Ici (mul_mem_orthant (hP r) hxo)
  set K := stdSimplex ℝ (Fin T) ∩ (S : Set (Fin T)).pi fun _ => {0}
  set L := Fintype.linearCombination ℝ fun r => P r * x
  set C := L '' K + Ici 0
  have hPsC (s) (hs : s ∉ S) : P s * x ∈ C :=
    ⟨_, ⟨Pi.single s 1, ⟨single_mem_stdSimplex ℝ s, fun r hr =>
      Pi.single_eq_of_ne (ne_of_mem_of_not_mem hr hs) 1⟩, rfl⟩, 0, self_mem_Ici, by simp [L]⟩
  have hC : ∀ c ∈ C, 1 ≤ h c := by
    rintro _ ⟨_, ⟨w, ⟨hw, hwS⟩, rfl⟩, v, hv, rfl⟩
    have hr (r) : w r ≤ w r * h (P r * x) := by
      by_cases hr : r ∈ S
      · simp [show w r = 0 from hwS r hr]
      · simpa using mul_le_mul_of_nonneg_left (hgt r hr).le (hw.1 r)
    have hJ := hh.concaveOn.le_map_sum (t := Finset.univ) (w := w) (p := fun r => P r * x)
      (fun r _ => hw.1 r) hw.2 fun r _ => hu r
    have hL : L w = ∑ r, w r • (P r * x) := by simp [L, Fintype.linearCombination_apply]
    have hM := hh.mono (Finset.sum_nonneg fun r _ => smul_nonneg (hw.1 r) (hu r))
      (le_add_of_nonneg_right hv : ∑ r, w r • (P r * x) ≤ _ + v)
    rw [← hL] at hM hJ
    simp only [smul_eq_mul] at hJ
    show 1 ≤ h (L w + v)
    linarith [Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hr r, hw.2]
  obtain ⟨f, u, hfu, hfC⟩ := geometric_hahn_banach_point_closed
    ((((convex_stdSimplex ℝ _).inter (convex_pi fun _ _ => convex_singleton 0)).linear_image
      L).add (convex_Ici 0))
    (isClosed_Ici.add_left_of_isCompact (((isCompact_stdSimplex _).inter_right
      (isClosed_set_pi fun _ _ => isClosed_singleton)).image L.continuous_of_finiteDimensional))
    (fun h' => (hlt t ht).not_ge (hC _ h'))
  have hf0 (v : Fin d → ℝ) (hv : 0 ≤ v) : 0 ≤ f v := not_lt.1 fun hfv => by
    obtain ⟨a, ha, b, hb, -⟩ := hPsC s₀ hs₀
    have hab := hfC _ ⟨a, ha, b, hb, rfl⟩
    have := hfC _ ⟨a, ha, b + ((f (a + b) - u) / -f v) • v,
      add_nonneg hb (smul_nonneg (div_nonneg (by linarith) (by linarith)) hv), rfl⟩
    simp only [← add_assoc, map_add, map_smul, smul_eq_mul] at this hab
    rw [div_mul_eq_mul_div, div_neg, mul_div_cancel_right₀ _ hfv.ne] at this
    linarith
  set ξ : Fin d → ℝ := fun i => f (fun j => if i = j then 1 else 0) * x i
  have key (p : Fin d → ℝ) : ξ ⬝ᵥ p = f (p * x) := by
    rw [← f.coe_coe, f.toLinearMap.pi_apply_eq_sum_univ]
    simp only [dotProduct, ξ, Pi.mul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos (s) (hs : s ∉ S) : 0 < ξ ⬝ᵥ (P s - P t) := by
    rw [key, sub_mul, map_sub]; linarith [hfC _ (hPsC s hs)]
  refine ⟨ξ, fun i => mul_nonneg (hf0 _ fun j => ?_) (hx0 i), fun h0 => ?_, hpos⟩
  · dsimp; split_ifs <;> norm_num
  · have := hpos s₀ hs₀
    rw [h0, zero_dotProduct] at this
    exact lt_irrefl _ this

end NeoTiling
