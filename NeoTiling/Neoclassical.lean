import Mathlib

/-!
# Neoclassical functions

The open positive orthant `ℝᵈ₊₊` (`orthant`) and neoclassical functions (`IsNeoclassical`):
continuous, concave, nonnegative and positively homogeneous of degree one on `ℝᵈ₊`.

Main results:

* `IsNeoclassical.mono`: a neoclassical function is monotone on `ℝᵈ₊`.
* `isNeoclassical_polyMin`: the polyhedral function `z ↦ min_j ⟨ξ_j, z⟩` with `ξ_j ≥ 0` is
  neoclassical.
-/

open Set

namespace NeoTiling

variable {d : ℕ}

/-- The open positive orthant `{x | ∀ i, 0 < x i}`. -/
def orthant (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, 0 < x i}

theorem isOpen_orthant : IsOpen (orthant d) := by
  simpa [orthant, Set.pi] using
    isOpen_set_pi finite_univ fun (_ : Fin d) _ => isOpen_Ioi (a := (0 : ℝ))

theorem orthant_subset_Ici : orthant d ⊆ Ici 0 := fun _ hx i => (hx i).le

theorem mul_mem_orthant {p x : Fin d → ℝ} (hp : p ∈ orthant d) (hx : x ∈ orthant d) :
    p * x ∈ orthant d := fun i => mul_pos (hp i) (hx i)

/-- A neoclassical function: continuous, concave, nonnegative and positively homogeneous of
degree one on the closed orthant `ℝᵈ₊`. -/
structure IsNeoclassical (h : (Fin d → ℝ) → ℝ) : Prop where
  continuousOn : ContinuousOn h (Ici 0)
  concaveOn : ConcaveOn ℝ (Ici 0) h
  nonneg : ∀ x, 0 ≤ x → 0 ≤ h x
  homogeneous : ∀ c : ℝ, 0 ≤ c → ∀ x, 0 ≤ x → h (c • x) = c * h x

/-- Neoclassical functions are monotone on `ℝᵈ₊`: by concavity and homogeneity,
`h b = 2 h (a / 2 + (b - a) / 2) ≥ h a + h (b - a) ≥ h a`. -/
theorem IsNeoclassical.mono {h : (Fin d → ℝ) → ℝ} (hh : IsNeoclassical h) {a b : Fin d → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : h a ≤ h b := by
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have := hh.homogeneous 2 zero_le_two _ (hh.concaveOn.1 ha hba one_half_pos.le one_half_pos.le
    (add_halves 1))
  have hc := hh.concaveOn.2 ha hba one_half_pos.le one_half_pos.le (add_halves 1)
  norm_num [smul_add, smul_smul] at this hc
  linarith [hh.nonneg _ hba]

/-! ### Polyhedral functions -/

section PolyMin

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The polyhedral function `z ↦ min_j ⟨ξ_j, z⟩`. -/
noncomputable def polyMin (ξ : ι → Fin d → ℝ) (z : Fin d → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => ξ j ⬝ᵥ z

theorem polyMin_le (ξ : ι → Fin d → ℝ) (z : Fin d → ℝ) (j : ι) : polyMin ξ z ≤ ξ j ⬝ᵥ z :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem le_polyMin {ξ : ι → Fin d → ℝ} {z : Fin d → ℝ} {c : ℝ} (H : ∀ j, c ≤ ξ j ⬝ᵥ z) :
    c ≤ polyMin ξ z :=
  Finset.le_inf' _ _ fun j _ => H j

theorem exists_dot_eq_polyMin (ξ : ι → Fin d → ℝ) (z : Fin d → ℝ) :
    ∃ j, ξ j ⬝ᵥ z = polyMin ξ z :=
  (Finset.exists_mem_eq_inf' Finset.univ_nonempty _).imp fun _ h => h.2.symm

theorem isNeoclassical_polyMin {ξ : ι → Fin d → ℝ} (hξ : ∀ j, 0 ≤ ξ j) :
    IsNeoclassical (polyMin ξ) where
  continuousOn := (Continuous.finset_inf'_apply Finset.univ_nonempty fun j _ =>
    continuous_const.dotProduct continuous_id).continuousOn
  concaveOn := ⟨convex_Ici 0, fun x _ y _ a b ha hb _ => le_polyMin fun j => by
    simpa [dotProduct_add] using add_le_add (mul_le_mul_of_nonneg_left (polyMin_le ξ x j) ha)
      (mul_le_mul_of_nonneg_left (polyMin_le ξ y j) hb)⟩
  nonneg x hx := le_polyMin fun j => dotProduct_nonneg_of_nonneg (hξ j) hx
  homogeneous c hc x _ := by
    obtain ⟨j, hj⟩ := exists_dot_eq_polyMin ξ x
    refine le_antisymm ((polyMin_le ξ _ j).trans_eq ?_) (le_polyMin fun l => ?_)
    · rw [dotProduct_smul, smul_eq_mul, hj]
    · simpa using mul_le_mul_of_nonneg_left (polyMin_le ξ x l) hc

end PolyMin

end NeoTiling
