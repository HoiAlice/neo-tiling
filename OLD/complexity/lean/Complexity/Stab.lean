import Complexity

/-!
# The stable set polytope: the balls needed by the ellipsoid method

The Turing reduction of Theorem 3.5 uses the Yudin–Nemirovski theorem and the strong
optimization theorem of Grötschel–Lovász–Schrijver for `STAB(G)`. Those theorems are cited, not
formalized. This file checks the facts about `STAB(G)` that the citation needs, for a graph
without loops:

* `inStab_of_nonneg_of_sum_le_one`: the simplex `{s ≥ 0, ∑ s ≤ 1}` lies in `STAB(G)`.
* `inStab_of_ball`: the ball of radius `1/(4n)` around `(1/(4n)) 𝟙` lies in `STAB(G)`, so the
  polytope is full-dimensional.
* `InStab.mem_Icc`, `InStab.sum_sq_le`: `STAB(G) ⊆ [0, 1]ⁿ`, inside the ball of radius `√n`
  around `0`. In particular queries with some `s v > 1` are answered "no" without the oracle.
-/

namespace NeoTiling.Complexity

open Finset

variable {n m : ℕ} {eu ev : Fin m → Fin n}

/-- The simplex `{s ≥ 0, ∑ s ≤ 1}` lies in the stable set polytope of a loopless graph:
`s = (1 - ∑ s) 1_∅ + ∑_v s_v 1_{v}`. -/
theorem inStab_of_nonneg_of_sum_le_one (hloop : ∀ k, eu k ≠ ev k) {s : Fin n → ℝ}
    (hs0 : ∀ v, 0 ≤ s v) (hs1 : ∑ v, s v ≤ 1) : InStab eu ev s := by
  classical
  let μ : Finset (Fin n) → ℝ := fun I =>
    (if I = ∅ then 1 - ∑ v, s v else 0) + ∑ v, if I = {v} then s v else 0
  have hsing : ∀ I : Finset (Fin n), (∑ v, if I = {v} then s v else 0) ≠ 0 → ∃ v, I = {v} := by
    intro I h
    by_contra hc
    push_neg at hc
    exact h (Finset.sum_eq_zero fun v _ => if_neg (hc v))
  refine ⟨μ, fun I => add_nonneg ?_ (sum_nonneg fun v _ => ?_), fun I hI => ?_, ?_, ?_⟩
  · split_ifs <;> linarith
  · split_ifs <;> simp [hs0]
  · by_cases h0 : I = ∅
    · subst h0; intro k; simp
    · have : (∑ v, if I = {v} then s v else 0) ≠ 0 := by simpa [μ, h0] using hI
      obtain ⟨v, rfl⟩ := hsing I this
      intro k ⟨h1, h2⟩
      simp only [mem_singleton] at h1 h2
      exact hloop k (h1.trans h2.symm)
  · simp only [μ, sum_add_distrib]
    rw [sum_comm]
    simp
  · funext u
    rw [Finset.sum_apply]
    simp only [μ, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, sum_mul, ite_mul,
      zero_mul]
    rw [sum_comm (s := univ) (t := univ)]
    simp [Set.indicator_apply]

/-- **Inner ball.** The ball of radius `1/(4n)` around `(1/(4n)) 𝟙` lies in `STAB(G)`. -/
theorem inStab_of_ball (hn : 0 < n) (hloop : ∀ k, eu k ≠ ev k) {s : Fin n → ℝ}
    (hs : ∑ v, (s v - 1 / (4 * (n : ℝ))) ^ 2 ≤ (1 / (4 * (n : ℝ))) ^ 2) : InStab eu ev s := by
  set c : ℝ := 1 / (4 * (n : ℝ))
  have hc : 0 < c := by positivity
  have hv : ∀ v, |s v - c| ≤ c := by
    intro v
    have : (s v - c) ^ 2 ≤ c ^ 2 :=
      (single_le_sum (fun w _ => sq_nonneg (s w - c)) (mem_univ v)).trans hs
    exact abs_le_of_sq_le_sq' this hc.le |> fun h => abs_le.2 h
  refine inStab_of_nonneg_of_sum_le_one hloop (fun v => by linarith [(abs_le.1 (hv v)).1]) ?_
  calc ∑ v, s v ≤ ∑ _v : Fin n, 2 * c := sum_le_sum fun v _ => by linarith [(abs_le.1 (hv v)).2]
    _ = 1 / 2 := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, c]
      field_simp
      ring
    _ ≤ 1 := by norm_num

/-- `STAB(G) ⊆ [0, 1]ⁿ`. -/
theorem InStab.mem_Icc {s : Fin n → ℝ} (hs : InStab eu ev s) (v : Fin n) :
    0 ≤ s v ∧ s v ≤ 1 := by
  classical
  obtain ⟨μ, h0, -, h1, rfl⟩ := hs
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, mem_coe,
    Pi.one_apply, mul_ite, mul_one, mul_zero]
  refine ⟨sum_nonneg fun I _ => ?_, h1 ▸ sum_le_sum fun I _ => ?_⟩ <;> split_ifs <;> simp [h0]

/-- **Outer ball.** `STAB(G)` lies in the ball of radius `√n` around `0`. -/
theorem InStab.sum_sq_le {s : Fin n → ℝ} (hs : InStab eu ev s) : ∑ v, s v ^ 2 ≤ (n : ℝ) := by
  calc ∑ v, s v ^ 2 ≤ ∑ _v : Fin n, (1 : ℝ) := sum_le_sum fun v _ => by
        obtain ⟨h0, h1⟩ := hs.mem_Icc v
        nlinarith
    _ = n := by simp

end NeoTiling.Complexity
