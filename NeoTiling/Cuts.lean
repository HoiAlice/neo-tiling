import NeoTiling.Perturbation

/-!
# Covering cuts: a relaxation of weak solvability

`t` is *blocked* by `R` at prices `Q` (`IsBlocked`) if some nonzero `ξ ≥ 0` has
`⟨ξ, q_r - q_t⟩ ≥ 0` for all `r ∈ R`, that is, `t` does not strictly cover `R`.

Main results:

* `exists_isBlocked_of_cut`: **covering cut.** Let `y` be weakly solvable at `Q`, `⟨w, y⟩ < 0`,
  and let `C` be a finite set of pairs `(t, R)` such that every `S` with `∑_{t ∈ S} w_t < 0`
  contains the `t` and misses the `R` of some pair in `C`. Then some pair of `C` is blocked.
* `isBlocked_singleton_iff`: `t` is blocked by `{s}` iff `q_t^i ≤ q_s^i` for some `i`.
* `le_of_dominates`: if `y` is weakly solvable at `Q` and `q_s < q_t` coordinatewise, then
  `y_t ≤ y_s`.
* `isBlocked_smul_iff`: blocking does not change under a positive rescaling of the coordinates.
* `le_minPert_of_relaxation`: any condition `Φ` implied by weak solvability gives the lower
  bound `inf {totalPert P Q | Φ Q, Q in the box of D} ≤ minPert P y` once `minPert P y ≤ D`.
-/

namespace NeoTiling

variable {d T : ℕ} {P Q : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

/-- `t` is blocked by `R` at `Q`: some nonzero `ξ ≥ 0` has `⟨ξ, q_r - q_t⟩ ≥ 0` for all
`r ∈ R`. -/
def IsBlocked (Q : Fin T → Fin d → ℝ) (t : Fin T) (R : Finset (Fin T)) : Prop :=
  ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ r ∈ R, 0 ≤ ξ ⬝ᵥ (Q r - Q t)

/-- **Covering cut.** If `y` is weakly solvable at `Q`, `⟨w, y⟩ < 0`, and every `S` with
`∑_{t ∈ S} w_t < 0` contains `c.1` and misses `c.2` for some `c ∈ C`, then some `c ∈ C` is
blocked. -/
theorem exists_isBlocked_of_cut (h : y ∈ indicatorCone (weakReachableSpectra Q))
    (w : Fin T → ℝ) (hw : ∑ t, w t * y t < 0) (C : Finset (Fin T × Finset (Fin T)))
    (hC : ∀ S : Finset (Fin T), ∑ t ∈ S, w t < 0 → ∃ c ∈ C, c.1 ∈ S ∧ Disjoint c.2 S) :
    ∃ c ∈ C, IsBlocked Q c.1 c.2 := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨m, hm0, hmA, -, rfl⟩ := exists_coef_of_mem_indicatorCone h
  -- every spectrum in the representation has `∑_{t ∈ S} w_t ≥ 0`
  have key : ∀ S, 0 ≤ m S * ∑ t ∈ S, w t := by
    intro S
    by_cases hS : m S = 0
    · simp [hS]
    refine mul_nonneg (hm0 S) (not_lt.1 fun hlt => ?_)
    obtain ⟨c, hc, hc1, hc2⟩ := hC S hlt
    obtain ⟨ξ, hξ0, hξ, hξS⟩ := hmA S hS c.1 hc1
    exact hno c hc ⟨ξ, hξ0, hξ, fun r hr => hξS r (Finset.disjoint_left.1 hc2 hr)⟩
  have hsum : ∑ t, w t * (∑ S, m S • (S : Set (Fin T)).indicator (1 : Fin T → ℝ)) t =
      ∑ S, m S * ∑ t ∈ S, w t := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp [Set.indicator_apply, Finset.sum_ite_mem, mul_comm]
  exact absurd hw (not_lt.2 (hsum ▸ Finset.sum_nonneg fun S _ => key S))

/-- In a weakly reachable `S`, every `t ∈ S` is blocked by every `R` disjoint from `S`: the weak
witness of `t` works. -/
theorem IsWeakReachable.isBlocked {S : Finset (Fin T)} (hS : IsWeakReachable Q S) {t : Fin T}
    (ht : t ∈ S) {R : Finset (Fin T)} (hR : Disjoint R S) : IsBlocked Q t R := by
  obtain ⟨ξ, hξ0, hξ, hξS⟩ := hS t ht
  exact ⟨ξ, hξ0, hξ, fun r hr => hξS r (Finset.disjoint_left.1 hR hr)⟩

/-- **Refutation block.** If `y` is weakly solvable at `Q` and `⟨w, y⟩ < 0`, then some weakly
reachable `S` has `∑_{t ∈ S} w_t < 0`. -/
theorem exists_weakReachable_sum_neg (h : y ∈ indicatorCone (weakReachableSpectra Q))
    (w : Fin T → ℝ) (hw : ∑ t, w t * y t < 0) :
    ∃ S, IsWeakReachable Q S ∧ ∑ t ∈ S, w t < 0 := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨m, hm0, hmA, -, rfl⟩ := exists_coef_of_mem_indicatorCone h
  have key : ∀ S, 0 ≤ m S * ∑ t ∈ S, w t := by
    intro S
    by_cases hS : m S = 0
    · simp [hS]
    exact mul_nonneg (hm0 S) (hno S (hmA S hS))
  have hsum : ∑ t, w t * (∑ S, m S • (S : Set (Fin T)).indicator (1 : Fin T → ℝ)) t =
      ∑ S, m S * ∑ t ∈ S, w t := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp [Set.indicator_apply, Finset.sum_ite_mem, mul_comm]
  exact absurd hw (not_lt.2 (hsum ▸ Finset.sum_nonneg fun S _ => key S))

/-- `t` is blocked by a single `s` iff `q_t^i ≤ q_s^i` in some coordinate. -/
theorem isBlocked_singleton_iff {s t : Fin T} :
    IsBlocked Q t {s} ↔ ∃ i, Q t i ≤ Q s i := by
  constructor
  · rintro ⟨ξ, hξ0, hξ, hξs⟩
    by_contra hall
    push_neg at hall
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
    have hi' : 0 < ξ i := lt_of_le_of_ne (hξ0 i) (Ne.symm hi)
    have : ξ ⬝ᵥ (Q s - Q t) < 0 := by
      calc ∑ j, ξ j * (Q s - Q t) j < ∑ _j : Fin d, (0 : ℝ) :=
            Finset.sum_lt_sum
              (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hξ0 j)
                (by simp only [Pi.sub_apply]; linarith [hall j]))
              ⟨i, Finset.mem_univ _, mul_neg_of_pos_of_neg hi'
                (by simp only [Pi.sub_apply]; linarith [hall i])⟩
        _ = 0 := by simp
    exact absurd (hξs s (Finset.mem_singleton_self s)) (not_le.2 this)
  · rintro ⟨i, hi⟩
    refine ⟨Pi.single i 1, Pi.single_nonneg.2 zero_le_one, fun h => by simpa using congr_fun h i,
      fun r hr => ?_⟩
    rw [Finset.mem_singleton] at hr
    subst hr
    simp [single_dotProduct, hi]

/-- **Convex combinations.** If `t` is blocked by `R`, then for all weights `w ≥ 0` with
`∑_{r ∈ R} w_r = 1` the price `q_t` does not strictly dominate `∑_{r ∈ R} w_r q_r`: some
coordinate has `q_t^i ≤ ∑_{r ∈ R} w_r q_r^i`. -/
theorem IsBlocked.exists_le_sum {t : Fin T} {R : Finset (Fin T)} (hb : IsBlocked Q t R)
    (w : Fin T → ℝ) (hw0 : ∀ r, 0 ≤ w r) (hw1 : ∑ r ∈ R, w r = 1) :
    ∃ i, Q t i ≤ ∑ r ∈ R, w r * Q r i := by
  obtain ⟨ξ, hξ0, hξ, hξR⟩ := hb
  by_contra hall
  push_neg at hall
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
  have hi' : 0 < ξ i := lt_of_le_of_ne (hξ0 i) (Ne.symm hi)
  -- `⟨ξ, c - q_t⟩ = ∑_{r ∈ R} w_r ⟨ξ, q_r - q_t⟩ ≥ 0` for `c = ∑_{r ∈ R} w_r q_r`
  have hnn : 0 ≤ ∑ j, ξ j * (∑ r ∈ R, w r * Q r j - Q t j) := by
    have e : ∀ j, ∑ r ∈ R, w r * Q r j - Q t j = ∑ r ∈ R, w r * (Q r j - Q t j) := by
      intro j
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    have : ∑ j, ξ j * (∑ r ∈ R, w r * Q r j - Q t j) = ∑ r ∈ R, w r * ξ ⬝ᵥ (Q r - Q t) := by
      simp only [e, Finset.mul_sum, dotProduct, Pi.sub_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact Finset.sum_nonneg fun r hr => mul_nonneg (hw0 r) (hξR r hr)
  -- but every coordinate of `c - q_t` is negative and `ξ ≥ 0`, `ξ_i > 0`
  have hneg : ∑ j, ξ j * (∑ r ∈ R, w r * Q r j - Q t j) < ∑ _j : Fin d, (0 : ℝ) :=
    Finset.sum_lt_sum
      (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hξ0 j) (by linarith [hall j]))
      ⟨i, Finset.mem_univ _, mul_neg_of_pos_of_neg hi' (by linarith [hall i])⟩
  simp only [Finset.sum_const_zero] at hneg
  linarith

/-- **Dominance.** If `y` is weakly solvable at `Q` and `q_s < q_t` coordinatewise, then
`y_t ≤ y_s`. -/
theorem le_of_dominates (h : y ∈ indicatorCone (weakReachableSpectra Q)) {s t : Fin T}
    (hst : ∀ i, Q s i < Q t i) : y t ≤ y s := by
  classical
  by_contra hlt
  push_neg at hlt
  -- the cut `w = e_s - e_t` with the single pair `(t, {s})`
  obtain ⟨c, hc, hb⟩ := exists_isBlocked_of_cut h (Pi.single s 1 - Pi.single t 1)
    (by simp [sub_mul, Pi.single_apply, hlt]) {(t, {s})} (fun S hS => by
      refine ⟨(t, {s}), Finset.mem_singleton_self _, ?_⟩
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single'] at hS
      by_cases hs : s ∈ S <;> by_cases ht : t ∈ S <;> simp [hs, ht] at hS ⊢
      all_goals norm_num at hS)
  rw [Finset.mem_singleton] at hc
  subst hc
  obtain ⟨i, hi⟩ := isBlocked_singleton_iff.1 hb
  exact absurd (hst i) (not_lt.2 hi)

/-- Blocking is invariant under rescaling the coordinates by positive factors. -/
theorem isBlocked_smul_iff {c : Fin d → ℝ} (hc : ∀ i, 0 < c i) {t : Fin T}
    {R : Finset (Fin T)} : IsBlocked (fun s i => c i * Q s i) t R ↔ IsBlocked Q t R := by
  -- one direction for every positive `c`; the other is the case `c⁻¹`
  have key : ∀ c : Fin d → ℝ, (∀ i, 0 < c i) → ∀ Q : Fin T → Fin d → ℝ,
      IsBlocked Q t R → IsBlocked (fun s i => c i * Q s i) t R := by
    rintro c hc Q ⟨ξ, hξ0, hξ, hξR⟩
    refine ⟨fun i => ξ i / c i, fun i => div_nonneg (hξ0 i) (hc i).le, fun h => hξ ?_,
      fun r hr => ?_⟩
    · funext i
      have := congr_fun h i
      simpa [(hc i).ne'] using this
    · convert hξR r hr using 1
      simp only [dotProduct, Pi.sub_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [(hc i).ne']
  refine ⟨fun h => ?_, key c hc Q⟩
  have := key (fun i => (c i)⁻¹) (fun i => inv_pos.2 (hc i)) _ h
  simpa [inv_mul_cancel_left₀ (hc _).ne'] using this

/-- **Lower bound from a relaxation.** Let `Φ` hold at every positive `Q` at which `y` is weakly
solvable, let `minPert P y ≤ D`, and let `L ≤ totalPert P Q` for every `Q` with `Φ Q` in the
box `P/(1+D) ≤ Q ≤ P(1+D)`. Then `L ≤ minPert P y`. -/
theorem le_minPert_of_relaxation (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) (hy : ∀ t, 0 ≤ y t)
    {D L : ℝ} (hD : minPert P y ≤ D) (Φ : (Fin T → Fin d → ℝ) → Prop)
    (hΦ : ∀ Q, (∀ t, Q t ∈ orthant d) → y ∈ indicatorCone (weakReachableSpectra Q) → Φ Q)
    (hL : ∀ Q, Φ Q → (∀ t i, P t i / (1 + D) ≤ Q t i ∧ Q t i ≤ P t i * (1 + D)) →
      L ≤ totalPert P Q) :
    L ≤ minPert P y := by
  obtain ⟨Q, hQ, hyQ, heq, -⟩ := exists_minPert hd hP hy
  rw [← heq]
  exact hL Q (hΦ Q hQ hyQ) (totalPert_le_box hP hQ (heq ▸ hD))

/-- **Finiteness of the cut loop (combinatorial core).** Points `x k` and cuts `c k` such that
the `k`-th cut is violated at `x k` while all earlier cuts hold there: then the cuts are
pairwise distinct, so there are at most `Fintype.card C` of them. -/
theorem card_le_of_cut_sequence {X C : Type*} [Fintype C] (sat : X → C → Prop) (n : ℕ)
    (x : Fin n → X) (c : Fin n → C) (hviol : ∀ k, ¬ sat (x k) (c k))
    (hold : ∀ j k, j < k → sat (x k) (c j)) : n ≤ Fintype.card C := by
  -- The cuts are pairwise distinct: an earlier cut holds where a later one is violated.
  have hinj : Function.Injective c := by
    intro j k hjk
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hviol k (hjk ▸ hold j k h)
    · exact hviol j (hjk ▸ hold k j h)
  simpa using Fintype.card_le_of_injective c hinj

end NeoTiling
