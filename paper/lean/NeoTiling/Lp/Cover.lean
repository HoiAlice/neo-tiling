import NeoTiling.Lp.Reduction

/-!
# Cover inequalities characterize weak reachability

`isWeakReachable_iff_no_cover`: for `d ≥ 1`, a set `S` of years is weakly reachable at prices `Q`
iff no year `t ∈ S` is *covered* by the years outside `S`, that is, no convex combination of the
prices `Q s`, `s ∉ S`, is strictly below `Q t` in every coordinate. This is the converse of
`meets_of_conv_lt`. `isWeakReachable_iff_no_small_cover`: by Carathéodory it suffices to exclude
covers that use at most `d + 1` years.
-/

namespace NeoTiling.L1Perturbation

open NeoTiling

variable {d T : ℕ}

/-- The convex combinations of the vectors `v s`, `s ∈ A`. -/
def convComb (v : Fin T → Fin d → ℝ) (A : Finset (Fin T)) : Set (Fin d → ℝ) :=
  {b | ∃ μ : Fin T → ℝ, (∀ s, 0 ≤ μ s) ∧ (∀ s ∉ A, μ s = 0) ∧ ∑ s, μ s = 1 ∧
    b = ∑ s, μ s • v s}

theorem convex_convComb (v : Fin T → Fin d → ℝ) (A : Finset (Fin T)) :
    Convex ℝ (convComb v A) := by
  rintro _ ⟨μ, h0, hA, h1, rfl⟩ _ ⟨ν, k0, kA, k1, rfl⟩ a b ha hb hab
  refine ⟨fun s => a * μ s + b * ν s, fun s => add_nonneg (mul_nonneg ha (h0 s))
    (mul_nonneg hb (k0 s)), fun s hs => by simp [hA s hs, kA s hs], ?_, ?_⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h1, k1]; linarith
  · simp [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]

/-- **Gordan's alternative.** If no convex combination of the vectors `v s`, `s ∈ A`, is strictly
negative in every coordinate, then some nonzero `ξ ≥ 0` has `⟨ξ, v s⟩ ≥ 0` for all `s ∈ A`.

Proof. Separate the open convex cone `N = {x | ∀ i, x i < 0}` from the convex set `convComb v A`
(disjoint by hypothesis, nonempty since `A ≠ ∅`) by `geometric_hahn_banach_open`: `f a < u ≤ f b`
for `a ∈ N`, `b ∈ convComb v A`. Put `ξ i := f (Pi.single i 1)`, so `f x = ξ ⬝ᵥ x`. Testing
`a = -λ e_i - ε 1` with `λ → ∞` gives `ξ i ≥ 0`; testing `a = -ε 1` with `ε → 0` gives `u ≥ 0`,
hence `⟨ξ, v s⟩ = f (v s) ≥ u ≥ 0`. If `ξ = 0` then `f = 0` and `0 < u ≤ 0`. -/
theorem gordan (v : Fin T → Fin d → ℝ) {A : Finset (Fin T)} (hA : A.Nonempty)
    (h : ∀ μ : Fin T → ℝ, (∀ s, 0 ≤ μ s) → (∀ s ∉ A, μ s = 0) → ∑ s, μ s = 1 →
      ¬ ∀ i, ∑ s, μ s * v s i < 0) :
    ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∈ A, 0 ≤ ξ ⬝ᵥ v s := by
  classical
  set N : Set (Fin d → ℝ) := {x | ∀ i, x i < 0} with hN
  have hNo : IsOpen N := by
    have : N = ⋂ i, {x : Fin d → ℝ | x i < 0} := by ext x; simp [hN]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  have hNc : Convex ℝ N := by
    intro x hx y hy a b ha hb hab i
    have h1 := hx i
    have h2 := hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · have : 0 < b := by linarith
      nlinarith
    · nlinarith
  have hdis : Disjoint N (convComb v A) := by
    rw [Set.disjoint_left]
    intro x hx ⟨μ, h0, hA', h1, hb⟩
    apply h μ h0 hA' h1
    intro i
    have := hx i
    rw [hb] at this
    simpa [Finset.sum_apply] using this
  obtain ⟨f, u, hfa, hfb⟩ := geometric_hahn_banach_open hNc hNo (convex_convComb v A) hdis
  have hfx : ∀ x, f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, dotProduct, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : (fun k => if j = k then (1:ℝ) else 0) = Pi.single j 1 := by
      ext k; simp [Pi.single_apply, eq_comm]
    rw [e1, mul_comm]
  set ξ : Fin d → ℝ := fun i => f (Pi.single i 1) with hξ
  set c : ℝ := f (fun _ => 1) with hc
  have hcξ : c = ∑ j, ξ j := by rw [hc, hfx]; simp [dotProduct]
  have hξ0 : 0 ≤ ξ := by
    intro i
    show (0:ℝ) ≤ ξ i
    by_contra hneg
    push_neg at hneg
    set l : ℝ := (|u + c| + 1) / (-ξ i) with hl
    have hlpos : 0 < l := div_pos (by positivity) (by linarith)
    have ha : ((-l) • (Pi.single i 1 : Fin d → ℝ) + (-1 : ℝ) • ((fun _ => 1) : Fin d → ℝ)) ∈ N := by
      intro j; by_cases hj : j = i <;> simp [hj]
      linarith
    have := hfa _ ha
    rw [map_add, map_smul, map_smul] at this
    have e : l * (-ξ i) = |u + c| + 1 := by
      have : -ξ i ≠ 0 := by linarith
      rw [hl, div_mul_cancel₀ _ this]
    have := le_abs_self (u + c)
    simp only [smul_eq_mul, ← hξ, ← hc] at *
    nlinarith
  have hc0 : 0 ≤ c := by rw [hcξ]; exact Finset.sum_nonneg fun j _ => hξ0 j
  have hu0 : 0 ≤ u := by
    by_contra hneg
    push_neg at hneg
    set e : ℝ := -u / (2 * (c + 1)) with he
    have hepos : 0 < e := div_pos (by linarith) (by linarith)
    have ha : (e • ((fun _ => -1) : Fin d → ℝ)) ∈ N := by
      intro j; simp [hepos]
    have h1 := hfa _ ha
    have h2 : ((fun _ => -1) : Fin d → ℝ) = (-1 : ℝ) • ((fun _ => 1) : Fin d → ℝ) := by ext; simp
    rw [h2, smul_smul, map_smul] at h1
    have h3 : e * (c + 1) = -u / 2 := by rw [he]; field_simp
    simp only [smul_eq_mul, ← hc] at h1
    nlinarith
  have hm : ∀ s ∈ A, v s ∈ convComb v A := by
    intro s hs
    refine ⟨fun r => if r = s then 1 else 0, fun r => by dsimp only; split_ifs <;> norm_num,
      fun r hr => ?_, by simp, by simp⟩
    have : r ≠ s := fun e => hr (e ▸ hs)
    simp [this]
  have hvs : ∀ s ∈ A, 0 ≤ ξ ⬝ᵥ v s := by
    intro s hs
    have := hfb _ (hm s hs)
    rw [hfx] at this
    linarith
  refine ⟨ξ, hξ0, ?_, hvs⟩
  intro hz
  obtain ⟨s, hs⟩ := hA
  have ha : ((fun _ => -1) : Fin d → ℝ) ∈ N := fun j => by simp
  have h1 := hfa _ ha
  have h2 := hfb _ (hm s hs)
  rw [hfx, hz] at h1 h2
  simp at h1 h2
  linarith

/-- **No cover.** For `d ≥ 1`, `S` is weakly reachable at `Q` iff no `t ∈ S` is covered by the
years outside `S`: no convex combination of `Q s`, `s ∉ S`, is strictly below `Q t`.

Proof. (→) is `meets_of_conv_lt` with `A := Sᶜ`. (←) Fix `t ∈ S`. If `S` is everything, any
nonzero `ξ ≥ 0` (here `e_0`) is a witness. Otherwise apply `gordan` to `v s := Q s - Q t` on
`A := Sᶜ`: since `∑ μ = 1`, `∑ μ s (Q s i - Q t i) < 0` is the cover inequality. -/
theorem isWeakReachable_iff_no_cover (hd : 0 < d) {Q : Fin T → Fin d → ℝ}
    {S : Finset (Fin T)} :
    IsWeakReachable Q S ↔ ∀ t ∈ S, ∀ μ : Fin T → ℝ, (∀ s, 0 ≤ μ s) → (∀ s ∈ S, μ s = 0) →
      ∑ s, μ s = 1 → ¬ ∀ i, ∑ s, μ s * Q s i < Q t i := by
  classical
  constructor
  · intro hS t ht μ h0 hS0 h1 hlt
    obtain ⟨s, hs, hsS⟩ := meets_of_conv_lt (A := Sᶜ) μ h0
      (fun s hs => hS0 s (by simpa using hs)) h1 hlt hS ht
    simp at hs; contradiction
  · intro h t ht
    by_cases hne' : (Sᶜ).Nonempty
    · obtain ⟨ξ, h0, hne, hξ⟩ := gordan (fun s => Q s - Q t) hne'
        (fun μ h0 hA h1 hneg => h t ht μ h0 (fun s hs => hA s (by simpa using hs)) h1
          (fun i => by
            have := hneg i
            simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1] at this
            linarith))
      exact ⟨ξ, h0, hne, fun s hs => by simpa using hξ s (by simpa using hs)⟩
    · refine ⟨Pi.single ⟨0, hd⟩ 1, fun i => ?_, fun h0 => ?_, fun s hs => ?_⟩
      · by_cases hi : i = ⟨0, hd⟩
        · subst hi; simp
        · simp [Pi.single_eq_of_ne hi]
      · simpa using congrFun h0 ⟨0, hd⟩
      · exact absurd ⟨s, by simpa using hs⟩ hne'

/-- **Carathéodory.** A convex combination of `Q s`, `s ∈ A`, is also a convex combination of at
most `d + 1` of them.

Proof. `∑ μ s • Q s ∈ convexHull ℝ (Q '' A)`; by `convexHull_eq_union` it lies in the hull of an
affinely independent finite `F ⊆ Q '' A`, so `F.card ≤ d + 1`
(`AffineIndependent.card_le_finrank_succ`, `Module.finrank_fin_fun`). Write the point with weights
`w` on `F` (`Finset.mem_convexHull`), choose `σ p ∈ A` with `Q (σ p) = p`, and put
`μ' s := ∑ p ∈ F with σ p = s, w p`; its support lies in `F.image σ`. -/
theorem exists_small_conv (Q : Fin T → Fin d → ℝ) {A : Finset (Fin T)} (μ : Fin T → ℝ)
    (hμ0 : ∀ s, 0 ≤ μ s) (hμA : ∀ s ∉ A, μ s = 0) (hμ1 : ∑ s, μ s = 1) :
    ∃ μ' : Fin T → ℝ, (∀ s, 0 ≤ μ' s) ∧ (∀ s ∉ A, μ' s = 0) ∧ ∑ s, μ' s = 1 ∧
      (Finset.univ.filter (μ' · ≠ 0)).card ≤ d + 1 ∧ ∑ s, μ' s • Q s = ∑ s, μ s • Q s := by
  classical
  have hx : ∑ s, μ s • Q s ∈ convexHull ℝ (Q '' (A : Set (Fin T))) := by
    have hsub : ∑ s ∈ A, μ s • Q s = ∑ s, μ s • Q s :=
      Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => by simp [hμA s hs])
    rw [← hsub]
    refine (convex_convexHull ℝ _).sum_mem (fun s _ => hμ0 s) ?_ (fun s hs => ?_)
    · rw [Finset.sum_subset (Finset.subset_univ A) (fun s _ hs => hμA s hs)]; exact hμ1
    · exact subset_convexHull ℝ _ ⟨s, hs, rfl⟩
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨F, hFs, hai, hxF⟩ := hx
  have hcard : F.card ≤ d + 1 := by
    have := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : F → Fin d → ℝ)))
    simp only [Module.finrank_fin_fun] at h2
    simp only [Fintype.card_coe] at this
    omega
  obtain ⟨w, hw0, hw1, hwc⟩ := Finset.mem_convexHull.mp hxF
  obtain ⟨q, hq⟩ : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hw1
  obtain ⟨s0, -, -⟩ := hFs hq
  have hex : ∀ p : Fin d → ℝ, ∃ s : Fin T, p ∈ F → s ∈ A ∧ Q s = p := by
    intro p
    by_cases hp : p ∈ F
    · obtain ⟨s, hs, hsp⟩ := hFs hp
      exact ⟨s, fun _ => ⟨hs, hsp⟩⟩
    · exact ⟨s0, fun h => absurd h hp⟩
  choose σ hσ using hex
  refine ⟨fun s => ∑ p ∈ F, if σ p = s then w p else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact Finset.sum_nonneg (fun p hp => by split_ifs <;> simp [hw0 p hp])
  · intro s hs
    refine Finset.sum_eq_zero (fun p hp => ?_)
    have := (hσ p hp).1
    rw [if_neg (fun h : σ p = s => hs (h ▸ this))]
  · simp only
    rw [Finset.sum_comm]
    simpa using hw1
  · refine le_trans (Finset.card_le_card (t := F.image σ) ?_) ((Finset.card_image_le).trans hcard)
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    by_contra hn
    apply hs
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [if_neg (fun h => hn (Finset.mem_image.mpr ⟨p, hp, h⟩))]
  · rw [← hwc, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    simp only [id, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp [(hσ p hp).2]

/-- **No small cover.** In `isWeakReachable_iff_no_cover` it suffices to exclude covers by at
most `d + 1` years.

Proof. (→) from `isWeakReachable_iff_no_cover`. (←) a cover `μ` gives by `exists_small_conv`
(with `A := Sᶜ`) a cover `μ'` with the same point `∑ μ' s • Q s` and at most `d + 1` years. -/
theorem isWeakReachable_iff_no_small_cover (hd : 0 < d) {Q : Fin T → Fin d → ℝ}
    {S : Finset (Fin T)} :
    IsWeakReachable Q S ↔ ∀ t ∈ S, ∀ μ : Fin T → ℝ, (∀ s, 0 ≤ μ s) → (∀ s ∈ S, μ s = 0) →
      ∑ s, μ s = 1 → (Finset.univ.filter (μ · ≠ 0)).card ≤ d + 1 →
      ¬ ∀ i, ∑ s, μ s * Q s i < Q t i := by
  constructor
  · intro hS t ht μ h0 hS0 h1 _
    exact (isWeakReachable_iff_no_cover hd).1 hS t ht μ h0 hS0 h1
  · intro h
    rw [isWeakReachable_iff_no_cover hd]
    intro t ht μ h0 hS0 h1 hlt
    obtain ⟨μ', h0', hA', h1', hcard, heq⟩ := exists_small_conv Q (A := Sᶜ) μ h0
      (fun s hs => hS0 s (by simpa using hs)) h1
    refine h t ht μ' h0' (fun s hs => hA' s (by simpa using hs)) h1' hcard (fun i => ?_)
    have := congrFun heq i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]; exact hlt i

end NeoTiling.L1Perturbation
