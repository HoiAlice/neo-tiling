import NeoTiling.Lp.Reduction

/-!
# Cover inequalities characterize weak reachability

`isWeakReachable_iff_no_cover`: for `d ≥ 1`, a set `S` of years is weakly reachable at prices `Q`
iff no year `t ∈ S` is *covered* by the years outside `S`, that is, no convex combination of the
prices `Q s`, `s ∉ S`, is strictly below `Q t` in every coordinate. This is the converse of
`meets_of_conv_lt`. `isWeakReachable_iff_no_small_cover`: by Carathéodory it suffices to exclude
covers that use at most `d + 1` years.
-/

namespace NeoTiling.Lp

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

Proof. Separate the open convex orthant `N = {x | ∀ i, x i < 0}` from the convex set
`convComb v A` (disjoint by hypothesis) by `geometric_hahn_banach_open`: `f a < u ≤ f b` for
`a ∈ N`, `b ∈ convComb v A`. Then `f ≤ u` on the closure `{x ≤ 0}`, a cone, so `u ≥ 0` and
`f ≤ 0` there; with `ξ i := f e_i` this gives `ξ ≥ 0` and `⟨ξ, v s⟩ = f (v s) ≥ u ≥ 0`. If `ξ = 0`
then `f = 0` and `0 < u ≤ 0`. -/
theorem gordan (v : Fin T → Fin d → ℝ) {A : Finset (Fin T)} (hA : A.Nonempty)
    (h : ∀ μ : Fin T → ℝ, (∀ s, 0 ≤ μ s) → (∀ s ∉ A, μ s = 0) → ∑ s, μ s = 1 →
      ¬ ∀ i, ∑ s, μ s * v s i < 0) :
    ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∈ A, 0 ≤ ξ ⬝ᵥ v s := by
  classical
  obtain ⟨f, u, hfa, hfb⟩ := geometric_hahn_banach_open (s := Set.univ.pi fun _ => Set.Iio 0)
    (convex_pi fun _ _ => convex_Iio 0) (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Iio)
    (convex_convComb v A) (Set.disjoint_left.2 fun x hx ⟨μ, h0, hA', h1, hb⟩ =>
      h μ h0 hA' h1 fun i => by simpa [hb, Finset.sum_apply] using hx i trivial)
  -- `f ≤ u` on the closure `{x ≤ 0}` of the open orthant, a cone, so `f ≤ 0` there
  have hcl : ∀ x : Fin d → ℝ, x ≤ 0 → f x ≤ u := fun x hx =>
    closure_minimal (fun a ha => (hfa a ha).le) (isClosed_le f.continuous continuous_const)
      (by rw [closure_pi_set]; exact fun i _ => by rw [closure_Iio]; exact hx i)
  have hle : ∀ x : Fin d → ℝ, x ≤ 0 → f x ≤ 0 := fun x hx => by
    by_contra! hpos
    have := hcl (((u + 1) / f x) • x) (smul_nonpos_of_nonneg_of_nonpos (by
      have := hcl 0 le_rfl; simp at this; positivity) hx)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  set ξ : Fin d → ℝ := fun i => f fun j => if i = j then 1 else 0
  have hfx (x : Fin d → ℝ) : f x = ξ ⬝ᵥ x := by
    rw [← f.coe_coe, f.toLinearMap.pi_apply_eq_sum_univ]
    simp [ξ, dotProduct, mul_comm]
  have hu : 0 ≤ u := by simpa using hcl 0 le_rfl
  have hm (s) (hs : s ∈ A) : v s ∈ convComb v A :=
    ⟨Pi.single s 1, fun r => by simp [Pi.single_apply]; split_ifs <;> norm_num,
      fun r hr => by simp [show r ≠ s by rintro rfl; exact hr hs], by simp, by simp⟩
  refine ⟨ξ, fun i => ?_, fun h0 => ?_, fun s hs => hfx (v s) ▸ hu.trans (hfb _ (hm s hs))⟩
  · have := hle (fun j => -if i = j then 1 else 0) fun j => by dsimp; split_ifs <;> norm_num
    have e : (fun j => -if i = j then (1:ℝ) else 0) = -fun j => if i = j then 1 else 0 := rfl
    rw [e, map_neg] at this
    exact neg_nonpos.1 this
  · obtain ⟨s, hs⟩ := hA
    have h1 := hfa (-1) fun i _ => by simp
    have h2 := hfb _ (hm s hs)
    rw [hfx, h0, zero_dotProduct] at h1 h2
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

Proof. `∑ μ s • Q s ∈ convexHull ℝ (Q '' A)`; by `eq_pos_convex_span_of_mem_convexHull` it is a
positive combination `∑ w i • z i` of affinely independent points `z i ∈ Q '' A`, `i : ι`, so
`card ι ≤ d + 1` (`AffineIndependent.card_le_finrank_succ`). Choose `σ i ∈ A` with
`Q (σ i) = z i` and put `μ' s := ∑ i with σ i = s, w i`; its support lies in the image of `σ`. -/
theorem exists_small_conv (Q : Fin T → Fin d → ℝ) {A : Finset (Fin T)} (μ : Fin T → ℝ)
    (hμ0 : ∀ s, 0 ≤ μ s) (hμA : ∀ s ∉ A, μ s = 0) (hμ1 : ∑ s, μ s = 1) :
    ∃ μ' : Fin T → ℝ, (∀ s, 0 ≤ μ' s) ∧ (∀ s ∉ A, μ' s = 0) ∧ ∑ s, μ' s = 1 ∧
      (Finset.univ.filter (μ' · ≠ 0)).card ≤ d + 1 ∧ ∑ s, μ' s • Q s = ∑ s, μ s • Q s := by
  classical
  have hx : ∑ s, μ s • Q s ∈ convexHull ℝ (Q '' (A : Set (Fin T))) := by
    rw [← Finset.sum_subset A.subset_univ fun s _ hs => by simp [hμA s hs]]
    exact (convex_convexHull ℝ _).sum_mem (fun s _ => hμ0 s)
      (by rwa [Finset.sum_subset A.subset_univ fun s _ hs => hμA s hs])
      fun s hs => subset_convexHull ℝ _ ⟨s, hs, rfl⟩
  obtain ⟨ι, _, z, w, hz, hai, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  choose σ hσA hσ using fun i => hz ⟨i, rfl⟩
  have hcard : Fintype.card ι ≤ d + 1 := by
    have := (Submodule.finrank_le (vectorSpan ℝ (Set.range z))).trans_eq (Module.finrank_fin_fun ℝ)
    have := hai.card_le_finrank_succ; omega
  refine ⟨fun s => ∑ i, if σ i = s then w i else 0, fun s => Finset.sum_nonneg fun i _ => by
      split_ifs <;> simp [(hw0 i).le], fun s hs => Finset.sum_eq_zero fun i _ =>
      if_neg fun (h : σ i = s) => hs (h ▸ hσA i), by rw [Finset.sum_comm]; simpa using hw1, ?_, ?_⟩
  · refine (Finset.card_le_card (t := Finset.univ.image σ) fun s hs => ?_).trans
      (Finset.card_image_le.trans hcard)
    by_contra hn
    exact (Finset.mem_filter.1 hs).2 (Finset.sum_eq_zero fun i _ =>
      if_neg fun h => hn (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩))
  · rw [← hwz]
    simp only [Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simp [hσ]

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

end NeoTiling.Lp
