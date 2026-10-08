import NeoTiling.Reachable

/-!
# The neoclassical solvability criterion

Main results:

* `IsReachable.exists_vector`: for `t ∈ S ∈ Sp(P)` a positive vector `ξ` separates `p_t` from
  the prices outside `S`: `⟨ξ, p_t⟩ < 1 < ⟨ξ, p_s⟩` for `s ∉ S`.
* `isReachable_iff_exists_witness`: reachability is equivalent to the existence of such
  witnesses in the non-strict form `⟨ξ, p_s - p_t⟩ ≥ 1`, `ξ ≥ 0`.
* `exists_polyMin_patch`: for `d ≥ 2`, all reachable spectra lie in the spectrum of one
  polyhedral function.
* `exists_spectrum_eq_reachableSpectra`: for `d ≥ 2` some neoclassical `h` has
  `Sp(h, P) = Sp(P)`.
* `neoSolvable_iff_mem_indicatorCone`: for `d ≥ 2`, outputs `y ≥ 0` are neoclassically solvable
  at positive prices `P` iff `y` lies in the cone spanned by the indicators of `Sp(P)`.
* `eventually_reachableSpectra_subset`, `NeoSolvable.eventually`: `Sp(P) ⊆ Sp(Q)` for `Q` near `P`,
  so solvability is an open condition on the prices.
* `reachableSpectra_eq_univ_of_hyperbola`, `neoSolvable_of_hyperbola`: for `d ≥ 2`, prices on a
  surface `x₀ x₁ = κ` with distinct `x₀` have `Sp(P) = 2^[T]`, so every `y ≥ 0` is solvable.
-/

open Set Filter Topology

namespace NeoTiling

variable {d T : ℕ} {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

open Pointwise in
/-- **Separation.** For `t ∈ S ∈ Sp(P)` some positive `ξ` has `⟨ξ, p_t⟩ < 1 < ⟨ξ, p_s⟩` for all
`s ∉ S`. The closed convex set `C = conv {p_s | s ∉ S} + ℝᵈ₊` misses `p_t` by reachability.
A functional `f` with `f(p_t) < u < f(C)` is nonnegative on `ℝᵈ₊`, since `C + ℝᵈ₊ ⊆ C`. Then
`ξ = (f + δ·1) / u` with small `δ > 0` works. -/
theorem IsReachable.exists_vector (hP : ∀ t, P t ∈ orthant d) {S : Finset (Fin T)}
    (hS : IsReachable P S) {t : Fin T} (ht : t ∈ S) :
    ∃ ξ ∈ orthant d, ξ ⬝ᵥ P t < 1 ∧ ∀ s ∉ S, 1 < ξ ⬝ᵥ P s := by
  set K := stdSimplex ℝ (Fin T) ∩ (S : Set (Fin T)).pi fun _ => {0}
  set L := Fintype.linearCombination ℝ P
  set C := L '' K + Ici 0
  have hPsC (s) (hs : s ∉ S) : P s ∈ C :=
    ⟨_, ⟨Pi.single s 1, ⟨single_mem_stdSimplex ℝ s, fun r hr =>
      Pi.single_eq_of_ne (ne_of_mem_of_not_mem hr hs) 1⟩, rfl⟩, 0, self_mem_Ici, by simp [L]⟩
  obtain ⟨f, u, hfu, hfC, hf0⟩ : ∃ (f : StrongDual ℝ (Fin d → ℝ)) (u : ℝ),
      f (P t) < u ∧ (∀ c ∈ C, u < f c) ∧ ∀ v, 0 ≤ v → 0 ≤ f v := by
    rcases C.eq_empty_or_nonempty with hC | ⟨-, a, ha, b, hb, rfl⟩
    · exact ⟨0, 1, by simp, by simp [hC], fun _ _ => le_rfl⟩
    obtain ⟨f, u, hfu, hfC⟩ := geometric_hahn_banach_point_closed
      ((((convex_stdSimplex ℝ _).inter (convex_pi fun _ _ => convex_singleton 0)).linear_image
        L).add (convex_Ici 0))
      (isClosed_Ici.add_left_of_isCompact (((isCompact_stdSimplex _).inter_right
        (isClosed_set_pi fun _ _ => isClosed_singleton)).image L.continuous_of_finiteDimensional))
      (by
        rintro ⟨-, ⟨w, ⟨hw, hwS⟩, rfl⟩, c, hc, hwc⟩
        refine hS t ht ⟨w, hw.1, fun r hr => hwS r (by simpa using hr), hw.2, ?_⟩
        exact (le_add_of_nonneg_right hc).trans_eq hwc)
    refine ⟨f, u, hfu, hfC, fun v hv => not_lt.1 fun hfv => ?_⟩
    have hab := hfC _ ⟨a, ha, b, hb, rfl⟩
    have := hfC _ ⟨a, ha, b + ((f (a + b) - u) / -f v) • v,
      add_nonneg hb (smul_nonneg (div_nonneg (by linarith) (by linarith)) hv), rfl⟩
    simp only [← add_assoc, map_add, map_smul, smul_eq_mul] at this hab
    rw [div_mul_eq_mul_div, div_neg, mul_div_cancel_right₀ _ hfv.ne] at this
    linarith
  have hu : 0 < u := (hf0 _ (orthant_subset_Ici (hP t))).trans_lt hfu
  obtain ⟨δ, hδ, hδt⟩ := exists_pos_mul_lt (sub_pos.2 hfu) (∑ i, P t i)
  set ξ : Fin d → ℝ := fun i => (f (fun j => if i = j then 1 else 0) + δ) / u
  have key (p : Fin d → ℝ) : ξ ⬝ᵥ p = (f p + δ * ∑ i, p i) / u := by
    rw [← f.coe_coe, f.toLinearMap.pi_apply_eq_sum_univ]
    simp [ξ, dotProduct, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  refine ⟨ξ, fun i => div_pos (add_pos_of_nonneg_of_pos (hf0 _ fun j => ?_) hδ) hu, ?_,
    fun s hs => ?_⟩
  · dsimp; split_ifs <;> norm_num
  · rw [key, div_lt_one hu]; linarith
  · rw [key, one_lt_div hu]
    nlinarith [hfC _ (hPsC s hs), Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (hP s i).le]

/-- **Reachability by witnesses.** `S` is reachable iff every `t ∈ S` has a nonnegative vector
`ξ` with `⟨ξ, p_s - p_t⟩ ≥ 1` for all `s ∉ S`: `→` rescales `IsReachable.exists_vector`, `←`
pairs `ξ` with a covering. -/
theorem isReachable_iff_exists_witness (hP : ∀ t, P t ∈ orthant d) {S : Finset (Fin T)} :
    IsReachable P S ↔ ∀ t ∈ S, ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ∀ s ∉ S, 1 ≤ ξ ⬝ᵥ (P s - P t) := by
  constructor
  · intro hS t ht
    obtain ⟨ξ, hξ, hξt, hξs⟩ := hS.exists_vector hP ht
    have hc : 0 < 1 - ξ ⬝ᵥ P t := by linarith
    refine ⟨(1 - ξ ⬝ᵥ P t)⁻¹ • ξ, smul_nonneg (inv_nonneg.2 hc.le) fun i => (hξ i).le,
      fun s hs => ?_⟩
    rw [smul_dotProduct, smul_eq_mul, dotProduct_sub, ← div_eq_inv_mul, le_div_iff₀ hc]
    linarith [hξs s hs]
  · rintro h t ht ⟨w, hw0, hwS, hw1, hwP⟩
    obtain ⟨ξ, hξ, hξs⟩ := h t ht
    have h1 := dotProduct_le_dotProduct_of_nonneg_left hwP hξ
    have h2 : ξ ⬝ᵥ ∑ r, w r • P r = ∑ r, w r * (ξ ⬝ᵥ P r) := by
      simp [dotProduct_sum, dotProduct_smul]
    have h3 : ∑ r, w r * (ξ ⬝ᵥ P t + 1) ≤ ∑ r, w r * (ξ ⬝ᵥ P r) := by
      refine Finset.sum_le_sum fun r _ => ?_
      by_cases hr : r ∈ S
      · simp [hwS r (by simpa using hr)]
      · have := hξs r hr
        rw [dotProduct_sub] at this
        exact mul_le_mul_of_nonneg_left (by linarith) (hw0 r)
    rw [← Finset.sum_mul, hw1] at h3
    linarith

/-- **Patching, `d ≥ 2`.** Take the vectors `η_{S,t}` of `IsReachable.exists_vector` for
`t ∈ S ∈ Sp(P)` and the extra vector `1`. Give `S` an exponent `E_S ≥ 1` and the extra vector
the exponent `0`, and let `x_z = (M^z, M^{-z}, 1, …, 1)`. The vectors `η_{S,t} / x_{E_S}` and
`1` define `h = polyMin`. At `x_{E_S}` the own vectors give `⟨η_{S,t}, p⟩`, the others give
`⟨η, p * x_z⟩` with `z ≠ 0`, which is `> 1` for large `M`. -/
theorem exists_polyMin_patch (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) :
    ∃ h, IsNeoclassical h ∧ reachableSpectra P ⊆ spectrum h P := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hd
  -- vectors `η_{S,t}` for `t ∈ S ∈ Sp(P)`, and the extra vector `1`
  set J := {p : Finset (Fin T) × Fin T // IsReachable P p.1 ∧ p.2 ∈ p.1}
  choose η₀ hη₀ hηt hηs using fun j : J => j.2.1.exists_vector hP j.2.2
  set η : Option J → Fin (n + 2) → ℝ := fun o => o.elim 1 η₀
  have hη (o : Option J) : η o ∈ orthant (n + 2) := by
    cases o
    exacts [fun _ => one_pos, hη₀ _]
  -- distinct exponents: `E S ≥ 1` for the point of `S`, `0` for the extra vector
  set E : Finset (Fin T) → ℤ := fun S => (Fintype.equivFin _ S : ℤ) + 1
  set e : Option J → ℤ := fun o => o.elim 0 fun j => E j.1.1
  obtain ⟨M, hM, hM1⟩ := ((eventually_all.2 fun o => eventually_all.2 fun s =>
    (tendsto_id.atTop_mul_const (lt_min (mul_pos (hη o 0) (hP s 0))
      (mul_pos (hη o 1) (hP s 1)))).eventually_gt_atTop 1).and (eventually_ge_atTop 1)).exists
  have hM0 : (0 : ℝ) < M := one_pos.trans_le hM1
  set x : ℤ → Fin (n + 2) → ℝ := fun z j =>
    M ^ (z * if j = 0 then 1 else if j = 1 then -1 else 0)
  have hx (z : ℤ) : x z ∈ orthant (n + 2) := fun j => zpow_pos hM0 _
  have hdot (a b : ℤ) (q p : Fin (n + 2) → ℝ) :
      (q * x (-a)) ⬝ᵥ (p * x b) = q ⬝ᵥ (p * x (b - a)) := by
    simp only [dotProduct, Pi.mul_apply, x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_eq_neg_add, add_mul, zpow_add₀ hM0.ne']; ring
  -- other exponents give values above `1`
  have hfar (o : Option J) (s : Fin T) {z : ℤ} (hz : z ≠ 0) : 1 < η o ⬝ᵥ (P s * x z) := by
    have h0 := Finset.single_le_sum (fun j _ => (mul_pos (hη o j) (mul_pos (hP s j) (hx z j))).le)
      (Finset.mem_univ (0 : Fin (n + 2)))
    have h1 := Finset.single_le_sum (fun j _ => (mul_pos (hη o j) (mul_pos (hP s j) (hx z j))).le)
      (Finset.mem_univ (1 : Fin (n + 2)))
    simp only [dotProduct, Pi.mul_apply] at h0 h1 ⊢
    have : 1 < M * _ := hM o s
    rcases hz.lt_or_gt with hz | hz
    · have : M ≤ x z 1 := by simpa [x] using zpow_le_zpow_right₀ hM1 (by omega : (1 : ℤ) ≤ -z)
      nlinarith [mul_le_mul_of_nonneg_left (min_le_right (η o 0 * P s 0) (η o 1 * P s 1)) hM0.le,
        mul_le_mul_of_nonneg_left this (mul_pos (hη o 1) (hP s 1)).le]
    · have : M ≤ x z 0 := by simpa [x] using zpow_le_zpow_right₀ hM1 (by omega : (1 : ℤ) ≤ z)
      nlinarith [mul_le_mul_of_nonneg_left (min_le_left (η o 0 * P s 0) (η o 1 * P s 1)) hM0.le,
        mul_le_mul_of_nonneg_left this (mul_pos (hη o 0) (hP s 0)).le]
  have hx0 : x 0 = 1 := by ext; simp [x]
  set ξ := fun o => η o * x (-e o)
  have hh := isNeoclassical_polyMin (ξ := ξ) fun o =>
    orthant_subset_Ici fun j => mul_pos (hη o j) (hx _ j)
  refine ⟨_, hh, fun S hS => ⟨x (E S), hx (E S), fun t ht => ?_, fun s hs => ?_⟩⟩
  · refine (polyMin_le ξ _ (some ⟨(S, t), hS, ht⟩)).trans_lt ?_
    rw [hdot]
    change η₀ _ ⬝ᵥ (P t * x (E S - E S)) < 1
    rw [sub_self, hx0, mul_one]
    exact hηt _
  · obtain ⟨o, ho⟩ := exists_dot_eq_polyMin ξ (P s * x (E S))
    rw [← ho, hdot]
    rcases eq_or_ne (E S) (e o) with h | h
    · rcases o with _ | j
      · simp [E, e] at h; omega
      obtain rfl : S = j.1.1 := by simpa [E, e, Fin.val_inj] using h
      rw [h, sub_self, hx0, mul_one]
      exact hηs j s hs
    · exact hfar o s (sub_ne_zero.2 h)

/-- **Spectra of neoclassical functions.** For `d ≥ 2` some neoclassical `h` has
`Sp(h, P) = Sp(P)`: patch all reachable spectra (`exists_polyMin_patch`); the other inclusion is
`IsNeoclassical.spectrum_subset_reachableSpectra`. -/
theorem exists_spectrum_eq_reachableSpectra (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) :
    ∃ h, IsNeoclassical h ∧ spectrum h P = reachableSpectra P :=
  let ⟨h, hh, hsub⟩ := exists_polyMin_patch hd hP
  ⟨h, hh, (hh.spectrum_subset_reachableSpectra hP).antisymm hsub⟩

/-- **Neoclassical solvability criterion.** For `d ≥ 2`, positive prices `P` and outputs
`y ≥ 0`, `y` is neoclassically solvable at `P` iff `y` lies in the cone spanned by the
indicators of the reachable spectra.

`→`: realization at `P` puts `y` into the cone of `Sp(h, P) ⊆ Sp(P)`. `←`: take `h` with
`Sp(h, P) = Sp(P)` (`exists_spectrum_eq_reachableSpectra`); near `P` the spectrum of `h` only
grows (`IsNeoclassical.eventually_spectrum_subset`), so `h` realizes `y` there. -/
theorem neoSolvable_iff_mem_indicatorCone (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (hy : ∀ t, 0 ≤ y t) :
    NeoSolvable P y ↔ y ∈ indicatorCone (reachableSpectra P) := by
  constructor
  · rintro ⟨h, hh, hev⟩
    exact Submodule.span_mono (image_mono (hh.spectrum_subset_reachableSpectra hP))
      ((hh.realizes_iff_mem_indicatorCone hP hy).1 hev.self_of_nhds)
  · intro hY
    obtain ⟨h, hh, hspec⟩ := exists_spectrum_eq_reachableSpectra hd hP
    refine ⟨h, hh, ?_⟩
    filter_upwards [hh.eventually_spectrum_subset hP, eventually_all.2 fun t =>
      ((continuous_apply t).tendsto P).eventually (isOpen_orthant.mem_nhds (hP t))] with Q hQ hQo
    exact (hh.realizes_iff_mem_indicatorCone hQo hy).2
      (Submodule.span_mono (image_mono (hspec ▸ hQ)) hY)

/-- **Reachable spectra do not shrink near `P`.** Take `h` with `Sp(h, P) = Sp(P)`; near `P`,
`Sp(P) = Sp(h, P) ⊆ Sp(h, Q) ⊆ Sp(Q)`. -/
theorem eventually_reachableSpectra_subset (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) :
    ∀ᶠ Q in 𝓝 P, reachableSpectra P ⊆ reachableSpectra Q := by
  obtain ⟨h, hh, hspec⟩ := exists_spectrum_eq_reachableSpectra hd hP
  filter_upwards [hh.eventually_spectrum_subset hP, eventually_all.2 fun t =>
    ((continuous_apply t).tendsto P).eventually (isOpen_orthant.mem_nhds (hP t))] with Q hQ hQo
  exact hspec ▸ hQ.trans (hh.spectrum_subset_reachableSpectra hQo)

/-- **Solvability is an open condition on the prices**: `y` solvable at `P` is solvable at all
`Q` near `P` (`eventually_reachableSpectra_subset`). Hence the infimum of a distance from `P` to
the solvable prices is not attained in general. -/
theorem NeoSolvable.eventually (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) (hy : ∀ t, 0 ≤ y t)
    (h : NeoSolvable P y) : ∀ᶠ Q in 𝓝 P, NeoSolvable Q y := by
  rw [neoSolvable_iff_mem_indicatorCone hd hP hy] at h
  filter_upwards [eventually_reachableSpectra_subset hd hP, eventually_all.2 fun t =>
    ((continuous_apply t).tendsto P).eventually (isOpen_orthant.mem_nhds (hP t))] with Q hQ hQo
  exact (neoSolvable_iff_mem_indicatorCone hd hQo hy).2 (Submodule.span_mono (image_mono hQ) h)

/-- **Full spectrum.** If all prices lie on the surface `x₀ x₁ = κ` with pairwise distinct `x₀`,
every `S` is reachable (`isReachable_iff_exists_witness` with `ξ ∝ (x₀⁻¹, x₁⁻¹, 0, …)` at `p_t`).
With `a = (p_s)₀`, `b = (p_t)₀` one gets `⟨ξ, p_s - p_t⟩ = c (a - b)² / (a b)`, which is `≥ 1`
for `s ≠ t` once `c ≥ ∑_s a b / (a - b)²`. -/
theorem reachableSpectra_eq_univ_of_hyperbola (hd : 2 ≤ d) (hQ : ∀ t, P t ∈ orthant d) {κ : ℝ}
    (hκ : ∀ t, P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩ = κ)
    (hinj : Function.Injective fun t => P t ⟨0, by omega⟩) : reachableSpectra P = Set.univ := by
  refine Set.eq_univ_of_forall fun S => (isReachable_iff_exists_witness hQ).2 fun t ht => ?_
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h10 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  set c := ∑ s, P s i0 * P t i0 / (P s i0 - P t i0) ^ 2
  have hc : ∀ s, P s i0 * P t i0 / (P s i0 - P t i0) ^ 2 ≤ c := fun s =>
    Finset.single_le_sum (f := fun s => P s i0 * P t i0 / (P s i0 - P t i0) ^ 2)
      (fun s _ => by have := hQ s i0; have := hQ t i0; positivity) (Finset.mem_univ s)
  refine ⟨fun i => c * (if i = i0 then (P t i0)⁻¹ else if i = i1 then (P t i1)⁻¹ else 0),
    fun i => ?_, fun s hs => ?_⟩
  · have := hQ t i0; have := hQ t i1; have : 0 ≤ c := le_trans (by positivity) (hc t)
    simp only [Pi.zero_apply]; split_ifs <;> positivity
  · have hst : P s i0 ≠ P t i0 := fun h => hs (hinj h ▸ ht)
    have ha := hQ s i0; have hb := hQ t i0; have hv := hQ t i1
    have hne : (P s i0 - P t i0) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hst)
    have hu : P s i1 = P t i0 * P t i1 / P s i0 := by
      rw [eq_div_iff ha.ne', mul_comm, hκ, hκ]
    rw [dotProduct, Finset.sum_eq_add i0 i1 h10.symm (fun j _ hj => by simp [hj.1, hj.2])
      (by simp) (by simp)]
    simp only [Pi.sub_apply, if_true, if_neg h10, hu]
    have key := hc s
    rw [div_le_iff₀ (by positivity)] at key
    have : c * (P t i0)⁻¹ * (P s i0 - P t i0)
        + c * (P t i1)⁻¹ * (P t i0 * P t i1 / P s i0 - P t i1)
        = c * (P s i0 - P t i0) ^ 2 / (P s i0 * P t i0) := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]; linarith

/-- **Full spectrum, solvability.** Under the hypotheses of
`reachableSpectra_eq_univ_of_hyperbola` every `y ≥ 0` is solvable: all sets are reachable, so
`y = ∑_t y_t 1_{t}` lies in the indicator cone. -/
theorem neoSolvable_of_hyperbola (hd : 2 ≤ d) (hQ : ∀ t, P t ∈ orthant d) {κ : ℝ}
    (hκ : ∀ t, P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩ = κ)
    (hinj : Function.Injective fun t => P t ⟨0, by omega⟩) (hy : ∀ t, 0 ≤ y t) :
    NeoSolvable P y := by
  rw [neoSolvable_iff_mem_indicatorCone hd hQ hy,
    reachableSpectra_eq_univ_of_hyperbola hd hQ hκ hinj]
  have : y = ∑ t, y t • ((({t} : Finset (Fin T)) : Set (Fin T)).indicator 1) := by
    ext r; simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun t _ =>
    PointedCone.smul_mem _ (hy t) (PointedCone.subset_span ⟨{t}, trivial, rfl⟩)

end NeoTiling
