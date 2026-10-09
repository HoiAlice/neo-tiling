import NeoTiling.Reachable

/-!
# The neoclassical solvability criterion

Main results:

* `IsReachable.exists_vector`: for `t ∈ S ∈ Sp(P)` a positive vector `ξ` separates `p_t` from
  the prices outside `S`: `⟨ξ, p_t⟩ < 1 < ⟨ξ, p_s⟩` for `s ∉ S` (perturb and rescale the
  witness).
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

/-- **Separation.** For `t ∈ S ∈ Sp(P)` some positive `ξ` has `⟨ξ, p_t⟩ < 1 < ⟨ξ, p_s⟩` for all
`s ∉ S`. Adding `δ 1` with small `δ > 0` makes the witness `ξ₀` positive and keeps
`⟨ξ₁, p_s - p_t⟩ > 0` for the finitely many `s ∉ S`; then divide `ξ₁` by a number between
`⟨ξ₁, p_t⟩` and `min_{s ∉ S} ⟨ξ₁, p_s⟩`. -/
theorem IsReachable.exists_vector (hP : ∀ t, P t ∈ orthant d) {S : Finset (Fin T)}
    (hS : IsReachable P S) {t : Fin T} (ht : t ∈ S) :
    ∃ ξ ∈ orthant d, ξ ⬝ᵥ P t < 1 ∧ ∀ s ∉ S, 1 < ξ ⬝ᵥ P s := by
  obtain ⟨ξ₀, hξ₀, hne, hξs⟩ := hS t ht
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hne
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ ∀ s ∈ Sᶜ, 0 < (ξ₀ + δ • 1) ⬝ᵥ (P s - P t) :=
    eventually_mem_nhdsWithin.and <| nhdsWithin_le_nhds <| (eventually_all_finset Sᶜ).2 fun s hs =>
      (by fun_prop : Continuous fun δ : ℝ => (ξ₀ + δ • 1) ⬝ᵥ (P s - P t)).continuousAt.eventually
        (lt_mem_nhds (by simpa using hξs s (by simpa using hs)))
  obtain ⟨δ, hδ, hδs⟩ := hev.exists
  set ξ₁ := ξ₀ + δ • (1 : Fin d → ℝ)
  have hξ₁ : ξ₁ ∈ orthant d := fun i => by
    have := hξ₀ i; simp only [ξ₁, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
      mul_one, Pi.zero_apply] at this ⊢; linarith
  have ha : 0 < ξ₁ ⬝ᵥ P t :=
    Finset.sum_pos (fun i _ => mul_pos (hξ₁ i) (hP t i)) ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨c, hac, hcs⟩ : ∃ c, ξ₁ ⬝ᵥ P t < c ∧ ∀ s ∉ S, c < ξ₁ ⬝ᵥ P s := by
    rcases (Sᶜ).eq_empty_or_nonempty with h | hne
    · refine ⟨ξ₁ ⬝ᵥ P t + 1, by linarith, fun s hs => ?_⟩
      have : s ∈ Sᶜ := Finset.mem_compl.2 hs
      simp [h] at this
    · obtain ⟨s₁, hs₁, hmin⟩ := Finset.exists_min_image Sᶜ (fun s => ξ₁ ⬝ᵥ P s) hne
      have := hδs s₁ hs₁
      rw [dotProduct_sub] at this
      exact ⟨(ξ₁ ⬝ᵥ P t + ξ₁ ⬝ᵥ P s₁) / 2, by linarith,
        fun s hs => by linarith [hmin s (Finset.mem_compl.2 hs)]⟩
  have hc : 0 < c := ha.trans hac
  refine ⟨c⁻¹ • ξ₁, fun i => by simpa using mul_pos (inv_pos.2 hc) (hξ₁ i), ?_, fun s hs => ?_⟩
  · rw [smul_dotProduct, smul_eq_mul, inv_mul_lt_one₀ hc]; exact hac
  · rw [smul_dotProduct, smul_eq_mul, one_lt_inv_mul₀ hc]; exact hcs s hs

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
  ⟨h, hh, (hh.spectrum_subset_reachableSpectra (by omega) hP).antisymm hsub⟩

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
    exact Submodule.span_mono (image_mono (hh.spectrum_subset_reachableSpectra (by omega) hP))
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
  exact hspec ▸ hQ.trans (hh.spectrum_subset_reachableSpectra (by omega) hQo)

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
every `S` is reachable with the witness `ξ = (x₀⁻¹, x₁⁻¹, 0, …)` at `p_t`. With `a = (p_s)₀`,
`b = (p_t)₀` one gets `⟨ξ, p_s - p_t⟩ = (a - b)² / (a b) > 0` for `s ≠ t`. -/
theorem reachableSpectra_eq_univ_of_hyperbola (hd : 2 ≤ d) (hQ : ∀ t, P t ∈ orthant d) {κ : ℝ}
    (hκ : ∀ t, P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩ = κ)
    (hinj : Function.Injective fun t => P t ⟨0, by omega⟩) : reachableSpectra P = Set.univ := by
  refine Set.eq_univ_of_forall fun S => show IsReachable P S from fun t ht => ?_
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h10 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨fun i => if i = i0 then (P t i0)⁻¹ else if i = i1 then (P t i1)⁻¹ else 0,
    fun i => ?_, fun h0 => ?_, fun s hs => ?_⟩
  · have := hQ t i0; have := hQ t i1
    simp only [Pi.zero_apply]; split_ifs <;> positivity
  · have := congrFun h0 i0
    simp only [if_true, Pi.zero_apply, inv_eq_zero] at this
    exact (hQ t i0).ne' this
  · have hst : P s i0 ≠ P t i0 := fun h => hs (hinj h ▸ ht)
    have ha := hQ s i0; have hb := hQ t i0; have hv := hQ t i1
    have hne : P s i0 - P t i0 ≠ 0 := sub_ne_zero.2 hst
    have hu : P s i1 = P t i0 * P t i1 / P s i0 := by
      rw [eq_div_iff ha.ne', mul_comm, hκ, hκ]
    rw [dotProduct, Finset.sum_eq_add i0 i1 h10.symm (fun j _ hj => by simp [hj.1, hj.2])
      (by simp) (by simp)]
    simp only [Pi.sub_apply, if_true, if_neg h10, hu]
    have : (P t i0)⁻¹ * (P s i0 - P t i0) + (P t i1)⁻¹ * (P t i0 * P t i1 / P s i0 - P t i1)
        = (P s i0 - P t i0) ^ 2 / (P s i0 * P t i0) := by field_simp; ring
    rw [this]
    positivity

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
