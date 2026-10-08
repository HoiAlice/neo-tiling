import NeoTiling.Neoclassical

/-!
# Realization and the spectrum

Demand sets (`demandSet`), realization of outputs (`Realizes`), neoclassical solvability
(`NeoSolvable`), open chambers (`specRegion`), the spectrum of nonempty chambers (`spectrum`) and
the cone spanned by indicators of a family of sets (`indicatorCone`).

Main results:

* `IsNeoclassical.volume_levelSet_eq_zero`: the level set `h (p * x) = 1` is null.
* `IsNeoclassical.realizes_iff_mem_indicatorCone`: `h` realizes `y ≥ 0` at `P` iff `y` lies in
  the cone spanned by the indicators of the spectrum `Sp(h, P)`.
* `IsNeoclassical.eventually_spectrum_subset`: the spectrum does not shrink near `P`.
* `exists_coef_of_mem_indicatorCone`: Carathéodory for the indicator cone, at most `T` indicators.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace NeoTiling

variable {d : ℕ}

/-! ### Definitions -/

/-- The demand set `{x ∈ ℝᵈ₊₊ | h (p * x) < 1}` of the price `p`. -/
def demandSet (h : (Fin d → ℝ) → ℝ) (p : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | x ∈ orthant d ∧ h (p * x) < 1}

/-- `h` realizes outputs `y` at prices `P`: some measure absolutely continuous w.r.t. Lebesgue
gives mass `y t` to the demand set of `P t`. -/
def Realizes (h : (Fin d → ℝ) → ℝ) {T : ℕ} (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ μ : Measure (Fin d → ℝ), μ ≪ volume ∧ ∀ t, μ (demandSet h (P t)) = ENNReal.ofReal (y t)

/-- `y` is neoclassically solvable at `P`: one neoclassical `h` realizes `y` at all prices near
`P`. -/
def NeoSolvable {T : ℕ} (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ h : (Fin d → ℝ) → ℝ, IsNeoclassical h ∧ ∀ᶠ Q in 𝓝 P, Realizes h Q y

/-- The open chamber `R_S`: points `x ∈ ℝᵈ₊₊` with `h (p_t * x) < 1` for `t ∈ S` and
`h (p_t * x) > 1` for `t ∉ S`. -/
def specRegion (h : (Fin d → ℝ) → ℝ) {T : ℕ} (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) :
    Set (Fin d → ℝ) :=
  {x | x ∈ orthant d ∧ (∀ t ∈ S, h (P t * x) < 1) ∧ ∀ t ∉ S, 1 < h (P t * x)}

/-- The spectrum `Sp(h, P)`: the sets `S` with nonempty chamber `R_S`. -/
def spectrum (h : (Fin d → ℝ) → ℝ) {T : ℕ} (P : Fin T → Fin d → ℝ) : Set (Finset (Fin T)) :=
  {S | (specRegion h P S).Nonempty}

/-- The cone spanned by the indicators `1_S`, `S ∈ A`. -/
def indicatorCone {T : ℕ} (A : Set (Finset (Fin T))) : PointedCone ℝ (Fin T → ℝ) :=
  PointedCone.span ℝ ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) '' A)

/-- **Level sets are null.** The set `{x ∈ ℝᵈ₊₊ | h (p * x) = c}` is the dilate by `c` of the
level set `1`; among the disjoint level sets `c > 0` only countably many have positive measure,
so all of them, the level set `1` included, are null. -/
theorem IsNeoclassical.volume_levelSet_eq_zero {h : (Fin d → ℝ) → ℝ} (hh : IsNeoclassical h)
    {p : Fin d → ℝ} (hp : p ∈ orthant d) :
    volume {x | x ∈ orthant d ∧ h (p * x) = 1} = 0 := by
  by_contra hne
  have hcont : ContinuousOn (fun x => h (p * x)) (orthant d) := hh.continuousOn.comp
    (by fun_prop) fun x hx => orthant_subset_Ici (mul_mem_orthant hp hx)
  refine absurd ((Measure.countable_meas_level_set_pos₀ (μ := volume.restrict (orthant d))
    (hcont.aemeasurable isOpen_orthant.measurableSet).nullMeasurable).mono (s₁ := Ioi 0)
    fun c (hc : 0 < c) => ?_)
    fun H => by simpa using H.measure_zero volume
  have hset : {x | h (p * x) = c} ∩ orthant d =
      c • {x | x ∈ orthant d ∧ h (p * x) = 1} := by
    ext x
    have ho : x ∈ orthant d ↔ c⁻¹ • x ∈ orthant d :=
      ⟨fun hx i => by simpa using mul_pos (inv_pos.2 hc) (hx i), fun hx i => by
        have := hx i; simp only [Pi.smul_apply, smul_eq_mul] at this
        exact pos_of_mul_pos_right this (inv_pos.2 hc).le⟩
    rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_inter_iff, and_comm, ho]
    refine and_congr_right fun hx => ?_
    rw [mem_setOf_eq, mul_smul_comm, hh.homogeneous _ (inv_pos.2 hc).le _ (orthant_subset_Ici
      (mul_mem_orthant hp (ho.2 hx))), inv_mul_eq_one₀ hc.ne', eq_comm]
  rw [mem_setOf_eq, Measure.restrict_apply' isOpen_orthant.measurableSet, hset,
    Measure.addHaar_smul_of_nonneg volume hc.le]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (pow_pos hc _)).ne' hne

/-! ### Chambers -/

section Spectrum

variable {g : (Fin d → ℝ) → ℝ} {T : ℕ} {P : Fin T → Fin d → ℝ}

/-- Chambers are open: strict inequalities at `x` persist near `x`. -/
theorem isOpen_specRegion (hg : ContinuousOn g (orthant d)) (hP : ∀ t, P t ∈ orthant d)
    (S : Finset (Fin T)) : IsOpen (specRegion g P S) := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨hx, hlt, hgt⟩ => ?_
  have hc t : ContinuousAt (fun z => g (P t * z)) x :=
    (hg.continuousAt (isOpen_orthant.mem_nhds (mul_mem_orthant (hP t) hx))).comp (by fun_prop)
  filter_upwards [isOpen_orthant.mem_nhds hx,
    eventually_all.2 fun t => eventually_imp_distrib_left.2 fun ht =>
      (hc t).eventually (eventually_lt_nhds (hlt t ht)),
    eventually_all.2 fun t => eventually_imp_distrib_left.2 fun ht =>
      (hc t).eventually (eventually_gt_nhds (hgt t ht))] with z hz h1 h2 using ⟨hz, h1, h2⟩

/-- Chambers are pairwise disjoint. -/
theorem eq_of_mem_specRegion {S S' : Finset (Fin T)} {x : Fin d → ℝ}
    (h : x ∈ specRegion g P S) (h' : x ∈ specRegion g P S') : S = S' :=
  Finset.ext fun t => ⟨fun ht => by_contra fun ht' => lt_asymm (h.2.1 t ht) (h'.2.2 t ht'),
    fun ht => by_contra fun ht' => lt_asymm (h'.2.1 t ht) (h.2.2 t ht')⟩

/-- For `μ ≪ volume`, `μ (A_t)` is the sum of the masses of the chambers `R_S`, `S ∋ t`: a point
of `A_t` off the null level sets lies in the chamber of `S = {u | h (p_u * x) < 1}`. -/
theorem measure_demandSet_eq_sum (hg : IsNeoclassical g) (hP : ∀ t, P t ∈ orthant d)
    {μ : Measure (Fin d → ℝ)} (hμ : μ ≪ volume) (t : Fin T) :
    μ (demandSet g (P t)) = ∑ S with t ∈ S, μ (specRegion g P S) := by
  classical
  set L := ⋃ s, {x | x ∈ orthant d ∧ g (P s * x) = 1}
  have hL : μ L = 0 := hμ (measure_iUnion_null fun s => hg.volume_levelSet_eq_zero (hP s))
  rw [← measure_biUnion_finset (fun S _ S' _ hne => disjoint_left.2 fun x h h' =>
    hne (eq_of_mem_specRegion h h')) fun S _ =>
      (isOpen_specRegion (hg.continuousOn.mono orthant_subset_Ici) hP S).measurableSet]
  refine le_antisymm ?_ (measure_mono fun x hx => ?_)
  · refine (measure_mono (t := (⋃ S ∈ Finset.univ.filter (t ∈ ·), specRegion g P S) ∪ L)
      fun x hx => ?_).trans <| (measure_union_le _ _).trans (by rw [hL, add_zero])
    obtain ⟨hx, hlt⟩ := hx
    by_cases hxL : x ∈ L
    · exact Or.inr hxL
    refine Or.inl (mem_iUnion₂.2 ⟨Finset.univ.filter fun u => g (P u * x) < 1, by simpa using hlt,
      hx, fun u hu => by simpa using hu, fun u hu => lt_of_le_of_ne (by simpa using hu)
        fun e => hxL (mem_iUnion.2 ⟨u, hx, e.symm⟩)⟩)
  · obtain ⟨S, hS, hx⟩ := mem_iUnion₂.1 hx
    exact ⟨hx.1, hx.2.1 t (Finset.mem_filter.1 hS).2⟩

end Spectrum

/-! ### The cone of realizable outputs -/

section Cone

variable {h : (Fin d → ℝ) → ℝ} {T : ℕ} {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

/-- The indicator of `S ∈ Sp(h, P)` is realized by the uniform probability on a ball inside the
nonempty open chamber `R_S`. -/
theorem realizes_indicator (hc : ContinuousOn h (orthant d)) (hP : ∀ t, P t ∈ orthant d)
    {S : Finset (Fin T)} (hS : S ∈ spectrum h P) :
    Realizes h P ((S : Set (Fin T)).indicator 1) := by
  classical
  obtain ⟨x, hx⟩ := hS
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (isOpen_specRegion hc hP S) x hx
  refine ⟨ProbabilityTheory.cond volume (Metric.ball x r),
    ProbabilityTheory.cond_absolutelyContinuous, fun t => ?_⟩
  rw [ProbabilityTheory.cond_apply measurableSet_ball]
  by_cases ht : t ∈ S
  · rw [(inter_eq_left (t := demandSet h (P t))).2 fun z hz => ⟨(hB hz).1, (hB hz).2.1 t ht⟩,
      ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume x hr).ne' measure_ball_ne_top]
    simp [ht]
  · rw [(eq_empty_iff_forall_notMem (s := Metric.ball x r ∩ _)).2 fun z hz =>
      lt_asymm hz.2.2 ((hB hz.1).2.2 t ht)]
    simp [ht]

/-- **Realizable outputs.** For neoclassical `h` and positive prices, outputs `y ≥ 0` are
realized by `h` at `P` iff `y` lies in the cone spanned by the indicators of the spectrum
`Sp(h, P)`. A realization `μ` gives `y = ∑_S μ (R_S) • 1_S` (`measure_demandSet_eq_sum`), and
`R_S = ∅` for `S ∉ Sp(h, P)`. Conversely, realizable outputs form a cone containing the
indicators of the spectrum (`realizes_indicator`). -/
theorem IsNeoclassical.realizes_iff_mem_indicatorCone (hh : IsNeoclassical h)
    (hP : ∀ t, P t ∈ orthant d) (hy : ∀ t, 0 ≤ y t) :
    Realizes h P y ↔ y ∈ indicatorCone (spectrum h P) := by
  classical
  have hc : ContinuousOn h (orthant d) := hh.continuousOn.mono orthant_subset_Ici
  constructor
  · rintro ⟨μ, hμ, hμy⟩
    have hy' : y = ∑ S, (μ (specRegion h P S)).toReal • (S : Set (Fin T)).indicator 1 := by
      ext t
      have hsum := (measure_demandSet_eq_sum hh hP hμ t).symm.trans (hμy t)
      have hntop : (∑ S with t ∈ S, μ (specRegion h P S)) ≠ ⊤ := hsum ▸ ENNReal.ofReal_ne_top
      rw [← ENNReal.toReal_ofReal (hy t), ← hsum,
        ENNReal.toReal_sum fun S hS => ENNReal.sum_ne_top.1 hntop S hS]
      simp [Finset.sum_apply, Set.indicator_apply, Finset.sum_filter]
    rw [hy']
    refine Submodule.sum_mem _ fun S _ => ?_
    by_cases hS : S ∈ spectrum h P
    · exact PointedCone.smul_mem _ ENNReal.toReal_nonneg (PointedCone.subset_span ⟨S, hS, rfl⟩)
    · simp [not_nonempty_iff_eq_empty.1 hS]
  · intro hy'
    refine (Submodule.span_induction (p := fun y _ => 0 ≤ y ∧ Realizes h P y) ?_ ?_ ?_ ?_ hy').2
    · rintro _ ⟨S, hS, rfl⟩
      exact ⟨indicator_nonneg (fun _ _ => zero_le_one), realizes_indicator hc hP hS⟩
    · exact ⟨le_rfl, 0, Measure.AbsolutelyContinuous.zero _, by simp⟩
    · rintro y₁ y₂ - - ⟨h₁, μ₁, hμ₁, e₁⟩ ⟨h₂, μ₂, hμ₂, e₂⟩
      exact ⟨add_nonneg h₁ h₂, μ₁ + μ₂, hμ₁.add_left hμ₂, fun t => by
        simp [e₁, e₂, ENNReal.ofReal_add (h₁ t) (h₂ t)]⟩
    · rintro r y - ⟨h₀, μ, hμ, e⟩
      exact ⟨smul_nonneg r.2 h₀, ENNReal.ofReal r • μ, hμ.smul_left _, fun t => by
        rw [Measure.smul_apply, e, smul_eq_mul, ← ENNReal.ofReal_mul r.2]; rfl⟩

/-- **The spectrum does not shrink near `P`.** The finitely many strict inequalities at a strict
point `x` of `S ∈ Sp(h, P)` persist for `Q` near `P`, by continuity of `Q ↦ h (Q t * x)`. -/
theorem IsNeoclassical.eventually_spectrum_subset (hh : IsNeoclassical h)
    (hP : ∀ t, P t ∈ orthant d) : ∀ᶠ Q in 𝓝 P, spectrum h P ⊆ spectrum h Q := by
  refine (toFinite (spectrum h P)).eventually_all.2 fun S ⟨x, hx, hlt, hgt⟩ => ?_
  have hcx t : ContinuousAt (fun Q : Fin T → Fin d → ℝ => h (Q t * x)) P :=
    (hh.continuousOn.continuousAt (mem_nhds_iff.2 ⟨_, orthant_subset_Ici, isOpen_orthant,
      mul_mem_orthant (hP t) hx⟩)).comp (f := fun Q : Fin T → Fin d → ℝ => Q t * x)
      ((continuous_apply t).mul continuous_const).continuousAt
  filter_upwards [eventually_all.2 fun t => eventually_imp_distrib_left.2 fun ht =>
      (hcx t).eventually (eventually_lt_nhds (hlt t ht)),
    eventually_all.2 fun t => eventually_imp_distrib_left.2 fun ht =>
      (hcx t).eventually (eventually_gt_nhds (hgt t ht))]
    with Q h1 h2 using ⟨x, hx, h1, h2⟩

end Cone

/-- **Carathéodory for the indicator cone.** A vector of `indicatorCone A` is a nonnegative
combination of at most `T` indicators of sets in `A`: a minimal-support representation has
linearly independent indicators, and `Fin T → ℝ` has dimension `T`. -/
theorem exists_coef_of_mem_indicatorCone {T : ℕ} {A : Set (Finset (Fin T))} {y : Fin T → ℝ}
    (hy : y ∈ indicatorCone A) :
    ∃ m : Finset (Fin T) → ℝ, (∀ S, 0 ≤ m S) ∧ (∀ S, m S ≠ 0 → S ∈ A) ∧
      (Finset.univ.filter fun S => m S ≠ 0).card ≤ T ∧
      y = ∑ S, m S • (S : Set (Fin T)).indicator 1 := by
  classical
  set ind : Finset (Fin T) → Fin T → ℝ := fun S => (S : Set (Fin T)).indicator 1
  -- some representation exists
  obtain ⟨m, hm0, hmA, hmy⟩ : ∃ m : Finset (Fin T) → ℝ, (∀ S, 0 ≤ m S) ∧
      (∀ S, m S ≠ 0 → S ∈ A) ∧ y = ∑ S, m S • ind S := by
    refine Submodule.span_induction (p := fun y _ => ∃ m : Finset (Fin T) → ℝ, (∀ S, 0 ≤ m S) ∧
      (∀ S, m S ≠ 0 → S ∈ A) ∧ y = ∑ S, m S • ind S) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨S, hS, rfl⟩
      refine ⟨Pi.single S 1, fun S' => ?_, fun S' h => ?_, ?_⟩
      · rw [Pi.single_apply]; split_ifs <;> norm_num
      · by_cases h' : S' = S <;> simp_all
      · simp [Pi.single_apply, ind]
    · exact ⟨0, fun _ => le_rfl, fun _ h => absurd rfl h, by simp⟩
    · rintro y₁ y₂ - - ⟨m₁, h₁, a₁, e₁⟩ ⟨m₂, h₂, a₂, e₂⟩
      refine ⟨m₁ + m₂, fun S => add_nonneg (h₁ S) (h₂ S), fun S h => ?_, ?_⟩
      · by_contra hS
        simp [not_imp_comm.1 (a₁ S) hS, not_imp_comm.1 (a₂ S) hS] at h
      · simp [e₁, e₂, add_smul, Finset.sum_add_distrib]
    · rintro r y - ⟨m, h₀, a, e⟩
      refine ⟨fun S => r * m S, fun S => mul_nonneg r.2 (h₀ S), fun S h => a S ?_, ?_⟩
      · exact right_ne_zero_of_mul h
      · simp [e, Finset.smul_sum, mul_smul]; rfl
  -- reduce the support
  suffices H : ∀ R : Finset (Finset (Fin T)), (∀ S ∈ R, S ∈ A) → ∀ m : Finset (Fin T) → ℝ,
      (∀ S, 0 ≤ m S) → (∀ S, m S ≠ 0 → S ∈ R) → y = ∑ S, m S • ind S →
      ∃ m : Finset (Fin T) → ℝ, (∀ S, 0 ≤ m S) ∧ (∀ S, m S ≠ 0 → S ∈ A) ∧
        (Finset.univ.filter fun S => m S ≠ 0).card ≤ T ∧ y = ∑ S, m S • ind S from
    H (Finset.univ.filter fun S => m S ≠ 0) (fun S hS => hmA S (by simpa using hS)) m hm0
      (fun S h => by simpa using h) hmy
  intro R
  induction R using Finset.strongInductionOn with | _ R ih =>
  intro hRA m hm0 hmR hmy
  by_cases hR : R.card ≤ T
  · exact ⟨m, hm0, fun S h => hRA S (hmR S h),
      (Finset.card_le_card fun S hS => hmR S (by simpa using hS)).trans hR, hmy⟩
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1
    fun h : LinearIndependent ℝ fun S : R => ind S =>
    by have := h.fintype_card_le_finrank; simp at this; omega
  wlog hgi : 0 < g i generalizing g
  · exact this (-g) (by simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hg, neg_zero])
      (by simpa using hi) (neg_pos.2 (lt_of_le_of_ne (not_lt.1 hgi) hi))
  let μ (S : Finset (Fin T)) : ℝ := if h : S ∈ R then g ⟨S, h⟩ else 0
  have hμR (S) (hS : S ∉ R) : μ S = 0 := by simp [μ, hS]
  have hμ : ∑ S, μ S • ind S = 0 := by
    rw [← Finset.sum_subset R.subset_univ fun S _ hS => by simp [hμR S hS],
      ← Finset.sum_coe_sort, ← hg]
    simp [μ]
  obtain ⟨S₀, hS₀, hmin⟩ := (Finset.univ.filter (0 < μ ·)).exists_min_image
    (fun S => m S / μ S) ⟨i, by simpa [μ] using hgi⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS₀ hmin
  have hS₀R : S₀ ∈ R := by by_contra h; simp [hμR S₀ h] at hS₀
  set θ := m S₀ / μ S₀
  have hθ : 0 ≤ θ := div_nonneg (hm0 _) hS₀.le
  refine ih _ (Finset.erase_ssubset hS₀R) (fun S hS => hRA S (Finset.mem_of_mem_erase hS))
    (fun S => m S - θ * μ S) (fun S => ?_) (fun S hS => ?_) ?_
  · rcases lt_or_ge 0 (μ S) with h | h
    · have := hmin S h; rw [le_div_iff₀ h] at this; linarith
    · nlinarith [hm0 S]
  · by_cases h : S = S₀
    · subst h; simp [θ, div_mul_cancel₀ _ hS₀.ne'] at hS
    · refine Finset.mem_erase.2 ⟨h, ?_⟩
      by_contra h'
      simp [hμR S h', not_imp_comm.1 (hmR S) h'] at hS
  · simp_rw [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμ, smul_zero,
      sub_zero, hmy]

end NeoTiling
