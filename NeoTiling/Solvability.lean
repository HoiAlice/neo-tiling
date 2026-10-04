import NeoTiling.GeneralPosition

/-!
# Neoclassical solvability

Notes, section 1, definition `def:neo-solvability`: demand sets (`demandSet`), realization
(`Realizes`) and neoclassical solvability (`NeoSolvable`). Notes, section "Разрешимость в общем
положении", lemma `lem:signature-points`: spectral regions (`specRegion`) and the spectrum
(`spectrum`).

Main results: `IsNeoclassical.realizes_iff_mem_span` (`lem:signature-points`: realizable outputs
form the cone spanned by the indicators of the spectrum), `Realizes.mono_spectrum` (realization
passes to a larger spectrum) and `IsNeoclassical.eventually_spectrum_subset` (the spectrum does
not shrink under small changes of prices).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace NeoTiling

/-! ### Definitions -/

/-- The demand set `A = {x ∈ ℝ²₊₊ | h (p ∘ x) < 1}` of the price `p`. -/
def demandSet (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ orthant ∧ h (hadamard p x) < 1}

/-- `h` realizes outputs `y` at prices `P`: some measure absolutely continuous w.r.t. Lebesgue
gives mass `y t` to the demand set of `P t`. -/
def Realizes (h : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ μ : Measure (ℝ × ℝ), μ ≪ volume ∧ ∀ t, μ (demandSet h (P t)) = ENNReal.ofReal (y t)

/-- **Neoclassical solvability** (notes, `def:neo-solvability`): one neoclassical `h` realizes
`y` at all prices near `P`. -/
def NeoSolvable {T : ℕ} (P : Fin T → ℝ × ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ h : ℝ × ℝ → ℝ, IsNeoclassical h ∧ ∀ᶠ Q in 𝓝 P, Realizes h Q y

/-- The *spectral region* `R_S = {x ∈ ℝ²₊₊ | h (p_t ∘ x) < 1 ↔ t ∈ S}` (notes,
`lem:signature-points`). The regions `R_S` partition `ℝ²₊₊`. -/
def specRegion (h : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) (S : Finset (Fin T)) :
    Set (ℝ × ℝ) :=
  {x | x ∈ orthant ∧ ∀ t, t ∈ S ↔ h (hadamard (P t) x) < 1}

/-- The *spectrum* `Sp(h, P)` (notes, `lem:signature-points`): the sets `S` whose spectral region
has nonempty interior. -/
def spectrum (h : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) : Set (Finset (Fin T)) :=
  {S | (interior (specRegion h P S)).Nonempty}

/-! ### Level curves are null -/

/-- `hadamard p` commutes with scalar multiplication. -/
theorem hadamard_smul (p x : ℝ × ℝ) (c : ℝ) : hadamard p (c • x) = c • hadamard p x := by
  ext <;> simp [hadamard] <;> ring

/-- The orthant is closed under multiplication by a positive scalar. -/
theorem smul_mem_orthant {c : ℝ} (hc : 0 < c) {x : ℝ × ℝ} (hx : x ∈ orthant) : c • x ∈ orthant :=
  mem_orthant.mpr ⟨by simpa using mul_pos hc (mem_orthant.mp hx).1,
    by simpa using mul_pos hc (mem_orthant.mp hx).2⟩

/-- The unit level set of `h (p ∘ ·)` in `ℝ²₊₊` is Lebesgue null: the level sets for `c > 0` are
its dilations by `c`, pairwise disjoint, so only countably many of them have positive measure. -/
theorem IsNeoclassical.volume_levelSet_eq_zero {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
    {p : ℝ × ℝ} (hp : p ∈ orthant) :
    volume {x | x ∈ orthant ∧ h (hadamard p x) = 1} = 0 := by
  by_contra hne
  have hcont : ContinuousOn (fun x => h (hadamard p x)) orthant := hh.continuousOn.comp
    (by unfold hadamard; fun_prop) fun x hx => orthant_subset_quadrant (hadamard_mem_orthant hp hx)
  refine absurd ((Measure.countable_meas_level_set_pos₀ (μ := volume.restrict orthant)
    (hcont.aemeasurable isOpen_orthant.measurableSet).nullMeasurable).mono (s₁ := Ioi 0)
    fun c (hc : 0 < c) => ?_)
    fun H => by simpa using H.measure_zero volume
  -- the level `c` is the dilation by `c` of the level `1`
  have hset : {x | h (hadamard p x) = c} ∩ orthant =
      c • {x | x ∈ orthant ∧ h (hadamard p x) = 1} := by
    ext x
    have ho : x ∈ orthant ↔ c⁻¹ • x ∈ orthant := ⟨smul_mem_orthant (inv_pos.2 hc), fun h' => by
      simpa [smul_smul, hc.ne'] using smul_mem_orthant hc h'⟩
    rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_inter_iff, and_comm, ho]
    refine and_congr_right fun hx => ?_
    rw [mem_setOf_eq, hadamard_smul, hh.homogeneous _ (inv_pos.2 hc) _ (orthant_subset_quadrant
      (hadamard_mem_orthant hp (ho.2 hx))), inv_mul_eq_one₀ hc.ne', eq_comm]
  rw [mem_setOf_eq, Measure.restrict_apply' isOpen_orthant.measurableSet, hset,
    Measure.addHaar_smul_of_nonneg volume hc.le]
  exact ENNReal.mul_pos (by simpa using hc.ne') hne

/-! ### Spectral regions -/

section Spectrum

variable {g : ℝ × ℝ → ℝ} {T : ℕ} {P : Fin T → ℝ × ℝ}

/-- A value closer to `b` than `b` is to `1` lies on the same side of `1` as `b`. -/
theorem lt_one_iff_of_abs_sub_lt {a b : ℝ} (H : |a - b| < |b - 1|) :
    (a < 1 ↔ b < 1) ∧ a ≠ 1 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 H
  rcases abs_cases (b - 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at h1 h2 <;>
    exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, fun _ => by linarith⟩

/-- `μ (A_t)` is the sum of the masses of the spectral regions `R_S`, `S ∋ t`. -/
theorem measure_demandSet_eq_sum (hg : ContinuousOn g orthant) (hP : ∀ t, P t ∈ orthant)
    (μ : Measure (ℝ × ℝ)) (t : Fin T) :
    μ (demandSet g (P t)) = ∑ S with t ∈ S, μ (specRegion g P S) := by
  classical
  have hU (u : Fin T) : MeasurableSet (orthant ∩ {x | g (hadamard (P u) x) < 1}) :=
    (ContinuousOn.isOpen_inter_preimage (hg.comp (by unfold hadamard; fun_prop)
      fun x hx => hadamard_mem_orthant (hP u) hx) isOpen_orthant isOpen_Iio).measurableSet
  rw [← measure_biUnion_finset (fun S _ S' _ hne => disjoint_left.2 fun x h h' =>
    hne (Finset.ext fun u => (h.2 u).trans (h'.2 u).symm)) fun S _ => ?_]
  · congr 1; ext x; simp only [demandSet, mem_setOf_eq, mem_iUnion, specRegion]
    refine ⟨fun ⟨hx, hlt⟩ => ⟨Finset.univ.filter (fun u => g (hadamard (P u) x) < 1),
      by simpa using hlt, hx, fun u => by simp⟩,
      fun ⟨i, hi, hx, hiff⟩ => ⟨hx, (hiff t).1 (by simpa using hi)⟩⟩
  convert isOpen_orthant.measurableSet.inter (MeasurableSet.iInter fun u =>
    measurableSet_setOf.2 ((measurable_const (a := u ∈ S)).iff (measurable_mem.2 (hU u))))
    using 1
  ext x; simp +contextual [specRegion, iff_iff_implies_and_implies]

/-- A point of `R_S` off all curves `g (p_t ∘ x) = 1` is an interior point of `R_S`: the strict
signs persist nearby. -/
theorem mem_interior_specRegion (hg : ContinuousOn g orthant) (hP : ∀ t, P t ∈ orthant)
    {S : Finset (Fin T)} {x : ℝ × ℝ} (hx : x ∈ specRegion g P S)
    (hx1 : ∀ t, g (hadamard (P t) x) ≠ 1) : x ∈ interior (specRegion g P S) := by
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [isOpen_orthant.mem_nhds hx.1, eventually_all.2 fun t =>
    (Metric.tendsto_nhds.1 ((hg.continuousAt (isOpen_orthant.mem_nhds
      (hadamard_mem_orthant (hP t) hx.1))).comp (f := hadamard (P t))
      (by unfold hadamard; fun_prop)) _ (abs_pos.2 (sub_ne_zero.2 (hx1 t)))).mono
      fun _ hz => (lt_one_iff_of_abs_sub_lt hz).1] with z hz hzt
  exact ⟨hz, fun t => (hx.2 t).trans (hzt t).symm⟩

/-- A spectral region outside the spectrum is null: its points off the null curves
`g (p_t ∘ x) = 1` are interior points (`mem_interior_specRegion`), and the interior is empty. -/
theorem volume_specRegion_eq_zero (hg : ContinuousOn g orthant) (hP : ∀ t, P t ∈ orthant)
    (hnull : ∀ t, volume {x | x ∈ orthant ∧ g (hadamard (P t) x) = 1} = 0)
    {S : Finset (Fin T)} (hS : S ∉ spectrum g P) : volume (specRegion g P S) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hnull)
  by_contra hne
  simp only [mem_iUnion, not_exists] at hne
  exact hS ⟨x, mem_interior_specRegion hg hP hx fun t e => hne t ⟨hx.1, e⟩⟩

/-- **Spectra depend only on signs.** If `x ∈ R_S` and every value `g' (q_t ∘ x)` is closer to
`g (p_t ∘ x)` than this value is to `1`, then `x` is an interior point of the region `R_S` of
`(g', Q)`, so `S` belongs to the spectrum of `(g', Q)`. -/
theorem mem_spectrum_of_abs_sub_lt {g' : ℝ × ℝ → ℝ} (hg' : ContinuousOn g' orthant)
    {Q : Fin T → ℝ × ℝ} (hQ : ∀ t, Q t ∈ orthant) {S : Finset (Fin T)} {x : ℝ × ℝ}
    (hx : x ∈ specRegion g P S)
    (H : ∀ t, |g' (hadamard (Q t) x) - g (hadamard (P t) x)| < |g (hadamard (P t) x) - 1|) :
    S ∈ spectrum g' Q := by
  have hs := fun t => lt_one_iff_of_abs_sub_lt (H t)
  exact ⟨x, mem_interior_specRegion hg' hQ ⟨hx.1, fun t => (hx.2 t).trans (hs t).1.symm⟩
    fun t => (hs t).2⟩

/-- Every `S` in the spectrum has a point of `R_S` off all curves: the interior of `R_S` has
positive measure and the curves are null. -/
theorem exists_mem_specRegion_ne_one
    (hnull : ∀ t, volume {x | x ∈ orthant ∧ g (hadamard (P t) x) = 1} = 0)
    {S : Finset (Fin T)} (hS : S ∈ spectrum g P) :
    ∃ x ∈ specRegion g P S, ∀ t, g (hadamard (P t) x) ≠ 1 := by
  set N : Set (ℝ × ℝ) := ⋃ t, {x | x ∈ orthant ∧ g (hadamard (P t) x) = 1} with hNdef
  have hNnull : volume N = 0 := measure_iUnion_null hnull
  have hpos : volume (interior (specRegion g P S) \ N) ≠ 0 := by
    rw [measure_diff_null hNnull]
    exact isOpen_interior.measure_ne_zero volume hS
  obtain ⟨x, hx1, hx2⟩ := nonempty_of_measure_ne_zero hpos
  refine ⟨x, interior_subset hx1, fun t hEq => hx2 (mem_iUnion.2 ⟨t, (interior_subset hx1).1, hEq⟩)⟩

end Spectrum

/-! ### The cone of realizable outputs -/

/-- Membership in the cone spanned by the indicators `1_S`, `S ∈ A`, written with coefficients:
`y_t = ∑_{S ∋ t} m_S` with `m ≥ 0` vanishing off `A`. -/
theorem mem_span_indicator_iff {T : ℕ} {A : Set (Finset (Fin T))} {y : Fin T → ℝ} :
    y ∈ PointedCone.span ℝ ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) '' A) ↔
      ∃ m : Finset (Fin T) → ℝ, (∀ S, 0 ≤ m S) ∧ (∀ S ∉ A, m S = 0) ∧
        ∀ t, y t = ∑ S with t ∈ S, m S := by
  classical
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      refine ⟨fun S' => if S' = S then 1 else 0, fun _ => by positivity,
        fun S' hS' => if_neg fun (e : S' = S) => hS' (e ▸ hS), fun t => ?_⟩
      simp [Set.indicator_apply, Finset.sum_ite_eq']
    | zero => exact ⟨0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
    | add x1 x2 _ _ ih1 ih2 =>
      obtain ⟨m1, hm1, hm1A, hy1⟩ := ih1
      obtain ⟨m2, hm2, hm2A, hy2⟩ := ih2
      exact ⟨m1 + m2, fun S => add_nonneg (hm1 S) (hm2 S),
        fun S hS => by simp [hm1A S hS, hm2A S hS],
        fun t => by simp [hy1 t, hy2 t, Finset.sum_add_distrib]⟩
    | smul r x _ ih =>
      obtain ⟨m, hm, hmA, hy⟩ := ih
      exact ⟨(r : ℝ) • m, fun S => mul_nonneg r.2 (hm S), fun S hS => by simp [hmA S hS],
        fun t => by show (r : ℝ) * x t = _; simp [hy t, Finset.mul_sum]⟩
  · rintro ⟨m, hm, hmA, hy⟩
    have key : y = ∑ S, m S • (S : Set (Fin T)).indicator 1 := by
      ext t
      simp [hy t, Set.indicator_apply, Finset.sum_filter]
    rw [key]
    refine Submodule.sum_mem _ fun S _ => ?_
    by_cases hS : S ∈ A
    · exact PointedCone.smul_mem _ (hm S) (PointedCone.subset_span ⟨S, hS, rfl⟩)
    · simp [hmA S hS]

section Cone

variable {h : ℝ × ℝ → ℝ} {T : ℕ} {P : Fin T → ℝ × ℝ} {y : Fin T → ℝ}

/-- A realization yields coefficients on the spectrum: `m_S = μ (R_S)`, which vanishes off the
spectrum (`volume_specRegion_eq_zero`); `y_t = ∑_{S ∋ t} μ (R_S)` by
`measure_demandSet_eq_sum`. The coefficient of `S = ∅` never enters, so `μ (R_∅) = ∞` is
harmless. -/
theorem IsNeoclassical.exists_coef_of_realizes (hh : IsNeoclassical h)
    (hP : ∀ t, P t ∈ orthant) (hy : ∀ t, 0 ≤ y t) (hR : Realizes h P y) :
    ∃ m : Finset (Fin T) → ℝ, (∀ S, 0 ≤ m S) ∧ (∀ S ∉ spectrum h P, m S = 0) ∧
      ∀ t, y t = ∑ S with t ∈ S, m S := by
  classical
  obtain ⟨μ, hμac, hμ⟩ := hR
  have hc : ContinuousOn h orthant := hh.continuousOn.mono orthant_subset_quadrant
  refine ⟨fun S => (μ (specRegion h P S)).toReal, fun S => ENNReal.toReal_nonneg,
    fun S hS => by
      show (μ (specRegion h P S)).toReal = 0
      rw [hμac (volume_specRegion_eq_zero hc hP (fun t => hh.volume_levelSet_eq_zero (hP t)) hS)]
      simp, fun t => ?_⟩
  have hsum := measure_demandSet_eq_sum hc hP μ t
  rw [hμ t] at hsum
  have hntop : (∑ S with t ∈ S, μ (specRegion h P S)) ≠ ⊤ := hsum ▸ ENNReal.ofReal_ne_top
  rw [← ENNReal.toReal_ofReal (hy t), hsum,
    ENNReal.toReal_sum fun S hSt => ENNReal.sum_ne_top.1 hntop S hSt]

/-- Coefficients on the spectrum are realized: put mass `m_S` uniformly on a ball inside the
interior of `R_S`. -/
theorem realizes_of_coef {m : Finset (Fin T) → ℝ} (hm : ∀ S, 0 ≤ m S)
    (hmS : ∀ S ∉ spectrum h P, m S = 0) (hy : ∀ t, y t = ∑ S with t ∈ S, m S) : Realizes h P y := by
  classical
  have hex : ∀ S : Finset (Fin T), ∃ c : ℝ × ℝ, ∃ r : ℝ, 0 < r ∧
      (S ∈ spectrum h P → Metric.ball c r ⊆ specRegion h P S) := by
    intro S
    by_cases hS : S ∈ spectrum h P
    · obtain ⟨x, hx⟩ := hS
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
      obtain ⟨r, hr, hsub⟩ := hx
      exact ⟨x, r, hr, fun _ => hsub⟩
    · exact ⟨0, 1, one_pos, fun h => absurd h hS⟩
  choose c r hr hrsub using hex
  refine ⟨∑ S, (ENNReal.ofReal (m S) / volume (Metric.ball (c S) (r S))) •
    volume.restrict (Metric.ball (c S) (r S)),
    fun A hA => by simp [fun B => Measure.absolutelyContinuous_of_le
      (Measure.restrict_le_self (s := B)) hA], fun t => ?_⟩
  rw [Measure.finset_sum_apply, hy t, ENNReal.ofReal_sum_of_nonneg (fun S _ => hm S),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_ball]
  by_cases hS : S ∈ spectrum h P
  · by_cases hts : t ∈ S
    · rw [(inter_eq_right (s := demandSet h (P t))).2 fun x hx =>
        ⟨(hrsub S hS hx).1, ((hrsub S hS hx).2 t).1 hts⟩,
        ENNReal.div_mul_cancel (Metric.measure_ball_pos volume (c S) (hr S)).ne'
          measure_ball_ne_top, if_pos hts]
    · rw [(eq_empty_iff_forall_notMem (s := demandSet h (P t) ∩ _)).2 fun x hx =>
        hts (((hrsub S hS hx.2).2 t).2 hx.1.2),
        measure_empty, mul_zero, if_neg hts]
  · simp [hmS S hS]

/-- **Lemma `lem:signature-points`.** For neoclassical `h` and prices in `ℝ²₊₊`, outputs
`y ≥ 0` are realized by `h` at `P` iff `y` lies in the cone spanned by the indicators `1_S` of the
sets `S` of the spectrum `Sp(h, P)`.

The cone is `PointedCone.span`, so that monotonicity in the spectrum is `Submodule.span_mono`;
the proof works with explicit coefficients (`mem_span_indicator_iff`):
`exists_coef_of_realizes` and `realizes_of_coef`. -/
theorem IsNeoclassical.realizes_iff_mem_span (hh : IsNeoclassical h) (hP : ∀ t, P t ∈ orthant)
    (hy : ∀ t, 0 ≤ y t) :
    Realizes h P y ↔
      y ∈ PointedCone.span ℝ ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) ''
        spectrum h P) := by
  rw [mem_span_indicator_iff]
  exact ⟨hh.exists_coef_of_realizes hP hy, fun ⟨m, hm, hmS, hym⟩ =>
    realizes_of_coef hm hmS hym⟩

/-- **Realization grows with the spectrum.** If `h` realizes `y` at `P` and the spectrum of
`(g, Q)` contains that of `(h, P)`, then `g` realizes `y` at `Q`. Only `max y 0` matters for
realization, and it lies in the larger cone (`realizes_iff_mem_span`). -/
theorem Realizes.mono_spectrum (hR : Realizes h P y) (hh : IsNeoclassical h)
    (hP : ∀ t, P t ∈ orthant) {g : ℝ × ℝ → ℝ} (hg : IsNeoclassical g) {Q : Fin T → ℝ × ℝ}
    (hQ : ∀ t, Q t ∈ orthant) (hS : spectrum h P ⊆ spectrum g Q) : Realizes g Q y := by
  have hpos (f : ℝ × ℝ → ℝ) (R : Fin T → ℝ × ℝ) :
      Realizes f R y ↔ Realizes f R fun t => max (y t) 0 := by
    simp [Realizes, ENNReal.ofReal_max]
  rw [hpos, hh.realizes_iff_mem_span hP fun t => le_max_right _ _] at hR
  rw [hpos, hg.realizes_iff_mem_span hQ fun t => le_max_right _ _]
  exact Submodule.span_mono (image_mono hS) hR

/-- **The spectrum does not shrink near `P`.** Each `S ∈ Sp(h, P)` has a point of `R_S` off the
curves (`exists_mem_specRegion_ne_one`); its strict signs persist for nearby prices
(`mem_spectrum_of_abs_sub_lt`). -/
theorem IsNeoclassical.eventually_spectrum_subset (hh : IsNeoclassical h)
    (hP : ∀ t, P t ∈ orthant) : ∀ᶠ Q in 𝓝 P, spectrum h P ⊆ spectrum h Q := by
  have hc : ContinuousOn h orthant := hh.continuousOn.mono orthant_subset_quadrant
  have hS (S) (hS : S ∈ spectrum h P) : ∀ᶠ Q in 𝓝 P, S ∈ spectrum h Q := by
    obtain ⟨x, hx, hx1⟩ :=
      exists_mem_specRegion_ne_one (fun t => hh.volume_levelSet_eq_zero (hP t)) hS
    filter_upwards [eventually_mem_orthant hP, eventually_all.2 fun t =>
      Metric.tendsto_nhds.1 ((hc.continuousAt (isOpen_orthant.mem_nhds
        (hadamard_mem_orthant (hP t) hx.1))).comp (f := fun Q : Fin T → ℝ × ℝ => hadamard (Q t) x)
        (by unfold hadamard; fun_prop)).tendsto _ (abs_pos.2 (sub_ne_zero.2 (hx1 t)))]
      with Q hQ hQt
    exact mem_spectrum_of_abs_sub_lt hc hQ hx hQt
  filter_upwards [(toFinite (spectrum h P)).eventually_all.2 hS] with Q hQ S hS' using hQ S hS'

end Cone

/-! ### Strictly positive approximation -/

/-- `h + ε (x₁ + x₂)` is strictly positive neoclassical for `ε > 0`. -/
theorem IsNeoclassical.isPosNeoclassical_add_linear {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
    {ε : ℝ} (hε : 0 < ε) : IsPosNeoclassical (fun z => h z + ε * (z.1 + z.2)) := by
  rw [isPosNeoclassical_iff_exists_linear_le]
  have hlin : ConcaveOn ℝ quadrant (fun z : ℝ × ℝ => ε * (z.1 + z.2)) := by
    refine ⟨hh.concaveOn.1, fun p _ q _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
    nlinarith [hab]
  refine ⟨⟨fun p hp => ?_, hh.continuousOn.add (by fun_prop), hh.concaveOn.add hlin,
    fun t ht p hp => ?_⟩, ε, ε, hε, hε, fun p hp => ?_⟩
  · have := hh.nonneg p hp
    obtain ⟨h1, h2⟩ := mem_quadrant.mp hp
    positivity
  · simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd]
    rw [hh.homogeneous t ht p hp]; ring
  · nlinarith [hh.nonneg p hp]

/-- A neoclassical `h` is approximated at finitely many points by the strictly positive
neoclassical `h + ε (x₁ + x₂)` with small `ε > 0` (`isPosNeoclassical_add_linear`). -/
theorem IsNeoclassical.exists_isPosNeoclassical_near {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
    (Z : Finset (ℝ × ℝ)) {η : ℝ × ℝ → ℝ} (hη : ∀ z ∈ Z, 0 < η z) :
    ∃ g, IsPosNeoclassical g ∧ ∀ z ∈ Z, |g z - h z| < η z := by
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ z ∈ Z, |h z + ε * (z.1 + z.2) - h z| < η z :=
    Z.eventually_all.2 fun z hz => by
      have hc : Continuous fun ε : ℝ => |h z + ε * (z.1 + z.2) - h z| := by fun_prop
      exact hc.continuousAt.eventually_lt_const (by simpa using hη z hz)
  obtain ⟨ε, hεZ, hε⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  exact ⟨_, hh.isPosNeoclassical_add_linear hε, hεZ⟩

end NeoTiling
