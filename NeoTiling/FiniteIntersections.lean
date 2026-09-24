import NeoTiling.BddNeoclassical

/-!
# Finitely many intersections for generic parameters

Let `f` be a profile (see `IsProfile`). For a parameter `p = (α, β)` with `α > 1 > β > 0`
consider the equation `α * f y = f (β * y)` on `y ∈ [0, 1]`. The condition `β < 1` makes
`β * y ∈ [0, 1]`, so that `f (β * y)` refers to the meaningful part of `f`.

Main result (`IsProfile.exists_finite_solutions`): every open set of parameters contains a
parameter for which the equation has only finitely many solutions. Equivalently, the good
parameters are dense in `Param = (1, ∞) × (0, 1)`.

The proof does not use smoothness of `f`. For fixed `β` the solutions are the level set
`{y | F y = α}` of `F y = f (β * y) / f y`, which is Lipschitz on the compact set where the
solutions live. If a level set is infinite it has an accumulation point, at which `F` either is
not differentiable or has derivative `0`. By Rademacher's theorem the first set is null, and
Lipschitz maps preserve null sets; by Sard's lemma the image of the second set is null. Hence
the set of bad `α` is null and cannot contain an interval.
-/

open Real Set Filter Topology MeasureTheory

namespace NeoTiling

/-! ### The one-variable measure-theoretic core -/

/-- For a Lipschitz function on a compact set, the set of values whose level set is infinite
has measure zero. This is the only place where measure theory is used. -/
theorem volume_infinite_level_eq_zero {F : ℝ → ℝ} {K : Set ℝ} {L : NNReal}
    (hK : IsCompact K) (hF : LipschitzOnWith L F K) :
    volume {α : ℝ | (K ∩ F ⁻¹' {α}).Infinite} = 0 := by
  -- `A`: points of `K` which are accumulation points of their own level set.
  set A : Set ℝ := {y | y ∈ K ∧ AccPt y (𝓟 (K ∩ F ⁻¹' {F y}))} with hA
  -- `D`: points of `K` where `F` is differentiable within `K`.
  set D : Set ℝ := {y | y ∈ K ∧ DifferentiableWithinAt ℝ F K y} with hD
  -- Every bad value is the value of `F` at a point of `A`.
  have hsub : {α : ℝ | (K ∩ F ⁻¹' {α}).Infinite} ⊆ F '' A := by
    intro α hα
    obtain ⟨y, hyK, hacc⟩ := hα.exists_accPt_of_subset_isCompact hK inter_subset_left
    have hclosed : IsClosed (K ∩ F ⁻¹' {α}) :=
      hF.continuousOn.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
    have hy : y ∈ K ∩ F ⁻¹' {α} :=
      hclosed.closure_subset (mem_closure_iff_clusterPt.mpr hacc.clusterPt)
    have hFy : F y = α := hy.2
    refine ⟨y, ⟨hyK, ?_⟩, hFy⟩
    rw [hFy]
    exact hacc
  -- At a point of `A ∩ D` the derivative within `K` vanishes.
  have hderiv : ∀ y ∈ A ∩ D, HasDerivWithinAt F 0 K y := by
    rintro y ⟨⟨hyK, hacc⟩, -, hdiff⟩
    have h := hdiff.hasDerivWithinAt
    set d := derivWithin F K y
    rw [hasDerivWithinAt_iff_tendsto_slope] at h ⊢
    set T := (K ∩ F ⁻¹' {F y}) \ {y} with hT
    have hne : (𝓝[T] y).NeBot := accPt_principal_iff_clusterPt.mp hacc
    have hle : 𝓝[T] y ≤ 𝓝[K \ {y}] y :=
      nhdsWithin_mono _ (diff_subset_diff_left inter_subset_left)
    have h1 : Tendsto (slope F y) (𝓝[T] y) (𝓝 d) := h.mono_left hle
    have h2 : Tendsto (slope F y) (𝓝[T] y) (𝓝 0) := by
      refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
      have hz' : F z = F y := hz.1.2
      simp [slope_def_field, hz']
    have hd : d = 0 := tendsto_nhds_unique h1 h2
    rw [← hd]
    exact h
  -- Sard: the image of `A ∩ D` is null.
  have hAD : volume (F '' (A ∩ D)) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (f' := fun _ => ContinuousLinearMap.toSpanSingleton ℝ (0 : ℝ)) ?_ ?_
    · intro y hy
      exact ((hderiv y hy).mono fun z hz => hz.1.1).hasFDerivWithinAt
    · intro y _
      simp [ContinuousLinearMap.det]
  -- Rademacher: the non-differentiability set is null, and so is its Lipschitz image.
  have hN : volume {y | y ∈ K ∧ ¬ DifferentiableWithinAt ℝ F K y} = 0 := by
    have := hF.ae_differentiableWithinAt_of_mem_real
    rw [ae_iff] at this
    simpa [Classical.not_imp] using this
  have hAD' : volume (F '' (A \ D)) = 0 := by
    have hsubN : A \ D ⊆ {y | y ∈ K ∧ ¬ DifferentiableWithinAt ℝ F K y} := by
      rintro y ⟨⟨hyK, -⟩, hyD⟩
      exact ⟨hyK, fun h => hyD ⟨hyK, h⟩⟩
    have hsubK : {y | y ∈ K ∧ ¬ DifferentiableWithinAt ℝ F K y} ⊆ K := fun _ h => h.1
    apply le_antisymm _ (zero_le _)
    calc volume (F '' (A \ D)) ≤ volume (F '' {y | y ∈ K ∧ ¬ DifferentiableWithinAt ℝ F K y}) :=
          measure_mono (image_mono hsubN)
      _ = μH[1] (F '' {y | y ∈ K ∧ ¬ DifferentiableWithinAt ℝ F K y}) := by
          rw [hausdorffMeasure_real]
      _ ≤ (L : ENNReal) ^ (1 : ℝ) * μH[1] {y | y ∈ K ∧ ¬ DifferentiableWithinAt ℝ F K y} :=
          (hF.mono hsubK).hausdorffMeasure_image_le zero_le_one
      _ = 0 := by rw [hausdorffMeasure_real, hN, mul_zero]
  apply le_antisymm _ (zero_le _)
  calc volume {α : ℝ | (K ∩ F ⁻¹' {α}).Infinite} ≤ volume (F '' A) := measure_mono hsub
    _ = volume (F '' (A ∩ D) ∪ F '' (A \ D)) := by rw [← image_union, inter_union_diff]
    _ ≤ volume (F '' (A ∩ D)) + volume (F '' (A \ D)) := measure_union_le _ _
    _ = 0 := by rw [hAD, hAD', add_zero]

/-! ### Parameters and solutions -/

/-- The parameter domain `(1, ∞) × (0, 1)`: `p.1 > 1 > p.2 > 0`. It is open in `ℝ²`, so an
open subset of `Param` is the same thing as an open subset of `ℝ²` contained in `Param`. -/
def Param : Set (ℝ × ℝ) := Ioi 1 ×ˢ Ioo 0 1

theorem isOpen_Param : IsOpen Param := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Param {p : ℝ × ℝ} : p ∈ Param ↔ 1 < p.1 ∧ 0 < p.2 ∧ p.2 < 1 := by
  simp only [Param, mem_prod, mem_Ioi, mem_Ioo]

/-- The solutions `y ∈ [0, 1]` of `p.1 * f y = f (p.2 * y)`. -/
def solutions (f : ℝ → ℝ) (p : ℝ × ℝ) : Set ℝ := {y | y ∈ Icc 0 1 ∧ p.1 * f y = f (p.2 * y)}

/-- For `p ∈ Param` the argument `p.2 * y` stays in `[0, 1]`: this is why `p.2 < 1` is required. -/
theorem mul_mem_Icc_of_mem_Param {p : ℝ × ℝ} (hp : p ∈ Param) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    p.2 * y ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨_, h0, h1⟩ := mem_Param.mp hp
  exact ⟨mul_nonneg h0.le hy.1, (mul_le_of_le_one_right h0.le hy.2).trans h1.le⟩

namespace IsProfile

variable {f : ℝ → ℝ} (hf : IsProfile f)
include hf

/-- The endpoints are never solutions. -/
theorem zero_not_mem_solutions {p : ℝ × ℝ} (hp : p ∈ Param) : (0 : ℝ) ∉ solutions f p := by
  rintro ⟨-, h⟩
  rw [mul_zero, hf.map_zero, mul_one] at h
  exact (mem_Param.mp hp).1.ne' h

theorem one_not_mem_solutions {p : ℝ × ℝ} (hp : p ∈ Param) : (1 : ℝ) ∉ solutions f p := by
  rintro ⟨-, h⟩
  obtain ⟨_, h0, h1⟩ := mem_Param.mp hp
  rw [hf.map_one, mul_zero, mul_one] at h
  exact (hf.pos ⟨h0.le, h1⟩).ne' h.symm

/-- A profile is Lipschitz on every compact subinterval of `(0, 1)`. -/
theorem exists_lipschitzOnWith_Icc {c d : ℝ} (hc : 0 < c) (hd : d < 1) :
    ∃ L : NNReal, LipschitzOnWith L f (Icc c d) := by
  have hball : Metric.ball (1 / 2 : ℝ) (1 / 2) = Ioo 0 1 := by
    rw [Real.ball_eq_Ioo]
    norm_num
  have hconv : ConvexOn ℝ (Metric.ball (1 / 2 : ℝ) (1 / 2)) f := by
    rw [hball]
    exact hf.convexOn.subset Ioo_subset_Icc_self (convex_Ioo 0 1)
  have hmin : 0 < min c (1 - d) := lt_min hc (by linarith)
  have hM : ∀ x, dist x (1 / 2 : ℝ) < 1 / 2 → |f x| ≤ 1 := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := by
      rw [← hball]
      exact hx
    have hx'' : x ∈ Icc (0 : ℝ) 1 := ⟨hx'.1.le, hx'.2.le⟩
    rw [abs_of_nonneg (hf.nonneg hx'')]
    exact hf.le_one hx''
  refine ⟨_, (hconv.lipschitzOnWith_of_abs_le (half_pos hmin) hM).mono ?_⟩
  intro x hx
  rw [Real.ball_eq_Ioo]
  have h1 := min_le_left c (1 - d)
  have h2 := min_le_right c (1 - d)
  constructor <;> linarith [hx.1, hx.2]

/-- All solutions for `α ∈ [a, b]` (with `a > 1`) lie in a fixed compact subinterval of
`(0, 1)`: near `0` we have `α * f y > 1 ≥ f (β * y)`, near `1` we have
`α * f y < f β ≤ f (β * y)`. -/
theorem exists_Icc_solutions_subset {a b β : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ c d : ℝ, 0 < c ∧ c ≤ d ∧ d < 1 ∧ ∀ α ∈ Icc a b, solutions f (α, β) ⊆ Icc c d := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h0 := hf.continuousOn 0 (left_mem_Icc.mpr zero_le_one)
  rw [Metric.continuousWithinAt_iff] at h0
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := h0 (1 - 1 / a)
    (by have : 1 / a < 1 := (div_lt_one ha0).mpr ha; linarith)
  have h1 := hf.continuousOn 1 (right_mem_Icc.mpr zero_le_one)
  rw [Metric.continuousWithinAt_iff] at h1
  have hfβ : 0 < f β := hf.pos ⟨hβ.1.le, hβ.2⟩
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := h1 (f β / b) (div_pos hfβ hb0)
  refine ⟨min (δ₀ / 2) (1 / 2), max (1 - δ₁ / 2) (1 / 2), lt_min (half_pos hδ₀) (by norm_num),
    (min_le_right _ _).trans (le_max_right _ _), ?_, ?_⟩
  · apply max_lt <;> linarith
  · rintro α ⟨hαa, hαb⟩ y ⟨⟨hy0, hy1⟩, hy⟩
    have hfy0 : 0 ≤ f y := hf.nonneg ⟨hy0, hy1⟩
    have hβy : β * y ≤ β := mul_le_of_le_one_right hβ.1.le hy1
    have hβy' : β * y ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hβ.1.le hy0, hβy.trans hβ.2.le⟩
    simp only at hy
    constructor
    · by_contra hlt
      push_neg at hlt
      have hyδ : dist y 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0]
        linarith [min_le_left (δ₀ / 2) (1 / 2)]
      have := hδ₀' ⟨hy0, hy1⟩ hyδ
      rw [Real.dist_eq, hf.map_zero] at this
      have hfy : 1 / a < f y := by
        have := (abs_lt.mp this).1
        linarith
      have h2 : f (β * y) ≤ 1 := hf.le_one hβy'
      have h3 : 1 < α * f y :=
        calc 1 = a * (1 / a) := by field_simp
          _ < a * f y := mul_lt_mul_of_pos_left hfy ha0
          _ ≤ α * f y := mul_le_mul_of_nonneg_right hαa hfy0
      linarith
    · by_contra hlt
      push_neg at hlt
      have hyδ : dist y 1 < δ₁ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - y)]
        linarith [le_max_left (1 - δ₁ / 2) (1 / 2)]
      have := hδ₁' ⟨hy0, hy1⟩ hyδ
      rw [Real.dist_eq, hf.map_one, sub_zero, abs_of_nonneg hfy0] at this
      have h2 : f β ≤ f (β * y) := hf.strictAntiOn.antitoneOn hβy' ⟨hβ.1.le, hβ.2.le⟩ hβy
      have h3 : α * f y < f β :=
        calc α * f y ≤ b * f y := mul_le_mul_of_nonneg_right hαb hfy0
          _ < b * (f β / b) := mul_lt_mul_of_pos_left this hb0
          _ = f β := by field_simp
      linarith

/-- `y ↦ f (β * y) / f y` is Lipschitz on compact subintervals of `(0, 1)`. -/
theorem exists_lipschitzOnWith_ratio {β c d : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) (hc : 0 < c)
    (hcd : c ≤ d) (hd : d < 1) :
    ∃ L : NNReal, LipschitzOnWith L (fun y => f (β * y) / f y) (Icc c d) := by
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith_Icc (mul_pos hβ.1 hc) hd
  have hm : 0 < f d := hf.pos ⟨by linarith, hd⟩
  set m := f d with hm_def
  have hLnn : (0 : ℝ) ≤ L := L.coe_nonneg
  refine ⟨(2 * L / m ^ 2).toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)]
  have hβc : β * c ≤ c := mul_le_of_le_one_left hc.le hβ.2.le
  have hx0 : 0 ≤ x := hc.le.trans hx.1
  have hy0 : 0 ≤ y := hc.le.trans hy.1
  have hx' : x ∈ Icc (β * c) d := ⟨hβc.trans hx.1, hx.2⟩
  have hy' : y ∈ Icc (β * c) d := ⟨hβc.trans hy.1, hy.2⟩
  have hβx : β * x ∈ Icc (β * c) d :=
    ⟨mul_le_mul_of_nonneg_left hx.1 hβ.1.le, (mul_le_of_le_one_left hx0 hβ.2.le).trans hx.2⟩
  have hβy : β * y ∈ Icc (β * c) d :=
    ⟨mul_le_mul_of_nonneg_left hy.1 hβ.1.le, (mul_le_of_le_one_left hy0 hβ.2.le).trans hy.2⟩
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, hx.2.trans hd.le⟩
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hy0, hy.2.trans hd.le⟩
  have hβy01 : β * y ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hβ.1.le hy0, hβy.2.trans hd.le⟩
  have hfx : m ≤ f x := hf.strictAntiOn.antitoneOn hx01 ⟨by linarith, hd.le⟩ hx.2
  have hfy : m ≤ f y := hf.strictAntiOn.antitoneOn hy01 ⟨by linarith, hd.le⟩ hy.2
  have hfy1 : f y ≤ 1 := hf.le_one hy01
  have hfβy1 : f (β * y) ≤ 1 := hf.le_one hβy01
  have hfy0 : 0 ≤ f y := hf.nonneg hy01
  have hfβy0 : 0 ≤ f (β * y) := hf.nonneg hβy01
  -- Lipschitz estimates for the two pieces
  have h1 : |f (β * x) - f (β * y)| ≤ L * |x - y| := by
    have := hL.dist_le_mul _ hβx _ hβy
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hβ.1] at this
    calc |f (β * x) - f (β * y)| ≤ L * (β * |x - y|) := this
      _ ≤ L * |x - y| := by
        apply mul_le_mul_of_nonneg_left _ hLnn
        exact mul_le_of_le_one_left (abs_nonneg _) hβ.2.le
  have h2 : |f y - f x| ≤ L * |x - y| := by
    have := hL.dist_le_mul _ hy' _ hx'
    rwa [Real.dist_eq, Real.dist_eq, abs_sub_comm y x] at this
  -- the quotient estimate
  rw [Real.dist_eq, Real.dist_eq]
  have hfx0 : f x ≠ 0 := by linarith
  have hfy0' : f y ≠ 0 := by linarith
  rw [div_sub_div _ _ hfx0 hfy0', abs_div, div_le_iff₀ (abs_pos.mpr (mul_ne_zero hfx0 hfy0'))]
  have hprod : m ^ 2 ≤ |f x * f y| := by
    rw [abs_of_pos (mul_pos (by linarith) (by linarith))]
    nlinarith
  have hnum : |f (β * x) * f y - f x * f (β * y)| ≤ 2 * L * |x - y| := by
    calc |f (β * x) * f y - f x * f (β * y)|
        = |(f (β * x) - f (β * y)) * f y + f (β * y) * (f y - f x)| := by congr 1; ring
      _ ≤ |(f (β * x) - f (β * y)) * f y| + |f (β * y) * (f y - f x)| := abs_add_le _ _
      _ = |f (β * x) - f (β * y)| * |f y| + |f (β * y)| * |f y - f x| := by
          rw [abs_mul, abs_mul]
      _ ≤ (L * |x - y|) * 1 + 1 * (L * |x - y|) := by
          apply add_le_add
          · exact mul_le_mul h1 (by rw [abs_of_nonneg hfy0]; exact hfy1) (abs_nonneg _)
              (by positivity)
          · exact mul_le_mul (by rw [abs_of_nonneg hfβy0]; exact hfβy1) h2 (abs_nonneg _)
              zero_le_one
      _ = 2 * L * |x - y| := by ring
  calc |f (β * x) * f y - f x * f (β * y)| ≤ 2 * L * |x - y| := hnum
    _ = 2 * L / m ^ 2 * |x - y| * m ^ 2 := by field_simp
    _ ≤ 2 * L / m ^ 2 * |x - y| * |f x * f y| := by
        apply mul_le_mul_of_nonneg_left hprod
        positivity

/-- **Main theorem.** Every open set of parameters contains a parameter for which the
equation `p.1 * f y = f (p.2 * y)` has finitely many solutions on `[0, 1]`. -/
theorem exists_finite_solutions {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : (U ∩ Param).Nonempty) :
    ∃ p ∈ U ∩ Param, (solutions f p).Finite := by
  obtain ⟨⟨α₀, β⟩, hpU, hpP⟩ := hne
  have hpP' : 1 < α₀ ∧ 0 < β ∧ β < 1 := mem_Param.mp hpP
  obtain ⟨hα₀, hβ0, hβ1⟩ := hpP'
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hpU
  -- an interval of `α`'s around `α₀`, inside the ball and inside `(1, ∞)`
  set r := min ε ((α₀ - 1) / 2) with hr
  have hr0 : 0 < r := lt_min hε (by linarith)
  have hrε : r ≤ ε := min_le_left _ _
  have hr1 : r ≤ (α₀ - 1) / 2 := min_le_right _ _
  have ha : 1 < α₀ - r := by linarith
  have hab : α₀ - r ≤ α₀ + r := by linarith
  obtain ⟨c, d, hc, hcd, hd, hsol⟩ := hf.exists_Icc_solutions_subset ha hab ⟨hβ0, hβ1⟩
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith_ratio ⟨hβ0, hβ1⟩ hc hcd hd
  have hnull := volume_infinite_level_eq_zero isCompact_Icc hL
  -- a null set cannot contain the interval of `α`'s
  have hnot : ¬ Ioo (α₀ - r) (α₀ + r) ⊆
      {α : ℝ | (Icc c d ∩ (fun y => f (β * y) / f y) ⁻¹' {α}).Infinite} := by
    intro hsub
    have hle := measure_mono (μ := volume) hsub
    rw [hnull, Real.volume_Ioo] at hle
    have h0 : ENNReal.ofReal (α₀ + r - (α₀ - r)) = 0 := le_antisymm hle (zero_le _)
    rw [ENNReal.ofReal_eq_zero] at h0
    linarith
  obtain ⟨α, hαI, hαgood⟩ := not_subset.mp hnot
  simp only [mem_setOf_eq, not_infinite] at hαgood
  refine ⟨(α, β), ⟨hball ?_, mem_Param.mpr ⟨ha.trans hαI.1, hβ0, hβ1⟩⟩, ?_⟩
  · rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    have : |α - α₀| < r := abs_sub_lt_iff.mpr ⟨by linarith [hαI.2], by linarith [hαI.1]⟩
    exact max_lt (this.trans_le hrε) hε
  · apply hαgood.subset
    intro y hy
    have hyK : y ∈ Icc c d := hsol α ⟨hαI.1.le, hαI.2.le⟩ hy
    refine ⟨hyK, ?_⟩
    obtain ⟨⟨hy0, hy1⟩, hy⟩ := hy
    have hfy : 0 < f y := hf.pos ⟨hy0, by linarith [hyK.2]⟩
    simp only [mem_preimage, mem_singleton_iff]
    rw [div_eq_iff hfy.ne']
    simpa using hy.symm

/-- **Density form.** Good parameters are dense in `Param`. -/
theorem exists_finite_solutions_near {p : ℝ × ℝ} (hp : p ∈ Param) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ Param, dist q p < ε ∧ (solutions f q).Finite := by
  obtain ⟨q, ⟨hqU, hqP⟩, hfin⟩ :=
    hf.exists_finite_solutions Metric.isOpen_ball ⟨p, Metric.mem_ball_self hε, hp⟩
  exact ⟨q, hqP, Metric.mem_ball.mp hqU, hfin⟩

end IsProfile

/-! ### Subdifferentials, transversality, and generic transversality

For a convex `f` on `[0, 1]` the *subdifferential* `subdiff f y` is the set of slopes of
supporting lines at `y`. An intersection `y` of the curves `α f` and `f (β ·)` is *transversal*
if the scaled subdifferentials `α • ∂f(y)` and `β • ∂f(βy)` are disjoint.

Main results:

* `IsProfile.finite_of_transversal`: transversal intersections are isolated, so a parameter with
  only transversal intersections has finitely many of them;
* `IsProfile.exists_open_transversal`: every open set of parameters contains a nonempty open set
  of parameters with only transversal intersections. Equivalently
  (`IsProfile.Param_subset_closure_interior_transversalParams`) the transversal parameters
  contain an open dense subset of `Param`.

The proof is the Sard argument of the previous section with the derivative of
`y ↦ f (β y) / f y` replaced by the *mixed* subdifferential condition `IsCritical`: some
`a ∈ ∂f(βy)` and `b ∈ ∂f(y)`, chosen independently, satisfy `β a f y = f (β y) b`. Unlike the
derivative, this condition has a closed graph, which makes the set of good parameters open.
No differentiability of `f` is assumed. -/

/-- A closed subset of a compact set all of whose points are isolated is finite. -/
theorem finite_of_isolated {s K : Set ℝ} (hK : IsCompact K) (hs : IsClosed s) (hsK : s ⊆ K)
    (hiso : ∀ y ∈ s, ∀ᶠ z in 𝓝[≠] y, z ∉ s) : s.Finite := by
  by_contra hinf
  have hinf' : s.Infinite := hinf
  obtain ⟨y, -, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hK hsK
  have hy : y ∈ s := hs.closure_subset (mem_closure_iff_clusterPt.mpr hacc.clusterPt)
  have hfreq := accPt_iff_frequently.mp hacc
  have hev := eventually_nhdsWithin_iff.mp (hiso y hy)
  obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := (hfreq.and_eventually hev).exists
  exact hz3 hz1 hz2

/-- The image of a null set under a Lipschitz map is null. -/
theorem volume_image_eq_zero_of_lipschitzOnWith {F : ℝ → ℝ} {K s : Set ℝ} {L : NNReal}
    (hF : LipschitzOnWith L F K) (hs : s ⊆ K) (h : volume s = 0) : volume (F '' s) = 0 := by
  apply le_antisymm _ (zero_le _)
  calc volume (F '' s) = μH[1] (F '' s) := by rw [hausdorffMeasure_real]
    _ ≤ (L : ENNReal) ^ (1 : ℝ) * μH[1] s := (hF.mono hs).hausdorffMeasure_image_le zero_le_one
    _ = 0 := by rw [hausdorffMeasure_real, h, mul_zero]

theorem mem_interior_Icc01 {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : y ∈ interior (Icc (0 : ℝ) 1) := by
  rw [interior_Icc]
  exact hy

/-- `ratio f (y, β) = f (β * y) / f y`. -/
noncomputable def ratio (f : ℝ → ℝ) (q : ℝ × ℝ) : ℝ := f (q.2 * q.1) / f q.1

/-- The subdifferential of `f : [0, 1] → ℝ` at `y`: the slopes of supporting lines. -/
def subdiff (f : ℝ → ℝ) (y : ℝ) : Set ℝ := {t | ∀ z ∈ Icc (0 : ℝ) 1, f y + t * (z - y) ≤ f z}

/-- `(y, β)` is a *critical pair*: for some subgradients `a ∈ ∂f(βy)`, `b ∈ ∂f(y)` the "derivative"
`β a f y - f (β y) b` of `y ↦ f (β y) / f y` vanishes. -/
def IsCritical (f : ℝ → ℝ) (y β : ℝ) : Prop :=
  ∃ a ∈ subdiff f (β * y), ∃ b ∈ subdiff f y, β * a * f y = f (β * y) * b

/-- All intersections for the parameter `p` are transversal: at every solution `y`, the scaled
subdifferentials `p.1 • ∂f(y)` and `p.2 • ∂f(p.2 y)` are disjoint. -/
def Transversal (f : ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  ∀ y ∈ solutions f p, ∀ a ∈ subdiff f (p.2 * y), ∀ b ∈ subdiff f y, p.2 * a ≠ p.1 * b

open scoped Pointwise in
theorem transversal_iff_disjoint {f : ℝ → ℝ} {p : ℝ × ℝ} :
    Transversal f p ↔
      ∀ y ∈ solutions f p, Disjoint (p.1 • subdiff f y) (p.2 • subdiff f (p.2 * y)) := by
  refine forall₂_congr fun y _ => ?_
  rw [Set.disjoint_left]
  constructor
  · rintro h _ ⟨b, hb, rfl⟩ ⟨a, ha, hab⟩
    exact h a ha b hb hab
  · intro h a ha b hb hab
    exact h ⟨b, hb, rfl⟩ ⟨a, ha, hab⟩

/-- The transversal parameters. -/
def transversalParams (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | p ∈ Param ∧ Transversal f p}

namespace IsProfile

variable {f : ℝ → ℝ} (hf : IsProfile f)
include hf

/-! #### Subdifferentials of a profile -/

/-- The right derivative is a subgradient. -/
theorem rightDeriv_mem_subdiff {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    derivWithin f (Ioi y) y ∈ subdiff f y := by
  intro z hz
  rcases lt_trichotomy z y with h | rfl | h
  · have h1 := hf.convexOn.slope_le_leftDeriv_of_mem_interior hz (mem_interior_Icc01 hy) h
    have h2 := hf.convexOn.leftDeriv_le_rightDeriv_of_mem_interior (mem_interior_Icc01 hy)
    rw [slope_def_field] at h1
    have h3 := h1.trans h2
    rw [div_le_iff₀ (sub_pos.mpr h)] at h3
    have e : derivWithin f (Ioi y) y * (z - y) = -(derivWithin f (Ioi y) y * (y - z)) := by ring
    rw [e]
    linarith
  · simp
  · have h1 := hf.convexOn.rightDeriv_le_slope_of_mem_interior (mem_interior_Icc01 hy) hz h
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at h1
    linarith

/-- The left derivative is a subgradient. -/
theorem leftDeriv_mem_subdiff {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    derivWithin f (Iio y) y ∈ subdiff f y := by
  intro z hz
  rcases lt_trichotomy z y with h | rfl | h
  · have h1 := hf.convexOn.slope_le_leftDeriv_of_mem_interior hz (mem_interior_Icc01 hy) h
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at h1
    have e : derivWithin f (Iio y) y * (z - y) = -(derivWithin f (Iio y) y * (y - z)) := by ring
    rw [e]
    linarith
  · simp
  · have h1 := hf.convexOn.rightDeriv_le_slope_of_mem_interior (mem_interior_Icc01 hy) hz h
    have h2 := hf.convexOn.leftDeriv_le_rightDeriv_of_mem_interior (mem_interior_Icc01 hy)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at h1
    have h3 := mul_le_mul_of_nonneg_right h2 (sub_pos.mpr h).le
    linarith

/-- Subgradients at interior points are bounded: `-1 / y ≤ t ≤ 0`. -/
theorem subdiff_subset_Icc {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : subdiff f y ⊆ Icc (-1 / y) 0 := by
  intro t ht
  have h1 := ht 1 (right_mem_Icc.mpr zero_le_one)
  have h0 := ht 0 (left_mem_Icc.mpr zero_le_one)
  rw [hf.map_one] at h1
  rw [hf.map_zero] at h0
  have hfy : 0 ≤ f y := hf.nonneg ⟨hy.1.le, hy.2.le⟩
  constructor
  · rw [div_le_iff₀ hy.1]
    simp only [zero_sub, mul_neg] at h0
    linarith
  · by_contra hpos
    push_neg at hpos
    have := mul_pos hpos (sub_pos.mpr hy.2)
    linarith

omit hf in
/-- At a point of differentiability the subdifferential is `{deriv f y}`. -/
theorem eq_deriv_of_mem_subdiff {y t : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hd : DifferentiableAt ℝ f y)
    (ht : t ∈ subdiff f y) : t = deriv f y := by
  have h := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
  apply le_antisymm
  · have h' : Tendsto (slope f y) (𝓝[>] y) (𝓝 (deriv f y)) :=
      h.mono_left (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
    refine ge_of_tendsto h' ?_
    filter_upwards [Ioo_mem_nhdsGT hy.2] with z hz
    have := ht z ⟨by linarith [hz.1, hy.1], hz.2.le⟩
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hz.1)]
    linarith
  · have h' : Tendsto (slope f y) (𝓝[<] y) (𝓝 (deriv f y)) :=
      h.mono_left (nhdsWithin_mono _ fun z hz => ne_of_lt hz)
    refine le_of_tendsto h' ?_
    filter_upwards [Ioo_mem_nhdsLT hy.1] with z hz
    have := ht z ⟨hz.1.le, by linarith [hz.2, hy.2]⟩
    rw [slope_def_field, div_le_iff_of_neg (sub_neg.mpr hz.2)]
    linarith

/-! #### Transversal intersections are isolated -/

/-- If solutions accumulate at a solution `y`, then `(y, β)` is a critical pair. -/
theorem isCritical_of_frequently {p : ℝ × ℝ} (hp : p ∈ Param) {y : ℝ} (hy : y ∈ solutions f p)
    (hfreq : ∃ᶠ z in 𝓝[≠] y, z ∈ solutions f p) : IsCritical f y p.2 := by
  obtain ⟨hα, hβ0, hβ1⟩ := mem_Param.mp hp
  have hy01 : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hy.1.1 fun h => hf.zero_not_mem_solutions hp (h ▸ hy),
      lt_of_le_of_ne hy.1.2 fun h => hf.one_not_mem_solutions hp (h ▸ hy)⟩
  have hβy : p.2 * y ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hβ0 hy01.1, (mul_le_of_le_one_left hy01.1.le hβ1.le).trans_lt hy01.2⟩
  have hsol : p.1 * f y = f (p.2 * y) := hy.2
  -- the one-sided argument, for `S = Ioi` and `S = Iio`
  have key : ∀ (S : ℝ → Set ℝ) (a b : ℝ),
      HasDerivWithinAt f a (S (p.2 * y)) (p.2 * y) → HasDerivWithinAt f b (S y) y →
      MapsTo (fun z => p.2 * z) (S y) (S (p.2 * y)) → y ∉ S y → (𝓝[S y] y).NeBot →
      (∃ᶠ z in 𝓝[S y] y, z ∈ solutions f p) → p.2 * a = p.1 * b := by
    intro S a b ha hb hmaps hyS hne hfr
    have h1 : HasDerivWithinAt (fun z : ℝ => p.2 * z) p.2 (S y) y := by
      simpa using ((hasDerivAt_id y).const_mul p.2).hasDerivWithinAt
    have hΦ : HasDerivWithinAt (fun z => p.1 * f z - f (p.2 * z)) (p.1 * b - a * p.2) (S y) y :=
      (hb.const_mul p.1).sub (ha.comp y h1 hmaps)
    rw [hasDerivWithinAt_iff_tendsto_slope] at hΦ
    have hle : 𝓝[S y] y ≤ 𝓝[S y \ {y}] y :=
      nhdsWithin_mono _ fun z hz => ⟨hz, fun h => hyS (h ▸ hz)⟩
    have hT := hΦ.mono_left hle
    have hfr' : ∃ᶠ z in 𝓝[S y] y,
        slope (fun z => p.1 * f z - f (p.2 * z)) y z = (fun _ => (0 : ℝ)) z := by
      refine hfr.mono fun z hz => ?_
      have hz' : p.1 * f z = f (p.2 * z) := hz.2
      simp [slope_def_field, hz', hsol]
    haveI := hne
    have := tendsto_nhds_unique_of_frequently_eq hT tendsto_const_nhds hfr'
    linear_combination -this
  rw [← nhdsLT_sup_nhdsGT, Filter.frequently_sup] at hfreq
  rcases hfreq with hfr | hfr
  · refine ⟨derivWithin f (Iio (p.2 * y)) (p.2 * y), hf.leftDeriv_mem_subdiff hβy,
      derivWithin f (Iio y) y, hf.leftDeriv_mem_subdiff hy01, ?_⟩
    have := key (fun x => Iio x) _ _
      (hf.convexOn.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc01 hβy))
      (hf.convexOn.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc01 hy01))
      (fun z hz => mul_lt_mul_of_pos_left hz hβ0) (lt_irrefl y) inferInstance hfr
    rw [← hsol]
    linear_combination f y * this
  · refine ⟨derivWithin f (Ioi (p.2 * y)) (p.2 * y), hf.rightDeriv_mem_subdiff hβy,
      derivWithin f (Ioi y) y, hf.rightDeriv_mem_subdiff hy01, ?_⟩
    have := key (fun x => Ioi x) _ _
      (hf.convexOn.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc01 hβy))
      (hf.convexOn.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc01 hy01))
      (fun z hz => mul_lt_mul_of_pos_left hz hβ0) (lt_irrefl y) inferInstance hfr
    rw [← hsol]
    linear_combination f y * this

theorem isClosed_solutions {p : ℝ × ℝ} (hp : p ∈ Param) : IsClosed (solutions f p) := by
  have : solutions f p = Icc 0 1 ∩ (fun y => p.1 * f y - f (p.2 * y)) ⁻¹' {0} := by
    ext y
    simp [solutions, sub_eq_zero]
  rw [this]
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_Icc isClosed_singleton
  have h1 : ContinuousOn (fun y => f (p.2 * y)) (Icc 0 1) :=
    hf.continuousOn.comp (by fun_prop : Continuous fun y : ℝ => p.2 * y).continuousOn
      (fun y hy => mul_mem_Icc_of_mem_Param hp hy)
  exact (continuousOn_const.mul hf.continuousOn).sub h1

/-- A parameter with only transversal intersections has finitely many of them. -/
theorem finite_of_transversal {p : ℝ × ℝ} (hp : p ∈ Param) (ht : Transversal f p) :
    (solutions f p).Finite := by
  refine finite_of_isolated isCompact_Icc (hf.isClosed_solutions hp) (fun y hy => hy.1)
    fun y hy => ?_
  by_contra h
  rw [Filter.not_eventually] at h
  simp only [not_not] at h
  obtain ⟨a, ha, b, hb, hab⟩ := hf.isCritical_of_frequently hp hy h
  have hy1 : y < 1 := lt_of_le_of_ne hy.1.2 fun h1 => hf.one_not_mem_solutions hp (h1 ▸ hy)
  have hfy : 0 < f y := hf.pos ⟨hy.1.1, hy1⟩
  apply ht y hy a ha b hb
  have hsol : p.1 * f y = f (p.2 * y) := hy.2
  rw [← hsol] at hab
  exact mul_right_cancel₀ hfy.ne' (show p.2 * a * f y = p.1 * b * f y by linear_combination hab)

/-! #### Analytic ingredients: continuity, compactness, Sard -/

theorem continuousOn_ratio {c d β₁ β₂ : ℝ} (hc : 0 < c) (hd : d < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : β₂ < 1) : ContinuousOn (ratio f) (Icc c d ×ˢ Icc β₁ β₂) := by
  have hm1 : MapsTo (fun q : ℝ × ℝ => q.2 * q.1) (Icc c d ×ˢ Icc β₁ β₂) (Icc 0 1) := by
    intro q hq
    have h1 : 0 ≤ q.1 := by linarith [hq.1.1]
    exact ⟨mul_nonneg (by linarith [hq.2.1]) h1,
      (mul_le_of_le_one_left h1 (by linarith [hq.2.2])).trans (by linarith [hq.1.2])⟩
  have hm2 : MapsTo (fun q : ℝ × ℝ => q.1) (Icc c d ×ˢ Icc β₁ β₂) (Icc 0 1) :=
    fun q hq => ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
  have h0 : ∀ q ∈ Icc c d ×ˢ Icc β₁ β₂, f q.1 ≠ 0 := fun q hq =>
    (hf.pos ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩).ne'
  show ContinuousOn (fun q : ℝ × ℝ => f (q.2 * q.1) / f q.1) _
  exact (hf.continuousOn.comp (by fun_prop : Continuous fun q : ℝ × ℝ => q.2 * q.1).continuousOn
    hm1).div (hf.continuousOn.comp continuous_fst.continuousOn hm2) h0

/-- Solutions for parameters in a compact box lie in a fixed compact subinterval of `(0, 1)`. -/
theorem exists_Icc_solutions_subset' {a b β₁ β₂ : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ ≤ β₂) (hβ₂ : β₂ < 1) :
    ∃ c d : ℝ, 0 < c ∧ c ≤ d ∧ d < 1 ∧
      ∀ α ∈ Icc a b, ∀ β ∈ Icc β₁ β₂, solutions f (α, β) ⊆ Icc c d := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h0 := hf.continuousOn 0 (left_mem_Icc.mpr zero_le_one)
  rw [Metric.continuousWithinAt_iff] at h0
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := h0 (1 - 1 / a)
    (by have : 1 / a < 1 := (div_lt_one ha0).mpr ha; linarith)
  have h1 := hf.continuousOn 1 (right_mem_Icc.mpr zero_le_one)
  rw [Metric.continuousWithinAt_iff] at h1
  have hfβ : 0 < f β₂ := hf.pos ⟨by linarith, hβ₂⟩
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := h1 (f β₂ / b) (div_pos hfβ hb0)
  refine ⟨min (δ₀ / 2) (1 / 2), max (1 - δ₁ / 2) (1 / 2), lt_min (half_pos hδ₀) (by norm_num),
    (min_le_right _ _).trans (le_max_right _ _), ?_, ?_⟩
  · apply max_lt <;> linarith
  · rintro α ⟨hαa, hαb⟩ β ⟨hβ₁', hβ₂'⟩ y ⟨⟨hy0, hy1⟩, hy⟩
    have hβ0 : 0 < β := hβ₁.trans_le hβ₁'
    have hβ1 : β < 1 := hβ₂'.trans_lt hβ₂
    have hfy0 : 0 ≤ f y := hf.nonneg ⟨hy0, hy1⟩
    have hβy : β * y ≤ β := mul_le_of_le_one_right hβ0.le hy1
    have hβy' : β * y ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hβ0.le hy0, hβy.trans hβ1.le⟩
    simp only at hy
    constructor
    · by_contra hlt
      push_neg at hlt
      have hyδ : dist y 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0]
        linarith [min_le_left (δ₀ / 2) (1 / 2)]
      have := hδ₀' ⟨hy0, hy1⟩ hyδ
      rw [Real.dist_eq, hf.map_zero] at this
      have hfy : 1 / a < f y := by
        have := (abs_lt.mp this).1
        linarith
      have h2 : f (β * y) ≤ 1 := hf.le_one hβy'
      have h3 : 1 < α * f y :=
        calc 1 = a * (1 / a) := by field_simp
          _ < a * f y := mul_lt_mul_of_pos_left hfy ha0
          _ ≤ α * f y := mul_le_mul_of_nonneg_right hαa hfy0
      linarith
    · by_contra hlt
      push_neg at hlt
      have hyδ : dist y 1 < δ₁ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - y)]
        linarith [le_max_left (1 - δ₁ / 2) (1 / 2)]
      have := hδ₁' ⟨hy0, hy1⟩ hyδ
      rw [Real.dist_eq, hf.map_one, sub_zero, abs_of_nonneg hfy0] at this
      have h2 : f β₂ ≤ f (β * y) :=
        hf.strictAntiOn.antitoneOn hβy' ⟨by linarith, hβ₂.le⟩ (hβy.trans hβ₂')
      have h3 : α * f y < f β₂ :=
        calc α * f y ≤ b * f y := mul_le_mul_of_nonneg_right hαb hfy0
          _ < b * (f β₂ / b) := mul_lt_mul_of_pos_left this hb0
          _ = f β₂ := by field_simp
      linarith

/-- The critical pairs in a compact box form a compact set. This is where the closed graph of
the subdifferential is used; the subdifferential conditions are written with the clamped `f`,
which is continuous on all of `ℝ`, so that they define closed sets. -/
theorem isCompact_critical {c d β₁ β₂ : ℝ} (hc : 0 < c) (hd : d < 1) (hβ₁ : 0 < β₁)
    (hβ₂ : β₂ < 1) : IsCompact {q ∈ Icc c d ×ˢ Icc β₁ β₂ | IsCritical f q.1 q.2} := by
  set K : Set (ℝ × ℝ) := Icc c d ×ˢ Icc β₁ β₂ with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set M : ℝ := 1 / (β₁ * c) with hM
  have hcont : Continuous (clampF f) := hf.continuous_clampF
  set T : Set ((ℝ × ℝ) × ℝ × ℝ) :=
    (Prod.fst ⁻¹' K) ∩ ((fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.1) ⁻¹' Icc (-M) 0) ∩
      ((fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.2) ⁻¹' Icc (-M) 0) ∩
      (⋂ z ∈ Icc (0 : ℝ) 1, {x : (ℝ × ℝ) × ℝ × ℝ |
        clampF f (x.1.2 * x.1.1) + x.2.1 * (z - x.1.2 * x.1.1) ≤ clampF f z}) ∩
      (⋂ z ∈ Icc (0 : ℝ) 1, {x : (ℝ × ℝ) × ℝ × ℝ |
        clampF f x.1.1 + x.2.2 * (z - x.1.1) ≤ clampF f z}) ∩
      {x : (ℝ × ℝ) × ℝ × ℝ | x.1.2 * x.2.1 * clampF f x.1.1 = clampF f (x.1.2 * x.1.1) * x.2.2}
    with hT
  have hTclosed : IsClosed T := by
    have hA : IsClosed (Prod.fst ⁻¹' K : Set ((ℝ × ℝ) × ℝ × ℝ)) :=
      hKc.isClosed.preimage continuous_fst
    have hB : IsClosed ((fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.1) ⁻¹' Icc (-M) 0) :=
      isClosed_Icc.preimage (by fun_prop)
    have hC : IsClosed ((fun x : (ℝ × ℝ) × ℝ × ℝ => x.2.2) ⁻¹' Icc (-M) 0) :=
      isClosed_Icc.preimage (by fun_prop)
    have hD : IsClosed (⋂ z ∈ Icc (0 : ℝ) 1, {x : (ℝ × ℝ) × ℝ × ℝ |
        clampF f (x.1.2 * x.1.1) + x.2.1 * (z - x.1.2 * x.1.1) ≤ clampF f z}) :=
      isClosed_biInter fun z _ => isClosed_le (by fun_prop) continuous_const
    have hE : IsClosed (⋂ z ∈ Icc (0 : ℝ) 1, {x : (ℝ × ℝ) × ℝ × ℝ |
        clampF f x.1.1 + x.2.2 * (z - x.1.1) ≤ clampF f z}) :=
      isClosed_biInter fun z _ => isClosed_le (by fun_prop) continuous_const
    have hF : IsClosed {x : (ℝ × ℝ) × ℝ × ℝ |
        x.1.2 * x.2.1 * clampF f x.1.1 = clampF f (x.1.2 * x.1.1) * x.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact ((((hA.inter hB).inter hC).inter hD).inter hE).inter hF
  have hTsub : T ⊆ K ×ˢ (Icc (-M) 0 ×ˢ Icc (-M) 0) := fun x hx =>
    ⟨hx.1.1.1.1.1, hx.1.1.1.1.2, hx.1.1.1.2⟩
  have hTc : IsCompact T :=
    (hKc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hTclosed hTsub
  have hfst : Prod.fst '' T = {q ∈ K | IsCritical f q.1 q.2} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨⟨⟨⟨⟨hxK, -⟩, -⟩, hxa⟩, hxb⟩, hxe⟩ := hx
      have hq1 : x.1.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hxK.1.1], by linarith [hxK.1.2]⟩
      have hq2 : x.1.2 * x.1.1 ∈ Icc (0 : ℝ) 1 :=
        ⟨mul_nonneg (by linarith [hxK.2.1]) hq1.1,
          (mul_le_of_le_one_left hq1.1 (by linarith [hxK.2.2])).trans hq1.2⟩
      refine ⟨hxK, x.2.1, ?_, x.2.2, ?_, ?_⟩
      · intro z hz
        have := mem_iInter₂.mp hxa z hz
        simpa only [mem_setOf_eq, clampF_eq hq2, clampF_eq hz] using this
      · intro z hz
        have := mem_iInter₂.mp hxb z hz
        simpa only [mem_setOf_eq, clampF_eq hq1, clampF_eq hz] using this
      · simpa only [mem_setOf_eq, clampF_eq hq1, clampF_eq hq2] using hxe
    · rintro ⟨hqK, a, ha, b, hb, hab⟩
      have hq1 : q.1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hqK.1.1], by linarith [hqK.1.2]⟩
      have hq2 : q.2 * q.1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨mul_pos (by linarith [hqK.2.1]) hq1.1,
          (mul_le_of_le_one_left hq1.1.le (by linarith [hqK.2.2])).trans_lt hq1.2⟩
      have hbc : β₁ * c ≤ q.2 * q.1 :=
        mul_le_mul hqK.2.1 hqK.1.1 hc.le (by linarith [hqK.2.1])
      have hbc' : β₁ * c ≤ q.1 :=
        hbc.trans (mul_le_of_le_one_left hq1.1.le (by linarith [hqK.2.2]))
      have hM1 : -M ≤ -1 / (q.2 * q.1) := by
        rw [hM, neg_div, neg_le_neg_iff]
        exact one_div_le_one_div_of_le (mul_pos hβ₁ hc) hbc
      have hM2 : -M ≤ -1 / q.1 := by
        rw [hM, neg_div, neg_le_neg_iff]
        exact one_div_le_one_div_of_le (mul_pos hβ₁ hc) hbc'
      have ha' := hf.subdiff_subset_Icc hq2 ha
      have hb' := hf.subdiff_subset_Icc hq1 hb
      refine ⟨(q, a, b), ⟨⟨⟨⟨⟨hqK, ⟨hM1.trans ha'.1, ha'.2⟩⟩, ⟨hM2.trans hb'.1, hb'.2⟩⟩, ?_⟩,
        ?_⟩, ?_⟩, rfl⟩
      · exact mem_iInter₂.mpr fun z hz => by
          simpa only [mem_setOf_eq, clampF_eq (Ioo_subset_Icc_self hq2), clampF_eq hz]
            using ha z hz
      · exact mem_iInter₂.mpr fun z hz => by
          simpa only [mem_setOf_eq, clampF_eq (Ioo_subset_Icc_self hq1), clampF_eq hz]
            using hb z hz
      · simpa only [mem_setOf_eq, clampF_eq (Ioo_subset_Icc_self hq1),
          clampF_eq (Ioo_subset_Icc_self hq2)] using hab
  rw [← hfst]
  exact hTc.image continuous_fst

/-- **Sard for one slice.** For fixed `β₀`, the values `f (β₀ y) / f y` at critical `y` form a null
set. At points where `f` is differentiable (at `y` and at `β₀ y`) this is Sard's lemma; the
remaining points form a null set by Rademacher's theorem, and their image is null because
`y ↦ f (β₀ y) / f y` is Lipschitz. -/
theorem volume_image_critical_slice {c d β₀ : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hd : d < 1)
    (hβ₀ : β₀ ∈ Ioo (0 : ℝ) 1) :
    volume ((fun y => ratio f (y, β₀)) '' {y ∈ Icc c d | IsCritical f y β₀}) = 0 := by
  set F₀ : ℝ → ℝ := fun y => ratio f (y, β₀) with hF₀
  set S : Set ℝ := {y ∈ Icc c d | IsCritical f y β₀} with hS
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith_ratio hβ₀ hc hcd hd
  set D : Set ℝ := {y | DifferentiableAt ℝ f y ∧ DifferentiableAt ℝ f (β₀ * y)} with hD
  -- Sard on the differentiable critical points
  have h1 : volume (F₀ '' (S ∩ D)) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (f' := fun _ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (0 : ℝ)) ?_ ?_
    · rintro y ⟨⟨hyK, a, ha, b, hb, hab⟩, hdy, hdβy⟩
      have hy01 : y ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hyK.1], by linarith [hyK.2]⟩
      have hβy : β₀ * y ∈ Ioo (0 : ℝ) 1 :=
        ⟨mul_pos hβ₀.1 hy01.1, (mul_le_of_le_one_left hy01.1.le hβ₀.2.le).trans_lt hy01.2⟩
      rw [eq_deriv_of_mem_subdiff hβy hdβy ha, eq_deriv_of_mem_subdiff hy01 hdy hb] at hab
      have hfy : f y ≠ 0 := (hf.pos ⟨hy01.1.le, hy01.2⟩).ne'
      have h3 : HasDerivAt (fun y : ℝ => β₀ * y) β₀ y := by
        simpa using (hasDerivAt_id y).const_mul β₀
      have h4 : HasDerivAt (fun y => f (β₀ * y)) (deriv f (β₀ * y) * β₀) y :=
        hdβy.hasDerivAt.comp y h3
      have h5 := h4.div hdy.hasDerivAt hfy
      have h6 : HasDerivAt F₀ 0 y := by
        refine h5.congr_deriv ?_
        rw [div_eq_zero_iff]
        left
        linear_combination hab
      exact h6.hasDerivWithinAt.hasFDerivWithinAt
    · intro y _
      simp [ContinuousLinearMap.det]
  -- Rademacher: the non-differentiability set is null
  have hc'c : β₀ * c / 2 < c := by nlinarith [mul_lt_mul_of_pos_right hβ₀.2 hc]
  have hdd' : d < (1 + d) / 2 := by linarith
  obtain ⟨L', hL'⟩ := hf.exists_lipschitzOnWith_Icc (div_pos (mul_pos hβ₀.1 hc) two_pos)
    (by linarith : (1 + d) / 2 < 1)
  have hN : volume {x | x ∈ Ioo (β₀ * c / 2) ((1 + d) / 2) ∧ ¬ DifferentiableAt ℝ f x} = 0 := by
    have := hL'.ae_differentiableWithinAt_of_mem_real
    rw [ae_iff] at this
    refine measure_mono_null ?_ this
    rintro x ⟨hx, hnd⟩
    simp only [mem_setOf_eq, Classical.not_imp]
    exact ⟨⟨hx.1.le, hx.2.le⟩, fun hd => hnd (hd.differentiableAt (Icc_mem_nhds hx.1 hx.2))⟩
  have hN1 : volume {y | y ∈ Icc c d ∧ ¬ DifferentiableAt ℝ f y} = 0 := by
    refine measure_mono_null ?_ hN
    rintro y ⟨hy, hnd⟩
    exact ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, hnd⟩
  have hN2 : volume {y | y ∈ Icc c d ∧ ¬ DifferentiableAt ℝ f (β₀ * y)} = 0 := by
    have hpre := Real.volume_preimage_mul_left hβ₀.1.ne'
      {x | x ∈ Ioo (β₀ * c / 2) ((1 + d) / 2) ∧ ¬ DifferentiableAt ℝ f x}
    rw [hN, mul_zero] at hpre
    refine measure_mono_null ?_ hpre
    rintro y ⟨hy, hnd⟩
    refine ⟨⟨?_, ?_⟩, hnd⟩
    · show β₀ * c / 2 < β₀ * y
      nlinarith [mul_le_mul_of_nonneg_left hy.1 hβ₀.1.le, mul_pos hβ₀.1 hc]
    · show β₀ * y < (1 + d) / 2
      have h1 : β₀ * y ≤ y := mul_le_of_le_one_left (hc.le.trans hy.1) hβ₀.2.le
      linarith [hy.2]
  have h2 : volume (F₀ '' (S \ D)) = 0 := by
    refine volume_image_eq_zero_of_lipschitzOnWith hL (fun y hy => hy.1.1) ?_
    refine measure_mono_null ?_ (measure_union_null hN1 hN2)
    rintro y ⟨⟨hyK, -⟩, hyD⟩
    simp only [hD, mem_setOf_eq, not_and_or] at hyD
    rcases hyD with h | h
    · exact Or.inl ⟨hyK, h⟩
    · exact Or.inr ⟨hyK, h⟩
  apply le_antisymm _ (zero_le _)
  calc volume (F₀ '' S) = volume (F₀ '' (S ∩ D) ∪ F₀ '' (S \ D)) := by
        rw [← image_union, inter_union_diff]
    _ ≤ volume (F₀ '' (S ∩ D)) + volume (F₀ '' (S \ D)) := measure_union_le _ _
    _ = 0 := by rw [h1, h2, add_zero]

/-! #### Main theorems -/

/-- **Generic transversality.** Every open set of parameters contains a nonempty open set of
parameters all of whose intersections are transversal. -/
theorem exists_open_transversal {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : (U ∩ Param).Nonempty) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∩ Param ∧ ∀ p ∈ V, Transversal f p := by
  obtain ⟨⟨α₀, β₀⟩, hpU, hpP⟩ := hne
  obtain ⟨hα₀, hβ0, hβ1⟩ := mem_Param.mp hpP
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hpU
  -- a box of parameters around `(α₀, β₀)`
  set r := min ε ((α₀ - 1) / 2) with hr
  have hr0 : 0 < r := lt_min hε (by linarith)
  have hrε : r ≤ ε := min_le_left _ _
  have hr1 : r ≤ (α₀ - 1) / 2 := min_le_right _ _
  have ha : 1 < α₀ - r := by linarith
  have hab : α₀ - r ≤ α₀ + r := by linarith
  set β₁ := β₀ / 2 with hβ₁
  set β₂ := (β₀ + 1) / 2 with hβ₂
  have hβ₁0 : 0 < β₁ := half_pos hβ0
  have hβ₁₂ : β₁ ≤ β₂ := by linarith [hβ₁, hβ₂]
  have hβ₂1 : β₂ < 1 := by linarith [hβ₂]
  have hβ₀I : β₀ ∈ Ioo β₁ β₂ := ⟨by linarith [hβ₁], by linarith [hβ₂]⟩
  obtain ⟨c, d, hc, hcd, hd, hsol⟩ := hf.exists_Icc_solutions_subset' ha hab hβ₁0 hβ₁₂ hβ₂1
  set K : Set (ℝ × ℝ) := Icc c d ×ˢ Icc β₁ β₂ with hK
  have hratio : ContinuousOn (ratio f) K := hf.continuousOn_ratio hc hd hβ₁0 hβ₂1
  -- the critical pairs and the bad parameters
  set Z : Set (ℝ × ℝ) := {q ∈ K | IsCritical f q.1 q.2} with hZ
  have hZc : IsCompact Z := hf.isCompact_critical hc hd hβ₁0 hβ₂1
  set Bad : Set (ℝ × ℝ) := (fun q => (ratio f q, q.2)) '' Z with hBad
  have hBadc : IsClosed Bad :=
    (hZc.image_of_continuousOn
      ((hratio.mono fun q hq => hq.1).prodMk continuousOn_snd)).isClosed
  -- Sard at `β₀` gives a regular `α₁` near `α₀`
  have hnull := hf.volume_image_critical_slice hc hcd hd ⟨hβ0, hβ1⟩
  have hnot : ¬ Ioo (α₀ - r) (α₀ + r) ⊆
      (fun y => ratio f (y, β₀)) '' {y ∈ Icc c d | IsCritical f y β₀} := by
    intro hsub
    have hle := measure_mono (μ := volume) hsub
    rw [hnull, Real.volume_Ioo] at hle
    have h0 : ENNReal.ofReal (α₀ + r - (α₀ - r)) = 0 := le_antisymm hle (zero_le _)
    rw [ENNReal.ofReal_eq_zero] at h0
    linarith
  obtain ⟨α₁, hα₁I, hα₁⟩ := not_subset.mp hnot
  have hgood : (α₁, β₀) ∉ Bad := by
    rintro ⟨q, ⟨hqK, hqc⟩, hq⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨hq1, hq2⟩ := hq
    apply hα₁
    refine ⟨q.1, ⟨hqK.1, ?_⟩, ?_⟩
    · rw [← hq2]
      exact hqc
    · rw [← hq2]
      simpa using hq1
  -- the open set of good parameters
  set V : Set (ℝ × ℝ) := U ∩ (Ioo (α₀ - r) (α₀ + r) ×ˢ Ioo β₁ β₂) ∩ Badᶜ with hV
  have hVopen : IsOpen V := (hU.inter (isOpen_Ioo.prod isOpen_Ioo)).inter hBadc.isOpen_compl
  have hmemV : (α₁, β₀) ∈ V := by
    refine ⟨⟨hball ?_, ⟨hα₁I, hβ₀I⟩⟩, hgood⟩
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    have : |α₁ - α₀| < r := abs_sub_lt_iff.mpr ⟨by linarith [hα₁I.2], by linarith [hα₁I.1]⟩
    exact max_lt (this.trans_le hrε) hε
  refine ⟨V, hVopen, ⟨(α₁, β₀), hmemV⟩, ?_, ?_⟩
  · rintro ⟨α, β⟩ ⟨⟨hpU', ⟨hαI, hβI⟩⟩, -⟩
    exact ⟨hpU', mem_Param.mpr ⟨ha.trans hαI.1, hβ₁0.trans hβI.1, hβI.2.trans hβ₂1⟩⟩
  · rintro ⟨α, β⟩ ⟨⟨-, ⟨hαI, hβI⟩⟩, hnb⟩
    intro y hy a ha' b hb hab'
    have hab'' : β * a = α * b := hab'
    have hyK : y ∈ Icc c d := hsol α ⟨hαI.1.le, hαI.2.le⟩ β ⟨hβI.1.le, hβI.2.le⟩ hy
    have hfy : 0 < f y := hf.pos ⟨by linarith [hyK.1], by linarith [hyK.2]⟩
    have hsol' : α * f y = f (β * y) := hy.2
    apply hnb
    refine ⟨(y, β), ⟨⟨hyK, ⟨hβI.1.le, hβI.2.le⟩⟩, a, ha', b, hb, ?_⟩, ?_⟩
    · show β * a * f y = f (β * y) * b
      rw [← hsol']
      linear_combination f y * hab''
    · simp only [Prod.mk.injEq, ratio, and_true]
      rw [div_eq_iff hfy.ne']
      exact hsol'.symm

/-- Every open set of parameters contains a nonempty open set of parameters with finitely many
intersections. -/
theorem exists_open_finite_solutions {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hne : (U ∩ Param).Nonempty) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∩ Param ∧
      ∀ p ∈ V, (solutions f p).Finite := by
  obtain ⟨V, hVo, hVne, hVU, hVt⟩ := hf.exists_open_transversal hU hne
  exact ⟨V, hVo, hVne, hVU, fun p hp => hf.finite_of_transversal (hVU hp).2 (hVt p hp)⟩

/-- Near every parameter there is one with only transversal intersections. -/
theorem exists_transversal_near {p : ℝ × ℝ} (hp : p ∈ Param) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ Param, dist q p < ε ∧ Transversal f q := by
  obtain ⟨V, -, ⟨q, hq⟩, hVU, hVt⟩ :=
    hf.exists_open_transversal Metric.isOpen_ball ⟨p, Metric.mem_ball_self hε, hp⟩
  exact ⟨q, (hVU hq).2, Metric.mem_ball.mp (hVU hq).1, hVt q hq⟩

/-- The transversal parameters contain an open dense subset of `Param`. -/
theorem Param_subset_closure_interior_transversalParams :
    Param ⊆ closure (interior (transversalParams f)) := by
  intro p hp
  rw [_root_.mem_closure_iff]
  intro U hU hpU
  obtain ⟨V, hVo, ⟨q, hq⟩, hVU, hVt⟩ := hf.exists_open_transversal hU ⟨p, hpU, hp⟩
  refine ⟨q, (hVU hq).1, interior_maximal (fun x hx => ?_) hVo hq⟩
  exact (⟨(hVU hx).2, hVt x hx⟩ : x ∈ Param ∧ Transversal f x)

end IsProfile

end NeoTiling
