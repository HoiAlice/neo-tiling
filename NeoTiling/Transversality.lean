import NeoTiling.LevelCurves

/-!
# Transversality of level curves via superdifferentials

Limiting (Mordukhovich) normal cones and the Kruger–Ioffe transversality condition
`N_A(x₀) ∩ (-N_B(x₀)) = {0}` for two sets in `ℝ²`.

Part 1: for the graph of a convex function `φ` on `[a, b]` at an interior point `t₀`, the
limiting normal cone is the wedge `{λ (s, -1) : λ ≥ 0, s ∈ [φ'₋, φ'₊]}` together with the two
lines `ℝ (φ'₋, -1)` and `ℝ (φ'₊, -1)`. Consequently two graphs meeting at `t₀` are transversal
iff the subdifferential intervals `[φ'₋, φ'₊]` and `[ψ'₋, ψ'₊]` are disjoint.

Part 2: for strictly positive neoclassical `h, g` with `h x₀ = g x₀ = 1` at an interior point,
the level curves `h = 1`, `g = 1` are transversal iff the superdifferentials `∂h(x₀)`, `∂g(x₀)`
are disjoint.
-/

open Real Set Filter Topology

namespace NeoTiling

/-! ### Normal cones -/

/-- Fréchet (regular) normal cone of `A` at `x₀`. -/
def frechetNormal (A : Set (ℝ × ℝ)) (x₀ : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {v | ∀ ε > 0, ∀ᶠ x in 𝓝[A] x₀, ip v (x - x₀) ≤ ε * dist x x₀}

/-- Limiting (Mordukhovich) normal cone of `A` at `x₀`. -/
def limitingNormal (A : Set (ℝ × ℝ)) (x₀ : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {v | ∃ x : ℕ → ℝ × ℝ, ∃ w : ℕ → ℝ × ℝ, (∀ n, x n ∈ A) ∧
    (∀ n, w n ∈ frechetNormal A (x n)) ∧ Tendsto x atTop (𝓝 x₀) ∧ Tendsto w atTop (𝓝 v)}

/-- Transversality of a pair of sets at a common point (Kruger, Ioffe):
`N_A(x₀) ∩ (-N_B(x₀)) = {0}`. -/
def SetTransversal (A B : Set (ℝ × ℝ)) (x₀ : ℝ × ℝ) : Prop :=
  ∀ v, v ∈ limitingNormal A x₀ → -v ∈ limitingNormal B x₀ → v = 0

theorem frechetNormal_subset_limitingNormal {A : Set (ℝ × ℝ)} {x₀ : ℝ × ℝ} (hx : x₀ ∈ A) :
    frechetNormal A x₀ ⊆ limitingNormal A x₀ :=
  fun v hv => ⟨fun _ => x₀, fun _ => v, fun _ => hx, fun _ => hv, tendsto_const_nhds,
    tendsto_const_nhds⟩

theorem frechetNormal_smul {A : Set (ℝ × ℝ)} {x₀ v : ℝ × ℝ} (hv : v ∈ frechetNormal A x₀)
    {c : ℝ} (hc : 0 ≤ c) : (c * v.1, c * v.2) ∈ frechetNormal A x₀ := by
  intro ε hε
  rcases hc.eq_or_lt with rfl | hc
  · exact Eventually.of_forall fun x => by simp [ip]; positivity
  · filter_upwards [hv (ε / c) (by positivity)] with x hx
    have : ip (c * v.1, c * v.2) (x - x₀) = c * ip v (x - x₀) := by simp only [ip]; ring
    rw [this]
    calc c * ip v (x - x₀) ≤ c * (ε / c * dist x x₀) := mul_le_mul_of_nonneg_left hx hc.le
      _ = ε * dist x x₀ := by field_simp

theorem limitingNormal_smul {A : Set (ℝ × ℝ)} {x₀ v : ℝ × ℝ} (hv : v ∈ limitingNormal A x₀)
    {c : ℝ} (hc : 0 ≤ c) : (c * v.1, c * v.2) ∈ limitingNormal A x₀ := by
  obtain ⟨x, w, hxA, hw, hx, hwv⟩ := hv
  refine ⟨x, fun n => (c * (w n).1, c * (w n).2), hxA, fun n => frechetNormal_smul (hw n) hc, hx,
    ?_⟩
  exact (tendsto_const_nhds.mul ((continuous_fst.tendsto _).comp hwv)).prodMk_nhds
    (tendsto_const_nhds.mul ((continuous_snd.tendsto _).comp hwv))

/-! ### Graphs of convex functions -/

/-- Graph of `φ` over `[a, b]`. -/
def graphOn (φ : ℝ → ℝ) (a b : ℝ) : Set (ℝ × ℝ) := {x | x.1 ∈ Icc a b ∧ x.2 = φ x.1}

/-- Supporting slopes of `φ` at `t` relative to `[a, b]`. -/
def subdiffOn (φ : ℝ → ℝ) (a b t : ℝ) : Set ℝ := {s | ∀ z ∈ Icc a b, φ t + s * (z - t) ≤ φ z}

/-- The wedge `{λ (s, -1) : λ ≥ 0, s ∈ [d₋, d₊]}`. -/
def wedge (dL dR : ℝ) : Set (ℝ × ℝ) := {v | ∃ l ≥ (0 : ℝ), ∃ s ∈ Icc dL dR, v = (l * s, -l)}

/-- The line `ℝ (d, -1)`. -/
def nline (d : ℝ) : Set (ℝ × ℝ) := {v | ∃ m : ℝ, v = (m * d, -m)}

theorem mem_interior_Icc_of_mem_Ioo {a b t : ℝ} (ht : t ∈ Ioo a b) : t ∈ interior (Icc a b) := by
  rw [interior_Icc]
  exact ht

/-- Algebraic classification of a vector satisfying the two one-sided inequalities. -/
theorem mem_wedge_or_nline {dL dR : ℝ} (hd : dL ≤ dR) {v : ℝ × ℝ} (h1 : v.1 + v.2 * dR ≤ 0)
    (h2 : 0 ≤ v.1 + v.2 * dL) : v ∈ wedge dL dR ∪ nline dL ∪ nline dR := by
  rcases lt_trichotomy v.2 0 with hneg | hzero | hpos
  · left; left
    have hne : -v.2 ≠ 0 := neg_ne_zero.mpr hneg.ne
    refine ⟨-v.2, by linarith, v.1 / (-v.2), ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ (by linarith)]
      nlinarith
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
    · exact Prod.ext (mul_div_cancel₀ _ hne).symm (neg_neg _).symm
  · left; left
    refine ⟨0, le_rfl, dL, ⟨le_rfl, hd⟩, ?_⟩
    rw [hzero] at h1 h2
    ext <;> simp
    · linarith
    · exact hzero
  · have heq : dL = dR := le_antisymm hd (by nlinarith)
    right
    refine ⟨-v.2, ?_⟩
    rw [heq] at h2
    ext <;> simp
    linarith

section Graph

variable {φ : ℝ → ℝ} {a b : ℝ} (hφ : ConvexOn ℝ (Icc a b) φ)
include hφ

theorem continuousAt_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo a b) : ContinuousAt φ t :=
  hφ.continuousOn_interior.continuousAt (by rw [interior_Icc]; exact Ioo_mem_nhds ht.1 ht.2)

/-- The supporting slopes at an interior point form the interval `[φ'₋, φ'₊]`. -/
theorem mem_subdiffOn_iff {t s : ℝ} (ht : t ∈ Ioo a b) :
    s ∈ subdiffOn φ a b t ↔ derivWithin φ (Iio t) t ≤ s ∧ s ≤ derivWithin φ (Ioi t) t := by
  constructor
  · intro hs
    constructor
    · have h := hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)
      rw [hasDerivWithinAt_iff_tendsto_slope] at h
      have h' : Tendsto (slope φ t) (𝓝[<] t) (𝓝 (derivWithin φ (Iio t) t)) :=
        h.mono_left (nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_lt hz⟩)
      refine le_of_tendsto h' ?_
      filter_upwards [Ioo_mem_nhdsLT ht.1] with z hz
      have := hs z ⟨hz.1.le, by linarith [hz.2, ht.2]⟩
      rw [slope_def_field, div_le_iff_of_neg (sub_neg.mpr hz.2)]
      linarith
    · have h := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)
      rw [hasDerivWithinAt_iff_tendsto_slope] at h
      have h' : Tendsto (slope φ t) (𝓝[>] t) (𝓝 (derivWithin φ (Ioi t) t)) :=
        h.mono_left (nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_gt hz⟩)
      refine ge_of_tendsto h' ?_
      filter_upwards [Ioo_mem_nhdsGT ht.2] with z hz
      have := hs z ⟨by linarith [hz.1, ht.1], hz.2.le⟩
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hz.1)]
      linarith
  · rintro ⟨h1, h2⟩ z hz
    rcases lt_trichotomy z t with h | rfl | h
    · have := hφ.slope_le_leftDeriv_of_mem_interior hz (mem_interior_Icc_of_mem_Ioo ht) h
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at this
      have h3 := mul_le_mul_of_nonneg_right h1 (sub_pos.mpr h).le
      have e : s * (z - t) = -(s * (t - z)) := by ring
      rw [e]
      linarith
    · simp
    · have := hφ.rightDeriv_le_slope_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht) hz h
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at this
      have h3 := mul_le_mul_of_nonneg_right h2 (sub_pos.mpr h).le
      linarith

theorem leftDeriv_le_rightDeriv' {t : ℝ} (ht : t ∈ Ioo a b) :
    derivWithin φ (Iio t) t ≤ derivWithin φ (Ioi t) t :=
  hφ.leftDeriv_le_rightDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)

/-- As `t ↓ t₀` both one-sided derivatives tend to `φ'₊(t₀)`. -/
theorem tendsto_derivs_nhdsGT {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    Tendsto (fun t => derivWithin φ (Ioi t) t) (𝓝[>] t₀) (𝓝 (derivWithin φ (Ioi t₀) t₀)) ∧
    Tendsto (fun t => derivWithin φ (Iio t) t) (𝓝[>] t₀) (𝓝 (derivWithin φ (Ioi t₀) t₀)) := by
  set d := derivWithin φ (Ioi t₀) t₀ with hd
  have hcont := continuousAt_of_mem_Ioo hφ ht
  have hlow : ∀ᶠ t in 𝓝[>] t₀, d ≤ derivWithin φ (Iio t) t ∧
      derivWithin φ (Iio t) t ≤ derivWithin φ (Ioi t) t := by
    filter_upwards [Ioo_mem_nhdsGT ht.2] with t htI
    have htI' : t ∈ Ioo a b := ⟨by linarith [ht.1, htI.1], htI.2⟩
    have h1 := hφ.rightDeriv_le_slope_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)
      ⟨htI'.1.le, htI'.2.le⟩ htI.1
    have h2 := hφ.slope_le_leftDeriv_of_mem_interior ⟨ht.1.le, ht.2.le⟩
      (mem_interior_Icc_of_mem_Ioo htI') htI.1
    exact ⟨h1.trans h2, leftDeriv_le_rightDeriv' hφ htI'⟩
  have hup : ∀ c, d < c → ∀ᶠ t in 𝓝[>] t₀, derivWithin φ (Ioi t) t < c := by
    intro c hc
    have hsl := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)
    rw [hasDerivWithinAt_iff_tendsto_slope] at hsl
    have hsl' : Tendsto (slope φ t₀) (𝓝[>] t₀) (𝓝 d) :=
      hsl.mono_left (nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_gt hz⟩)
    have hev := hsl'.eventually_lt_const (show d < (c + d) / 2 by linarith)
    obtain ⟨t', hslt', ht'⟩ := (hev.and (Ioo_mem_nhdsGT ht.2)).exists
    have hcs : Tendsto (fun t => slope φ t t') (𝓝[>] t₀) (𝓝 (slope φ t₀ t')) := by
      have : Tendsto (fun t => (φ t' - φ t) / (t' - t)) (𝓝 t₀) (𝓝 ((φ t' - φ t₀) / (t' - t₀))) :=
        (tendsto_const_nhds.sub hcont.tendsto).div (tendsto_const_nhds.sub tendsto_id)
          (sub_ne_zero.mpr ht'.1.ne')
      rw [slope_def_field]
      exact (this.mono_left nhdsWithin_le_nhds).congr'
        (Eventually.of_forall fun t => (slope_def_field φ t t').symm)
    have hlt : slope φ t₀ t' < c := by linarith
    filter_upwards [hcs.eventually_lt_const hlt, Ioo_mem_nhdsGT ht'.1] with t h1 h2
    have htI' : t ∈ Ioo a b := ⟨by linarith [ht.1, h2.1], by linarith [h2.2, ht'.2]⟩
    have := hφ.rightDeriv_le_slope_of_mem_interior (mem_interior_Icc_of_mem_Ioo htI')
      ⟨by linarith [ht'.1, ht.1], ht'.2.le⟩ h2.2
    linarith
  constructor
  · rw [tendsto_order]
    constructor
    · intro c hc
      filter_upwards [hlow] with t ht'
      linarith [ht'.1, ht'.2]
    · intro c hc
      exact hup c hc
  · rw [tendsto_order]
    constructor
    · intro c hc
      filter_upwards [hlow] with t ht'
      linarith [ht'.1]
    · intro c hc
      filter_upwards [hup c hc, hlow] with t h1 h2
      linarith [h2.2]

/-- As `t ↑ t₀` both one-sided derivatives tend to `φ'₋(t₀)`. -/
theorem tendsto_derivs_nhdsLT {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    Tendsto (fun t => derivWithin φ (Ioi t) t) (𝓝[<] t₀) (𝓝 (derivWithin φ (Iio t₀) t₀)) ∧
    Tendsto (fun t => derivWithin φ (Iio t) t) (𝓝[<] t₀) (𝓝 (derivWithin φ (Iio t₀) t₀)) := by
  set d := derivWithin φ (Iio t₀) t₀ with hd
  have hcont := continuousAt_of_mem_Ioo hφ ht
  have hup : ∀ᶠ t in 𝓝[<] t₀, derivWithin φ (Ioi t) t ≤ d ∧
      derivWithin φ (Iio t) t ≤ derivWithin φ (Ioi t) t := by
    filter_upwards [Ioo_mem_nhdsLT ht.1] with t htI
    have htI' : t ∈ Ioo a b := ⟨htI.1, by linarith [htI.2, ht.2]⟩
    have h1 := hφ.rightDeriv_le_slope_of_mem_interior (mem_interior_Icc_of_mem_Ioo htI')
      ⟨ht.1.le, ht.2.le⟩ htI.2
    have h2 := hφ.slope_le_leftDeriv_of_mem_interior ⟨htI'.1.le, htI'.2.le⟩
      (mem_interior_Icc_of_mem_Ioo ht) htI.2
    exact ⟨h1.trans h2, leftDeriv_le_rightDeriv' hφ htI'⟩
  have hlow : ∀ c, c < d → ∀ᶠ t in 𝓝[<] t₀, c < derivWithin φ (Iio t) t := by
    intro c hc
    have hsl := hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)
    rw [hasDerivWithinAt_iff_tendsto_slope] at hsl
    have hsl' : Tendsto (slope φ t₀) (𝓝[<] t₀) (𝓝 d) :=
      hsl.mono_left (nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_lt hz⟩)
    have hev := hsl'.eventually_const_lt (show (c + d) / 2 < d by linarith)
    obtain ⟨t', hslt', ht'⟩ := (hev.and (Ioo_mem_nhdsLT ht.1)).exists
    have hcs : Tendsto (fun t => slope φ t' t) (𝓝[<] t₀) (𝓝 (slope φ t' t₀)) := by
      have : Tendsto (fun t => (φ t - φ t') / (t - t')) (𝓝 t₀) (𝓝 ((φ t₀ - φ t') / (t₀ - t'))) :=
        (hcont.tendsto.sub tendsto_const_nhds).div (tendsto_id.sub tendsto_const_nhds)
          (sub_ne_zero.mpr ht'.2.ne')
      rw [slope_def_field]
      exact (this.mono_left nhdsWithin_le_nhds).congr'
        (Eventually.of_forall fun t => (slope_def_field φ t' t).symm)
    have hslt'' : slope φ t' t₀ = slope φ t₀ t' := slope_comm φ t' t₀
    have hlt : c < slope φ t' t₀ := by rw [hslt'']; linarith
    filter_upwards [hcs.eventually_const_lt hlt, Ioo_mem_nhdsLT ht'.2] with t h1 h2
    have htI' : t ∈ Ioo a b := ⟨by linarith [h2.1, ht'.1], by linarith [h2.2, ht.2]⟩
    have := hφ.slope_le_leftDeriv_of_mem_interior ⟨ht'.1.le, by linarith [ht'.2, ht.2]⟩
      (mem_interior_Icc_of_mem_Ioo htI') h2.1
    linarith
  constructor
  · rw [tendsto_order]
    constructor
    · intro c hc
      filter_upwards [hlow c hc, hup] with t h1 h2
      linarith [h2.2]
    · intro c hc
      filter_upwards [hup] with t ht'
      linarith [ht'.1]
  · rw [tendsto_order]
    constructor
    · intro c hc
      exact hlow c hc
    · intro c hc
      filter_upwards [hup] with t ht'
      linarith [ht'.1, ht'.2]

/-! #### Fréchet normals of the graph -/

omit hφ in
theorem mem_graphOn_of_mem_Ioo {t : ℝ} (ht : t ∈ Ioo a b) : (t, φ t) ∈ graphOn φ a b :=
  ⟨⟨ht.1.le, ht.2.le⟩, rfl⟩

/-- The parametrisation `t ↦ (t, φ t)` tends to the point within the graph, from the right. -/
theorem tendsto_param_nhdsGT {t₁ : ℝ} (ht : t₁ ∈ Ioo a b) :
    Tendsto (fun t => (t, φ t)) (𝓝[>] t₁) (𝓝[graphOn φ a b] (t₁, φ t₁)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (tendsto_id.prodMk_nhds (continuousAt_of_mem_Ioo hφ ht).tendsto).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT ht.2] with t htI
    exact ⟨⟨by linarith [ht.1, htI.1], htI.2.le⟩, rfl⟩

theorem tendsto_param_nhdsLT {t₁ : ℝ} (ht : t₁ ∈ Ioo a b) :
    Tendsto (fun t => (t, φ t)) (𝓝[<] t₁) (𝓝[graphOn φ a b] (t₁, φ t₁)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact (tendsto_id.prodMk_nhds (continuousAt_of_mem_Ioo hφ ht).tendsto).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT ht.1] with t htI
    exact ⟨⟨htI.1.le, by linarith [ht.2, htI.2]⟩, rfl⟩

/-- A Fréchet normal `v` at `(t₁, φ t₁)` satisfies `v₁ + v₂ φ'₊(t₁) ≤ 0`. -/
theorem frechet_graph_bound_right {t₁ : ℝ} (ht : t₁ ∈ Ioo a b) {v : ℝ × ℝ}
    (hv : v ∈ frechetNormal (graphOn φ a b) (t₁, φ t₁)) :
    v.1 + v.2 * derivWithin φ (Ioi t₁) t₁ ≤ 0 := by
  set dR := derivWithin φ (Ioi t₁) t₁ with hdR
  have hsl := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hsl
  have hsl' : Tendsto (slope φ t₁) (𝓝[>] t₁) (𝓝 dR) :=
    hsl.mono_left (nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_gt hz⟩)
  have hpar := tendsto_param_nhdsGT hφ ht
  by_contra hpos
  push_neg at hpos
  set M := max 1 |dR| with hM
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  set ε := (v.1 + v.2 * dR) / (2 * M) with hε
  have hε0 : 0 < ε := div_pos hpos (mul_pos two_pos hM0)
  have hev := hpar.eventually (hv ε hε0)
  have hev' : ∀ᶠ t in 𝓝[>] t₁, v.1 + v.2 * slope φ t₁ t ≤ ε * max 1 |slope φ t₁ t| := by
    filter_upwards [hev, self_mem_nhdsWithin] with t h1 h2
    have hpos' : 0 < t - t₁ := sub_pos.mpr h2
    simp only [ip, Prod.fst_sub, Prod.snd_sub, Prod.dist_eq, Real.dist_eq] at h1
    rw [abs_of_pos hpos'] at h1
    have hmax : max (t - t₁) |φ t - φ t₁| = (t - t₁) * max 1 |slope φ t₁ t| := by
      rw [slope_def_field, abs_div, abs_of_pos hpos', mul_max_of_nonneg _ _ hpos'.le, mul_one,
        mul_div_cancel₀ _ hpos'.ne']
    refine le_of_mul_le_mul_right ?_ hpos'
    calc (v.1 + v.2 * slope φ t₁ t) * (t - t₁) = v.1 * (t - t₁) + v.2 * (φ t - φ t₁) := by
          rw [slope_def_field, add_mul, mul_assoc, div_mul_cancel₀ _ hpos'.ne']
      _ ≤ ε * max (t - t₁) |φ t - φ t₁| := h1
      _ = ε * max 1 |slope φ t₁ t| * (t - t₁) := by rw [hmax]; ring
  have hT1 : Tendsto (fun t => v.1 + v.2 * slope φ t₁ t) (𝓝[>] t₁) (𝓝 (v.1 + v.2 * dR)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hsl')
  have hT2 : Tendsto (fun t => ε * max 1 |slope φ t₁ t|) (𝓝[>] t₁) (𝓝 (ε * M)) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.max hsl'.abs)
  have hle := le_of_tendsto_of_tendsto hT1 hT2 hev'
  have : ε * M = (v.1 + v.2 * dR) / 2 := by
    rw [hε, div_mul_eq_mul_div, mul_div_mul_right _ _ hM0.ne']
  linarith

/-- A Fréchet normal `v` at `(t₁, φ t₁)` satisfies `0 ≤ v₁ + v₂ φ'₋(t₁)`. -/
theorem frechet_graph_bound_left {t₁ : ℝ} (ht : t₁ ∈ Ioo a b) {v : ℝ × ℝ}
    (hv : v ∈ frechetNormal (graphOn φ a b) (t₁, φ t₁)) :
    0 ≤ v.1 + v.2 * derivWithin φ (Iio t₁) t₁ := by
  set dL := derivWithin φ (Iio t₁) t₁ with hdL
  have hsl := hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo ht)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hsl
  have hsl' : Tendsto (slope φ t₁) (𝓝[<] t₁) (𝓝 dL) :=
    hsl.mono_left (nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_lt hz⟩)
  have hpar := tendsto_param_nhdsLT hφ ht
  by_contra hneg
  push_neg at hneg
  set M := max 1 |dL| with hM
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  set ε := -(v.1 + v.2 * dL) / (2 * M) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (mul_pos two_pos hM0)
  have hev := hpar.eventually (hv ε hε0)
  have hev' : ∀ᶠ t in 𝓝[<] t₁, -(v.1 + v.2 * slope φ t₁ t) ≤ ε * max 1 |slope φ t₁ t| := by
    filter_upwards [hev, self_mem_nhdsWithin] with t h1 h2
    have hpos' : 0 < t₁ - t := sub_pos.mpr h2
    simp only [ip, Prod.fst_sub, Prod.snd_sub, Prod.dist_eq, Real.dist_eq] at h1
    rw [abs_sub_comm t t₁, abs_of_pos hpos'] at h1
    have hmax : max (t₁ - t) |φ t - φ t₁| = (t₁ - t) * max 1 |slope φ t₁ t| := by
      rw [slope_def_field, abs_div, abs_sub_comm t t₁, abs_of_pos hpos',
        mul_max_of_nonneg _ _ hpos'.le, mul_one, mul_div_cancel₀ _ hpos'.ne']
    have hne : t - t₁ ≠ 0 := sub_ne_zero.mpr h2.ne
    refine le_of_mul_le_mul_right ?_ hpos'
    calc -(v.1 + v.2 * slope φ t₁ t) * (t₁ - t) = (v.1 + v.2 * slope φ t₁ t) * (t - t₁) := by ring
      _ = v.1 * (t - t₁) + v.2 * (φ t - φ t₁) := by
          rw [slope_def_field, add_mul, mul_assoc, div_mul_cancel₀ _ hne]
      _ ≤ ε * max (t₁ - t) |φ t - φ t₁| := h1
      _ = ε * max 1 |slope φ t₁ t| * (t₁ - t) := by rw [hmax]; ring
  have hT1 : Tendsto (fun t => -(v.1 + v.2 * slope φ t₁ t)) (𝓝[<] t₁) (𝓝 (-(v.1 + v.2 * dL))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hsl')).neg
  have hT2 : Tendsto (fun t => ε * max 1 |slope φ t₁ t|) (𝓝[<] t₁) (𝓝 (ε * M)) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.max hsl'.abs)
  have hle := le_of_tendsto_of_tendsto hT1 hT2 hev'
  have : ε * M = -(v.1 + v.2 * dL) / 2 := by
    rw [hε, div_mul_eq_mul_div, mul_div_mul_right _ _ hM0.ne']
  linarith

/-- The wedge is contained in the Fréchet normal cone. -/
theorem wedge_subset_frechet {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    wedge (derivWithin φ (Iio t₀) t₀) (derivWithin φ (Ioi t₀) t₀) ⊆
      frechetNormal (graphOn φ a b) (t₀, φ t₀) := by
  rintro v ⟨l, hl, s, hs, rfl⟩ ε hε
  have hsub : s ∈ subdiffOn φ a b t₀ := (mem_subdiffOn_iff hφ ht).mpr hs
  refine eventually_nhdsWithin_of_forall fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := hx
  have h := hsub x.1 hx1
  simp only [ip, Prod.fst_sub, Prod.snd_sub]
  rw [hx2]
  have h0 : l * s * (x.1 - t₀) + -l * (φ x.1 - φ t₀) ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left h hl]
  exact h0.trans (by positivity)

omit hφ in
/-- At a point of differentiability the "upward" normal `(-φ', 1)` is a Fréchet normal. -/
theorem neg_grad_mem_frechet {t₁ : ℝ} (hd : DifferentiableAt ℝ φ t₁) :
    (-(deriv φ t₁), 1) ∈ frechetNormal (graphOn φ a b) (t₁, φ t₁) := by
  intro ε hε
  have h := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
  have hev : ∀ᶠ t in 𝓝[≠] t₁, |slope φ t₁ t - deriv φ t₁| < ε := by
    have := Metric.tendsto_nhds.mp h ε hε
    simpa using this
  rw [eventually_nhdsWithin_iff] at hev
  have hT : Tendsto (fun x : ℝ × ℝ => x.1) (𝓝[graphOn φ a b] (t₁, φ t₁)) (𝓝 t₁) :=
    (continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds
  filter_upwards [hT.eventually hev, self_mem_nhdsWithin] with x hx hxG
  obtain ⟨hx1, hx2⟩ := hxG
  simp only [ip, Prod.fst_sub, Prod.snd_sub]
  rw [hx2]
  rcases eq_or_ne x.1 t₁ with h1 | h1
  · rw [h1]
    simp only [sub_self, mul_zero, zero_add]
    positivity
  · have hlt := hx h1
    rw [slope_def_field] at hlt
    have hne : x.1 - t₁ ≠ 0 := sub_ne_zero.mpr h1
    have hdist : |x.1 - t₁| ≤ dist x (t₁, φ t₁) := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hfac : φ x.1 - φ t₁ - deriv φ t₁ * (x.1 - t₁) =
        ((φ x.1 - φ t₁) / (x.1 - t₁) - deriv φ t₁) * (x.1 - t₁) := by
      rw [sub_mul, div_mul_cancel₀ _ hne]
    have key : φ x.1 - φ t₁ - deriv φ t₁ * (x.1 - t₁) ≤ ε * |x.1 - t₁| := by
      rw [hfac]
      calc ((φ x.1 - φ t₁) / (x.1 - t₁) - deriv φ t₁) * (x.1 - t₁)
          ≤ |((φ x.1 - φ t₁) / (x.1 - t₁) - deriv φ t₁) * (x.1 - t₁)| := le_abs_self _
        _ = |(φ x.1 - φ t₁) / (x.1 - t₁) - deriv φ t₁| * |x.1 - t₁| := abs_mul _ _
        _ ≤ ε * |x.1 - t₁| := mul_le_mul_of_nonneg_right hlt.le (abs_nonneg _)
    calc -(deriv φ t₁) * (x.1 - t₁) + 1 * (φ x.1 - φ t₁)
        = φ x.1 - φ t₁ - deriv φ t₁ * (x.1 - t₁) := by ring
      _ ≤ ε * |x.1 - t₁| := key
      _ ≤ ε * dist x (t₁, φ t₁) := mul_le_mul_of_nonneg_left hdist hε.le

/-! #### Density of differentiability points -/

/-- Differentiability points of a convex function are dense in `(a, b)`. -/
theorem exists_differentiableAt_Ioo {c d : ℝ} (hc : a ≤ c) (hcd : c < d) (hd : d ≤ b) :
    ∃ t ∈ Ioo c d, DifferentiableAt ℝ φ t := by
  have hmono : MonotoneOn (fun x => derivWithin φ (Ioi x) x) (Ioo a b) := by
    have := hφ.monotoneOn_rightDeriv
    rwa [interior_Icc] at this
  have hcount := hmono.countable_not_continuousWithinAt
  have hdense := hcount.dense_compl ℝ
  obtain ⟨t, htc, htI⟩ := hdense.exists_mem_open (isOpen_Ioo : IsOpen (Ioo c d))
    ⟨(c + d) / 2, ⟨by linarith, by linarith⟩⟩
  refine ⟨t, htI, ?_⟩
  have htab : t ∈ Ioo a b := ⟨by linarith [htI.1], by linarith [htI.2]⟩
  have hcont : ContinuousWithinAt (fun x => derivWithin φ (Ioi x) x) (Ioo a b) t := by
    by_contra h
    exact htc ⟨htab, h⟩
  have hcontAt := hcont.continuousAt (Ioo_mem_nhds htab.1 htab.2)
  have h1 : Tendsto (fun x => derivWithin φ (Ioi x) x) (𝓝[<] t) (𝓝 (derivWithin φ (Ioi t) t)) :=
    hcontAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 := (tendsto_derivs_nhdsLT hφ htab).1
  have heq : derivWithin φ (Ioi t) t = derivWithin φ (Iio t) t := tendsto_nhds_unique h1 h2
  have hR := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo htab)
  have hL := hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc_of_mem_Ioo htab)
  rw [← heq] at hL
  rw [hasDerivWithinAt_Ioi_iff_Ici] at hR
  rw [hasDerivWithinAt_Iio_iff_Iic] at hL
  have := hL.union hR
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
  exact this.differentiableAt

theorem exists_seq_diff_right {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    ∃ s : ℕ → ℝ, (∀ k, s k ∈ Ioo a b ∧ DifferentiableAt ℝ φ (s k)) ∧
      Tendsto s atTop (𝓝[>] t₀) := by
  have hex : ∀ k : ℕ, ∃ t ∈ Ioo t₀ (min b (t₀ + 1 / ((k : ℝ) + 1))), DifferentiableAt ℝ φ t :=
    fun k => exists_differentiableAt_Ioo hφ ht.1.le
      (lt_min ht.2 (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]))
      (min_le_left _ _)
  choose s hs using hex
  have hlt : ∀ k, t₀ < s k := fun k => (hs k).1.1
  have hub : ∀ k, s k ≤ t₀ + 1 / ((k : ℝ) + 1) :=
    fun k => ((hs k).1.2.trans_le (min_le_right _ _)).le
  refine ⟨s, fun k => ⟨⟨by linarith [hlt k, ht.1], (hs k).1.2.trans_le (min_le_left _ _)⟩,
    (hs k).2⟩, ?_⟩
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall hlt⟩
  have h1 : Tendsto (fun k : ℕ => t₀ + 1 / ((k : ℝ) + 1)) atTop (𝓝 (t₀ + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun k => (hlt k).le) hub

theorem exists_seq_diff_left {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    ∃ s : ℕ → ℝ, (∀ k, s k ∈ Ioo a b ∧ DifferentiableAt ℝ φ (s k)) ∧
      Tendsto s atTop (𝓝[<] t₀) := by
  have hex : ∀ k : ℕ, ∃ t ∈ Ioo (max a (t₀ - 1 / ((k : ℝ) + 1))) t₀, DifferentiableAt ℝ φ t :=
    fun k => exists_differentiableAt_Ioo hφ (le_max_left _ _)
      (max_lt ht.1 (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])) ht.2.le
  choose s hs using hex
  have hlt : ∀ k, s k < t₀ := fun k => (hs k).1.2
  have hlb : ∀ k : ℕ, t₀ - 1 / ((k : ℝ) + 1) ≤ s k :=
    fun k => ((le_max_right _ _).trans_lt (hs k).1.1).le
  refine ⟨s, fun k => ⟨⟨(le_max_left _ _).trans_lt (hs k).1.1, by linarith [hlt k, ht.2]⟩,
    (hs k).2⟩, ?_⟩
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall hlt⟩
  have h1 : Tendsto (fun k : ℕ => t₀ - 1 / ((k : ℝ) + 1)) atTop (𝓝 (t₀ - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlb (fun k => (hlt k).le)

/-! #### The limiting normal cone of the graph -/

theorem nline_right_subset_limiting {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    nline (derivWithin φ (Ioi t₀) t₀) ⊆ limitingNormal (graphOn φ a b) (t₀, φ t₀) := by
  rintro v ⟨m, rfl⟩
  set dR := derivWithin φ (Ioi t₀) t₀ with hdR
  have hx₀ : (t₀, φ t₀) ∈ graphOn φ a b := mem_graphOn_of_mem_Ioo ht
  rcases le_or_gt 0 m with hm | hm
  · apply frechetNormal_subset_limitingNormal hx₀
    apply wedge_subset_frechet hφ ht
    exact ⟨m, hm, dR, ⟨leftDeriv_le_rightDeriv' hφ ht, le_rfl⟩, rfl⟩
  · have hkey : (-dR, 1) ∈ limitingNormal (graphOn φ a b) (t₀, φ t₀) := by
      obtain ⟨s, hs, hst⟩ := exists_seq_diff_right hφ ht
      refine ⟨fun k => (s k, φ (s k)), fun k => (-(deriv φ (s k)), 1),
        fun k => mem_graphOn_of_mem_Ioo (hs k).1, fun k => neg_grad_mem_frechet (hs k).2,
        ?_, ?_⟩
      · have := tendsto_nhds_of_tendsto_nhdsWithin hst
        exact this.prodMk_nhds ((continuousAt_of_mem_Ioo hφ ht).tendsto.comp this)
      · have h1 : Tendsto (fun k => derivWithin φ (Ioi (s k)) (s k)) atTop (𝓝 dR) :=
          (tendsto_derivs_nhdsGT hφ ht).1.comp hst
        have h2 : ∀ k, deriv φ (s k) = derivWithin φ (Ioi (s k)) (s k) := fun k =>
          ((hs k).2.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi _)).symm
        refine (h1.neg.prodMk_nhds tendsto_const_nhds).congr' (Eventually.of_forall fun k => ?_)
        simp only [h2 k]
    have := limitingNormal_smul hkey (show 0 ≤ -m by linarith)
    have e : (m * dR, -m) = (-m * -dR, -m * 1) := Prod.ext (by ring) (by ring)
    rw [e]
    exact this

theorem nline_left_subset_limiting {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    nline (derivWithin φ (Iio t₀) t₀) ⊆ limitingNormal (graphOn φ a b) (t₀, φ t₀) := by
  rintro v ⟨m, rfl⟩
  set dL := derivWithin φ (Iio t₀) t₀ with hdL
  have hx₀ : (t₀, φ t₀) ∈ graphOn φ a b := mem_graphOn_of_mem_Ioo ht
  rcases le_or_gt 0 m with hm | hm
  · apply frechetNormal_subset_limitingNormal hx₀
    apply wedge_subset_frechet hφ ht
    exact ⟨m, hm, dL, ⟨le_rfl, leftDeriv_le_rightDeriv' hφ ht⟩, rfl⟩
  · have hkey : (-dL, 1) ∈ limitingNormal (graphOn φ a b) (t₀, φ t₀) := by
      obtain ⟨s, hs, hst⟩ := exists_seq_diff_left hφ ht
      refine ⟨fun k => (s k, φ (s k)), fun k => (-(deriv φ (s k)), 1),
        fun k => mem_graphOn_of_mem_Ioo (hs k).1, fun k => neg_grad_mem_frechet (hs k).2,
        ?_, ?_⟩
      · have := tendsto_nhds_of_tendsto_nhdsWithin hst
        exact this.prodMk_nhds ((continuousAt_of_mem_Ioo hφ ht).tendsto.comp this)
      · have h1 : Tendsto (fun k => derivWithin φ (Ioi (s k)) (s k)) atTop (𝓝 dL) :=
          (tendsto_derivs_nhdsLT hφ ht).1.comp hst
        have h2 : ∀ k, deriv φ (s k) = derivWithin φ (Ioi (s k)) (s k) := fun k =>
          ((hs k).2.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi _)).symm
        refine (h1.neg.prodMk_nhds tendsto_const_nhds).congr' (Eventually.of_forall fun k => ?_)
        simp only [h2 k]
    have := limitingNormal_smul hkey (show 0 ≤ -m by linarith)
    have e : (m * dL, -m) = (-m * -dL, -m * 1) := Prod.ext (by ring) (by ring)
    rw [e]
    exact this

/-- Upper bound: every limiting normal lies in the wedge or on one of the two lines. -/
theorem limiting_graph_subset {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    limitingNormal (graphOn φ a b) (t₀, φ t₀) ⊆
      wedge (derivWithin φ (Iio t₀) t₀) (derivWithin φ (Ioi t₀) t₀) ∪
        nline (derivWithin φ (Iio t₀) t₀) ∪ nline (derivWithin φ (Ioi t₀) t₀) := by
  rintro v ⟨x, w, hxG, hw, hx, hwv⟩
  set dL := derivWithin φ (Iio t₀) t₀ with hdL
  set dR := derivWithin φ (Ioi t₀) t₀ with hdR
  set t : ℕ → ℝ := fun n => (x n).1 with ht_def
  have hxt : ∀ n, x n = (t n, φ (t n)) := fun n => Prod.ext rfl (hxG n).2
  have htt : Tendsto t atTop (𝓝 t₀) := (continuous_fst.tendsto _).comp hx
  have hev : ∀ᶠ n in atTop, t n ∈ Ioo a b := htt (Ioo_mem_nhds ht.1 ht.2)
  have hb : ∀ᶠ n in atTop, (w n).1 + (w n).2 * derivWithin φ (Ioi (t n)) (t n) ≤ 0 ∧
      0 ≤ (w n).1 + (w n).2 * derivWithin φ (Iio (t n)) (t n) := by
    filter_upwards [hev] with n hn
    have := hw n
    rw [hxt n] at this
    exact ⟨frechet_graph_bound_right hφ hn this, frechet_graph_bound_left hφ hn this⟩
  have hw1 : Tendsto (fun n => (w n).1) atTop (𝓝 v.1) := (continuous_fst.tendsto _).comp hwv
  have hw2 : Tendsto (fun n => (w n).2) atTop (𝓝 v.2) := (continuous_snd.tendsto _).comp hwv
  by_cases hfreq : ∃ᶠ n in atTop, t n = t₀
  · have h1 : v.1 + v.2 * dR ≤ 0 := by
      refine IsClosed.mem_of_frequently_of_tendsto (s := Iic 0) isClosed_Iic ?_
        (hw1.add (hw2.mul tendsto_const_nhds))
      refine (hfreq.and_eventually hb).mono fun n ⟨hn, hb1, _⟩ => ?_
      rw [hn] at hb1
      exact hb1
    have h2 : 0 ≤ v.1 + v.2 * dL := by
      refine IsClosed.mem_of_frequently_of_tendsto (s := Ici 0) isClosed_Ici ?_
        (hw1.add (hw2.mul tendsto_const_nhds))
      refine (hfreq.and_eventually hb).mono fun n ⟨hn, _, hb2⟩ => ?_
      rw [hn] at hb2
      exact hb2
    exact mem_wedge_or_nline (leftDeriv_le_rightDeriv' hφ ht) h1 h2
  · rw [not_frequently] at hfreq
    by_cases hR : ∃ᶠ n in atTop, t₀ < t n
    · obtain ⟨ψ, hψ, hψR⟩ := extraction_of_frequently_atTop hR
      have hsub : Tendsto (t ∘ ψ) atTop (𝓝[>] t₀) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨htt.comp hψ.tendsto_atTop, Eventually.of_forall hψR⟩
      obtain ⟨e1, e2⟩ := tendsto_derivs_nhdsGT hφ ht
      have f1 : Tendsto (fun k => derivWithin φ (Ioi (t (ψ k))) (t (ψ k))) atTop (𝓝 dR) :=
        e1.comp hsub
      have f2 : Tendsto (fun k => derivWithin φ (Iio (t (ψ k))) (t (ψ k))) atTop (𝓝 dR) :=
        e2.comp hsub
      have g1 : Tendsto (fun k => (w (ψ k)).1) atTop (𝓝 v.1) := hw1.comp hψ.tendsto_atTop
      have g2 : Tendsto (fun k => (w (ψ k)).2) atTop (𝓝 v.2) := hw2.comp hψ.tendsto_atTop
      have hb' := hψ.tendsto_atTop.eventually hb
      have hA : v.1 + v.2 * dR ≤ 0 :=
        le_of_tendsto (g1.add (g2.mul f1)) (hb'.mono fun k hk => hk.1)
      have hB : 0 ≤ v.1 + v.2 * dR :=
        ge_of_tendsto (g1.add (g2.mul f2)) (hb'.mono fun k hk => hk.2)
      right
      exact ⟨-v.2, Prod.ext (by simp; linarith) (by simp)⟩
    · rw [not_frequently] at hR
      by_cases hL : ∃ᶠ n in atTop, t n < t₀
      · obtain ⟨ψ, hψ, hψL⟩ := extraction_of_frequently_atTop hL
        have hsub : Tendsto (t ∘ ψ) atTop (𝓝[<] t₀) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨htt.comp hψ.tendsto_atTop, Eventually.of_forall hψL⟩
        obtain ⟨e1, e2⟩ := tendsto_derivs_nhdsLT hφ ht
        have f1 : Tendsto (fun k => derivWithin φ (Ioi (t (ψ k))) (t (ψ k))) atTop (𝓝 dL) :=
          e1.comp hsub
        have f2 : Tendsto (fun k => derivWithin φ (Iio (t (ψ k))) (t (ψ k))) atTop (𝓝 dL) :=
          e2.comp hsub
        have g1 : Tendsto (fun k => (w (ψ k)).1) atTop (𝓝 v.1) := hw1.comp hψ.tendsto_atTop
        have g2 : Tendsto (fun k => (w (ψ k)).2) atTop (𝓝 v.2) := hw2.comp hψ.tendsto_atTop
        have hb' := hψ.tendsto_atTop.eventually hb
        have hA : v.1 + v.2 * dL ≤ 0 :=
          le_of_tendsto (g1.add (g2.mul f1)) (hb'.mono fun k hk => hk.1)
        have hB : 0 ≤ v.1 + v.2 * dL :=
          ge_of_tendsto (g1.add (g2.mul f2)) (hb'.mono fun k hk => hk.2)
        left; right
        exact ⟨-v.2, Prod.ext (by simp; linarith) (by simp)⟩
      · rw [not_frequently] at hL
        exfalso
        obtain ⟨n, h1, h2, h3⟩ := (hfreq.and (hR.and hL)).exists
        rcases lt_trichotomy (t n) t₀ with h | h | h
        · exact h3 h
        · exact h1 h
        · exact h2 h

/-- **The limiting normal cone of the graph of a convex function at an interior point.** -/
theorem limitingNormal_graph_eq {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) :
    limitingNormal (graphOn φ a b) (t₀, φ t₀) =
      wedge (derivWithin φ (Iio t₀) t₀) (derivWithin φ (Ioi t₀) t₀) ∪
        nline (derivWithin φ (Iio t₀) t₀) ∪ nline (derivWithin φ (Ioi t₀) t₀) := by
  apply Subset.antisymm (limiting_graph_subset hφ ht)
  rintro v ((hv | hv) | hv)
  · exact frechetNormal_subset_limitingNormal (mem_graphOn_of_mem_Ioo ht)
      (wedge_subset_frechet hφ ht hv)
  · exact nline_left_subset_limiting hφ ht hv
  · exact nline_right_subset_limiting hφ ht hv

end Graph

/-! #### Transversality of two wedge-and-lines cones -/

theorem transversal_cones_iff {dL dR eL eR : ℝ} (hd : dL ≤ dR) (he : eL ≤ eR) :
    (∀ v : ℝ × ℝ, v ∈ wedge dL dR ∪ nline dL ∪ nline dR →
        -v ∈ wedge eL eR ∪ nline eL ∪ nline eR → v = 0) ↔
      Disjoint (Icc dL dR) (Icc eL eR) := by
  constructor
  · intro htr
    rw [Set.disjoint_left]
    intro s hs hs'
    -- an endpoint of one interval lies in the other
    have hcases : dR ∈ Icc eL eR ∨ dL ∈ Icc eL eR ∨ eR ∈ Icc dL dR ∨ eL ∈ Icc dL dR := by
      obtain ⟨h1, h2⟩ := hs
      obtain ⟨h3, h4⟩ := hs'
      by_cases hdR : dR ≤ eR
      · left; exact ⟨by linarith, hdR⟩
      · by_cases heR : eR ≤ dR
        · right; right; left; exact ⟨by linarith, heR⟩
        · exfalso; linarith
    rcases hcases with h | h | h | h
    · have := htr (-dR, 1) (Or.inr ⟨-1, by ext <;> simp⟩)
        (Or.inl (Or.inl ⟨1, zero_le_one, dR, h, by ext <;> simp⟩))
      simp [Prod.ext_iff] at this
    · have := htr (-dL, 1) (Or.inl (Or.inr ⟨-1, by ext <;> simp⟩))
        (Or.inl (Or.inl ⟨1, zero_le_one, dL, h, by ext <;> simp⟩))
      simp [Prod.ext_iff] at this
    · have := htr (eR, -1) (Or.inl (Or.inl ⟨1, zero_le_one, eR, h, by ext <;> simp⟩))
        (Or.inr ⟨-1, by ext <;> simp⟩)
      simp [Prod.ext_iff] at this
    · have := htr (eL, -1) (Or.inl (Or.inl ⟨1, zero_le_one, eL, h, by ext <;> simp⟩))
        (Or.inl (Or.inr ⟨-1, by ext <;> simp⟩))
      simp [Prod.ext_iff] at this
  · intro hdis v hv hv'
    have hnot : ∀ s ∈ Icc dL dR, s ∉ Icc eL eR := Set.disjoint_left.mp hdis
    rcases hv with (⟨l, hl, s, hs, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩
    · rcases hv' with (⟨l', hl', s', hs', h⟩ | ⟨m', h⟩) | ⟨m', h⟩ <;>
        simp only [Prod.neg_mk, Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h
      · have : l = 0 := by linarith
        simp [this]
      · rcases eq_or_ne l 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : l * s = l * eL := by linear_combination -h1 - eL * h2
          have hse : s = eL := mul_left_cancel₀ h0 this
          exact hnot s hs (by rw [hse]; exact left_mem_Icc.mpr he)
      · rcases eq_or_ne l 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : l * s = l * eR := by linear_combination -h1 - eR * h2
          have hse : s = eR := mul_left_cancel₀ h0 this
          exact hnot s hs (by rw [hse]; exact right_mem_Icc.mpr he)
    · rcases hv' with (⟨l', hl', s', hs', h⟩ | ⟨m', h⟩) | ⟨m', h⟩ <;>
        simp only [Prod.neg_mk, Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h
      · rcases eq_or_ne m 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : m * dL = m * s' := by linear_combination -h1 - s' * h2
          have hde : dL = s' := mul_left_cancel₀ h0 this
          exact hnot dL (left_mem_Icc.mpr hd) (by rw [hde]; exact hs')
      · rcases eq_or_ne m 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : m * dL = m * eL := by linear_combination -h1 - eL * h2
          have hde : dL = eL := mul_left_cancel₀ h0 this
          exact hnot dL (left_mem_Icc.mpr hd) (by rw [hde]; exact left_mem_Icc.mpr he)
      · rcases eq_or_ne m 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : m * dL = m * eR := by linear_combination -h1 - eR * h2
          have hde : dL = eR := mul_left_cancel₀ h0 this
          exact hnot dL (left_mem_Icc.mpr hd) (by rw [hde]; exact right_mem_Icc.mpr he)
    · rcases hv' with (⟨l', hl', s', hs', h⟩ | ⟨m', h⟩) | ⟨m', h⟩ <;>
        simp only [Prod.neg_mk, Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h
      · rcases eq_or_ne m 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : m * dR = m * s' := by linear_combination -h1 - s' * h2
          have hde : dR = s' := mul_left_cancel₀ h0 this
          exact hnot dR (right_mem_Icc.mpr hd) (by rw [hde]; exact hs')
      · rcases eq_or_ne m 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : m * dR = m * eL := by linear_combination -h1 - eL * h2
          have hde : dR = eL := mul_left_cancel₀ h0 this
          exact hnot dR (right_mem_Icc.mpr hd) (by rw [hde]; exact left_mem_Icc.mpr he)
      · rcases eq_or_ne m 0 with h0 | h0
        · simp [h0]
        · exfalso
          have : m * dR = m * eR := by linear_combination -h1 - eR * h2
          have hde : dR = eR := mul_left_cancel₀ h0 this
          exact hnot dR (right_mem_Icc.mpr hd) (by rw [hde]; exact right_mem_Icc.mpr he)

/-- **Transversality of two convex graphs** at a common interior point is equivalent to
disjointness of the subdifferential intervals. -/
theorem transversal_graphs_iff {φ ψ : ℝ → ℝ} {a b c d : ℝ} (hφ : ConvexOn ℝ (Icc a b) φ)
    (hψ : ConvexOn ℝ (Icc c d) ψ) {t₀ : ℝ} (ht : t₀ ∈ Ioo a b) (ht' : t₀ ∈ Ioo c d)
    (heq : φ t₀ = ψ t₀) :
    SetTransversal (graphOn φ a b) (graphOn ψ c d) (t₀, φ t₀) ↔
      Disjoint (Icc (derivWithin φ (Iio t₀) t₀) (derivWithin φ (Ioi t₀) t₀))
        (Icc (derivWithin ψ (Iio t₀) t₀) (derivWithin ψ (Ioi t₀) t₀)) := by
  have hφc := limitingNormal_graph_eq hφ ht
  have hψc := limitingNormal_graph_eq hψ ht'
  rw [← heq] at hψc
  rw [← transversal_cones_iff (leftDeriv_le_rightDeriv' hφ ht) (leftDeriv_le_rightDeriv' hψ ht')]
  simp only [SetTransversal, hφc, hψc]

/-! ### Level curves of strictly positive neoclassical functions -/

/-- The unit level curve of `h` in the closed quadrant. -/
def levelCurve (h : ℝ × ℝ → ℝ) : Set (ℝ × ℝ) := {x | x ∈ quadrant ∧ h x = 1}

/-- The level curve `h = 1` is the graph of `curveFun h` over `[0, curveEnd h]`. -/
noncomputable def curveFun (h : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := profile h (h (1, 0) * t) / h (0, 1)

/-- Right endpoint of the level curve: `1 / h (1, 0)`. -/
noncomputable def curveEnd (h : ℝ × ℝ → ℝ) : ℝ := 1 / h (1, 0)

namespace IsPosNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

theorem curveEnd_pos : 0 < curveEnd h := one_div_pos.mpr hh.pos_fst

theorem curveFun_end : curveFun h (curveEnd h) = 0 := by
  rw [curveFun, curveEnd, mul_one_div_cancel hh.pos_fst.ne', hh.profile_isProfile.map_one,
    zero_div]

theorem mul_mem_Icc_of_mem {t : ℝ} (ht : t ∈ Icc 0 (curveEnd h)) : h (1, 0) * t ∈ Icc (0 : ℝ) 1 := by
  have hc₁ := hh.pos_fst
  refine ⟨mul_nonneg hc₁.le ht.1, ?_⟩
  calc h (1, 0) * t ≤ h (1, 0) * curveEnd h := mul_le_mul_of_nonneg_left ht.2 hc₁.le
    _ = 1 := by rw [curveEnd, mul_one_div_cancel hc₁.ne']

theorem curveFun_nonneg {t : ℝ} (ht : t ∈ Icc 0 (curveEnd h)) : 0 ≤ curveFun h t :=
  div_nonneg (hh.profile_isProfile.nonneg (hh.mul_mem_Icc_of_mem ht)) hh.pos_snd.le

theorem curveFun_pos {t : ℝ} (ht : t ∈ Ico 0 (curveEnd h)) : 0 < curveFun h t := by
  have hc₁ := hh.pos_fst
  refine div_pos (hh.profile_isProfile.pos ⟨mul_nonneg hc₁.le ht.1, ?_⟩) hh.pos_snd
  calc h (1, 0) * t < h (1, 0) * curveEnd h := mul_lt_mul_of_pos_left ht.2 hc₁
    _ = 1 := by rw [curveEnd, mul_one_div_cancel hc₁.ne']

/-- The level curve is the graph of `curveFun h`. -/
theorem levelCurve_eq_graphOn : levelCurve h = graphOn (curveFun h) 0 (curveEnd h) := by
  have hf := hh.profile_isProfile
  have hc₁ := hh.pos_fst
  have hc₂ := hh.pos_snd
  have hcq : (h (1, 0), h (0, 1)) ∈ quadrant := orthant_subset_quadrant hh.scaling_mem_orthant
  ext x
  constructor
  · rintro ⟨hx, h1⟩
    obtain ⟨hx1, hx2⟩ := mem_quadrant.mp hx
    rw [hh.eq_ofProfile_hadamard hx] at h1
    have hu : hadamard (h (1, 0), h (0, 1)) x ∈ quadrant := hadamard_mem_quadrant hcq hx
    have hu1 : (hadamard (h (1, 0), h (0, 1)) x).1 ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      exact (hf.one_lt_ofProfile_of_one_lt hu hcon).ne' h1
    rw [hf.ofProfile_eq_one_iff hu hu1] at h1
    simp only [hadamard_fst, hadamard_snd] at h1 hu1
    refine ⟨⟨hx1, ?_⟩, ?_⟩
    · rw [curveEnd, le_div_iff₀ hc₁]
      linarith [hu1]
    · rw [curveFun, h1, mul_div_cancel_left₀ _ hc₂.ne']
  · rintro ⟨hxI, hx2⟩
    have hc1x := hh.mul_mem_Icc_of_mem hxI
    have hx : x ∈ quadrant := mem_quadrant.mpr ⟨hxI.1, by rw [hx2]; exact hh.curveFun_nonneg hxI⟩
    refine ⟨hx, ?_⟩
    rw [hh.eq_ofProfile_hadamard hx]
    have hu : hadamard (h (1, 0), h (0, 1)) x ∈ quadrant := hadamard_mem_quadrant hcq hx
    rw [hf.ofProfile_eq_one_iff hu (by simpa using hc1x.2)]
    simp only [hadamard_fst, hadamard_snd]
    rw [hx2, curveFun, mul_div_cancel₀ _ hc₂.ne']

theorem curveFun_convexOn : ConvexOn ℝ (Icc 0 (curveEnd h)) (curveFun h) := by
  have hf := hh.profile_isProfile
  have hc₂ := hh.pos_snd
  refine ⟨convex_Icc 0 _, fun x hx y hy a' b' ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hx' := hh.mul_mem_Icc_of_mem hx
  have hy' := hh.mul_mem_Icc_of_mem hy
  have := hf.convexOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at this
  show profile h (h (1, 0) * (a' * x + b' * y)) / h (0, 1) ≤
    a' * (profile h (h (1, 0) * x) / h (0, 1)) + b' * (profile h (h (1, 0) * y) / h (0, 1))
  rw [show h (1, 0) * (a' * x + b' * y) = a' * (h (1, 0) * x) + b' * (h (1, 0) * y) by ring,
    show a' * (profile h (h (1, 0) * x) / h (0, 1)) + b' * (profile h (h (1, 0) * y) / h (0, 1))
      = (a' * profile h (h (1, 0) * x) + b' * profile h (h (1, 0) * y)) / h (0, 1) by ring]
  exact div_le_div_of_nonneg_right this hc₂.le

/-- A point of the level curve in the open orthant is an interior point of the graph. -/
theorem mem_Ioo_of_mem_levelCurve {x₀ : ℝ × ℝ} (hx : x₀ ∈ levelCurve h) (hx₀ : x₀ ∈ orthant) :
    x₀.1 ∈ Ioo 0 (curveEnd h) ∧ x₀.2 = curveFun h x₀.1 := by
  rw [hh.levelCurve_eq_graphOn] at hx
  obtain ⟨⟨h0, hb⟩, h2⟩ := hx
  obtain ⟨hx1, hx2⟩ := mem_orthant.mp hx₀
  refine ⟨⟨hx1, lt_of_le_of_ne hb fun heq => ?_⟩, h2⟩
  rw [heq, hh.curveFun_end] at h2
  linarith

/-- Euler's identity for supergradients: `⟪ξ, x₀⟫ = h x₀`. -/
theorem ip_eq_of_mem_superdiff {x₀ ξ : ℝ × ℝ} (hx₀ : x₀ ∈ quadrant) (hξ : ξ ∈ superdiff h x₀) :
    ip ξ x₀ = h x₀ := by
  have key : ∀ t : ℝ, 0 < t → (t - 1) * (h x₀ - ip ξ x₀) ≤ 0 := by
    intro t ht
    have := hξ (t • x₀) (quadrant_smul ht.le hx₀)
    rw [hh.homogeneous t ht x₀ hx₀] at this
    have e : ip ξ (t • x₀ - x₀) = (t - 1) * ip ξ x₀ := by
      simp only [ip, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [e] at this
    linarith
  have h2 := key 2 two_pos
  have h3 := key (1 / 2) (by norm_num)
  linarith

theorem snd_pos_of_mem_superdiff {x₀ ξ : ℝ × ℝ} (hx₀ : x₀ ∈ quadrant) (hξ : ξ ∈ superdiff h x₀) :
    0 < ξ.2 := by
  have hq : x₀ + (0, 1) ∈ quadrant := quadrant_add hx₀ (mk_mem_quadrant le_rfl zero_le_one)
  have h2 := hξ _ hq
  have h3 := hh.superadditive hx₀ (mk_mem_quadrant le_rfl zero_le_one)
  have e : ip ξ (x₀ + (0, 1) - x₀) = ξ.2 := by simp [ip]
  rw [e] at h2
  linarith [hh.pos_snd]

/-- A supergradient `ξ` of `h` at `x₀` gives the supporting slope `-ξ₁ / ξ₂` of the graph. -/
theorem neg_div_mem_subdiffOn {x₀ ξ : ℝ × ℝ} (hx₀ : x₀ ∈ orthant) (h1 : h x₀ = 1)
    (hξ : ξ ∈ superdiff h x₀) :
    -ξ.1 / ξ.2 ∈ subdiffOn (curveFun h) 0 (curveEnd h) x₀.1 := by
  have hx₀q := orthant_subset_quadrant hx₀
  have hpos := hh.snd_pos_of_mem_superdiff hx₀q hξ
  obtain ⟨ht₀, hx₀2⟩ := hh.mem_Ioo_of_mem_levelCurve ⟨hx₀q, h1⟩ hx₀
  intro z hz
  have hzc : (z, curveFun h z) ∈ levelCurve h := by
    rw [hh.levelCurve_eq_graphOn]
    exact ⟨hz, rfl⟩
  have h2 := hξ _ hzc.1
  rw [hzc.2, h1] at h2
  simp only [ip, Prod.fst_sub, Prod.snd_sub] at h2
  rw [hx₀2] at h2
  refine le_of_mul_le_mul_left ?_ hpos
  have e : ξ.2 * (curveFun h x₀.1 + -ξ.1 / ξ.2 * (z - x₀.1)) =
      ξ.2 * curveFun h x₀.1 - ξ.1 * (z - x₀.1) := by
    rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hpos.ne']
    ring
  rw [e]
  linarith

/-- A supporting slope `s` of the graph gives the supergradient `(1 / (x₀₂ - s x₀₁)) (-s, 1)`. -/
theorem mem_superdiff_of_mem_subdiffOn {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ orthant) (h1 : h x₀ = 1) {s : ℝ}
    (hs : s ∈ subdiffOn (curveFun h) 0 (curveEnd h) x₀.1) :
    (1 / (x₀.2 - s * x₀.1) * -s, 1 / (x₀.2 - s * x₀.1)) ∈ superdiff h x₀ := by
  have hx₀q := orthant_subset_quadrant hx₀
  obtain ⟨ht₀, hx₀2⟩ := hh.mem_Ioo_of_mem_levelCurve ⟨hx₀q, h1⟩ hx₀
  obtain ⟨hx1, hx2⟩ := mem_orthant.mp hx₀
  have hsneg : s < 0 := by
    have := hs (curveEnd h) ⟨hh.curveEnd_pos.le, le_rfl⟩
    rw [hh.curveFun_end, ← hx₀2] at this
    nlinarith [ht₀.2]
  have hden : 0 < x₀.2 - s * x₀.1 := by nlinarith
  set l := 1 / (x₀.2 - s * x₀.1) with hl
  have hl0 : 0 < l := by positivity
  have hip : l * -s * x₀.1 + l * x₀.2 = 1 := by
    have : l * -s * x₀.1 + l * x₀.2 = l * (x₀.2 - s * x₀.1) := by ring
    rw [this, hl, one_div_mul_cancel hden.ne']
  intro x hx
  have hrhs : h x₀ + ip (l * -s, l) (x - x₀) = l * -s * x.1 + l * x.2 := by
    rw [h1]
    simp only [ip, Prod.fst_sub, Prod.snd_sub]
    linear_combination -hip
  rw [hrhs]
  by_cases hx0 : x = 0
  · rw [hx0, hh.map_zero]
    simp
  · have hxpos : 0 < h x := hh.pos x hx hx0
    have hxne : h x ≠ 0 := hxpos.ne'
    set y := (1 / h x) • x with hy
    have hyq : y ∈ quadrant := quadrant_smul (by positivity) hx
    have hy1 : h y = 1 := by
      rw [hy, hh.homogeneous _ (one_div_pos.mpr hxpos) x hx, one_div_mul_cancel hxne]
    have hyc : y ∈ levelCurve h := ⟨hyq, hy1⟩
    rw [hh.levelCurve_eq_graphOn] at hyc
    obtain ⟨hy1', hy2'⟩ := hyc
    have hsub := hs y.1 hy1'
    rw [← hy2', ← hx₀2] at hsub
    have hy1e : y.1 = x.1 / h x := by rw [hy]; simp [div_eq_inv_mul]
    have hy2e : y.2 = x.2 / h x := by rw [hy]; simp [div_eq_inv_mul]
    rw [hy1e, hy2e] at hsub
    have h3 : (x₀.2 - s * x₀.1) * h x ≤ x.2 - s * x.1 := by
      have := mul_le_mul_of_nonneg_left hsub hxpos.le
      have e1 : h x * (x₀.2 + s * (x.1 / h x - x₀.1)) = (x₀.2 - s * x₀.1) * h x + s * x.1 := by
        have hc : h x * (x.1 / h x) = x.1 := mul_div_cancel₀ _ hxne
        calc h x * (x₀.2 + s * (x.1 / h x - x₀.1))
            = h x * x₀.2 + s * (h x * (x.1 / h x)) - h x * s * x₀.1 := by ring
          _ = (x₀.2 - s * x₀.1) * h x + s * x.1 := by rw [hc]; ring
      have e2 : h x * (x.2 / h x) = x.2 := mul_div_cancel₀ _ hxne
      rw [e1, e2] at this
      linarith
    have e : l * -s * x.1 + l * x.2 = (x.2 - s * x.1) / (x₀.2 - s * x₀.1) := by
      rw [hl]
      ring
    rw [e, le_div_iff₀ hden]
    linarith

end IsPosNeoclassical

/-- Disjointness of superdifferentials is the same as disjointness of the supporting-slope
intervals of the two graphs. -/
theorem disjoint_superdiff_iff {h g : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    (hg : IsPosNeoclassical g) {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ orthant) (h1 : h x₀ = 1) (g1 : g x₀ = 1) :
    Disjoint (superdiff h x₀) (superdiff g x₀) ↔
      Disjoint (subdiffOn (curveFun h) 0 (curveEnd h) x₀.1)
        (subdiffOn (curveFun g) 0 (curveEnd g) x₀.1) := by
  rw [Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro H s hs hs'
    exact H (hh.mem_superdiff_of_mem_subdiffOn hx₀ h1 hs) (hg.mem_superdiff_of_mem_subdiffOn hx₀ g1 hs')
  · intro H ξ hξ hξ'
    exact H (hh.neg_div_mem_subdiffOn hx₀ h1 hξ) (hg.neg_div_mem_subdiffOn hx₀ g1 hξ')

/-- **Transversality of level curves via superdifferentials.** For strictly positive neoclassical
`h, g` and an interior point `x₀` with `h x₀ = g x₀ = 1`, the level curves `h = 1` and `g = 1`
are transversal at `x₀` (in the sense of limiting normal cones) iff the superdifferentials
`∂h(x₀)` and `∂g(x₀)` are disjoint. -/
theorem transversal_levelCurves_iff {h g : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    (hg : IsPosNeoclassical g) {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ orthant) (h1 : h x₀ = 1) (g1 : g x₀ = 1) :
    SetTransversal (levelCurve h) (levelCurve g) x₀ ↔ Disjoint (superdiff h x₀) (superdiff g x₀) := by
  have hx₀q := orthant_subset_quadrant hx₀
  obtain ⟨ht, hx2⟩ := hh.mem_Ioo_of_mem_levelCurve ⟨hx₀q, h1⟩ hx₀
  obtain ⟨ht', hx2'⟩ := hg.mem_Ioo_of_mem_levelCurve ⟨hx₀q, g1⟩ hx₀
  have hx₀e : x₀ = (x₀.1, curveFun h x₀.1) := Prod.ext rfl hx2
  have heq : curveFun h x₀.1 = curveFun g x₀.1 := hx2.symm.trans hx2'
  have hφ := hh.curveFun_convexOn
  have hψ := hg.curveFun_convexOn
  have e1 : subdiffOn (curveFun h) 0 (curveEnd h) x₀.1 =
      Icc (derivWithin (curveFun h) (Iio x₀.1) x₀.1) (derivWithin (curveFun h) (Ioi x₀.1) x₀.1) :=
    Set.ext fun s => (mem_subdiffOn_iff hφ ht).trans mem_Icc.symm
  have e2 : subdiffOn (curveFun g) 0 (curveEnd g) x₀.1 =
      Icc (derivWithin (curveFun g) (Iio x₀.1) x₀.1) (derivWithin (curveFun g) (Ioi x₀.1) x₀.1) :=
    Set.ext fun s => (mem_subdiffOn_iff hψ ht').trans mem_Icc.symm
  rw [disjoint_superdiff_iff hh hg hx₀ h1 g1, e1, e2, hh.levelCurve_eq_graphOn,
    hg.levelCurve_eq_graphOn]
  have := transversal_graphs_iff hφ hψ ht ht' heq
  rw [← hx₀e] at this
  exact this

end NeoTiling
