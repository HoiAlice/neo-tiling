import NeoTiling.FiniteIntersections

/-!
# Level curves of a bounded neoclassical function and their intersections

For a bounded neoclassical `h` and a price vector `p ∈ ℝ²₊₊` consider the unit level curves
`h x = 1` and `h (p ∘ x) = 1`, where `p ∘ x` is the coordinatewise product. This file proves
the two-variable form of generic finiteness and transversality:

* `IsBddNeoclassical.exists_open_finite_levelIntersections`: every nonempty open set
  `U ⊆ ℝ²₊₊` contains a nonempty open set `V` such that for every `p ∈ V` the two curves meet in
  finitely many points, and every intersection point has *four chambers*: in every neighbourhood
  of it all four sign patterns of `(h - 1, h (p ∘ ·) - 1)` occur.

The proof reduces to the one-variable results of `FiniteIntersections`. After normalising `h`
(`IsBddNeoclassical.ofProfile_profile`) the curve `h x = 1` is the graph of the profile `f` and
the curve `h (p ∘ x) = 1` is the graph of `t ↦ f (p₁ t) / p₂`, so intersections correspond to
solutions of `f (p₁ t) = p₂ f t`, i.e. to `solutions f (1 / p₂, 1 / p₁)`. Transversality of the
one-variable problem (disjoint scaled subdifferentials) forces the difference of the two graphs
to change sign with nonzero one-sided slopes, which produces the four chambers.

The cases `p₁, p₂ > 1` and `p₁, p₂ < 1` have no intersections at all; the case `p₁ < 1 < p₂`
reduces to `p₁ > 1 > p₂` by the substitution `x ↦ p ∘ x`, which exchanges the two curves.
-/

open Real Set Filter Topology

namespace NeoTiling

/-! ### Coordinatewise products -/

/-- The open positive orthant `ℝ²₊₊`. -/
def orthant : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

theorem mem_orthant {p : ℝ × ℝ} : p ∈ orthant ↔ 0 < p.1 ∧ 0 < p.2 := by
  simp [orthant]

theorem orthant_subset_quadrant : orthant ⊆ quadrant := fun _ hp =>
  mem_quadrant.mpr ⟨(mem_orthant.mp hp).1.le, (mem_orthant.mp hp).2.le⟩

theorem isOpen_orthant : IsOpen orthant := isOpen_Ioi.prod isOpen_Ioi

/-- Coordinatewise product `p ∘ x = (p₁ x₁, p₂ x₂)`. -/
def hadamard (p x : ℝ × ℝ) : ℝ × ℝ := (p.1 * x.1, p.2 * x.2)

/-- Coordinatewise inverse `(1 / p₁, 1 / p₂)`. -/
noncomputable def hinv (p : ℝ × ℝ) : ℝ × ℝ := (1 / p.1, 1 / p.2)

@[simp] theorem hadamard_mk (p : ℝ × ℝ) (a b : ℝ) : hadamard p (a, b) = (p.1 * a, p.2 * b) := rfl

@[simp] theorem hadamard_fst (p x : ℝ × ℝ) : (hadamard p x).1 = p.1 * x.1 := rfl

@[simp] theorem hadamard_snd (p x : ℝ × ℝ) : (hadamard p x).2 = p.2 * x.2 := rfl

@[simp] theorem hinv_fst (p : ℝ × ℝ) : (hinv p).1 = 1 / p.1 := rfl

@[simp] theorem hinv_snd (p : ℝ × ℝ) : (hinv p).2 = 1 / p.2 := rfl

theorem hadamard_comm (p q x : ℝ × ℝ) : hadamard p (hadamard q x) = hadamard q (hadamard p x) := by
  ext <;> simp [hadamard] <;> ring

theorem hadamard_hinv_hadamard {c : ℝ × ℝ} (hc : c ∈ orthant) (x : ℝ × ℝ) :
    hadamard (hinv c) (hadamard c x) = x := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hc
  ext <;> simp [hadamard, hinv] <;> field_simp

theorem hadamard_hadamard_hinv {c : ℝ × ℝ} (hc : c ∈ orthant) (x : ℝ × ℝ) :
    hadamard c (hadamard (hinv c) x) = x := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hc
  ext <;> simp [hadamard, hinv] <;> field_simp

theorem hinv_mem_orthant {c : ℝ × ℝ} (hc : c ∈ orthant) : hinv c ∈ orthant := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hc
  exact mem_orthant.mpr ⟨one_div_pos.mpr h1, one_div_pos.mpr h2⟩

theorem hinv_hinv {c : ℝ × ℝ} (_hc : c ∈ orthant) : hinv (hinv c) = c := by
  ext <;> simp [hinv]

theorem continuousOn_hinv : ContinuousOn hinv orthant := by
  apply ContinuousOn.prodMk
  · exact continuousOn_const.div continuousOn_fst fun p hp => (mem_orthant.mp hp).1.ne'
  · exact continuousOn_const.div continuousOn_snd fun p hp => (mem_orthant.mp hp).2.ne'

theorem hadamard_mem_quadrant {p x : ℝ × ℝ} (hp : p ∈ quadrant) (hx : x ∈ quadrant) :
    hadamard p x ∈ quadrant := by
  obtain ⟨h1, h2⟩ := mem_quadrant.mp hp
  obtain ⟨h3, h4⟩ := mem_quadrant.mp hx
  exact mem_quadrant.mpr ⟨mul_nonneg h1 h3, mul_nonneg h2 h4⟩

theorem mem_quadrant_of_hadamard_mem {p x : ℝ × ℝ} (hp : p ∈ orthant)
    (hx : hadamard p x ∈ quadrant) : x ∈ quadrant := by
  have := hadamard_mem_quadrant (orthant_subset_quadrant (hinv_mem_orthant hp)) hx
  rwa [hadamard_hinv_hadamard hp] at this

theorem continuous_hadamard (p : ℝ × ℝ) : Continuous (hadamard p) := by
  unfold hadamard
  fun_prop

theorem hadamard_injective {c : ℝ × ℝ} (hc : c ∈ orthant) : Function.Injective (hadamard c) :=
  Function.LeftInverse.injective (hadamard_hinv_hadamard hc)

/-- Transport of "frequently near `x₀`" along a coordinatewise scaling. -/
theorem frequently_hadamard {c x₀ : ℝ × ℝ} (hc : c ∈ orthant) {P : ℝ × ℝ → Prop}
    (h : ∃ᶠ u in 𝓝 (hadamard c x₀), P u) : ∃ᶠ x in 𝓝 x₀, P (hadamard c x) := by
  have hT : Tendsto (hadamard (hinv c)) (𝓝 (hadamard c x₀)) (𝓝 x₀) := by
    have := (continuous_hadamard (hinv c)).tendsto (hadamard c x₀)
    rwa [hadamard_hinv_hadamard hc] at this
  refine hT.frequently (h.mono fun u hu => ?_)
  rwa [hadamard_hadamard_hinv hc]

/-! ### Level curves, intersections, chambers -/

/-- Intersection points of the unit level curves of `h` and of `h (p ∘ ·)`, in the closed
quadrant. -/
def levelIntersections (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ quadrant ∧ h x = 1 ∧ h (hadamard p x) = 1}

/-- `onSide s v` says on which side of `1` the value `v` lies: `v < 1` for `s = true`,
`1 < v` for `s = false`. -/
def onSide : Bool → ℝ → Prop
  | true, v => v < 1
  | false, v => 1 < v

/-- `x₀` has *four chambers* for `(h, p)`: every neighbourhood of `x₀` contains points of the
quadrant realising each of the four sign patterns of `(h - 1, h (p ∘ ·) - 1)`. -/
def FourChambers (h : ℝ × ℝ → ℝ) (p x₀ : ℝ × ℝ) : Prop :=
  ∀ s₁ s₂ : Bool, ∃ᶠ x in 𝓝 x₀, x ∈ quadrant ∧ onSide s₁ (h x) ∧ onSide s₂ (h (hadamard p x))

/-! ### No intersections when both prices are on the same side of `1` -/

theorem IsNeoclassical.levelIntersections_eq_empty_of_one_lt {h : ℝ × ℝ → ℝ}
    (hh : IsNeoclassical h) {p : ℝ × ℝ} (hp1 : 1 < p.1) (hp2 : 1 < p.2) :
    levelIntersections h p = ∅ := by
  ext x
  simp only [levelIntersections, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro hx h1 h2
  obtain ⟨hx1, hx2⟩ := mem_quadrant.mp hx
  set m := min p.1 p.2 with hm
  have hm1 : 1 < m := lt_min hp1 hp2
  have hmp1 : m ≤ p.1 := min_le_left _ _
  have hmp2 : m ≤ p.2 := min_le_right _ _
  have hd : hadamard p x = m • x + ((p.1 - m) * x.1, (p.2 - m) * x.2) := by
    ext <;> simp [hadamard] <;> ring
  have hdq : ((p.1 - m) * x.1, (p.2 - m) * x.2) ∈ quadrant :=
    mk_mem_quadrant (mul_nonneg (by linarith) hx1) (mul_nonneg (by linarith) hx2)
  have := hh.mono (quadrant_smul (by linarith) hx) hdq
  rw [← hd, hh.homogeneous m (by linarith) x hx, h1, h2, mul_one] at this
  linarith

theorem IsNeoclassical.levelIntersections_eq_empty_of_lt_one {h : ℝ × ℝ → ℝ}
    (hh : IsNeoclassical h) {p : ℝ × ℝ} (hp : p ∈ orthant) (hp1 : p.1 < 1) (hp2 : p.2 < 1) :
    levelIntersections h p = ∅ := by
  ext x
  simp only [levelIntersections, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro hx h1 h2
  obtain ⟨hx1, hx2⟩ := mem_quadrant.mp hx
  obtain ⟨hp1', hp2'⟩ := mem_orthant.mp hp
  set M := max p.1 p.2 with hM
  have hM1 : M < 1 := max_lt hp1 hp2
  have hM0 : 0 < M := hp1'.trans_le (le_max_left _ _)
  have hMp1 : p.1 ≤ M := le_max_left _ _
  have hMp2 : p.2 ≤ M := le_max_right _ _
  have hd : M • x = hadamard p x + ((M - p.1) * x.1, (M - p.2) * x.2) := by
    ext <;> simp [hadamard] <;> ring
  have hdq : ((M - p.1) * x.1, (M - p.2) * x.2) ∈ quadrant :=
    mk_mem_quadrant (mul_nonneg (by linarith) hx1) (mul_nonneg (by linarith) hx2)
  have := hh.mono (hadamard_mem_quadrant (orthant_subset_quadrant hp) hx) hdq
  rw [← hd, hh.homogeneous M hM0 x hx, h1, h2, mul_one] at this
  linarith

/-! ### The substitution `x ↦ p ∘ x` exchanges the two curves -/

theorem levelIntersections_hinv {h : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ orthant) :
    levelIntersections h p = hadamard (hinv p) '' levelIntersections h (hinv p) := by
  ext x
  constructor
  · rintro ⟨hx, h1, h2⟩
    refine ⟨hadamard p x, ⟨hadamard_mem_quadrant (orthant_subset_quadrant hp) hx, h2, ?_⟩,
      hadamard_hinv_hadamard hp x⟩
    rwa [hadamard_hinv_hadamard hp]
  · rintro ⟨y, ⟨hy, h1, h2⟩, rfl⟩
    refine ⟨hadamard_mem_quadrant (orthant_subset_quadrant (hinv_mem_orthant hp)) hy, h2, ?_⟩
    rwa [hadamard_hadamard_hinv hp]

theorem FourChambers.of_hinv {h : ℝ × ℝ → ℝ} {p x₀ : ℝ × ℝ} (hp : p ∈ orthant)
    (H : FourChambers h (hinv p) (hadamard p x₀)) : FourChambers h p x₀ := by
  intro s₁ s₂
  have := frequently_hadamard hp (H s₂ s₁)
  refine this.mono fun x ⟨hx, h1, h2⟩ => ?_
  rw [hadamard_hinv_hadamard hp] at h2
  exact ⟨mem_quadrant_of_hadamard_mem hp hx, h2, h1⟩

/-! ### Normalisation: transport along `x ↦ (h (1,0) x₁, h (0,1) x₂)` -/

namespace IsBddNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsBddNeoclassical h)
include hh

/-- The normalising scaling. -/
theorem scaling_mem_orthant : (h (1, 0), h (0, 1)) ∈ orthant :=
  mem_orthant.mpr ⟨hh.pos_fst, hh.pos_snd⟩

theorem eq_ofProfile_hadamard {x : ℝ × ℝ} (hx : x ∈ quadrant) :
    h x = ofProfile (profile h) (hadamard (h (1, 0), h (0, 1)) x) :=
  (hh.ofProfile_profile hx).symm

theorem levelIntersections_eq_preimage {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    levelIntersections h p =
      hadamard (h (1, 0), h (0, 1)) ⁻¹' levelIntersections (ofProfile (profile h)) p := by
  have hc := hh.scaling_mem_orthant
  ext x
  simp only [levelIntersections, mem_preimage, mem_setOf_eq]
  constructor
  · rintro ⟨hx, h1, h2⟩
    refine ⟨hadamard_mem_quadrant (orthant_subset_quadrant hc) hx, ?_, ?_⟩
    · rw [← hh.eq_ofProfile_hadamard hx]
      exact h1
    · rw [hadamard_comm, ← hh.eq_ofProfile_hadamard (hadamard_mem_quadrant hp hx)]
      exact h2
  · rintro ⟨hx, h1, h2⟩
    have hx' := mem_quadrant_of_hadamard_mem hc hx
    refine ⟨hx', ?_, ?_⟩
    · rw [hh.eq_ofProfile_hadamard hx']
      exact h1
    · rw [hh.eq_ofProfile_hadamard (hadamard_mem_quadrant hp hx'), hadamard_comm]
      exact h2

theorem fourChambers_of_ofProfile {p x₀ : ℝ × ℝ} (hp : p ∈ quadrant)
    (H : FourChambers (ofProfile (profile h)) p (hadamard (h (1, 0), h (0, 1)) x₀)) :
    FourChambers h p x₀ := by
  have hc := hh.scaling_mem_orthant
  intro s₁ s₂
  refine (frequently_hadamard hc (H s₁ s₂)).mono fun x ⟨hx, h1, h2⟩ => ?_
  have hx' := mem_quadrant_of_hadamard_mem hc hx
  refine ⟨hx', ?_, ?_⟩
  · rwa [hh.eq_ofProfile_hadamard hx']
  · rwa [hh.eq_ofProfile_hadamard (hadamard_mem_quadrant hp hx'), hadamard_comm]

end IsBddNeoclassical

/-! ### One-sided slopes and signs -/

/-- A function vanishing at `t₀` with a negative (resp. positive) right derivative is negative
(resp. positive) immediately to the right of `t₀`. -/
theorem eventually_sign_of_hasDerivWithinAt_Ioi {φ : ℝ → ℝ} {t₀ d : ℝ}
    (h : HasDerivWithinAt φ d (Ioi t₀) t₀) (h0 : φ t₀ = 0) :
    (d < 0 → ∀ᶠ t in 𝓝[>] t₀, φ t < 0) ∧ (0 < d → ∀ᶠ t in 𝓝[>] t₀, 0 < φ t) := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at h
  have hle : 𝓝[>] t₀ ≤ 𝓝[Ioi t₀ \ {t₀}] t₀ :=
    nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_gt hz⟩
  have hT := h.mono_left hle
  constructor
  · intro hd
    filter_upwards [hT.eventually_lt_const hd, self_mem_nhdsWithin] with t ht ht'
    rw [slope_def_field, h0, sub_zero, div_lt_iff₀ (sub_pos.mpr ht'), zero_mul] at ht
    exact ht
  · intro hd
    filter_upwards [hT.eventually_const_lt hd, self_mem_nhdsWithin] with t ht ht'
    rw [slope_def_field, h0, sub_zero, lt_div_iff₀ (sub_pos.mpr ht'), zero_mul] at ht
    exact ht

/-- A function vanishing at `t₀` with a negative (resp. positive) left derivative is positive
(resp. negative) immediately to the left of `t₀`. -/
theorem eventually_sign_of_hasDerivWithinAt_Iio {φ : ℝ → ℝ} {t₀ d : ℝ}
    (h : HasDerivWithinAt φ d (Iio t₀) t₀) (h0 : φ t₀ = 0) :
    (d < 0 → ∀ᶠ t in 𝓝[<] t₀, 0 < φ t) ∧ (0 < d → ∀ᶠ t in 𝓝[<] t₀, φ t < 0) := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at h
  have hle : 𝓝[<] t₀ ≤ 𝓝[Iio t₀ \ {t₀}] t₀ :=
    nhdsWithin_mono _ fun z hz => ⟨hz, ne_of_lt hz⟩
  have hT := h.mono_left hle
  constructor
  · intro hd
    filter_upwards [hT.eventually_lt_const hd, self_mem_nhdsWithin] with t ht ht'
    rw [slope_def_field, h0, sub_zero, div_lt_iff_of_neg (sub_neg.mpr ht'), zero_mul] at ht
    exact ht
  · intro hd
    filter_upwards [hT.eventually_const_lt hd, self_mem_nhdsWithin] with t ht ht'
    rw [slope_def_field, h0, sub_zero, lt_div_iff_of_neg (sub_neg.mpr ht'), zero_mul] at ht
    exact ht

/-- The subdifferential is an interval. -/
theorem mem_subdiff_of_between {f : ℝ → ℝ} {y a b t : ℝ} (ha : a ∈ subdiff f y)
    (hb : b ∈ subdiff f y) (hat : a ≤ t) (htb : t ≤ b) : t ∈ subdiff f y := by
  intro z hz
  rcases le_or_gt y z with hyz | hyz
  · have h1 := hb z hz
    have h2 := mul_le_mul_of_nonneg_right htb (sub_nonneg.mpr hyz)
    linarith
  · have h1 := ha z hz
    have h2 := mul_le_mul_of_nonpos_right hat (sub_nonpos.mpr hyz.le)
    linarith

/-- To show a property holds frequently near `x₀`, exhibit witnesses in every ball. -/
theorem frequently_nhds_of_forall_ball {X : Type*} [PseudoMetricSpace X] {x₀ : X} {Q : X → Prop}
    (h : ∀ ε > 0, ∃ x, dist x x₀ < ε ∧ Q x) : ∃ᶠ x in 𝓝 x₀, Q x := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨x, hx, hQ⟩ := h ε hε
  exact ⟨x, hball (Metric.mem_ball.mpr hx), hQ⟩

/-! ### The normalised picture: graphs of the profile -/

namespace IsProfile

variable {f : ℝ → ℝ} (hf : IsProfile f)
include hf

theorem one_lt_ofProfile_iff {u : ℝ × ℝ} (hu : u ∈ quadrant) (hu1 : u.1 ≤ 1) :
    1 < ofProfile f u ↔ f u.1 < u.2 := by
  rw [ofProfile_eq_of_mem hu, hf.lt_ofProfile₀_iff hu hu1, one_mul, div_one]

theorem ofProfile_lt_one_iff {u : ℝ × ℝ} (hu : u ∈ quadrant) (hu1 : u.1 ≤ 1) :
    ofProfile f u < 1 ↔ u.2 < f u.1 := by
  rw [ofProfile_eq_of_mem hu, hf.ofProfile₀_lt_iff hu hu1, one_mul, div_one]

theorem ofProfile_eq_one_iff {u : ℝ × ℝ} (hu : u ∈ quadrant) (hu1 : u.1 ≤ 1) :
    ofProfile f u = 1 ↔ f u.1 = u.2 := by
  constructor
  · intro h
    have h1 : ¬ f u.1 < u.2 := by
      rw [← hf.one_lt_ofProfile_iff hu hu1, h]
      exact lt_irrefl _
    have h2 : ¬ u.2 < f u.1 := by
      rw [← hf.ofProfile_lt_one_iff hu hu1, h]
      exact lt_irrefl _
    exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
  · intro h
    have h1 : ¬ 1 < ofProfile f u := by
      rw [hf.one_lt_ofProfile_iff hu hu1, h]
      exact lt_irrefl _
    have h2 : ¬ ofProfile f u < 1 := by
      rw [hf.ofProfile_lt_one_iff hu hu1, h]
      exact lt_irrefl _
    exact le_antisymm (not_lt.mp h1) (not_lt.mp h2)

theorem one_lt_ofProfile_of_one_lt {u : ℝ × ℝ} (hu : u ∈ quadrant) (hu1 : 1 < u.1) :
    1 < ofProfile f u := by
  rw [ofProfile_eq_of_mem hu]
  exact hu1.trans_le (hf.fst_le_ofProfile₀ hu)

/-- Parametrisation of the intersections by the solutions of the profile equation
`f (p₁ t) = p₂ f t`, written as `(1 / p₂) f y = f ((1 / p₁) y)` with `y = p₁ t`. -/
theorem levelIntersections_ofProfile {p : ℝ × ℝ} (hp1 : 1 ≤ p.1) (hp2 : 0 < p.2) :
    levelIntersections (ofProfile f) p =
      (fun y => (y / p.1, f (y / p.1))) '' solutions f (1 / p.2, 1 / p.1) := by
  have hp1' : 0 < p.1 := by linarith
  have hp2' : p.2 ≠ 0 := hp2.ne'
  have hp1'' : p.1 ≠ 0 := hp1'.ne'
  ext u
  constructor
  · rintro ⟨hu, h1, h2⟩
    obtain ⟨hu1', hu2'⟩ := mem_quadrant.mp hu
    have hu1 : u.1 ≤ 1 := by
      by_contra h
      push_neg at h
      exact (hf.one_lt_ofProfile_of_one_lt hu h).ne' h1
    have hpu : hadamard p u ∈ quadrant :=
      hadamard_mem_quadrant (mk_mem_quadrant hp1'.le hp2.le) hu
    have hpu1 : p.1 * u.1 ≤ 1 := by
      by_contra h
      push_neg at h
      exact (hf.one_lt_ofProfile_of_one_lt hpu h).ne' h2
    rw [hf.ofProfile_eq_one_iff hu hu1] at h1
    rw [hf.ofProfile_eq_one_iff hpu hpu1] at h2
    simp only [hadamard_fst, hadamard_snd] at h2
    refine ⟨p.1 * u.1, ⟨⟨mul_nonneg hp1'.le hu1', hpu1⟩, ?_⟩, ?_⟩
    · show 1 / p.2 * f (p.1 * u.1) = f (1 / p.1 * (p.1 * u.1))
      rw [h2, show 1 / p.1 * (p.1 * u.1) = u.1 by field_simp, h1]
      field_simp
    · show (p.1 * u.1 / p.1, f (p.1 * u.1 / p.1)) = u
      rw [show p.1 * u.1 / p.1 = u.1 by field_simp, h1]
  · rintro ⟨y, ⟨⟨hy0, hy1⟩, hy⟩, rfl⟩
    have hy' : 1 / p.2 * f y = f (1 / p.1 * y) := hy
    have ht0 : 0 ≤ y / p.1 := div_nonneg hy0 hp1'.le
    have ht1 : y / p.1 ≤ 1 := (div_le_one hp1').mpr (hy1.trans hp1)
    have hft : 0 ≤ f (y / p.1) := hf.nonneg ⟨ht0, ht1⟩
    have hu : (y / p.1, f (y / p.1)) ∈ quadrant := mk_mem_quadrant ht0 hft
    have hpu : hadamard p (y / p.1, f (y / p.1)) = (y, p.2 * f (y / p.1)) := by
      simp only [hadamard_mk]
      rw [mul_div_cancel₀ _ hp1'']
    have hpuq : (y, p.2 * f (y / p.1)) ∈ quadrant := mk_mem_quadrant hy0 (mul_nonneg hp2.le hft)
    refine ⟨hu, (hf.ofProfile_eq_one_iff hu ht1).mpr rfl, ?_⟩
    rw [hpu, hf.ofProfile_eq_one_iff hpuq hy1]
    show f y = p.2 * f (y / p.1)
    rw [show 1 / p.1 * y = y / p.1 by ring] at hy'
    field_simp at hy'
    linear_combination hy'

/-- Signs of the one-sided derivatives of `φ t = f t - f (p₁ t) / p₂` at a transversal
intersection: both are strictly negative or both are strictly positive. -/
theorem slopes_of_transversal {p : ℝ × ℝ} (hp1 : 1 < p.1) (hp2 : 0 < p.2) (hp2' : p.2 < 1)
    (ht : Transversal f (1 / p.2, 1 / p.1)) {t₀ : ℝ}
    (hy₀ : p.1 * t₀ ∈ solutions f (1 / p.2, 1 / p.1)) :
    ∃ dR dL : ℝ, HasDerivWithinAt (fun t => f t - f (p.1 * t) / p.2) dR (Ioi t₀) t₀ ∧
      HasDerivWithinAt (fun t => f t - f (p.1 * t) / p.2) dL (Iio t₀) t₀ ∧
      ((dR < 0 ∧ dL < 0) ∨ (0 < dR ∧ 0 < dL)) := by
  have hp1' : 0 < p.1 := by linarith
  have hP : (1 / p.2, 1 / p.1) ∈ Param :=
    mem_Param.mpr ⟨(one_lt_div hp2).mpr hp2', one_div_pos.mpr hp1', (div_lt_one hp1').mpr hp1⟩
  set y₀ := p.1 * t₀ with hy₀def
  have hy₀I : y₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hy₀.1.1 fun h => hf.zero_not_mem_solutions hP (h ▸ hy₀),
      lt_of_le_of_ne hy₀.1.2 fun h => hf.one_not_mem_solutions hP (h ▸ hy₀)⟩
  have ht₀I : t₀ ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · have : 0 < p.1 * t₀ := hy₀I.1
      exact pos_of_mul_pos_right this hp1'.le
    · have h1 : t₀ ≤ p.1 * t₀ := le_mul_of_one_le_left (by
        have : 0 < p.1 * t₀ := hy₀I.1
        exact (pos_of_mul_pos_right this hp1'.le).le) hp1.le
      exact h1.trans_lt hy₀I.2
  -- one-sided derivatives of `f` at `t₀` and at `y₀`
  set AL := derivWithin f (Iio t₀) t₀ with hAL
  set AR := derivWithin f (Ioi t₀) t₀ with hAR
  set BL := derivWithin f (Iio y₀) y₀ with hBL
  set BR := derivWithin f (Ioi y₀) y₀ with hBR
  have hALm : AL ∈ subdiff f t₀ := hf.leftDeriv_mem_subdiff ht₀I
  have hARm : AR ∈ subdiff f t₀ := hf.rightDeriv_mem_subdiff ht₀I
  have hBLm : BL ∈ subdiff f y₀ := hf.leftDeriv_mem_subdiff hy₀I
  have hBRm : BR ∈ subdiff f y₀ := hf.rightDeriv_mem_subdiff hy₀I
  have hAle : AL ≤ AR := hf.convexOn.leftDeriv_le_rightDeriv_of_mem_interior (mem_interior_Icc01 ht₀I)
  have hBle : BL ≤ BR := hf.convexOn.leftDeriv_le_rightDeriv_of_mem_interior (mem_interior_Icc01 hy₀I)
  -- transversality in the form `p₂ a ≠ p₁ b`
  have htr : ∀ a ∈ subdiff f t₀, ∀ b ∈ subdiff f y₀, p.2 * a ≠ p.1 * b := by
    intro a ha b hb hab
    have h1 : 1 / p.1 * y₀ = t₀ := by rw [hy₀def]; field_simp
    have := ht y₀ hy₀ a (by rw [show (1 / p.2, 1 / p.1).2 * y₀ = t₀ from h1]; exact ha) b hb
    apply this
    show 1 / p.1 * a = 1 / p.2 * b
    field_simp
    linear_combination hab
  -- the two scaled intervals are disjoint, hence one lies entirely below the other
  have key : p.2 * AR < p.1 * BL ∨ p.1 * BR < p.2 * AL := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    set m := max (p.2 * AL) (p.1 * BL) with hm
    have ha : m / p.2 ∈ subdiff f t₀ := by
      refine mem_subdiff_of_between hALm hARm ?_ ?_
      · rw [le_div_iff₀ hp2, mul_comm]
        exact le_max_left _ _
      · rw [div_le_iff₀ hp2, mul_comm]
        exact max_le (mul_le_mul_of_nonneg_left hAle hp2.le) hc1
    have hb : m / p.1 ∈ subdiff f y₀ := by
      refine mem_subdiff_of_between hBLm hBRm ?_ ?_
      · rw [le_div_iff₀ hp1', mul_comm]
        exact le_max_right _ _
      · rw [div_le_iff₀ hp1', mul_comm]
        exact max_le hc2 (mul_le_mul_of_nonneg_left hBle hp1'.le)
    have e1 : p.2 * (m / p.2) = m := by field_simp
    have e2 : p.1 * (m / p.1) = m := by field_simp
    exact htr _ ha _ hb (e1.trans e2.symm)
  -- the one-sided derivatives of `φ`
  have hlin : HasDerivWithinAt (fun t : ℝ => p.1 * t) p.1 (Ioi t₀) t₀ := by
    simpa using ((hasDerivAt_id t₀).const_mul p.1).hasDerivWithinAt
  have hlin' : HasDerivWithinAt (fun t : ℝ => p.1 * t) p.1 (Iio t₀) t₀ := by
    simpa using ((hasDerivAt_id t₀).const_mul p.1).hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ => p.1 * t) (Ioi t₀) (Ioi (p.1 * t₀)) :=
    fun z hz => mul_lt_mul_of_pos_left hz hp1'
  have hmaps' : MapsTo (fun t : ℝ => p.1 * t) (Iio t₀) (Iio (p.1 * t₀)) :=
    fun z hz => mul_lt_mul_of_pos_left hz hp1'
  have hARd : HasDerivWithinAt f AR (Ioi t₀) t₀ :=
    hf.convexOn.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc01 ht₀I)
  have hALd : HasDerivWithinAt f AL (Iio t₀) t₀ :=
    hf.convexOn.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc01 ht₀I)
  have hBRd : HasDerivWithinAt f BR (Ioi (p.1 * t₀)) (p.1 * t₀) :=
    hf.convexOn.hasDerivWithinAt_rightDeriv_of_mem_interior (mem_interior_Icc01 hy₀I)
  have hBLd : HasDerivWithinAt f BL (Iio (p.1 * t₀)) (p.1 * t₀) :=
    hf.convexOn.hasDerivWithinAt_leftDeriv_of_mem_interior (mem_interior_Icc01 hy₀I)
  have hφR : HasDerivWithinAt (fun t => f t - f (p.1 * t) / p.2) (AR - BR * p.1 / p.2)
      (Ioi t₀) t₀ := hARd.sub ((hBRd.comp t₀ hlin hmaps).div_const p.2)
  have hφL : HasDerivWithinAt (fun t => f t - f (p.1 * t) / p.2) (AL - BL * p.1 / p.2)
      (Iio t₀) t₀ := hALd.sub ((hBLd.comp t₀ hlin' hmaps').div_const p.2)
  refine ⟨_, _, hφR, hφL, ?_⟩
  rcases key with hk | hk
  · left
    constructor
    · rw [sub_neg, lt_div_iff₀ hp2, mul_comm AR, mul_comm BR]
      linarith [mul_le_mul_of_nonneg_left hBle hp1'.le]
    · rw [sub_neg, lt_div_iff₀ hp2, mul_comm AL, mul_comm BL]
      linarith [mul_le_mul_of_nonneg_left hAle hp2.le]
  · right
    constructor
    · rw [sub_pos, div_lt_iff₀ hp2, mul_comm AR, mul_comm BR]
      linarith [mul_le_mul_of_nonneg_left hAle hp2.le]
    · rw [sub_pos, div_lt_iff₀ hp2, mul_comm AL, mul_comm BL]
      linarith [mul_le_mul_of_nonneg_left hBle hp1'.le]

/-- **Four chambers at a transversal intersection** (normalised case). -/
theorem fourChambers_ofProfile {p : ℝ × ℝ} (hp1 : 1 < p.1) (hp2 : 0 < p.2) (hp2' : p.2 < 1)
    (ht : Transversal f (1 / p.2, 1 / p.1)) {u₀ : ℝ × ℝ}
    (hu₀ : u₀ ∈ levelIntersections (ofProfile f) p) : FourChambers (ofProfile f) p u₀ := by
  have hp1' : 0 < p.1 := by linarith
  have hP : (1 / p.2, 1 / p.1) ∈ Param :=
    mem_Param.mpr ⟨(one_lt_div hp2).mpr hp2', one_div_pos.mpr hp1', (div_lt_one hp1').mpr hp1⟩
  rw [hf.levelIntersections_ofProfile hp1.le hp2] at hu₀
  obtain ⟨y₀, hy₀, rfl⟩ := hu₀
  set t₀ := y₀ / p.1 with ht₀
  have hy₀t : p.1 * t₀ = y₀ := by rw [ht₀]; field_simp
  have hy₀I : y₀ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hy₀.1.1 fun h => hf.zero_not_mem_solutions hP (h ▸ hy₀),
      lt_of_le_of_ne hy₀.1.2 fun h => hf.one_not_mem_solutions hP (h ▸ hy₀)⟩
  have ht₀0 : 0 < t₀ := div_pos hy₀I.1 hp1'
  have ht₀1 : t₀ < 1 / p.1 := by rw [ht₀]; exact div_lt_div_of_pos_right hy₀I.2 hp1'
  have h1p : 1 / p.1 < 1 := (div_lt_one hp1').mpr hp1
  have ht₀I : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨ht₀0, ht₀1.trans h1p⟩
  have hft₀ : 0 < f t₀ := hf.pos ⟨ht₀0.le, ht₀I.2⟩
  -- the solution equation
  have hsol : f (p.1 * t₀) = p.2 * f t₀ := by
    have h := hy₀.2
    have h' : 1 / p.2 * f y₀ = f (1 / p.1 * y₀) := h
    rw [show 1 / p.1 * y₀ = t₀ by rw [ht₀]; ring] at h'
    rw [hy₀t]
    field_simp at h'
    linear_combination h'
  have hg0 : f (p.1 * t₀) / p.2 = f t₀ := by
    rw [hsol, mul_div_cancel_left₀ _ hp2.ne']
  -- signs of the one-sided slopes of `φ`
  obtain ⟨dR, dL, hdR, hdL, hsign⟩ :=
    hf.slopes_of_transversal hp1 hp2 hp2' ht (by rw [hy₀t]; exact hy₀)
  have h0 : (fun t => f t - f (p.1 * t) / p.2) t₀ = 0 := by
    show f t₀ - f (p.1 * t₀) / p.2 = 0
    rw [hg0, sub_self]
  have hR := eventually_sign_of_hasDerivWithinAt_Ioi hdR h0
  have hL := eventually_sign_of_hasDerivWithinAt_Iio hdL h0
  have hneg : ∃ l : Filter ℝ, l.NeBot ∧ l ≤ 𝓝 t₀ ∧ ∀ᶠ t in l, f t - f (p.1 * t) / p.2 < 0 := by
    rcases hsign with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact ⟨𝓝[>] t₀, inferInstance, nhdsWithin_le_nhds, hR.1 h1⟩
    · exact ⟨𝓝[<] t₀, inferInstance, nhdsWithin_le_nhds, hL.2 h2⟩
  have hpos : ∃ l : Filter ℝ, l.NeBot ∧ l ≤ 𝓝 t₀ ∧ ∀ᶠ t in l, 0 < f t - f (p.1 * t) / p.2 := by
    rcases hsign with ⟨_, h1⟩ | ⟨h2, _⟩
    · exact ⟨𝓝[<] t₀, inferInstance, nhdsWithin_le_nhds, hL.1 h1⟩
    · exact ⟨𝓝[>] t₀, inferInstance, nhdsWithin_le_nhds, hR.2 h2⟩
  -- continuity: nearby `t` have `f t`, `f (p₁ t) / p₂` close to `f t₀`
  have hcf : ContinuousAt f t₀ := hf.continuousOn.continuousAt (Icc_mem_nhds ht₀0 ht₀I.2)
  have hcg : ContinuousAt (fun t => f (p.1 * t) / p.2) t₀ := by
    have h1 : ContinuousAt f (p.1 * t₀) :=
      hf.continuousOn.continuousAt (Icc_mem_nhds (by rw [hy₀t]; exact hy₀I.1)
        (by rw [hy₀t]; exact hy₀I.2))
    exact (h1.comp (by fun_prop : Continuous fun t : ℝ => p.1 * t).continuousAt).div_const p.2
  have hev : ∀ ε > 0, ∀ᶠ t in 𝓝 t₀, |t - t₀| < ε ∧ |f t - f t₀| < ε ∧
      |f (p.1 * t) / p.2 - f t₀| < ε ∧ 0 < t ∧ p.1 * t < 1 := by
    intro ε hε
    have e1 : ∀ᶠ t in 𝓝 t₀, |t - t₀| < ε := by
      filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
      rwa [Metric.mem_ball, Real.dist_eq] at ht
    have e2 : ∀ᶠ t in 𝓝 t₀, |f t - f t₀| < ε := by
      filter_upwards [(hcf : Tendsto f (𝓝 t₀) (𝓝 (f t₀))).eventually
        (Metric.ball_mem_nhds (f t₀) hε)] with t ht
      rwa [Real.dist_eq] at ht
    have e3 : ∀ᶠ t in 𝓝 t₀, |f (p.1 * t) / p.2 - f t₀| < ε := by
      filter_upwards [(hcg : Tendsto (fun t => f (p.1 * t) / p.2) (𝓝 t₀)
        (𝓝 (f (p.1 * t₀) / p.2))).eventually (Metric.ball_mem_nhds _ hε)] with t ht
      rwa [Real.dist_eq, hg0] at ht
    have e4 : ∀ᶠ t in 𝓝 t₀, 0 < t := Ioi_mem_nhds ht₀0
    have e5 : ∀ᶠ t in 𝓝 t₀, p.1 * t < 1 := by
      filter_upwards [Iio_mem_nhds ht₀1] with t ht
      have := (lt_div_iff₀ hp1').mp ht
      linarith
    filter_upwards [e1, e2, e3, e4, e5] with t h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have habs : ∀ a b : ℝ, ∀ ε > 0, |a| < ε → |b| < ε → |(a + b) / 2| < ε := by
    intro a b ε _ ha hb
    obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
    obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdist : ∀ t x₂ : ℝ, dist (t, x₂) (t₀, f t₀) = max |t - t₀| |x₂ - f t₀| := by
    intro t x₂
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  -- the sign pattern of `(F u, F (p ∘ u))` for `u = (t, x₂)`
  have hpat : ∀ t x₂ : ℝ, 0 ≤ t → t ≤ 1 → p.1 * t ≤ 1 → 0 ≤ x₂ →
      (t, x₂) ∈ quadrant ∧ (ofProfile f (t, x₂) < 1 ↔ x₂ < f t) ∧
        (1 < ofProfile f (t, x₂) ↔ f t < x₂) ∧
        (ofProfile f (hadamard p (t, x₂)) < 1 ↔ p.2 * x₂ < f (p.1 * t)) ∧
        (1 < ofProfile f (hadamard p (t, x₂)) ↔ f (p.1 * t) < p.2 * x₂) := by
    intro t x₂ ht0 ht1 hpt hx2
    have hu : (t, x₂) ∈ quadrant := mk_mem_quadrant ht0 hx2
    have hpu : (p.1 * t, p.2 * x₂) ∈ quadrant :=
      mk_mem_quadrant (mul_nonneg hp1'.le ht0) (mul_nonneg hp2.le hx2)
    refine ⟨hu, hf.ofProfile_lt_one_iff hu ht1, hf.one_lt_ofProfile_iff hu ht1, ?_, ?_⟩
    · rw [hadamard_mk]
      exact hf.ofProfile_lt_one_iff hpu hpt
    · rw [hadamard_mk]
      exact hf.one_lt_ofProfile_iff hpu hpt
  have hpt₀ : p.1 * t₀ ≤ 1 := by rw [hy₀t]; exact hy₀I.2.le
  -- a point on the wrong side of both graphs, from a sign of `φ` along a filter `l`
  have hmixed : ∀ l : Filter ℝ, l.NeBot → l ≤ 𝓝 t₀ →
      ∀ ε > 0, ∃ t, (∀ᶠ s in l, s = t → True) ∧ (|t - t₀| < ε ∧ |f t - f t₀| < ε ∧
        |f (p.1 * t) / p.2 - f t₀| < ε ∧ 0 < t ∧ p.1 * t < 1) ∧ True := by
    intro l hl hle ε hε
    haveI := hl
    obtain ⟨t, ht⟩ := ((hev ε hε).filter_mono hle).exists
    exact ⟨t, by simp, ht, trivial⟩
  intro s₁ s₂
  cases s₁ <;> cases s₂
  · -- `1 < F u`, `1 < F (p ∘ u)`: above both graphs
    apply frequently_nhds_of_forall_ball
    intro ε hε
    refine ⟨(t₀, f t₀ + ε / 2), ?_, ?_⟩
    · rw [hdist, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      exact max_lt hε (by linarith)
    · obtain ⟨hu, -, h2, -, h4⟩ := hpat t₀ (f t₀ + ε / 2) ht₀0.le ht₀I.2.le hpt₀ (by linarith)
      refine ⟨hu, h2.mpr (by linarith), h4.mpr ?_⟩
      rw [hsol]
      exact mul_lt_mul_of_pos_left (by linarith) hp2
  · -- `1 < F u`, `F (p ∘ u) < 1`: between the graphs where `f < g`
    obtain ⟨l, hl, hle, hφ⟩ := hneg
    apply frequently_nhds_of_forall_ball
    intro ε hε
    haveI := hl
    obtain ⟨t, hφt, ht1, ht2, ht3, ht4, ht5⟩ := (hφ.and ((hev ε hε).filter_mono hle)).exists
    set g := f (p.1 * t) / p.2 with hg
    have hfg : f t < g := by linarith
    have htle : t ≤ 1 := (le_mul_of_one_le_left ht4.le hp1.le).trans ht5.le
    have hg0' : 0 ≤ g := div_nonneg (hf.nonneg ⟨mul_nonneg hp1'.le ht4.le, ht5.le⟩) hp2.le
    have hpg : p.2 * g = f (p.1 * t) := by rw [hg, mul_div_cancel₀ _ hp2.ne']
    refine ⟨(t, (f t + g) / 2), ?_, ?_⟩
    · rw [hdist]
      refine max_lt ht1 ?_
      rw [show (f t + g) / 2 - f t₀ = ((f t - f t₀) + (g - f t₀)) / 2 by ring]
      exact habs _ _ ε hε ht2 ht3
    · obtain ⟨hu, -, h2, h3, -⟩ := hpat t ((f t + g) / 2) ht4.le htle ht5.le
        (by linarith [hf.nonneg ⟨ht4.le, htle⟩])
      refine ⟨hu, h2.mpr (by linarith), h3.mpr ?_⟩
      calc p.2 * ((f t + g) / 2) < p.2 * g := mul_lt_mul_of_pos_left (by linarith) hp2
        _ = f (p.1 * t) := hpg
  · -- `F u < 1`, `1 < F (p ∘ u)`: between the graphs where `g < f`
    obtain ⟨l, hl, hle, hφ⟩ := hpos
    apply frequently_nhds_of_forall_ball
    intro ε hε
    haveI := hl
    obtain ⟨t, hφt, ht1, ht2, ht3, ht4, ht5⟩ := (hφ.and ((hev ε hε).filter_mono hle)).exists
    set g := f (p.1 * t) / p.2 with hg
    have hfg : g < f t := by linarith
    have htle : t ≤ 1 := (le_mul_of_one_le_left ht4.le hp1.le).trans ht5.le
    have hg0' : 0 ≤ g := div_nonneg (hf.nonneg ⟨mul_nonneg hp1'.le ht4.le, ht5.le⟩) hp2.le
    have hpg : p.2 * g = f (p.1 * t) := by rw [hg, mul_div_cancel₀ _ hp2.ne']
    refine ⟨(t, (f t + g) / 2), ?_, ?_⟩
    · rw [hdist]
      refine max_lt ht1 ?_
      rw [show (f t + g) / 2 - f t₀ = ((f t - f t₀) + (g - f t₀)) / 2 by ring]
      exact habs _ _ ε hε ht2 ht3
    · obtain ⟨hu, h1, -, -, h4⟩ := hpat t ((f t + g) / 2) ht4.le htle ht5.le (by linarith)
      refine ⟨hu, h1.mpr (by linarith), h4.mpr ?_⟩
      calc f (p.1 * t) = p.2 * g := hpg.symm
        _ < p.2 * ((f t + g) / 2) := mul_lt_mul_of_pos_left (by linarith) hp2
  · -- `F u < 1`, `F (p ∘ u) < 1`: below both graphs
    apply frequently_nhds_of_forall_ball
    intro ε hε
    set η := min (ε / 2) (f t₀ / 2) with hη
    have hη0 : 0 < η := lt_min (half_pos hε) (half_pos hft₀)
    have hηε : η ≤ ε / 2 := min_le_left _ _
    have hηf : η ≤ f t₀ / 2 := min_le_right _ _
    refine ⟨(t₀, f t₀ - η), ?_, ?_⟩
    · rw [hdist, sub_self, abs_zero, show f t₀ - η - f t₀ = -η by ring, abs_neg, abs_of_pos hη0]
      exact max_lt hε (by linarith)
    · obtain ⟨hu, h1, -, h3, -⟩ := hpat t₀ (f t₀ - η) ht₀0.le ht₀I.2.le hpt₀ (by linarith)
      refine ⟨hu, h1.mpr (by linarith), h3.mpr ?_⟩
      rw [hsol]
      exact mul_lt_mul_of_pos_left (by linarith) hp2

end IsProfile

/-! ### The parameter change `p ↦ (1 / p₂, 1 / p₁)` -/

/-- `tau p = (1 / p₂, 1 / p₁)`, an involution of `ℝ²₊₊` mapping `{p₁ > 1 > p₂}` onto `Param`. -/
noncomputable def tau (p : ℝ × ℝ) : ℝ × ℝ := (1 / p.2, 1 / p.1)

theorem tau_tau {p : ℝ × ℝ} (_hp : p ∈ orthant) : tau (tau p) = p := by
  ext <;> simp [tau]

theorem tau_mem_orthant {p : ℝ × ℝ} (hp : p ∈ orthant) : tau p ∈ orthant := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hp
  exact mem_orthant.mpr ⟨one_div_pos.mpr h2, one_div_pos.mpr h1⟩

theorem Param_subset_orthant : Param ⊆ orthant := fun p hp => by
  obtain ⟨h1, h2, _⟩ := mem_Param.mp hp
  exact mem_orthant.mpr ⟨by linarith, h2⟩

theorem tau_mem_Param_iff {p : ℝ × ℝ} (hp : p ∈ orthant) : tau p ∈ Param ↔ 1 < p.1 ∧ p.2 < 1 := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hp
  rw [mem_Param]
  show 1 < 1 / p.2 ∧ 0 < 1 / p.1 ∧ 1 / p.1 < 1 ↔ 1 < p.1 ∧ p.2 < 1
  rw [one_lt_div h2, div_lt_one h1]
  constructor
  · rintro ⟨a, -, c⟩
    exact ⟨c, a⟩
  · rintro ⟨a, c⟩
    exact ⟨c, one_div_pos.mpr h1, a⟩

theorem continuousOn_tau : ContinuousOn tau orthant := by
  apply ContinuousOn.prodMk
  · exact continuousOn_const.div continuousOn_snd fun p hp => (mem_orthant.mp hp).2.ne'
  · exact continuousOn_const.div continuousOn_fst fun p hp => (mem_orthant.mp hp).1.ne'

/-! ### Main theorem -/

namespace IsBddNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsBddNeoclassical h)
include hh

/-- The main case `p₁ > 1 > p₂`. -/
theorem exists_open_aux {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ U)
    (h1 : 1 < p₀.1) (h2 : 0 < p₀.2) (h3 : p₀.2 < 1) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∩ orthant ∧
      ∀ p ∈ V, (levelIntersections h p).Finite ∧
        ∀ x₀ ∈ levelIntersections h p, FourChambers h p x₀ := by
  have hf := hh.profile_isProfile
  have hc := hh.scaling_mem_orthant
  have hp₀o : p₀ ∈ orthant := mem_orthant.mpr ⟨by linarith, h2⟩
  set U' : Set (ℝ × ℝ) := orthant ∩ tau ⁻¹' U with hU'
  have hU'o : IsOpen U' := continuousOn_tau.isOpen_inter_preimage isOpen_orthant hU
  have hne : (U' ∩ Param).Nonempty := by
    refine ⟨tau p₀, ⟨tau_mem_orthant hp₀o, ?_⟩, (tau_mem_Param_iff hp₀o).mpr ⟨h1, h3⟩⟩
    rw [mem_preimage, tau_tau hp₀o]
    exact hp₀
  obtain ⟨V', hV'o, hV'ne, hV'U, hV't⟩ := hf.exists_open_transversal hU'o hne
  refine ⟨orthant ∩ tau ⁻¹' V', continuousOn_tau.isOpen_inter_preimage isOpen_orthant hV'o,
    ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hV'ne
    have hqo : q ∈ orthant := Param_subset_orthant (hV'U hq).2
    refine ⟨tau q, tau_mem_orthant hqo, ?_⟩
    rw [mem_preimage, tau_tau hqo]
    exact hq
  · rintro p ⟨hpo, hpV⟩
    have := (hV'U hpV).1.2
    rw [mem_preimage, tau_tau hpo] at this
    exact ⟨this, hpo⟩
  · rintro p ⟨hpo, hpV⟩
    have hpP := (hV'U hpV).2
    obtain ⟨hp1, hp2⟩ := (tau_mem_Param_iff hpo).mp hpP
    have hp2' := (mem_orthant.mp hpo).2
    have htr : Transversal (profile h) (1 / p.2, 1 / p.1) := hV't _ hpV
    have hfin : (levelIntersections (ofProfile (profile h)) p).Finite := by
      rw [hf.levelIntersections_ofProfile hp1.le hp2']
      exact (hf.finite_of_transversal hpP htr).image _
    refine ⟨?_, ?_⟩
    · rw [hh.levelIntersections_eq_preimage (orthant_subset_quadrant hpo)]
      exact hfin.preimage (hadamard_injective hc).injOn
    · intro x₀ hx₀
      apply hh.fourChambers_of_ofProfile (orthant_subset_quadrant hpo)
      apply hf.fourChambers_ofProfile hp1 hp2' hp2 htr
      rw [hh.levelIntersections_eq_preimage (orthant_subset_quadrant hpo)] at hx₀
      exact hx₀

/-- **Generic finiteness and transversality of level-curve intersections.** For a bounded
neoclassical `h`, every nonempty open set `U ⊆ ℝ²₊₊` of prices contains a nonempty open set `V`
such that for every `p ∈ V` the curves `h x = 1` and `h (p ∘ x) = 1` meet in finitely many
points, each of which has four chambers. -/
theorem exists_open_finite_levelIntersections {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hne : (U ∩ orthant).Nonempty) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∩ orthant ∧
      ∀ p ∈ V, (levelIntersections h p).Finite ∧
        ∀ x₀ ∈ levelIntersections h p, FourChambers h p x₀ := by
  -- a point of `U ∩ orthant` off the lines `p₁ = 1`, `p₂ = 1`
  obtain ⟨p₀, hp₀U, hp₀o⟩ := hne
  have hUo : IsOpen (U ∩ orthant) := hU.inter isOpen_orthant
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo p₀ ⟨hp₀U, hp₀o⟩
  obtain ⟨δ, hδI, hδ⟩ := (Ioo_infinite (half_pos hr)).exists_notMem_finset
    ({1 - p₀.1, 1 - p₀.2} : Finset ℝ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hδ
  set p₁ : ℝ × ℝ := (p₀.1 + δ, p₀.2 + δ) with hp₁
  have hp₁U : p₁ ∈ U ∩ orthant := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [hp₁, add_sub_cancel_left, abs_of_pos hδI.1]
    exact max_lt (by linarith [hδI.2]) (by linarith [hδI.2])
  have hp₁1 : p₁.1 ≠ 1 := fun h => hδ.1 (by simp only [hp₁] at h; linarith)
  have hp₁2 : p₁.2 ≠ 1 := fun h => hδ.2 (by simp only [hp₁] at h; linarith)
  obtain ⟨hp₁o1, hp₁o2⟩ := mem_orthant.mp hp₁U.2
  rcases lt_or_gt_of_ne hp₁1 with h1 | h1 <;> rcases lt_or_gt_of_ne hp₁2 with h2 | h2
  · -- `p₁ < 1`, `p₂ < 1`: no intersections
    refine ⟨U ∩ orthant ∩ {p | p.1 < 1} ∩ {p | p.2 < 1},
      (hUo.inter (isOpen_lt continuous_fst continuous_const)).inter
        (isOpen_lt continuous_snd continuous_const),
      ⟨p₁, ⟨hp₁U, h1⟩, h2⟩, fun p hp => hp.1.1, ?_⟩
    rintro p ⟨⟨hpU, hp1⟩, hp2⟩
    rw [hh.levelIntersections_eq_empty_of_lt_one hpU.2 hp1 hp2]
    exact ⟨finite_empty, fun x hx => hx.elim⟩
  · -- `p₁ < 1 < p₂`: invert the prices
    set U' : Set (ℝ × ℝ) := orthant ∩ hinv ⁻¹' U with hU'
    have hU'o : IsOpen U' := continuousOn_hinv.isOpen_inter_preimage isOpen_orthant hU
    have hq₀ : hinv p₁ ∈ U' := ⟨hinv_mem_orthant hp₁U.2, by
      rw [mem_preimage, hinv_hinv hp₁U.2]; exact hp₁U.1⟩
    obtain ⟨V', hV'o, hV'ne, hV'U, hV'⟩ := hh.exists_open_aux hU'o hq₀
      (by show 1 < 1 / p₁.1; exact (one_lt_div hp₁o1).mpr h1)
      (by show 0 < 1 / p₁.2; exact one_div_pos.mpr hp₁o2)
      (by show 1 / p₁.2 < 1; exact (div_lt_one hp₁o2).mpr h2)
    refine ⟨orthant ∩ hinv ⁻¹' V', continuousOn_hinv.isOpen_inter_preimage isOpen_orthant hV'o,
      ?_, ?_, ?_⟩
    · obtain ⟨q, hq⟩ := hV'ne
      have hqo : q ∈ orthant := (hV'U hq).2
      refine ⟨hinv q, hinv_mem_orthant hqo, ?_⟩
      rw [mem_preimage, hinv_hinv hqo]
      exact hq
    · rintro p ⟨hpo, hpV⟩
      have := (hV'U hpV).1.2
      rw [mem_preimage, hinv_hinv hpo] at this
      exact ⟨this, hpo⟩
    · rintro p ⟨hpo, hpV⟩
      obtain ⟨hfin, hcham⟩ := hV' _ hpV
      refine ⟨?_, ?_⟩
      · rw [levelIntersections_hinv hpo]
        exact hfin.image _
      · intro x₀ hx₀
        rw [levelIntersections_hinv hpo] at hx₀
        obtain ⟨y, hy, rfl⟩ := hx₀
        apply FourChambers.of_hinv hpo
        rw [hadamard_hadamard_hinv hpo]
        exact hcham y hy
  · -- `p₁ > 1 > p₂`: the main case
    exact hh.exists_open_aux hU hp₁U.1 h1 hp₁o2 h2
  · -- `p₁ > 1`, `p₂ > 1`: no intersections
    refine ⟨U ∩ orthant ∩ {p | 1 < p.1} ∩ {p | 1 < p.2},
      (hUo.inter (isOpen_lt continuous_const continuous_fst)).inter
        (isOpen_lt continuous_const continuous_snd),
      ⟨p₁, ⟨hp₁U, h1⟩, h2⟩, fun p hp => hp.1.1, ?_⟩
    rintro p ⟨⟨hpU, hp1⟩, hp2⟩
    rw [hh.levelIntersections_eq_empty_of_one_lt hp1 hp2]
    exact ⟨finite_empty, fun x hx => hx.elim⟩

end IsBddNeoclassical

end NeoTiling
