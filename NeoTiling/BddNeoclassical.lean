import NeoTiling.Neoclassical

/-!
# Bounded neoclassical functions and their profiles

A neoclassical function `h : ℝ₊² → ℝ₊` is *bounded* if it is bounded below by a linear
function with positive weights: `a x + b y ≤ h (x, y)` for some `a, b > 0`.

A *profile* is a function `f : [0, 1] → [0, 1]` which is continuous, convex, strictly
decreasing, with `f 0 = 1` and `f 1 = 0`.

Main results:

* `isBddNeoclassical_iff_pos`: a neoclassical `h` is bounded iff `h (1, 0) > 0` and
  `h (0, 1) > 0`. This is the convenient form of the definition.
* `isBddNeoclassical_iff_profile`: `h` is bounded neoclassical iff
  `h (x, y) = ofProfile f (α x, β y)` on the quadrant for some `α, β > 0` and profile `f`.
* `profile_ofProfile`, `ofProfile_profile`: the two constructions `profile` and `ofProfile`
  are inverse to each other, and the data `(α, β, f)` is uniquely determined by `h`
  (`IsBddNeoclassical.eq_of_ofProfile_eq`).

The profile of `h` is the unit level curve of the normalised function
`(x, y) ↦ h (x / h (1, 0), y / h (0, 1))`, written as a graph `y = f x`, `x ∈ [0, 1]`.
Conversely `ofProfile f (x, y)` is the largest `λ` such that `(x, y) / λ` lies on or above
the graph of `f`, i.e. `λ * f (x / λ) ≤ y`.
-/

open Real Set

namespace NeoTiling

/-- A neoclassical function bounded below by a linear function with positive weights. -/
structure IsBddNeoclassical (h : ℝ × ℝ → ℝ) : Prop extends IsNeoclassical h where
  /-- `a * x + b * y ≤ h (x, y)` on the quadrant for some `a, b > 0`. -/
  bdd : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ p ∈ quadrant, a * p.1 + b * p.2 ≤ h p

/-- A profile: `f : [0, 1] → [0, 1]` continuous, convex, strictly decreasing, `f 0 = 1`,
`f 1 = 0`. Only the values of `f` on `[0, 1]` matter. -/
structure IsProfile (f : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn f (Icc 0 1)
  convexOn : ConvexOn ℝ (Icc 0 1) f
  strictAntiOn : StrictAntiOn f (Icc 0 1)
  map_zero : f 0 = 1
  map_one : f 1 = 0

/-! ### Elementary facts about the quadrant and neoclassical functions -/

theorem mem_quadrant {p : ℝ × ℝ} : p ∈ quadrant ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  simp only [quadrant, Set.mem_prod, Set.mem_Ici]

theorem mk_mem_quadrant {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x, y) ∈ quadrant :=
  mem_quadrant.mpr ⟨hx, hy⟩

theorem quadrant_add {p q : ℝ × ℝ} (hp : p ∈ quadrant) (hq : q ∈ quadrant) :
    p + q ∈ quadrant := by
  rw [mem_quadrant] at *
  exact ⟨by simpa using add_nonneg hp.1 hq.1, by simpa using add_nonneg hp.2 hq.2⟩

theorem quadrant_smul {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    t • p ∈ quadrant := by
  rw [mem_quadrant] at *
  exact ⟨by simpa using mul_nonneg ht hp.1, by simpa using mul_nonneg ht hp.2⟩

theorem zero_mem_quadrant : (0 : ℝ × ℝ) ∈ quadrant := mem_quadrant.mpr ⟨le_rfl, le_rfl⟩

namespace IsNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
include hh

theorem map_zero : h 0 = 0 := by
  have := hh.homogeneous 2 (by norm_num) 0 zero_mem_quadrant
  simp only [smul_zero] at this
  linarith

/-- Concavity plus homogeneity gives superadditivity. -/
theorem superadditive {p q : ℝ × ℝ} (hp : p ∈ quadrant) (hq : q ∈ quadrant) :
    h p + h q ≤ h (p + q) := by
  have hc := hh.concaveOn.2 hp hq (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmem : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ quadrant :=
    quadrant_add (quadrant_smul (by norm_num) hp) (quadrant_smul (by norm_num) hq)
  have hhom := hh.homogeneous 2 (by norm_num) _ hmem
  rw [smul_add, smul_smul, smul_smul] at hhom
  norm_num at hhom
  simp only [smul_eq_mul] at hc
  linarith

/-- Neoclassical functions are monotone on the quadrant. -/
theorem mono {p d : ℝ × ℝ} (hp : p ∈ quadrant) (hd : d ∈ quadrant) : h p ≤ h (p + d) :=
  le_trans (le_add_of_nonneg_right (hh.nonneg d hd)) (hh.superadditive hp hd)

theorem fst_axis {x : ℝ} (hx : 0 ≤ x) : h (x, 0) = x * h (1, 0) := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [zero_mul]
    exact hh.map_zero
  · have := hh.homogeneous x hx (1, 0) (mk_mem_quadrant zero_le_one le_rfl)
    simpa using this

theorem snd_axis {y : ℝ} (hy : 0 ≤ y) : h (0, y) = y * h (0, 1) := by
  rcases hy.eq_or_lt with rfl | hy
  · rw [zero_mul]
    exact hh.map_zero
  · have := hh.homogeneous y hy (0, 1) (mk_mem_quadrant le_rfl zero_le_one)
    simpa using this

/-- The best linear lower bound: `h (1,0) * x + h (0,1) * y ≤ h (x, y)`. -/
theorem linear_le {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    h (1, 0) * p.1 + h (0, 1) * p.2 ≤ h p := by
  obtain ⟨h1, h2⟩ := mem_quadrant.mp hp
  have := hh.superadditive (mk_mem_quadrant h1 le_rfl) (mk_mem_quadrant le_rfl h2)
  rw [hh.fst_axis h1, hh.snd_axis h2] at this
  simpa [mul_comm] using this

/-- Only the values on the quadrant matter. -/
theorem congr {g : ℝ × ℝ → ℝ} (hfg : EqOn h g quadrant) : IsNeoclassical g where
  nonneg p hp := hfg hp ▸ hh.nonneg p hp
  continuousOn := hh.continuousOn.congr hfg.symm
  concaveOn := hh.concaveOn.congr hfg
  homogeneous t ht p hp := by
    rw [← hfg (quadrant_smul ht.le hp), ← hfg hp]
    exact hh.homogeneous t ht p hp

end IsNeoclassical

/-! ### Bounded neoclassical functions -/

namespace IsBddNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsBddNeoclassical h)
include hh

theorem pos_fst : 0 < h (1, 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hh.bdd
  have := hab (1, 0) (mk_mem_quadrant zero_le_one le_rfl)
  simp at this
  linarith

theorem pos_snd : 0 < h (0, 1) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hh.bdd
  have := hab (0, 1) (mk_mem_quadrant le_rfl zero_le_one)
  simp at this
  linarith

theorem congr {g : ℝ × ℝ → ℝ} (hfg : EqOn h g quadrant) : IsBddNeoclassical g where
  toIsNeoclassical := hh.toIsNeoclassical.congr hfg
  bdd := by
    obtain ⟨a, b, ha, hb, hab⟩ := hh.bdd
    exact ⟨a, b, ha, hb, fun p hp => hfg hp ▸ hab p hp⟩

/-- Rescaling the two coordinates by positive factors preserves the class. -/
theorem scale {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsBddNeoclassical (fun p => h (α * p.1, β * p.2)) := by
  have hmem : ∀ p ∈ quadrant, (α * p.1, β * p.2) ∈ quadrant := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_quadrant.mp hp
    exact mk_mem_quadrant (by positivity) (by positivity)
  have hcont : Continuous (fun p : ℝ × ℝ => (α * p.1, β * p.2)) := by fun_prop
  refine ⟨⟨fun p hp => hh.nonneg _ (hmem p hp), ?_, ?_, ?_⟩, ?_⟩
  · exact hh.continuousOn.comp hcont.continuousOn hmem
  · refine ⟨(convex_Ici 0).prod (convex_Ici 0), ?_⟩
    intro p hp q hq a b ha hb hab
    have := hh.concaveOn.2 (hmem p hp) (hmem q hq) ha hb hab
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd] at this ⊢
    convert this using 3 <;> ring
  · intro t ht p hp
    have := hh.homogeneous t ht _ (hmem p hp)
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk] at this ⊢
    rw [show (α * (t * p.1), β * (t * p.2)) = (t * (α * p.1), t * (β * p.2)) by ring_nf]
    exact this
  · obtain ⟨a, b, ha, hb, hab⟩ := hh.bdd
    refine ⟨a * α, b * β, by positivity, by positivity, fun p hp => ?_⟩
    have := hab _ (hmem p hp)
    simp only at this
    linarith

end IsBddNeoclassical

/-- The convenient form of the definition: a neoclassical function is bounded iff it is
positive on the two unit vectors. -/
theorem isBddNeoclassical_iff_pos {h : ℝ × ℝ → ℝ} :
    IsBddNeoclassical h ↔ IsNeoclassical h ∧ 0 < h (1, 0) ∧ 0 < h (0, 1) := by
  constructor
  · intro hh
    exact ⟨hh.toIsNeoclassical, hh.pos_fst, hh.pos_snd⟩
  · rintro ⟨hh, h1, h2⟩
    exact ⟨hh, h (1, 0), h (0, 1), h1, h2, fun p hp => hh.linear_le hp⟩

/-! ### From a bounded neoclassical function to its profile -/

/-- The set whose supremum is the profile at `t`: the `s ≥ 0` with `g (t, s) ≤ 1`. -/
def profileSet (g : ℝ × ℝ → ℝ) (t : ℝ) : Set ℝ := {s | 0 ≤ s ∧ g (t, s) ≤ 1}

/-- Profile of a *normalised* function `g` (`g (1,0) = g (0,1) = 1`): `profile₀ g t` is the
`s` with `g (t, s) = 1`, i.e. the unit level curve of `g` is the graph of `profile₀ g`. -/
noncomputable def profile₀ (g : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := sSup (profileSet g t)

/-- The normalisation `(x, y) ↦ h (x / h (1,0), y / h (0,1))`. -/
noncomputable def normalize (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := h (p.1 / h (1, 0), p.2 / h (0, 1))

/-- The profile of a bounded neoclassical function: the unit level curve of its normalisation. -/
noncomputable def profile (h : ℝ × ℝ → ℝ) : ℝ → ℝ := profile₀ (normalize h)

namespace IsBddNeoclassical

section Normalized

variable {g : ℝ × ℝ → ℝ} (hg : IsBddNeoclassical g) (hg1 : g (1, 0) = 1) (hg2 : g (0, 1) = 1)
include hg hg1 hg2

theorem add_le_of_normalized {p : ℝ × ℝ} (hp : p ∈ quadrant) : p.1 + p.2 ≤ g p := by
  have := hg.linear_le hp
  rwa [hg1, hg2, one_mul, one_mul] at this

omit hg1 in
theorem strictMonoOn_snd {t : ℝ} (ht : 0 ≤ t) : StrictMonoOn (fun s => g (t, s)) (Ici 0) := by
  intro s hs s' _ hss
  have h1 := hg.superadditive (mk_mem_quadrant ht hs)
    (mk_mem_quadrant le_rfl (by linarith : 0 ≤ s' - s))
  rw [hg.snd_axis (by linarith), hg2, mul_one,
    show (t, s) + (0, s' - s) = (t, s') by ext <;> simp] at h1
  simp only
  linarith

omit hg2 in
theorem strictMonoOn_fst {s : ℝ} (hs : 0 ≤ s) : StrictMonoOn (fun t => g (t, s)) (Ici 0) := by
  intro t ht t' _ htt
  have h1 := hg.superadditive (mk_mem_quadrant ht hs)
    (mk_mem_quadrant (by linarith : 0 ≤ t' - t) le_rfl)
  rw [hg.fst_axis (by linarith), hg1, mul_one,
    show (t, s) + (t' - t, 0) = (t', s) by ext <;> simp] at h1
  simp only
  linarith

/-- The unit level curve meets every vertical line `x = t`, `t ∈ [0, 1]`. -/
theorem exists_level {t : ℝ} (ht : t ∈ Icc 0 1) : ∃ s ∈ Icc (0 : ℝ) 1, g (t, s) = 1 := by
  have hcont : ContinuousOn (fun s => g (t, s)) (Icc 0 1) :=
    hg.continuousOn.comp (by fun_prop : Continuous fun s : ℝ => (t, s)).continuousOn
      (fun s hs => mk_mem_quadrant ht.1 hs.1)
  have h0 : g (t, 0) = t := by rw [hg.fst_axis ht.1, hg1, mul_one]
  have h1 : 1 ≤ g (t, 1) := by
    have := hg.add_le_of_normalized hg1 hg2 (mk_mem_quadrant ht.1 zero_le_one)
    simp only at this
    linarith [ht.1]
  have hmem : (1 : ℝ) ∈ Icc (g (t, 0)) (g (t, 1)) := ⟨by rw [h0]; exact ht.2, h1⟩
  obtain ⟨s, hs, hs1⟩ := intermediate_value_Icc zero_le_one hcont hmem
  exact ⟨s, hs, hs1⟩

theorem profile₀_spec {t : ℝ} (ht : t ∈ Icc 0 1) :
    g (t, profile₀ g t) = 1 ∧ profile₀ g t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨s, hs, hs1⟩ := hg.exists_level hg1 hg2 ht
  have hG : IsGreatest (profileSet g t) s := by
    refine ⟨⟨hs.1, hs1.le⟩, fun s' hs' => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := hg.strictMonoOn_snd hg2 ht.1 (mem_Ici.mpr hs.1) (mem_Ici.mpr hs'.1) hlt
    simp only at this
    linarith [hs'.2]
  rw [profile₀, hG.csSup_eq]
  exact ⟨hs1, hs⟩

theorem le_profile₀_iff {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : 0 ≤ s) :
    s ≤ profile₀ g t ↔ g (t, s) ≤ 1 := by
  obtain ⟨hf, hf01⟩ := hg.profile₀_spec hg1 hg2 ht
  rw [← hf]
  exact ((hg.strictMonoOn_snd hg2 ht.1).le_iff_le hs hf01.1).symm

theorem lt_profile₀_iff {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : 0 ≤ s) :
    s < profile₀ g t ↔ g (t, s) < 1 := by
  obtain ⟨hf, hf01⟩ := hg.profile₀_spec hg1 hg2 ht
  rw [← hf]
  exact ((hg.strictMonoOn_snd hg2 ht.1).lt_iff_lt hs hf01.1).symm

theorem profile₀_le_iff {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : 0 ≤ s) :
    profile₀ g t ≤ s ↔ 1 ≤ g (t, s) := by
  obtain ⟨hf, hf01⟩ := hg.profile₀_spec hg1 hg2 ht
  rw [← hf]
  exact ((hg.strictMonoOn_snd hg2 ht.1).le_iff_le hf01.1 hs).symm

theorem profile₀_lt_iff {t s : ℝ} (ht : t ∈ Icc 0 1) (hs : 0 ≤ s) :
    profile₀ g t < s ↔ 1 < g (t, s) := by
  obtain ⟨hf, hf01⟩ := hg.profile₀_spec hg1 hg2 ht
  rw [← hf]
  exact ((hg.strictMonoOn_snd hg2 ht.1).lt_iff_lt hf01.1 hs).symm

/-- The profile of a normalised bounded neoclassical function is a profile. -/
theorem profile₀_isProfile : IsProfile (profile₀ g) where
  map_zero := by
    obtain ⟨hf, hf01⟩ := hg.profile₀_spec hg1 hg2 (left_mem_Icc.mpr zero_le_one)
    rw [hg.snd_axis hf01.1, hg2, mul_one] at hf
    exact hf
  map_one := by
    obtain ⟨hf, hf01⟩ := hg.profile₀_spec hg1 hg2 (right_mem_Icc.mpr zero_le_one)
    have := hg.add_le_of_normalized hg1 hg2 (mk_mem_quadrant zero_le_one hf01.1)
    simp only at this
    linarith [hf01.1]
  strictAntiOn := by
    intro t ht t' ht' htt'
    obtain ⟨hf, hf01⟩ := hg.profile₀_spec hg1 hg2 ht
    rw [hg.profile₀_lt_iff hg1 hg2 ht' hf01.1, ← hf]
    exact hg.strictMonoOn_fst hg1 hf01.1 (mem_Ici.mpr ht.1) (mem_Ici.mpr ht'.1) htt'
  convexOn := by
    refine ⟨convex_Icc 0 1, fun t₁ ht₁ t₂ ht₂ a b ha hb hab => ?_⟩
    have ht : a • t₁ + b • t₂ ∈ Icc (0 : ℝ) 1 := convex_Icc 0 1 ht₁ ht₂ ha hb hab
    simp only [smul_eq_mul] at ht ⊢
    obtain ⟨hf₁, hf₁01⟩ := hg.profile₀_spec hg1 hg2 ht₁
    obtain ⟨hf₂, hf₂01⟩ := hg.profile₀_spec hg1 hg2 ht₂
    rw [hg.profile₀_le_iff hg1 hg2 ht
      (add_nonneg (mul_nonneg ha hf₁01.1) (mul_nonneg hb hf₂01.1))]
    have := hg.concaveOn.2 (mk_mem_quadrant ht₁.1 hf₁01.1) (mk_mem_quadrant ht₂.1 hf₂01.1)
      ha hb hab
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk, hf₁, hf₂] at this
    linarith
  continuousOn := by
    -- Clamp `t` to `[0, 1]` to get a globally defined function, and prove it continuous
    -- through lower and upper semicontinuity.
    set c : ℝ → ℝ := fun t => max 0 (min t 1) with hc
    have hc_mem : ∀ t, c t ∈ Icc (0 : ℝ) 1 := fun t =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    have hG : ∀ s : ℝ, 0 ≤ s → Continuous (fun t => g (c t, s)) := fun s hs =>
      hg.continuousOn.comp_continuous (by fun_prop) (fun t => mk_mem_quadrant (hc_mem t).1 hs)
    have hF : Continuous (fun t => profile₀ g (c t)) := by
      rw [continuous_iff_lower_upperSemicontinuous]
      constructor
      · rw [lowerSemicontinuous_iff_isOpen_preimage]
        intro s
        rcases lt_or_ge s 0 with hs | hs
        · convert isOpen_univ
          ext t
          simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
          exact hs.trans_le (hg.profile₀_spec hg1 hg2 (hc_mem t)).2.1
        · convert isOpen_Iio.preimage (hG s hs) using 1
          ext t
          simp only [mem_preimage, mem_Ioi, mem_Iio]
          exact hg.lt_profile₀_iff hg1 hg2 (hc_mem t) hs
      · rw [upperSemicontinuous_iff_isOpen_preimage]
        intro s
        rcases le_or_gt s 0 with hs | hs
        · convert isOpen_empty
          ext t
          simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
          exact hs.trans (hg.profile₀_spec hg1 hg2 (hc_mem t)).2.1
        · convert isOpen_Ioi.preimage (hG s hs.le) using 1
          ext t
          simp only [mem_preimage, mem_Iio, mem_Ioi]
          exact hg.profile₀_lt_iff hg1 hg2 (hc_mem t) hs.le
    refine hF.continuousOn.congr fun t ht => ?_
    simp only [hc, min_eq_left ht.2, max_eq_right ht.1]

end Normalized

variable {h : ℝ × ℝ → ℝ} (hh : IsBddNeoclassical h)
include hh

theorem normalize_isBdd : IsBddNeoclassical (normalize h) := by
  have := hh.scale (inv_pos.mpr hh.pos_fst) (inv_pos.mpr hh.pos_snd)
  refine this.congr fun p _ => ?_
  simp only [normalize, div_eq_inv_mul]

theorem normalize_fst : normalize h (1, 0) = 1 := by
  simp only [normalize, zero_div]
  rw [hh.fst_axis (one_div_pos.mpr hh.pos_fst).le, one_div_mul_cancel hh.pos_fst.ne']

theorem normalize_snd : normalize h (0, 1) = 1 := by
  simp only [normalize, zero_div]
  rw [hh.snd_axis (one_div_pos.mpr hh.pos_snd).le, one_div_mul_cancel hh.pos_snd.ne']

/-- **Direction 1 of the correspondence.** The profile of a bounded neoclassical function
is a profile. -/
theorem profile_isProfile : IsProfile (profile h) :=
  hh.normalize_isBdd.profile₀_isProfile hh.normalize_fst hh.normalize_snd

end IsBddNeoclassical

/-! ### From a profile to a bounded neoclassical function -/

/-- The set whose supremum defines `ofProfile₀ f p`: the `l ≥ p.1` such that `p / l` lies on or
above the graph of `f`, i.e. `l * f (p.1 / l) ≤ p.2`. -/
def levelSet (f : ℝ → ℝ) (p : ℝ × ℝ) : Set ℝ := {l | p.1 ≤ l ∧ l * f (p.1 / l) ≤ p.2}

/-- `ofProfile₀ f p` is the largest `l` with `p / l` on or above the graph of `f`. -/
noncomputable def ofProfile₀ (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := sSup (levelSet f p)

/-- Retraction of the plane onto the quadrant. -/
def clampQ (p : ℝ × ℝ) : ℝ × ℝ := (max p.1 0, max p.2 0)

/-- The bounded neoclassical function with unit level curve `y = f x`. Outside the quadrant it
is extended by clamping, which makes it continuous on the whole plane. -/
noncomputable def ofProfile (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := ofProfile₀ f (clampQ p)

/-- `f` extended to a continuous function on `ℝ` by clamping the argument to `[0, 1]`. -/
noncomputable def clampF (f : ℝ → ℝ) (t : ℝ) : ℝ := f (max 0 (min t 1))

theorem clampQ_mem (p : ℝ × ℝ) : clampQ p ∈ quadrant :=
  mk_mem_quadrant (le_max_right _ _) (le_max_right _ _)

theorem clampQ_of_mem {p : ℝ × ℝ} (hp : p ∈ quadrant) : clampQ p = p := by
  obtain ⟨h1, h2⟩ := mem_quadrant.mp hp
  simp [clampQ, max_eq_left h1, max_eq_left h2]

theorem continuous_clampQ : Continuous clampQ := by
  unfold clampQ
  fun_prop

theorem ofProfile_eq_of_mem {f : ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    ofProfile f p = ofProfile₀ f p := by
  rw [ofProfile, clampQ_of_mem hp]

theorem clampF_eq {f : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampF f t = f t := by
  simp [clampF, min_eq_left ht.2, max_eq_right ht.1]

namespace IsProfile

variable {f : ℝ → ℝ} (hf : IsProfile f)
include hf

theorem nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ f t := by
  rw [← hf.map_one]
  exact hf.strictAntiOn.antitoneOn ht (right_mem_Icc.mpr zero_le_one) ht.2

theorem le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : f t ≤ 1 := by
  rw [← hf.map_zero]
  exact hf.strictAntiOn.antitoneOn (left_mem_Icc.mpr zero_le_one) ht ht.1

theorem pos {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : 0 < f t := by
  rw [← hf.map_one]
  exact hf.strictAntiOn ⟨ht.1, ht.2.le⟩ (right_mem_Icc.mpr zero_le_one) ht.2

/-- A convex function lies below its chord: `f t ≤ 1 - t`. -/
theorem le_chord {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : f t ≤ 1 - t := by
  have := hf.convexOn.2 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    (show (0 : ℝ) ≤ 1 - t by linarith [ht.2]) (show (0 : ℝ) ≤ t from ht.1)
    (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero, hf.map_zero, hf.map_one] at this
  linarith

theorem continuous_clampF : Continuous (clampF f) :=
  hf.continuousOn.comp_continuous (by fun_prop)
    (fun _ => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩)

/-- `l ↦ l * f (x / l)` is strictly increasing on `[x, ∞)`. -/
theorem strictMonoOn_mul_div {x : ℝ} (hx : 0 ≤ x) :
    StrictMonoOn (fun l => l * f (x / l)) (Ici x) := by
  intro l hl m hm hlm
  simp only [mem_Ici] at hl hm
  simp only
  rcases hx.eq_or_lt with h0 | hx
  · rw [← h0]
    simp only [zero_div, hf.map_zero, mul_one]
    exact hlm
  · have hl0 : 0 < l := hx.trans_le hl
    have hm0 : 0 < m := hl0.trans hlm
    have hu : x / l ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hl0).mpr hl⟩
    have hv : x / m ∈ Ico (0 : ℝ) 1 := ⟨by positivity, (div_lt_one hm0).mpr (hl.trans_lt hlm)⟩
    have hvu : x / m ≤ x / l := div_le_div_of_nonneg_left hx.le hl0 hlm.le
    have h1 : f (x / l) ≤ f (x / m) := hf.strictAntiOn.antitoneOn ⟨hv.1, hv.2.le⟩ hu hvu
    have h2 : 0 < f (x / m) := hf.pos hv
    calc l * f (x / l) ≤ l * f (x / m) := mul_le_mul_of_nonneg_left h1 hl0.le
      _ < m * f (x / m) := mul_lt_mul_of_pos_right hlm h2

/-- `l ↦ l * f (x / l)` grows at most linearly: this is where convexity enters. -/
theorem mul_div_le_add {x l m : ℝ} (hx : 0 ≤ x) (hl : x ≤ l) (hlm : l ≤ m) :
    m * f (x / m) ≤ l * f (x / l) + (m - l) := by
  rcases hx.eq_or_lt with h0 | hx
  · rw [← h0]
    simp only [zero_div, hf.map_zero, mul_one]
    linarith
  · have hl0 : 0 < l := hx.trans_le hl
    have hm0 : 0 < m := hl0.trans_le hlm
    have hu : x / l ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hl0).mpr hl⟩
    have ha : 0 ≤ l / m := by positivity
    have hb : 0 ≤ 1 - l / m := by
      rw [sub_nonneg]
      exact (div_le_one hm0).mpr hlm
    have hconv := hf.convexOn.2 hu (left_mem_Icc.mpr zero_le_one) ha hb (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, hf.map_zero, mul_one] at hconv
    rw [show l / m * (x / l) = x / m by field_simp] at hconv
    calc m * f (x / m) ≤ m * (l / m * f (x / l) + (1 - l / m)) :=
          mul_le_mul_of_nonneg_left hconv hm0.le
      _ = l * f (x / l) + (m - l) := by field_simp

theorem fst_mem_levelSet {p : ℝ × ℝ} (hp : p ∈ quadrant) : p.1 ∈ levelSet f p := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  refine ⟨le_rfl, ?_⟩
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    simpa using hy
  · rw [div_self h.ne', hf.map_one, mul_zero]
    exact hy

theorem bddAbove_levelSet {p : ℝ × ℝ} (hp : p ∈ quadrant) : BddAbove (levelSet f p) := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hc : 0 < f (1 / 2) := hf.pos ⟨by norm_num, by norm_num⟩
  refine ⟨max (2 * p.1) (p.2 / f (1 / 2)), fun l ⟨hl, hl2⟩ => ?_⟩
  rcases le_or_gt l (2 * p.1) with h | h
  · exact h.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hl0 : 0 < l := by linarith
    have hxl : p.1 / l ≤ 1 / 2 := by
      rw [div_le_iff₀ hl0]
      linarith
    have hfx : f (1 / 2) ≤ f (p.1 / l) :=
      hf.strictAntiOn.antitoneOn ⟨by positivity, hxl.trans (by norm_num)⟩
        ⟨by norm_num, by norm_num⟩ hxl
    rw [le_div_iff₀ hc]
    calc l * f (1 / 2) ≤ l * f (p.1 / l) := mul_le_mul_of_nonneg_left hfx hl0.le
      _ ≤ p.2 := hl2

theorem isGreatest_levelSet {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    IsGreatest (levelSet f p) (ofProfile₀ f p) := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hne : (levelSet f p).Nonempty := ⟨p.1, hf.fst_mem_levelSet hp⟩
  have hbdd := hf.bddAbove_levelSet hp
  have hxL : p.1 ≤ ofProfile₀ f p := le_csSup hbdd (hf.fst_mem_levelSet hp)
  refine ⟨⟨hxL, ?_⟩, fun l hl => le_csSup hbdd hl⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨l, ⟨hl1, hl2⟩, hl⟩ := exists_lt_of_lt_csSup hne
    (show ofProfile₀ f p - ε < sSup (levelSet f p) by unfold ofProfile₀; linarith)
  have hlL : l ≤ ofProfile₀ f p := le_csSup hbdd ⟨hl1, hl2⟩
  calc ofProfile₀ f p * f (p.1 / ofProfile₀ f p)
      ≤ l * f (p.1 / l) + (ofProfile₀ f p - l) := hf.mul_div_le_add hx hl1 hlL
    _ ≤ p.2 + ε := by linarith

theorem fst_le_ofProfile₀ {p : ℝ × ℝ} (hp : p ∈ quadrant) : p.1 ≤ ofProfile₀ f p :=
  (hf.isGreatest_levelSet hp).1.1

theorem nonneg_ofProfile₀ {p : ℝ × ℝ} (hp : p ∈ quadrant) : 0 ≤ ofProfile₀ f p :=
  (mem_quadrant.mp hp).1.trans (hf.fst_le_ofProfile₀ hp)

theorem le_ofProfile₀_iff {p : ℝ × ℝ} {l : ℝ} (hp : p ∈ quadrant) (hl : p.1 ≤ l) :
    l ≤ ofProfile₀ f p ↔ l * f (p.1 / l) ≤ p.2 := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hG := hf.isGreatest_levelSet hp
  constructor
  · intro h
    calc l * f (p.1 / l) ≤ ofProfile₀ f p * f (p.1 / ofProfile₀ f p) :=
          (hf.strictMonoOn_mul_div hx).monotoneOn (mem_Ici.mpr hl) (mem_Ici.mpr hG.1.1) h
      _ ≤ p.2 := hG.1.2
  · intro h
    exact hG.2 ⟨hl, h⟩

theorem lt_ofProfile₀_iff {p : ℝ × ℝ} {l : ℝ} (hp : p ∈ quadrant) (hl : p.1 ≤ l) :
    l < ofProfile₀ f p ↔ l * f (p.1 / l) < p.2 := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hG := hf.isGreatest_levelSet hp
  constructor
  · intro h
    calc l * f (p.1 / l) < ofProfile₀ f p * f (p.1 / ofProfile₀ f p) :=
          hf.strictMonoOn_mul_div hx (mem_Ici.mpr hl) (mem_Ici.mpr hG.1.1) h
      _ ≤ p.2 := hG.1.2
  · intro h
    set m := l + (p.2 - l * f (p.1 / l)) with hm
    have hlm : l < m := by
      rw [hm]
      linarith
    have hmem : m ∈ levelSet f p := by
      refine ⟨hl.trans hlm.le, ?_⟩
      calc m * f (p.1 / m) ≤ l * f (p.1 / l) + (m - l) := hf.mul_div_le_add hx hl hlm.le
        _ = p.2 := by rw [hm]; ring
    exact hlm.trans_le (hG.2 hmem)

theorem ofProfile₀_lt_iff {p : ℝ × ℝ} {l : ℝ} (hp : p ∈ quadrant) (hl : p.1 ≤ l) :
    ofProfile₀ f p < l ↔ p.2 < l * f (p.1 / l) := by
  rw [← not_le, hf.le_ofProfile₀_iff hp hl, not_le]

theorem ofProfile₀_mk_zero {x : ℝ} (hx : 0 ≤ x) : ofProfile₀ f (x, 0) = x := by
  have hp : (x, 0) ∈ quadrant := mk_mem_quadrant hx le_rfl
  have hG := hf.isGreatest_levelSet hp
  refine le_antisymm ?_ hG.1.1
  by_contra h
  push_neg at h
  have := (hf.lt_ofProfile₀_iff hp le_rfl).mp h
  dsimp only at this
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0] at this
    simp at this
  · rw [div_self h0.ne', hf.map_one, mul_zero] at this
    exact lt_irrefl _ this

theorem ofProfile₀_zero_mk {y : ℝ} (hy : 0 ≤ y) : ofProfile₀ f (0, y) = y := by
  have hG : IsGreatest (levelSet f (0, y)) y := by
    refine ⟨⟨hy, by simp [hf.map_zero]⟩, fun l ⟨_, hl2⟩ => ?_⟩
    simpa [hf.map_zero] using hl2
  exact hG.csSup_eq

theorem ofProfile₀_zero : ofProfile₀ f 0 = 0 :=
  hf.ofProfile₀_mk_zero le_rfl

theorem ofProfile₀_smul {t : ℝ} (ht : 0 < t) {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    ofProfile₀ f (t • p) = t * ofProfile₀ f p := by
  have hG := hf.isGreatest_levelSet hp
  have : IsGreatest (levelSet f (t • p)) (t * ofProfile₀ f p) := by
    refine ⟨⟨?_, ?_⟩, fun l ⟨hl1, hl2⟩ => ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hG.1.1 ht.le
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_div_mul_left _ _ ht.ne']
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hG.1.2 ht.le
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hl1 hl2
      have hmem : l / t ∈ levelSet f p := by
        refine ⟨by rwa [le_div_iff₀ ht, mul_comm], ?_⟩
        rw [div_div_eq_mul_div, mul_comm p.1 t, div_mul_eq_mul_div, div_le_iff₀ ht]
        linarith [hl2]
      have := hG.2 hmem
      rwa [div_le_iff₀ ht, mul_comm] at this
  exact this.csSup_eq

theorem ofProfile₀_smul' {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    ofProfile₀ f (t • p) = t * ofProfile₀ f p := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, zero_smul, zero_mul, hf.ofProfile₀_zero]
  · exact hf.ofProfile₀_smul h hp

/-- The linear lower bound `x + y ≤ ofProfile₀ f (x, y)`. -/
theorem add_le_ofProfile₀ {p : ℝ × ℝ} (hp : p ∈ quadrant) : p.1 + p.2 ≤ ofProfile₀ f p := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hG := hf.isGreatest_levelSet hp
  apply hG.2
  refine ⟨by linarith, ?_⟩
  rcases (add_nonneg hx hy).eq_or_lt with h | h
  · rw [← h]
    simpa using hy
  · have hu : p.1 / (p.1 + p.2) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one h).mpr (by linarith)⟩
    have hne : p.1 + p.2 ≠ 0 := h.ne'
    calc (p.1 + p.2) * f (p.1 / (p.1 + p.2))
        ≤ (p.1 + p.2) * (1 - p.1 / (p.1 + p.2)) :=
          mul_le_mul_of_nonneg_left (hf.le_chord hu) h.le
      _ = p.2 := by field_simp; ring

theorem pos_ofProfile₀ {p : ℝ × ℝ} (hp : p ∈ quadrant) (hp0 : p ≠ 0) : 0 < ofProfile₀ f p := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  refine lt_of_lt_of_le ?_ (hf.add_le_ofProfile₀ hp)
  rcases (add_nonneg hx hy).eq_or_lt with h | h
  · exfalso
    apply hp0
    ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> linarith
  · exact h

/-- The perspective inequality for the convex function `f`. -/
theorem perspective_le {x y l m : ℝ} (hl : 0 < l) (hm : 0 < m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxl : x ≤ l) (hym : y ≤ m) :
    (l + m) * f ((x + y) / (l + m)) ≤ l * f (x / l) + m * f (y / m) := by
  have hn : 0 < l + m := by positivity
  have hu : x / l ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hl).mpr hxl⟩
  have hv : y / m ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hm).mpr hym⟩
  have hconv := hf.convexOn.2 hu hv (show (0 : ℝ) ≤ l / (l + m) by positivity)
    (show (0 : ℝ) ≤ m / (l + m) by positivity)
    (show l / (l + m) + m / (l + m) = 1 by rw [← add_div, div_self hn.ne'])
  simp only [smul_eq_mul] at hconv
  rw [show l / (l + m) * (x / l) + m / (l + m) * (y / m) = (x + y) / (l + m) by
    field_simp] at hconv
  calc (l + m) * f ((x + y) / (l + m))
      ≤ (l + m) * (l / (l + m) * f (x / l) + m / (l + m) * f (y / m)) :=
        mul_le_mul_of_nonneg_left hconv hn.le
    _ = l * f (x / l) + m * f (y / m) := by field_simp

theorem superadditive_ofProfile₀ {p q : ℝ × ℝ} (hp : p ∈ quadrant) (hq : q ∈ quadrant) :
    ofProfile₀ f p + ofProfile₀ f q ≤ ofProfile₀ f (p + q) := by
  by_cases hp0 : p = 0
  · rw [hp0, hf.ofProfile₀_zero, zero_add, zero_add]
  by_cases hq0 : q = 0
  · rw [hq0, hf.ofProfile₀_zero, add_zero, add_zero]
  have hGp := hf.isGreatest_levelSet hp
  have hGq := hf.isGreatest_levelSet hq
  have hlp := hf.pos_ofProfile₀ hp hp0
  have hlq := hf.pos_ofProfile₀ hq hq0
  obtain ⟨hx₁, hx₂⟩ := mem_quadrant.mp hp
  obtain ⟨hy₁, hy₂⟩ := mem_quadrant.mp hq
  apply (hf.isGreatest_levelSet (quadrant_add hp hq)).2
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add]
    exact add_le_add hGp.1.1 hGq.1.1
  · simp only [Prod.fst_add, Prod.snd_add]
    calc (ofProfile₀ f p + ofProfile₀ f q) * f ((p.1 + q.1) / (ofProfile₀ f p + ofProfile₀ f q))
        ≤ ofProfile₀ f p * f (p.1 / ofProfile₀ f p) + ofProfile₀ f q * f (q.1 / ofProfile₀ f q) :=
          hf.perspective_le hlp hlq hx₁ hy₁ hGp.1.1 hGq.1.1
      _ ≤ p.2 + q.2 := add_le_add hGp.1.2 hGq.1.2

theorem concaveOn_ofProfile₀ : ConcaveOn ℝ quadrant (ofProfile₀ f) := by
  refine ⟨(convex_Ici 0).prod (convex_Ici 0), fun p hp q hq a b ha hb _ => ?_⟩
  simp only [smul_eq_mul]
  rw [← hf.ofProfile₀_smul' ha hp, ← hf.ofProfile₀_smul' hb hq]
  exact hf.superadditive_ofProfile₀ (quadrant_smul ha hp) (quadrant_smul hb hq)

/-- Characterisation of `s < ofProfile₀ f p` by an open condition. -/
theorem lt_ofProfile₀_iff' {p : ℝ × ℝ} {s : ℝ} (hp : p ∈ quadrant) (hs : 0 ≤ s) :
    s < ofProfile₀ f p ↔ s < p.1 ∨ s * clampF f (p.1 / s) < p.2 := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  rcases lt_or_ge s p.1 with h | h
  · exact ⟨fun _ => Or.inl h, fun _ => h.trans_le (hf.fst_le_ofProfile₀ hp)⟩
  · have hu : p.1 / s ∈ Icc (0 : ℝ) 1 := by
      rcases hs.eq_or_lt with h0 | h0
      · rw [← h0, div_zero]
        exact left_mem_Icc.mpr zero_le_one
      · exact ⟨by positivity, (div_le_one h0).mpr h⟩
    rw [clampF_eq hu, hf.lt_ofProfile₀_iff hp h]
    exact ⟨Or.inr, fun h' => h'.resolve_left (not_lt.mpr h)⟩

/-- Characterisation of `ofProfile₀ f p < s` by an open condition. -/
theorem ofProfile₀_lt_iff' {p : ℝ × ℝ} {s : ℝ} (hp : p ∈ quadrant) (hs : 0 < s) :
    ofProfile₀ f p < s ↔ p.1 < s ∧ p.2 < s * clampF f (p.1 / s) := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  constructor
  · intro h
    have h1 : p.1 < s := (hf.fst_le_ofProfile₀ hp).trans_lt h
    have hu : p.1 / s ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hs).mpr h1.le⟩
    rw [clampF_eq hu]
    exact ⟨h1, (hf.ofProfile₀_lt_iff hp h1.le).mp h⟩
  · rintro ⟨h1, h2⟩
    have hu : p.1 / s ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hs).mpr h1.le⟩
    rw [clampF_eq hu] at h2
    exact (hf.ofProfile₀_lt_iff hp h1.le).mpr h2

theorem continuous_ofProfile : Continuous (ofProfile f) := by
  rw [continuous_iff_lower_upperSemicontinuous]
  constructor
  · rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro s
    rcases lt_or_ge s 0 with hs | hs
    · convert isOpen_univ
      ext p
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact hs.trans_le (hf.nonneg_ofProfile₀ (clampQ_mem p))
    · have hU : IsOpen ({q : ℝ × ℝ | s < q.1} ∪ {q | s * clampF f (q.1 / s) < q.2}) :=
        (isOpen_lt continuous_const continuous_fst).union
          (isOpen_lt (continuous_const.mul (hf.continuous_clampF.comp (continuous_fst.div_const s)))
            continuous_snd)
      convert hU.preimage continuous_clampQ using 1
      ext p
      simp only [mem_preimage, mem_Ioi, mem_union, mem_setOf_eq, ofProfile]
      exact hf.lt_ofProfile₀_iff' (clampQ_mem p) hs
  · rw [upperSemicontinuous_iff_isOpen_preimage]
    intro s
    rcases le_or_gt s 0 with hs | hs
    · convert isOpen_empty
      ext p
      simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
      exact hs.trans (hf.nonneg_ofProfile₀ (clampQ_mem p))
    · have hV : IsOpen ({q : ℝ × ℝ | q.1 < s} ∩ {q | q.2 < s * clampF f (q.1 / s)}) :=
        (isOpen_lt continuous_fst continuous_const).inter
          (isOpen_lt continuous_snd
            (continuous_const.mul (hf.continuous_clampF.comp (continuous_fst.div_const s))))
      convert hV.preimage continuous_clampQ using 1
      ext p
      simp only [mem_preimage, mem_Iio, mem_inter_iff, mem_setOf_eq, ofProfile]
      exact hf.ofProfile₀_lt_iff' (clampQ_mem p) hs

/-- **Direction 2 of the correspondence.** `ofProfile f` is bounded neoclassical. -/
theorem ofProfile_isBdd : IsBddNeoclassical (ofProfile f) := by
  refine ⟨⟨?_, hf.continuous_ofProfile.continuousOn, ?_, ?_⟩, 1, 1, one_pos, one_pos, ?_⟩
  · intro p hp
    rw [ofProfile_eq_of_mem hp]
    exact hf.nonneg_ofProfile₀ hp
  · exact hf.concaveOn_ofProfile₀.congr fun p hp => (ofProfile_eq_of_mem hp).symm
  · intro t ht p hp
    rw [ofProfile_eq_of_mem (quadrant_smul ht.le hp), ofProfile_eq_of_mem hp]
    exact hf.ofProfile₀_smul ht hp
  · intro p hp
    rw [ofProfile_eq_of_mem hp, one_mul, one_mul]
    exact hf.add_le_ofProfile₀ hp

theorem ofProfile_fst : ofProfile f (1, 0) = 1 := by
  rw [ofProfile_eq_of_mem (mk_mem_quadrant zero_le_one le_rfl)]
  exact hf.ofProfile₀_mk_zero zero_le_one

theorem ofProfile_snd : ofProfile f (0, 1) = 1 := by
  rw [ofProfile_eq_of_mem (mk_mem_quadrant le_rfl zero_le_one)]
  exact hf.ofProfile₀_zero_mk zero_le_one

end IsProfile

/-! ### The two constructions are inverse to each other -/

theorem profile₀_congr {g g' : ℝ × ℝ → ℝ} (hgg' : EqOn g g' quadrant) {t : ℝ} (ht : 0 ≤ t) :
    profile₀ g t = profile₀ g' t := by
  unfold profile₀ profileSet
  congr 1
  ext s
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨hs, by rwa [← hgg' (mk_mem_quadrant ht hs)]⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs, by rwa [hgg' (mk_mem_quadrant ht hs)]⟩

namespace IsBddNeoclassical

section Normalized

variable {g : ℝ × ℝ → ℝ} (hg : IsBddNeoclassical g) (hg1 : g (1, 0) = 1) (hg2 : g (0, 1) = 1)
include hg hg1 hg2

/-- The profile is the unique `s` with `g (t, s) = 1`. -/
theorem profile₀_eq_of {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 ≤ s) (h : g (t, s) = 1) :
    profile₀ g t = s :=
  le_antisymm ((hg.profile₀_le_iff hg1 hg2 ht hs).mpr h.ge)
    ((hg.le_profile₀_iff hg1 hg2 ht hs).mpr h.le)

/-- Reconstructing a normalised function from its profile gives it back. -/
theorem ofProfile_profile₀ {p : ℝ × ℝ} (hp : p ∈ quadrant) : ofProfile (profile₀ g) p = g p := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  rw [ofProfile_eq_of_mem hp]
  have hxG : p.1 ≤ g p := by
    have := hg.add_le_of_normalized hg1 hg2 hp
    linarith
  have key : ∀ l : ℝ, 0 < l → p.1 ≤ l → (l * profile₀ g (p.1 / l) ≤ p.2 ↔ l ≤ g p) := by
    intro l hl hpl
    have ht : p.1 / l ∈ Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hl).mpr hpl⟩
    have hs : 0 ≤ p.2 / l := by positivity
    have hhom : g (p.1 / l, p.2 / l) = g p / l := by
      have := hg.homogeneous (1 / l) (by positivity) p hp
      rw [show (1 / l) • p = (p.1 / l, p.2 / l) by
        ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring] at this
      rw [this]
      ring
    rw [mul_comm, ← le_div_iff₀ hl, hg.profile₀_le_iff hg1 hg2 ht hs, hhom, le_div_iff₀ hl,
      one_mul]
  have hG : IsGreatest (levelSet (profile₀ g) p) (g p) := by
    refine ⟨⟨hxG, ?_⟩, fun l ⟨hl1, hl2⟩ => ?_⟩
    · rcases (hg.nonneg p hp).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]
        exact hy
      · exact (key _ h0 hxG).mpr le_rfl
    · rcases (hx.trans hl1).eq_or_lt with h0 | h0
      · rw [← h0]
        exact hg.nonneg p hp
      · exact (key _ h0 hl1).mp hl2
  exact hG.csSup_eq

end Normalized

variable {h : ℝ × ℝ → ℝ} (hh : IsBddNeoclassical h)
include hh

/-- **Round trip 1.** A bounded neoclassical function is recovered from `(h (1,0), h (0,1))`
and its profile. -/
theorem ofProfile_profile {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    ofProfile (profile h) (h (1, 0) * p.1, h (0, 1) * p.2) = h p := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hq : (h (1, 0) * p.1, h (0, 1) * p.2) ∈ quadrant :=
    mk_mem_quadrant (mul_nonneg hh.pos_fst.le hx) (mul_nonneg hh.pos_snd.le hy)
  rw [profile, hh.normalize_isBdd.ofProfile_profile₀ hh.normalize_fst hh.normalize_snd hq]
  simp only [normalize, mul_div_cancel_left₀ _ hh.pos_fst.ne', mul_div_cancel_left₀ _ hh.pos_snd.ne']

end IsBddNeoclassical

namespace IsProfile

variable {f : ℝ → ℝ} (hf : IsProfile f)
include hf

/-- The graph of `f` is the unit level curve of `ofProfile f`. -/
theorem ofProfile_mk_self {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ofProfile f (t, f t) = 1 := by
  rw [ofProfile_eq_of_mem (mk_mem_quadrant ht.1 (hf.nonneg ht))]
  have hG : IsGreatest (levelSet f (t, f t)) 1 := by
    refine ⟨⟨ht.2, by simp⟩, fun l ⟨hl1, hl2⟩ => ?_⟩
    have := (hf.strictMonoOn_mul_div ht.1).le_iff_le (mem_Ici.mpr hl1) (mem_Ici.mpr ht.2)
    simp only [div_one, one_mul] at this
    exact this.mp hl2
  exact hG.csSup_eq

theorem profile₀_ofProfile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : profile₀ (ofProfile f) t = f t :=
  hf.ofProfile_isBdd.profile₀_eq_of hf.ofProfile_fst hf.ofProfile_snd ht (hf.nonneg ht)
    (hf.ofProfile_mk_self ht)

theorem normalize_ofProfile : normalize (ofProfile f) = ofProfile f := by
  funext p
  simp [normalize, hf.ofProfile_fst, hf.ofProfile_snd]

/-- **Round trip 2.** A profile is recovered from the function it defines. -/
theorem profile_ofProfile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : profile (ofProfile f) t = f t := by
  rw [profile, hf.normalize_ofProfile, hf.profile₀_ofProfile ht]

/-- **Uniqueness.** If `h = ofProfile f (α x, β y)` on the quadrant, then `α`, `β` and `f`
(on `[0, 1]`) are determined by `h`. -/
theorem eq_of_ofProfile_eq {h : ℝ × ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hfh : ∀ p ∈ quadrant, h p = ofProfile f (α * p.1, β * p.2)) :
    h (1, 0) = α ∧ h (0, 1) = β ∧ EqOn f (profile h) (Icc 0 1) := by
  have h1 : h (1, 0) = α := by
    rw [hfh _ (mk_mem_quadrant zero_le_one le_rfl)]
    simp only [mul_one, mul_zero]
    rw [ofProfile_eq_of_mem (mk_mem_quadrant hα.le le_rfl)]
    exact hf.ofProfile₀_mk_zero hα.le
  have h2 : h (0, 1) = β := by
    rw [hfh _ (mk_mem_quadrant le_rfl zero_le_one)]
    simp only [mul_one, mul_zero]
    rw [ofProfile_eq_of_mem (mk_mem_quadrant le_rfl hβ.le)]
    exact hf.ofProfile₀_zero_mk hβ.le
  refine ⟨h1, h2, fun t ht => ?_⟩
  have hnorm : EqOn (normalize h) (ofProfile f) quadrant := fun p hp => by
    obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
    simp only [normalize, h1, h2]
    rw [hfh _ (mk_mem_quadrant (div_nonneg hx hα.le) (div_nonneg hy hβ.le))]
    simp only [mul_div_cancel₀ _ hα.ne', mul_div_cancel₀ _ hβ.ne']
  rw [profile, profile₀_congr hnorm ht.1, hf.profile₀_ofProfile ht]

end IsProfile

/-- **The correspondence.** A function is bounded neoclassical iff, on the quadrant, it is of
the form `(x, y) ↦ ofProfile f (α x, β y)` with `α, β > 0` and `f` a profile. Together with
`IsProfile.eq_of_ofProfile_eq`, `IsBddNeoclassical.profile_isProfile` and
`IsProfile.profile_ofProfile` this says that `h ↦ (h (1,0), h (0,1), profile h)` is a bijection
between bounded neoclassical functions of two variables (up to their values off the quadrant)
and triples `(α, β, f)` with `α, β > 0` and `f` a profile (up to its values off `[0, 1]`). -/
theorem isBddNeoclassical_iff_profile {h : ℝ × ℝ → ℝ} :
    IsBddNeoclassical h ↔ ∃ α β : ℝ, ∃ f : ℝ → ℝ, 0 < α ∧ 0 < β ∧ IsProfile f ∧
      ∀ p ∈ quadrant, h p = ofProfile f (α * p.1, β * p.2) := by
  constructor
  · intro hh
    exact ⟨h (1, 0), h (0, 1), profile h, hh.pos_fst, hh.pos_snd, hh.profile_isProfile,
      fun p hp => (hh.ofProfile_profile hp).symm⟩
  · rintro ⟨α, β, f, hα, hβ, hf, hfh⟩
    exact (hf.ofProfile_isBdd.scale hα hβ).congr fun p hp => (hfh p hp).symm

end NeoTiling
