import NeoTiling.Neoclassical

/-!
# Profiles of strictly positive neoclassical functions

A *profile* is a function `f : [0, 1] → [0, 1]` which is continuous, convex, strictly
decreasing, with `f 0 = 1` and `f 1 = 0`. Strict monotonicity cannot be weakened to
monotonicity: a profile with a flat zero segment would give an open set of parameters with
infinitely many intersections in `FiniteIntersections`.

Every strictly positive neoclassical `h` determines a profile: after normalising
`(x, y) ↦ h (x / h (1,0), y / h (0,1))`, the unit level curve is the graph of `profile h`
(`IsPosNeoclassical.profile_isProfile`). Conversely, `ofProfile f (x, y)` is the largest `λ`
such that `(x, y) / λ` lies on or above the graph of `f`, i.e. `λ * f (x / λ) ≤ y`, and `h` is
recovered from its profile by
`h (x, y) = ofProfile (profile h) (h (1,0) x, h (0,1) y)` (`IsPosNeoclassical.ofProfile_profile`).

This representation is what reduces questions about the level curves of `h` to questions about
the one-variable function `f`. The converse direction (every profile comes from a strictly
positive neoclassical function) is not needed for the main theorem and is not proved here.
-/

open Real Set

namespace NeoTiling

/-- A profile: `f : [0, 1] → [0, 1]` continuous, convex, strictly decreasing, `f 0 = 1`,
`f 1 = 0`. Only the values of `f` on `[0, 1]` matter. -/
structure IsProfile (f : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn f (Icc 0 1)
  convexOn : ConvexOn ℝ (Icc 0 1) f
  strictAntiOn : StrictAntiOn f (Icc 0 1)
  map_zero : f 0 = 1
  map_one : f 1 = 0

/-! ### From a strictly positive neoclassical function to its profile -/

/-- The set whose supremum is the profile at `t`: the `s ≥ 0` with `g (t, s) ≤ 1`. -/
def profileSet (g : ℝ × ℝ → ℝ) (t : ℝ) : Set ℝ := {s | 0 ≤ s ∧ g (t, s) ≤ 1}

/-- Profile of a *normalised* function `g` (`g (1,0) = g (0,1) = 1`): `profile₀ g t` is the
`s` with `g (t, s) = 1`, i.e. the unit level curve of `g` is the graph of `profile₀ g`. -/
noncomputable def profile₀ (g : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := sSup (profileSet g t)

/-- The normalisation `(x, y) ↦ h (x / h (1,0), y / h (0,1))`. -/
noncomputable def normalize (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := h (p.1 / h (1, 0), p.2 / h (0, 1))

/-- The profile of a strictly positive neoclassical function: the unit level curve of its
normalisation. -/
noncomputable def profile (h : ℝ × ℝ → ℝ) : ℝ → ℝ := profile₀ (normalize h)

namespace IsPosNeoclassical

section Normalized

variable {g : ℝ × ℝ → ℝ} (hg : IsPosNeoclassical g) (hg1 : g (1, 0) = 1) (hg2 : g (0, 1) = 1)
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

/-- The profile of a normalised strictly positive neoclassical function is a profile. -/
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

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

theorem normalize_isPos : IsPosNeoclassical (normalize h) := by
  have := hh.scale (inv_pos.mpr hh.pos_fst) (inv_pos.mpr hh.pos_snd)
  refine this.congr fun p _ => ?_
  simp only [normalize, div_eq_inv_mul]

theorem normalize_fst : normalize h (1, 0) = 1 := by
  simp only [normalize, zero_div]
  rw [hh.fst_axis (one_div_pos.mpr hh.pos_fst).le, one_div_mul_cancel hh.pos_fst.ne']

theorem normalize_snd : normalize h (0, 1) = 1 := by
  simp only [normalize, zero_div]
  rw [hh.snd_axis (one_div_pos.mpr hh.pos_snd).le, one_div_mul_cancel hh.pos_snd.ne']

/-- The profile of a strictly positive neoclassical function is a profile. -/
theorem profile_isProfile : IsProfile (profile h) :=
  hh.normalize_isPos.profile₀_isProfile hh.normalize_fst hh.normalize_snd

end IsPosNeoclassical

/-! ### The function with a given unit level curve -/

/-- The set whose supremum defines `ofProfile f p`: the `l ≥ p.1` such that `p / l` lies on or
above the graph of `f`, i.e. `l * f (p.1 / l) ≤ p.2`. -/
def levelSet (f : ℝ → ℝ) (p : ℝ × ℝ) : Set ℝ := {l | p.1 ≤ l ∧ l * f (p.1 / l) ≤ p.2}

/-- `ofProfile f p` is the largest `l` with `p / l` on or above the graph of `f`. Its unit level
curve in the quadrant is the graph of `f`. Only the values on the quadrant are used. -/
noncomputable def ofProfile (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := sSup (levelSet f p)

/-- `f` extended to a continuous function on `ℝ` by clamping the argument to `[0, 1]`. -/
noncomputable def clampF (f : ℝ → ℝ) (t : ℝ) : ℝ := f (max 0 (min t 1))

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
    IsGreatest (levelSet f p) (ofProfile f p) := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hne : (levelSet f p).Nonempty := ⟨p.1, hf.fst_mem_levelSet hp⟩
  have hbdd := hf.bddAbove_levelSet hp
  have hxL : p.1 ≤ ofProfile f p := le_csSup hbdd (hf.fst_mem_levelSet hp)
  refine ⟨⟨hxL, ?_⟩, fun l hl => le_csSup hbdd hl⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨l, ⟨hl1, hl2⟩, hl⟩ := exists_lt_of_lt_csSup hne
    (show ofProfile f p - ε < sSup (levelSet f p) by unfold ofProfile; linarith)
  have hlL : l ≤ ofProfile f p := le_csSup hbdd ⟨hl1, hl2⟩
  calc ofProfile f p * f (p.1 / ofProfile f p)
      ≤ l * f (p.1 / l) + (ofProfile f p - l) := hf.mul_div_le_add hx hl1 hlL
    _ ≤ p.2 + ε := by linarith

theorem fst_le_ofProfile {p : ℝ × ℝ} (hp : p ∈ quadrant) : p.1 ≤ ofProfile f p :=
  (hf.isGreatest_levelSet hp).1.1

theorem le_ofProfile_iff {p : ℝ × ℝ} {l : ℝ} (hp : p ∈ quadrant) (hl : p.1 ≤ l) :
    l ≤ ofProfile f p ↔ l * f (p.1 / l) ≤ p.2 := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hG := hf.isGreatest_levelSet hp
  constructor
  · intro h
    calc l * f (p.1 / l) ≤ ofProfile f p * f (p.1 / ofProfile f p) :=
          (hf.strictMonoOn_mul_div hx).monotoneOn (mem_Ici.mpr hl) (mem_Ici.mpr hG.1.1) h
      _ ≤ p.2 := hG.1.2
  · intro h
    exact hG.2 ⟨hl, h⟩

theorem lt_ofProfile_iff {p : ℝ × ℝ} {l : ℝ} (hp : p ∈ quadrant) (hl : p.1 ≤ l) :
    l < ofProfile f p ↔ l * f (p.1 / l) < p.2 := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hG := hf.isGreatest_levelSet hp
  constructor
  · intro h
    calc l * f (p.1 / l) < ofProfile f p * f (p.1 / ofProfile f p) :=
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

theorem ofProfile_lt_iff {p : ℝ × ℝ} {l : ℝ} (hp : p ∈ quadrant) (hl : p.1 ≤ l) :
    ofProfile f p < l ↔ p.2 < l * f (p.1 / l) := by
  rw [← not_le, hf.le_ofProfile_iff hp hl, not_le]

end IsProfile

/-! ### Reconstruction of `h` from its profile -/

namespace IsPosNeoclassical

section Normalized

variable {g : ℝ × ℝ → ℝ} (hg : IsPosNeoclassical g) (hg1 : g (1, 0) = 1) (hg2 : g (0, 1) = 1)
include hg hg1 hg2

/-- Reconstructing a normalised function from its profile gives it back. -/
theorem ofProfile_profile₀ {p : ℝ × ℝ} (hp : p ∈ quadrant) : ofProfile (profile₀ g) p = g p := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
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

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

/-- **Representation.** A strictly positive neoclassical function is recovered from
`(h (1,0), h (0,1))` and its profile. -/
theorem ofProfile_profile {p : ℝ × ℝ} (hp : p ∈ quadrant) :
    ofProfile (profile h) (h (1, 0) * p.1, h (0, 1) * p.2) = h p := by
  obtain ⟨hx, hy⟩ := mem_quadrant.mp hp
  have hq : (h (1, 0) * p.1, h (0, 1) * p.2) ∈ quadrant :=
    mk_mem_quadrant (mul_nonneg hh.pos_fst.le hx) (mul_nonneg hh.pos_snd.le hy)
  rw [profile, hh.normalize_isPos.ofProfile_profile₀ hh.normalize_fst hh.normalize_snd hq]
  simp only [normalize, mul_div_cancel_left₀ _ hh.pos_fst.ne', mul_div_cancel_left₀ _ hh.pos_snd.ne']

end IsPosNeoclassical

end NeoTiling
