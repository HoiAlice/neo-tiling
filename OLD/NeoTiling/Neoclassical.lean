import Mathlib

/-!
# Neoclassical functions of two variables

Informal definition (notes, Definition "Neoclassical functions", specialised to `n = 2`):
a function `h : ℝ₊² → ℝ₊` is *neoclassical* if it is continuous, concave and homogeneous of
degree 1. It is *strictly positive* if moreover `h x > 0` for every `x ∈ ℝ₊² \ {0}`.

We model `ℝ₊²` as the closed nonnegative quadrant `quadrant ⊆ ℝ × ℝ` and a function
`ℝ₊² → ℝ₊` as a function `h : ℝ × ℝ → ℝ` together with the requirement that `h` is
nonnegative on the quadrant. Only the values of `h` on the quadrant matter
(`IsNeoclassical.congr`).

The strictly positive class is the one for which the main theorem
(`IsPosNeoclassical.exists_open_finite_levelIntersections` in `LevelCurves`) holds. For
neoclassical functions strict positivity is equivalent to a linear lower bound
`a x₁ + b x₂ ≤ h (x₁, x₂)` with `a, b > 0` (`isPosNeoclassical_iff_exists_linear_le`): the
best such bound is `h (1,0) x₁ + h (0,1) x₂` (`IsNeoclassical.linear_le`), a consequence of
superadditivity, which in turn follows from concavity and homogeneity.
-/

open Real Set

namespace NeoTiling

/-- The closed nonnegative quadrant `ℝ₊² = {(x, y) | 0 ≤ x, 0 ≤ y}`. -/
def quadrant : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ Set.Ici 0

/-- `h : ℝ × ℝ → ℝ` is *neoclassical* if, viewed as a function `ℝ₊² → ℝ₊`, it is
continuous, concave and (positively) homogeneous of degree 1. -/
structure IsNeoclassical (h : ℝ × ℝ → ℝ) : Prop where
  /-- `h` takes values in `ℝ₊` on the quadrant. -/
  nonneg : ∀ p ∈ quadrant, 0 ≤ h p
  /-- `h` is continuous on the closed quadrant (boundary included). -/
  continuousOn : ContinuousOn h quadrant
  /-- `h` is concave on the quadrant. -/
  concaveOn : ConcaveOn ℝ quadrant h
  /-- `h (t • p) = t * h p` for every `t > 0` and every `p` in the quadrant. -/
  homogeneous : ∀ t : ℝ, 0 < t → ∀ p ∈ quadrant, h (t • p) = t * h p

/-- A *strictly positive* neoclassical function: `h x > 0` for `x ∈ ℝ₊² \ {0}`. -/
structure IsPosNeoclassical (h : ℝ × ℝ → ℝ) : Prop extends IsNeoclassical h where
  /-- `h` is positive away from the origin. -/
  pos : ∀ x ∈ quadrant, x ≠ 0 → 0 < h x

/-! ### The quadrant -/

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

/-! ### Elementary consequences of concavity and homogeneity -/

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

/-! ### Strictly positive neoclassical functions -/

namespace IsPosNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

theorem pos_fst : 0 < h (1, 0) :=
  hh.pos (1, 0) (mk_mem_quadrant zero_le_one le_rfl) (by simp)

theorem pos_snd : 0 < h (0, 1) :=
  hh.pos (0, 1) (mk_mem_quadrant le_rfl zero_le_one) (by simp)

theorem congr {g : ℝ × ℝ → ℝ} (hfg : EqOn h g quadrant) : IsPosNeoclassical g where
  toIsNeoclassical := hh.toIsNeoclassical.congr hfg
  pos x hx hx0 := hfg hx ▸ hh.pos x hx hx0

/-- Rescaling the two coordinates by positive factors preserves the class. -/
theorem scale {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsPosNeoclassical (fun p => h (α * p.1, β * p.2)) := by
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
  · intro p hp hp0
    apply hh.pos _ (hmem p hp)
    intro h0
    apply hp0
    rw [Prod.mk_eq_zero] at h0
    obtain ⟨h1, h2⟩ := h0
    exact Prod.ext (by simpa using (mul_eq_zero.mp h1).resolve_left hα.ne')
      (by simpa using (mul_eq_zero.mp h2).resolve_left hβ.ne')

end IsPosNeoclassical

/-- Strict positivity is the same as a linear lower bound with positive weights. This links the
present definition with the description "bounded below by `a x₁ + b x₂`, `a, b > 0`". -/
theorem isPosNeoclassical_iff_exists_linear_le {h : ℝ × ℝ → ℝ} :
    IsPosNeoclassical h ↔
      IsNeoclassical h ∧ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ p ∈ quadrant, a * p.1 + b * p.2 ≤ h p := by
  constructor
  · intro hh
    exact ⟨hh.toIsNeoclassical, h (1, 0), h (0, 1), hh.pos_fst, hh.pos_snd,
      fun p hp => hh.linear_le hp⟩
  · rintro ⟨hh, a, b, ha, hb, hab⟩
    refine ⟨hh, fun p hp hp0 => ?_⟩
    obtain ⟨h1, h2⟩ := mem_quadrant.mp hp
    refine lt_of_lt_of_le ?_ (hab p hp)
    rcases h1.eq_or_lt with h1 | h1
    · rcases h2.eq_or_lt with h2 | h2
      · exact absurd (Prod.ext h1.symm h2.symm) hp0
      · nlinarith
    · nlinarith

end NeoTiling
