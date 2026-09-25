import NeoTiling.FiniteIntersections

/-!
# Level curves of a strictly positive neoclassical function and their intersections

For a strictly positive neoclassical `h` and a price vector `p ∈ ℝ²₊₊` consider the unit level
curves `h x = 1` and `h (p ∘ x) = 1`, where `p ∘ x` is the coordinatewise product. An
intersection point `x₀` is *transversal* (`TransversalAt`) if it lies in the open orthant and
the superdifferentials of the two concave functions `h` and `h (p ∘ ·)` at `x₀` are disjoint.

Main theorem (`IsPosNeoclassical.exists_open_finite_levelIntersections`): every nonempty open
set `U ⊆ ℝ²₊₊` contains a nonempty open set `V` such that for every `p ∈ V` the two curves meet
in finitely many points, all of them transversal.

The proof reduces to the one-variable results of `FiniteIntersections`. After normalising `h`
(`IsPosNeoclassical.ofProfile_profile`) the curve `h x = 1` is the graph of the profile `f` and
the curve `h (p ∘ x) = 1` is the graph of `t ↦ f (p₁ t) / p₂`, so intersections correspond to
solutions of `f (p₁ t) = p₂ f t`, i.e. to `solutions f (1 / p₂, 1 / p₁)`. A common supergradient
`ξ` of the two functions at an intersection point yields, by restricting the supporting
inequalities to the two graphs, subgradients `s ∈ ∂f(t₀)` and `p₂ s / p₁ ∈ ∂f(p₁ t₀)`, which is
exactly what one-variable transversality (`Transversal`) forbids.

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

theorem mem_orthant_of_hadamard_mem {p x : ℝ × ℝ} (hp : p ∈ orthant)
    (hx : hadamard p x ∈ orthant) : x ∈ orthant := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hp
  obtain ⟨h3, h4⟩ := mem_orthant.mp hx
  exact mem_orthant.mpr ⟨pos_of_mul_pos_right h3 h1.le, pos_of_mul_pos_right h4 h2.le⟩

theorem hadamard_injective {c : ℝ × ℝ} (hc : c ∈ orthant) : Function.Injective (hadamard c) :=
  Function.LeftInverse.injective (hadamard_hinv_hadamard hc)

/-! ### Level curves, intersections, superdifferentials, transversality -/

/-- Intersection points of the unit level curves of `h` and of `h (p ∘ ·)`, in the closed
quadrant. -/
def levelIntersections (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ quadrant ∧ h x = 1 ∧ h (hadamard p x) = 1}

/-- Inner product on `ℝ × ℝ`. -/
def ip (v w : ℝ × ℝ) : ℝ := v.1 * w.1 + v.2 * w.2

/-- The superdifferential of `h : ℝ₊² → ℝ` at `x₀`: the slopes `ξ` of supporting affine
majorants, `h x ≤ h x₀ + ⟨ξ, x - x₀⟩` for all `x` in the closed quadrant. -/
def superdiff (h : ℝ × ℝ → ℝ) (x₀ : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {ξ | ∀ x ∈ quadrant, h x ≤ h x₀ + ip ξ (x - x₀)}

/-- `x₀` is a *transversal* intersection of the curves `h x = 1` and `h (p ∘ x) = 1`: it lies in
the open orthant and the superdifferentials of `h` and of `h (p ∘ ·)` at `x₀` are disjoint. -/
def TransversalAt (h : ℝ × ℝ → ℝ) (p x₀ : ℝ × ℝ) : Prop :=
  x₀ ∈ orthant ∧ Disjoint (superdiff h x₀) (superdiff (fun x => h (hadamard p x)) x₀)

theorem superdiff_congr {h g : ℝ × ℝ → ℝ} (hfg : EqOn h g quadrant) {x : ℝ × ℝ}
    (hx : x ∈ quadrant) : superdiff h x = superdiff g x := by
  ext ξ
  simp only [superdiff, mem_setOf_eq]
  constructor
  · intro H y hy
    rw [← hfg hy, ← hfg hx]
    exact H y hy
  · intro H y hy
    rw [hfg hy, hfg hx]
    exact H y hy

/-- Supergradients of `g ∘ (c ∘ ·)` at `x` are pulled back from supergradients of `g` at
`c ∘ x` by the coordinatewise inverse scaling. -/
theorem superdiff_comp_hadamard {g : ℝ × ℝ → ℝ} {c x ξ : ℝ × ℝ} (hc : c ∈ orthant)
    (hξ : ξ ∈ superdiff (fun z => g (hadamard c z)) x) :
    hadamard (hinv c) ξ ∈ superdiff g (hadamard c x) := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hc
  intro w hw
  have hz : hadamard (hinv c) w ∈ quadrant :=
    hadamard_mem_quadrant (orthant_subset_quadrant (hinv_mem_orthant hc)) hw
  have := hξ _ hz
  simp only [hadamard_hadamard_hinv hc, ip, Prod.fst_sub, Prod.snd_sub] at this
  simp only [ip, Prod.fst_sub, Prod.snd_sub]
  have key : ξ.1 * ((hadamard (hinv c) w).1 - x.1) + ξ.2 * ((hadamard (hinv c) w).2 - x.2) =
      (hadamard (hinv c) ξ).1 * (w.1 - (hadamard c x).1) +
        (hadamard (hinv c) ξ).2 * (w.2 - (hadamard c x).2) := by
    simp only [hadamard_fst, hadamard_snd, hinv_fst, hinv_snd]
    field_simp
  linarith

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

theorem TransversalAt.of_hinv {h : ℝ × ℝ → ℝ} {p x₀ : ℝ × ℝ} (hp : p ∈ orthant)
    (H : TransversalAt h (hinv p) (hadamard p x₀)) : TransversalAt h p x₀ := by
  obtain ⟨Ho, Hd⟩ := H
  refine ⟨mem_orthant_of_hadamard_mem hp Ho, ?_⟩
  rw [Set.disjoint_left] at Hd ⊢
  intro ξ h1 h2
  have h1' : hadamard (hinv p) ξ ∈
      superdiff (fun x => h (hadamard (hinv p) x)) (hadamard p x₀) := by
    apply superdiff_comp_hadamard hp
    simpa only [hadamard_hinv_hadamard hp] using h1
  have h2' : hadamard (hinv p) ξ ∈ superdiff h (hadamard p x₀) := superdiff_comp_hadamard hp h2
  exact Hd h2' h1'

/-! ### Normalisation: transport along `x ↦ (h (1,0) x₁, h (0,1) x₂)` -/

namespace IsPosNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
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

theorem transversalAt_of_ofProfile {p x₀ : ℝ × ℝ} (hp : p ∈ quadrant)
    (H : TransversalAt (ofProfile (profile h)) p (hadamard (h (1, 0), h (0, 1)) x₀)) :
    TransversalAt h p x₀ := by
  have hc := hh.scaling_mem_orthant
  obtain ⟨Ho, Hd⟩ := H
  have hx₀ : x₀ ∈ orthant := mem_orthant_of_hadamard_mem hc Ho
  refine ⟨hx₀, ?_⟩
  rw [Set.disjoint_left] at Hd ⊢
  intro ξ h1 h2
  have e1 : EqOn h (fun z => ofProfile (profile h) (hadamard (h (1, 0), h (0, 1)) z)) quadrant :=
    fun z hz => hh.eq_ofProfile_hadamard hz
  have e2 : EqOn (fun x => h (hadamard p x))
      (fun z => (fun x => ofProfile (profile h) (hadamard p x))
        (hadamard (h (1, 0), h (0, 1)) z)) quadrant := fun z hz => by
    show h (hadamard p z) = ofProfile (profile h) (hadamard p (hadamard (h (1, 0), h (0, 1)) z))
    rw [hh.eq_ofProfile_hadamard (hadamard_mem_quadrant hp hz), hadamard_comm]
  rw [superdiff_congr e1 (orthant_subset_quadrant hx₀)] at h1
  rw [superdiff_congr e2 (orthant_subset_quadrant hx₀)] at h2
  exact Hd (superdiff_comp_hadamard hc h1) (superdiff_comp_hadamard hc h2)

end IsPosNeoclassical

/-! ### The normalised picture: graphs of the profile -/

namespace IsProfile

variable {f : ℝ → ℝ} (hf : IsProfile f)
include hf

theorem one_lt_ofProfile_iff {u : ℝ × ℝ} (hu : u ∈ quadrant) (hu1 : u.1 ≤ 1) :
    1 < ofProfile f u ↔ f u.1 < u.2 := by
  rw [hf.lt_ofProfile_iff hu hu1, one_mul, div_one]

theorem ofProfile_lt_one_iff {u : ℝ × ℝ} (hu : u ∈ quadrant) (hu1 : u.1 ≤ 1) :
    ofProfile f u < 1 ↔ u.2 < f u.1 := by
  rw [hf.ofProfile_lt_iff hu hu1, one_mul, div_one]

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
    1 < ofProfile f u :=
  hu1.trans_le (hf.fst_le_ofProfile hu)

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

/-- **Transversality at an intersection** (normalised case). A common supergradient `ξ` of
`ofProfile f` and `ofProfile f (p ∘ ·)` at `(t₀, f t₀)` has `ξ₂ > 0`; restricting the two
supporting inequalities to the two graphs gives `s = -ξ₁ / ξ₂ ∈ ∂f(t₀)` and
`p₂ s / p₁ ∈ ∂f(p₁ t₀)`, contradicting one-variable transversality. -/
theorem transversalAt_ofProfile {p : ℝ × ℝ} (hp1 : 1 < p.1) (hp2 : 0 < p.2) (hp2' : p.2 < 1)
    (ht : Transversal f (1 / p.2, 1 / p.1)) {u₀ : ℝ × ℝ}
    (hu₀ : u₀ ∈ levelIntersections (ofProfile f) p) : TransversalAt (ofProfile f) p u₀ := by
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
  have ht₀1 : t₀ < 1 := (div_le_self hy₀I.1.le hp1.le).trans_lt hy₀I.2
  have hft₀ : 0 < f t₀ := hf.pos ⟨ht₀0.le, ht₀1⟩
  -- the solution equation
  have hsol : f y₀ = p.2 * f t₀ := by
    have h' : 1 / p.2 * f y₀ = f (1 / p.1 * y₀) := hy₀.2
    rw [show 1 / p.1 * y₀ = t₀ by rw [ht₀]; ring] at h'
    field_simp at h'
    linear_combination h'
  refine ⟨mem_orthant.mpr ⟨ht₀0, hft₀⟩, ?_⟩
  rw [Set.disjoint_left]
  intro ξ hξ hξp
  -- values of the two functions at the intersection point
  have hu₀q : (t₀, f t₀) ∈ quadrant := mk_mem_quadrant ht₀0.le hft₀.le
  have hFu₀ : ofProfile f (t₀, f t₀) = 1 := (hf.ofProfile_eq_one_iff hu₀q ht₀1.le).mpr rfl
  have hFpu₀ : ofProfile f (hadamard p (t₀, f t₀)) = 1 := by
    rw [hadamard_mk, hy₀t]
    have hq : (y₀, p.2 * f t₀) ∈ quadrant :=
      mk_mem_quadrant hy₀I.1.le (mul_nonneg hp2.le hft₀.le)
    exact (hf.ofProfile_eq_one_iff hq hy₀I.2.le).mpr hsol
  -- `ξ₂ > 0`: compare with the point `(t₀, f t₀ + 1)` above the graph
  have hξ2 : 0 < ξ.2 := by
    have hy : (t₀, f t₀ + 1) ∈ quadrant := mk_mem_quadrant ht₀0.le (by linarith)
    have h1 := hξ _ hy
    have h2 : 1 < ofProfile f (t₀, f t₀ + 1) :=
      (hf.one_lt_ofProfile_iff hy ht₀1.le).mpr (by linarith)
    simp only [ip, Prod.fst_sub, Prod.snd_sub] at h1
    have e : ξ.1 * (t₀ - t₀) + ξ.2 * (f t₀ + 1 - f t₀) = ξ.2 := by ring
    linarith
  set s := -ξ.1 / ξ.2 with hs_def
  -- `s` is a subgradient of `f` at `t₀`: restrict the supporting inequality to the graph of `f`
  have hs : s ∈ subdiff f t₀ := by
    intro z hz
    have hzq : (z, f z) ∈ quadrant := mk_mem_quadrant hz.1 (hf.nonneg hz)
    have hFz : ofProfile f (z, f z) = 1 := (hf.ofProfile_eq_one_iff hzq hz.2).mpr rfl
    have h1 := hξ _ hzq
    simp only [hFz, ip, Prod.fst_sub, Prod.snd_sub] at h1
    have key : 0 ≤ ξ.1 * (z - t₀) + ξ.2 * (f z - f t₀) := by linarith
    have e : s * (z - t₀) = -(ξ.1 * (z - t₀)) / ξ.2 := by rw [hs_def]; ring
    have h2 : -(ξ.1 * (z - t₀)) / ξ.2 ≤ f z - f t₀ := by
      rw [div_le_iff₀ hξ2, mul_comm]
      linarith
    rw [e]
    linarith
  -- `p₂ s / p₁` is a subgradient of `f` at `y₀ = p₁ t₀`: restrict to the graph of `f (p₁ ·) / p₂`
  have hs' : p.2 * s / p.1 ∈ subdiff f y₀ := by
    intro w hw
    set z := w / p.1 with hz_def
    have hz01 : z ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hw.1 hp1'.le, (div_le_one hp1').mpr (hw.2.trans hp1.le)⟩
    have hzq : (z, f w / p.2) ∈ quadrant :=
      mk_mem_quadrant hz01.1 (div_nonneg (hf.nonneg hw) hp2.le)
    have hpz : hadamard p (z, f w / p.2) = (w, f w) := by
      simp only [hadamard_mk]
      rw [hz_def, mul_div_cancel₀ _ hp1'.ne', mul_div_cancel₀ _ hp2.ne']
    have hFz : ofProfile f (hadamard p (z, f w / p.2)) = 1 := by
      rw [hpz]
      exact (hf.ofProfile_eq_one_iff (mk_mem_quadrant hw.1 (hf.nonneg hw)) hw.2).mpr rfl
    have h1 := hξp _ hzq
    simp only [hFz, ip, Prod.fst_sub, Prod.snd_sub] at h1
    have key : 0 ≤ ξ.1 * (z - t₀) + ξ.2 * (f w / p.2 - f t₀) := by linarith
    have e0 : ξ.1 * (z - t₀) + ξ.2 * (f w / p.2 - f t₀) =
        (p.2 * (ξ.1 * (z - t₀)) + ξ.2 * (f w - p.2 * f t₀)) / p.2 := by
      field_simp
    rw [e0] at key
    have key' : 0 ≤ p.2 * (ξ.1 * (z - t₀)) + ξ.2 * (f w - p.2 * f t₀) := by
      have := (le_div_iff₀ hp2).mp key
      rwa [zero_mul] at this
    have e : p.2 * s / p.1 * (w - y₀) = -(p.2 * (ξ.1 * (z - t₀))) / ξ.2 := by
      rw [hs_def, hz_def, ht₀]
      field_simp
    have h2 : -(p.2 * (ξ.1 * (z - t₀))) / ξ.2 ≤ f w - p.2 * f t₀ := by
      rw [div_le_iff₀ hξ2, mul_comm]
      linarith
    rw [e, hsol]
    linarith
  -- contradiction with one-variable transversality
  have hβ : (1 / p.2, 1 / p.1).2 * y₀ = t₀ := by
    show 1 / p.1 * y₀ = t₀
    rw [ht₀]
    ring
  have := ht y₀ hy₀ s (by rw [hβ]; exact hs) (p.2 * s / p.1) hs'
  apply this
  show 1 / p.1 * s = 1 / p.2 * (p.2 * s / p.1)
  field_simp

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

namespace IsPosNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

/-- The main case `p₁ > 1 > p₂`. -/
theorem exists_open_aux {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ U)
    (h1 : 1 < p₀.1) (h2 : 0 < p₀.2) (h3 : p₀.2 < 1) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∩ orthant ∧
      ∀ p ∈ V, (levelIntersections h p).Finite ∧
        ∀ x₀ ∈ levelIntersections h p, TransversalAt h p x₀ := by
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
      apply hh.transversalAt_of_ofProfile (orthant_subset_quadrant hpo)
      apply hf.transversalAt_ofProfile hp1 hp2' hp2 htr
      rw [hh.levelIntersections_eq_preimage (orthant_subset_quadrant hpo)] at hx₀
      exact hx₀

/-- **Generic finiteness and transversality of level-curve intersections.** For a strictly
positive neoclassical `h`, every nonempty open set `U ⊆ ℝ²₊₊` of prices contains a nonempty open
set `V` such that for every `p ∈ V` the curves `h x = 1` and `h (p ∘ x) = 1` meet in finitely
many points, all of them transversal. -/
theorem exists_open_finite_levelIntersections {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hne : (U ∩ orthant).Nonempty) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∩ orthant ∧
      ∀ p ∈ V, (levelIntersections h p).Finite ∧
        ∀ x₀ ∈ levelIntersections h p, TransversalAt h p x₀ := by
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
      obtain ⟨hfin, htr⟩ := hV' _ hpV
      refine ⟨?_, ?_⟩
      · rw [levelIntersections_hinv hpo]
        exact hfin.image _
      · intro x₀ hx₀
        rw [levelIntersections_hinv hpo] at hx₀
        obtain ⟨y, hy, rfl⟩ := hx₀
        apply TransversalAt.of_hinv hpo
        rw [hadamard_hadamard_hinv hpo]
        exact htr y hy
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

end IsPosNeoclassical

end NeoTiling
