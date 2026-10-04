import NeoTiling.Transversality

/-!
# General position of a set of prices

For a strictly positive neoclassical `h` and a finite family of prices `P = (p_t)_{t < T}` in
`ℝ²₊₊` consider the unit level curves `h (p_t ∘ x) = 1`. The pair `(h, P)` is in *general
position* (`GeneralPosition`) if any two of the curves meet in finitely many points, all of them
transversal, and no three of the curves pass through one point.

Main results: general position is stable under small perturbations of the prices
(`IsPosNeoclassical.generalPosition_stable`) and is attained in every nonempty open set of prices
(`IsPosNeoclassical.exists_generalPosition`).

The substitution `y = p ∘ x` turns the curves of a pair `(p, q)` into the curves `h y = 1` and
`h (r ∘ y) = 1`, `r = p⁻¹ ∘ q`, of `LevelCurves`. Being a *good price* (`IsGoodPrice`: finitely
many intersections, all transversal) is an open condition on `r`: in the main chamber
`r₁ > 1 > r₂` it is equivalent to one-variable transversality of `tau r`, and the bad
one-variable parameters near a point form a closed set (the construction of
`IsProfile.exists_open_transversal` without Sard). Condition 2 of general position is
equivalent to separation by rays (`RaySep`) of the intersection points of two pairs with a common
index, since a ray meets each curve once by homogeneity.
-/

open Set Filter Topology

namespace NeoTiling

/-- Intersection points of the unit level curves `h (p ∘ x) = 1` and `h (q ∘ x) = 1`, in the
closed quadrant. -/
def pairIntersections (h : ℝ × ℝ → ℝ) (p q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ quadrant ∧ h (hadamard p x) = 1 ∧ h (hadamard q x) = 1}

/-- `x₀` is a *transversal* intersection of the curves `h (p ∘ x) = 1` and `h (q ∘ x) = 1`: it
lies in the open orthant and the superdifferentials of `h (p ∘ ·)` and of `h (q ∘ ·)` at `x₀` are
disjoint. -/
def PairTransversalAt (h : ℝ × ℝ → ℝ) (p q x₀ : ℝ × ℝ) : Prop :=
  x₀ ∈ orthant ∧
    Disjoint (superdiff (fun x => h (hadamard p x)) x₀) (superdiff (fun x => h (hadamard q x)) x₀)

/-- **General position** (definition 2.8 of the notes). The pair `(h, P)`, `P = (p_t)_{t < T}`,
is in general position if all prices lie in `ℝ²₊₊` and
1. for `s ≠ t` the curves `h (p_s ∘ x) = 1` and `h (p_t ∘ x) = 1` meet in finitely many points,
   all of them transversal;
2. no three curves with pairwise distinct indices pass through one point. -/
structure GeneralPosition (h : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) : Prop where
  mem_orthant : ∀ t, P t ∈ orthant
  finite : ∀ s t, s ≠ t → (pairIntersections h (P s) (P t)).Finite
  transversal : ∀ s t, s ≠ t → ∀ x ∈ pairIntersections h (P s) (P t),
    PairTransversalAt h (P s) (P t) x
  no_triple : ∀ r s t, r ≠ s → s ≠ t → r ≠ t → ∀ x ∈ pairIntersections h (P r) (P s),
    h (hadamard (P t) x) ≠ 1

/-- `r` is a *good price*: the curves `h x = 1` and `h (r ∘ x) = 1` meet in finitely many points,
all of them transversal. -/
def IsGoodPrice (h : ℝ × ℝ → ℝ) (r : ℝ × ℝ) : Prop :=
  (levelIntersections h r).Finite ∧ ∀ x ∈ levelIntersections h r, TransversalAt h r x

/-- No intersection point of the pair `(r, s)` lies on one ray from the origin with an
intersection point of the pair `(r, t)`. -/
def RaySep (h : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) (r s t : Fin T) : Prop :=
  ∀ x ∈ pairIntersections h (P r) (P s), ∀ y ∈ pairIntersections h (P r) (P t),
    x.1 * y.2 ≠ x.2 * y.1

theorem pairIntersections_comm (h : ℝ × ℝ → ℝ) (p q : ℝ × ℝ) :
    pairIntersections h p q = pairIntersections h q p := by
  ext x; simp only [pairIntersections, mem_setOf_eq]; tauto

/-! ### A pair of prices as one price: the substitution `y = p ∘ x` -/

theorem hadamard_mem_orthant {p x : ℝ × ℝ} (hp : p ∈ orthant) (hx : x ∈ orthant) :
    hadamard p x ∈ orthant :=
  mem_orthant.mpr ⟨mul_pos hp.1 hx.1, mul_pos hp.2 hx.2⟩

/-- `(p⁻¹ ∘ q) ∘ (p ∘ z) = q ∘ z`. -/
theorem hadamard_comp_hadamard {p q z : ℝ × ℝ} (hp : p ∈ orthant) :
    hadamard (hadamard (hinv p) q) (hadamard p z) = hadamard q z := by
  obtain ⟨h1, h2⟩ := mem_orthant.mp hp
  ext <;> simp [hadamard, hinv] <;> field_simp [h1.ne', h2.ne']

/-- Supergradients of `g (c ∘ ·)` at `x` are the supergradients of `g` at `c ∘ x`, pulled back
by `c⁻¹ ∘ ·`. -/
theorem superdiff_comp_hadamard_eq {g : ℝ × ℝ → ℝ} {c x : ℝ × ℝ} (hc : c ∈ orthant) :
    superdiff (fun z => g (hadamard c z)) x = hadamard (hinv c) ⁻¹' superdiff g (hadamard c x) := by
  refine Set.ext fun ξ => ⟨superdiff_comp_hadamard hc, fun hξ => ?_⟩
  -- `superdiff_comp_hadamard` for the function `g (c ∘ ·)` and the scaling `c⁻¹`
  have hξ' : hadamard (hinv c) ξ ∈
      superdiff (fun z => g (hadamard c (hadamard (hinv c) z))) (hadamard c x) := by
    simpa only [hadamard_hadamard_hinv hc] using hξ
  have := superdiff_comp_hadamard (g := fun z => g (hadamard c z)) (hinv_mem_orthant hc) hξ'
  rwa [hinv_hinv hc, hadamard_hinv_hadamard hc, hadamard_hadamard_hinv hc] at this

theorem pairIntersections_eq_image {h : ℝ × ℝ → ℝ} {p q : ℝ × ℝ} (hp : p ∈ orthant) :
    pairIntersections h p q = hadamard (hinv p) '' levelIntersections h (hadamard (hinv p) q) := by
  rw [Set.image_eq_preimage_of_inverse (hadamard_hadamard_hinv hp) (hadamard_hinv_hadamard hp)]
  ext x
  simp only [pairIntersections, levelIntersections, mem_setOf_eq, mem_preimage,
    hadamard_comp_hadamard hp]
  exact and_congr_left fun _ =>
    ⟨hadamard_mem_quadrant (orthant_subset_quadrant hp), mem_quadrant_of_hadamard_mem hp⟩

theorem pairTransversalAt_iff {h : ℝ × ℝ → ℝ} {p q x : ℝ × ℝ} (hp : p ∈ orthant) :
    PairTransversalAt h p q x ↔ TransversalAt h (hadamard (hinv p) q) (hadamard p x) := by
  -- both superdifferentials are pulled back by the bijection `p⁻¹ ∘ ·`
  have e := superdiff_comp_hadamard_eq (g := fun y => h (hadamard (hadamard (hinv p) q) y))
    (x := x) hp
  simp only [hadamard_comp_hadamard hp] at e
  rw [PairTransversalAt, TransversalAt, e, superdiff_comp_hadamard_eq (g := h) hp,
    Set.disjoint_preimage_iff (Function.LeftInverse.surjective (hadamard_hinv_hadamard hp))]
  exact and_congr_left fun _ => ⟨hadamard_mem_orthant hp, mem_orthant_of_hadamard_mem hp⟩

/-- Condition 1 of general position for the pair `(p, q)` says that `p⁻¹ ∘ q` is a good price. -/
theorem pairGood_iff {h : ℝ × ℝ → ℝ} {p q : ℝ × ℝ} (hp : p ∈ orthant) :
    ((pairIntersections h p q).Finite ∧ ∀ x ∈ pairIntersections h p q, PairTransversalAt h p q x)
      ↔ IsGoodPrice h (hadamard (hinv p) q) := by
  rw [pairIntersections_eq_image hp]
  simp only [IsGoodPrice, Set.finite_image_iff (hadamard_injective (hinv_mem_orthant hp)).injOn,
    Set.forall_mem_image, pairTransversalAt_iff hp, hadamard_hadamard_hinv hp]

/-- The substitution `x ↦ r ∘ x` exchanges the two curves. -/
theorem isGoodPrice_hinv {h : ℝ × ℝ → ℝ} {r : ℝ × ℝ} (hr : r ∈ orthant) :
    IsGoodPrice h (hinv r) ↔ IsGoodPrice h r := by
  have aux : ∀ r : ℝ × ℝ, r ∈ orthant → IsGoodPrice h (hinv r) → IsGoodPrice h r := by
    rintro r hr ⟨hfin, htr⟩
    refine ⟨levelIntersections_hinv hr ▸ hfin.image _, fun x₀ hx₀ => ?_⟩
    rw [levelIntersections_hinv hr] at hx₀; obtain ⟨y, hy, rfl⟩ := hx₀
    exact TransversalAt.of_hinv hr (by rw [hadamard_hadamard_hinv hr]; exact htr y hy)
  refine ⟨aux r hr, fun hG => aux (hinv r) (hinv_mem_orthant hr) ?_⟩; rwa [hinv_hinv hr]

/-! ### Good prices form an open set -/

/-- A subgradient of `f` at `k₁ t`, rescaled, is a supporting slope of `t ↦ f (k₁ t) / k₂`. -/
theorem mem_subdiffOn_of_mem_subdiff {f : ℝ → ℝ} {k₁ k₂ t a : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (ha : a ∈ subdiff f (k₁ * t)) :
    k₁ / k₂ * a ∈ subdiffOn (fun t => f (k₁ * t) / k₂) 0 (1 / k₁) t := by
  intro z hz
  -- the subgradient inequality at `k₁ z ∈ [0, 1]`, divided by `k₂ > 0`
  convert div_le_div_of_nonneg_right (ha (k₁ * z) ⟨mul_nonneg hk₁.le hz.1,
    (le_div_iff₀' hk₁).mp hz.2⟩) hk₂.le using 1
  field_simp

/-- **One-variable transversality is open** (`exists_open_transversal` without Sard). -/
theorem IsProfile.eventually_transversal {f : ℝ → ℝ} (hf : IsProfile f) {p : ℝ × ℝ}
    (hp : p ∈ Param) (ht : Transversal f p) : ∀ᶠ q in 𝓝 p, Transversal f q := by
  obtain ⟨α₀, β₀⟩ := p
  obtain ⟨hα₀, hβ0, hβ1⟩ : 1 < α₀ ∧ 0 < β₀ ∧ β₀ < 1 := mem_Param.mp hp
  -- a box `B` of parameters around `(α₀, β₀)`; its solutions lie in `[c, d]`
  set r := (α₀ - 1) / 2 with hr
  set β₁ := β₀ / 2 with hβ₁
  set β₂ := (β₀ + 1) / 2 with hβ₂
  have hβ₁0 : 0 < β₁ := half_pos hβ0
  have hβ₂1 : β₂ < 1 := by linarith
  obtain ⟨c, d, hc, -, hd, hsol⟩ := hf.exists_Icc_solutions_subset (a := α₀ - r) (b := α₀ + r)
    (by linarith) (by linarith) hβ₁0 (by linarith) hβ₂1
  have hfy : ∀ y ∈ Icc c d, f y ≠ 0 := fun y hy =>
    (hf.pos ⟨by linarith [hy.1], by linarith [hy.2]⟩).ne'
  set B : Set (ℝ × ℝ) := Ioo (α₀ - r) (α₀ + r) ×ˢ Ioo β₁ β₂
  -- the bad parameters: images of critical pairs under `(y, β) ↦ (ratio f (y, β), β)`
  set Bad : Set (ℝ × ℝ) :=
    (fun q => (ratio f q, q.2)) '' {q ∈ Icc c d ×ˢ Icc β₁ β₂ | IsCritical f q.1 q.2}
  have hBadc : IsClosed Bad :=
    ((hf.isCompact_critical hc hd hβ₁0 hβ₂1).image_of_continuousOn
      (((hf.continuousOn_ratio hc hd hβ₁0 hβ₂1).mono fun q hq => hq.1).prodMk
        continuousOn_snd)).isClosed
  -- in the box, the good parameters are exactly the transversal ones
  have key : ∀ q ∈ B, q ∉ Bad ↔ Transversal f q := by
    rintro ⟨α, β⟩ ⟨hαI, hβ₁, hβ₂⟩
    constructor
    · rintro hq y hy a ha b hb (hab : β * a = α * b)
      have hy2 : α * f y = f (β * y) := hy.2
      have hyK := hsol α ⟨hαI.1.le, hαI.2.le⟩ β ⟨hβ₁.le, hβ₂.le⟩ hy
      refine hq ⟨(y, β), ⟨⟨hyK, hβ₁.le, hβ₂.le⟩, a, ha, b, hb, ?_⟩, ?_⟩
      · show β * a * f y = f (β * y) * b
        rw [← hy2]; linear_combination f y * hab
      · show (f (β * y) / f y, β) = (α, β)
        rw [← hy2, mul_div_cancel_right₀ _ (hfy y hyK)]
    · rintro ht' ⟨⟨y, β'⟩, ⟨⟨hy, -⟩, a, ha, b, hb, hab⟩, hq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      have hα : ratio f (y, β') * f y = f (β' * y) := div_mul_cancel₀ _ (hfy y hy)
      refine ht' y ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, hα⟩ a ha b hb ?_
      exact mul_right_cancel₀ (hfy y hy) (by linear_combination hab - b * hα)
  have hmem : (α₀, β₀) ∈ B := ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem,
    hBadc.isOpen_compl.mem_nhds ((key _ hmem).mpr ht)] with q hqB hq
  exact (key q hqB).mp hq

namespace IsPosNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

/-- A good price has no coordinate `1`: otherwise an axis point is a common point of the curves. -/
theorem ne_one_of_isGoodPrice {r : ℝ × ℝ} (H : IsGoodPrice h r) : r.1 ≠ 1 ∧ r.2 ≠ 1 := by
  have hc₁ := one_div_nonneg.mpr hh.pos_fst.le
  have hc₂ := one_div_nonneg.mpr hh.pos_snd.le
  have hx1 : h (1 / h (1, 0), 0) = 1 := by rw [hh.fst_axis hc₁, one_div_mul_cancel hh.pos_fst.ne']
  have hx2 : h (0, 1 / h (0, 1)) = 1 := by rw [hh.snd_axis hc₂, one_div_mul_cancel hh.pos_snd.ne']
  -- the axis points `(1 / h(1,0), 0)`, `(0, 1 / h(0,1))` are not in the open orthant
  constructor <;> intro hr
  · have := H.2 _ ⟨mk_mem_quadrant hc₁ le_rfl, hx1, by simpa [hadamard, hr] using hx1⟩
    exact lt_irrefl 0 (mem_orthant.mp this.1).2
  · have := H.2 _ ⟨mk_mem_quadrant le_rfl hc₂, hx2, by simpa [hadamard, hr] using hx2⟩
    exact lt_irrefl 0 (mem_orthant.mp this.1).1

/-- The curve `h (r ∘ x) = 1` is the graph of `t ↦ profile h (r₁ h(1,0) t) / (r₂ h(0,1))`. -/
theorem curveFun_comp_hadamard {r : ℝ × ℝ} (hr : r ∈ orthant) :
    curveFun (fun x => h (hadamard r x)) =
        (fun t => profile h (r.1 * h (1, 0) * t) / (r.2 * h (0, 1))) ∧
      curveEnd (fun x => h (hadamard r x)) = 1 / (r.1 * h (1, 0)) := by
  obtain ⟨hr1, hr2⟩ := mem_orthant.mp hr
  -- the normalising values of `h (r ∘ ·)` are `r` times those of `h`
  have hg1 : h (hadamard r (1, 0)) = r.1 * h (1, 0) := by simp [hadamard, hh.fst_axis hr1.le]
  have hg2 : h (hadamard r (0, 1)) = r.2 * h (0, 1) := by simp [hadamard, hh.snd_axis hr2.le]
  -- hence `h (r ∘ ·)` and `h` have the same normalisation and the same profile
  have hprof : profile (fun x => h (hadamard r x)) = profile h := by
    refine congrArg profile₀ (funext fun p => ?_)
    simp only [normalize]; rw [hg1, hg2]
    congr 1; ext <;> simp only [hadamard] <;> field_simp [hr1.ne', hr2.ne']
  exact ⟨funext fun t => by rw [curveFun, hg1, hg2, hprof], by rw [curveEnd, hg1]⟩

/-- Conversely, a good price in the main chamber gives one-variable transversality. -/
theorem transversal_of_isGoodPrice {r : ℝ × ℝ} (hr : r ∈ orthant) (h1 : 1 < r.1) (h2 : r.2 < 1)
    (H : IsGoodPrice h r) : Transversal (profile h) (tau r) := by
  obtain ⟨hr1, hr2⟩ := mem_orthant.mp hr
  obtain ⟨hc₁, hc₂⟩ : 0 < h (1, 0) ∧ 0 < h (0, 1) := ⟨hh.pos_fst, hh.pos_snd⟩
  have hg : IsPosNeoclassical (fun x => h (hadamard r x)) := hh.scale hr1 hr2
  obtain ⟨hcf, hce⟩ := hh.curveFun_comp_hadamard hr
  rintro y hy a ha b hb (hab : 1 / r.1 * a = 1 / r.2 * b)
  -- the parameter `t₀` with `h(1,0) t₀ = y / r₁` and `r₁ h(1,0) t₀ = y`
  have hy0 : 0 < y := hy.1.1.lt_of_ne fun h0 =>
    hh.profile_isProfile.zero_not_mem_solutions ((tau_mem_Param_iff hr).mpr ⟨h1, h2⟩) (h0 ▸ hy)
  obtain ⟨t₀, ht₀⟩ : ∃ t, h (1, 0) * t = (tau r).2 * y := ⟨_, mul_div_cancel₀ _ hc₁.ne'⟩
  have hgt : r.1 * h (1, 0) * t₀ = y := by rw [mul_assoc, ht₀]; simp [tau, hr1.ne']
  have ht₀0 : 0 < t₀ := pos_of_mul_pos_right (a := r.1 * h (1, 0)) (hgt ▸ hy0) (by positivity)
  have ht₀1 : t₀ < curveEnd h := (lt_div_iff₀' hc₁).mpr (by nlinarith [hy.1.2, mul_pos hc₁ ht₀0])
  -- `x₀ = (t₀, curveFun h t₀)` lies on both curves
  have hx₀o : (t₀, curveFun h t₀) ∈ orthant := ⟨ht₀0, hh.curveFun_pos ⟨ht₀0.le, ht₀1⟩⟩
  have hx₀h : (t₀, curveFun h t₀) ∈ levelCurve h :=
    hh.levelCurve_eq_graphOn ▸ ⟨⟨ht₀0.le, ht₀1.le⟩, rfl⟩
  have hx₀g : (t₀, curveFun h t₀) ∈ levelCurve (fun x => h (hadamard r x)) := by
    rw [hg.levelCurve_eq_graphOn, hcf, hce]
    refine ⟨⟨ht₀0.le, by rw [le_div_iff₀' (by positivity), hgt]; exact hy.1.2⟩, ?_⟩
    dsimp only; rw [curveFun, ht₀, hgt, ← hy.2]; show 1 / r.2 * _ / _ = _; field_simp
  -- the common supporting slope `h(1,0) / h(0,1) * a` contradicts transversality at `x₀`
  have hdisj := (H.2 _ ⟨orthant_subset_quadrant hx₀o, hx₀h.2, hx₀g.2⟩).2
  rw [disjoint_superdiff_iff hh hg hx₀o hx₀h.2 hx₀g.2, hcf, hce] at hdisj
  have heq : h (1, 0) / h (0, 1) * a = r.1 * h (1, 0) / (r.2 * h (0, 1)) * b := by
    field_simp at hab ⊢; linear_combination hab
  refine Set.disjoint_left.mp hdisj (mem_subdiffOn_of_mem_subdiff hc₁ hc₂ (by rwa [ht₀])) ?_
  exact heq ▸ mem_subdiffOn_of_mem_subdiff (mul_pos hr1 hc₁) (mul_pos hr2 hc₂) (by rwa [hgt])

/-- Good prices form an open set in the main chamber `r₁ > 1 > r₂`. -/
theorem eventually_isGoodPrice_of_one_lt {r₀ : ℝ × ℝ} (hr₀ : r₀ ∈ orthant) (h1 : 1 < r₀.1)
    (h2 : r₀.2 < 1) (H : IsGoodPrice h r₀) : ∀ᶠ r in 𝓝 r₀, IsGoodPrice h r := by
  have hf := hh.profile_isProfile
  have hev := hf.eventually_transversal ((tau_mem_Param_iff hr₀).mpr ⟨h1, h2⟩)
    (hh.transversal_of_isGoodPrice hr₀ h1 h2 H)
  filter_upwards [(continuousOn_tau.continuousAt (isOpen_orthant.mem_nhds hr₀)).eventually hev,
    isOpen_orthant.mem_nhds hr₀, (isOpen_lt continuous_const continuous_fst).mem_nhds h1,
    (isOpen_lt continuous_snd continuous_const).mem_nhds h2] with r ht hro hr1 hr2
  -- one-variable transversality of `tau r` makes `r` good (the last step of `exists_open_aux`)
  have hrq := orthant_subset_quadrant hro
  have hfin : (levelIntersections (ofProfile (profile h)) r).Finite := by
    rw [hf.levelIntersections_ofProfile hr1.le hro.2]
    exact (hf.finite_of_transversal ((tau_mem_Param_iff hro).mpr ⟨hr1, hr2⟩) ht).image _
  rw [IsGoodPrice, hh.levelIntersections_eq_preimage hrq]
  exact ⟨hfin.preimage (hadamard_injective hh.scaling_mem_orthant).injOn, fun x₀ hx₀ =>
    hh.transversalAt_of_ofProfile hrq (hf.transversalAt_ofProfile hr1 hro.2 hr2 ht hx₀)⟩

/-- **Good prices form an open set.** -/
theorem eventually_isGoodPrice {r₀ : ℝ × ℝ} (hr₀ : r₀ ∈ orthant) (H : IsGoodPrice h r₀) :
    ∀ᶠ r in 𝓝 r₀, IsGoodPrice h r := by
  obtain ⟨h1, h2⟩ := hh.ne_one_of_isGoodPrice H
  rcases lt_or_gt_of_ne h1 with hc1 | hc1 <;> rcases lt_or_gt_of_ne h2 with hc2 | hc2
  · -- `r₀.1 < 1`, `r₀.2 < 1`: no intersections nearby
    filter_upwards [isOpen_orthant.mem_nhds hr₀,
      (isOpen_lt continuous_fst continuous_const).mem_nhds hc1,
      (isOpen_lt continuous_snd continuous_const).mem_nhds hc2] with r hro hc1' hc2'
    simp [IsGoodPrice, hh.levelIntersections_eq_empty_of_lt_one hro hc1' hc2']
  · -- `r₀.1 < 1 < r₀.2`: invert the price
    have hev := hh.eventually_isGoodPrice_of_one_lt (hinv_mem_orthant hr₀)
      ((one_lt_div hr₀.1).mpr hc1) ((div_lt_one hr₀.2).mpr hc2) ((isGoodPrice_hinv hr₀).mpr H)
    filter_upwards [(continuousOn_hinv.continuousAt (isOpen_orthant.mem_nhds hr₀)).eventually hev,
      isOpen_orthant.mem_nhds hr₀] with r hr' hro
    exact (isGoodPrice_hinv hro).mp hr'
  · -- `r₀.1 > 1 > r₀.2`: the main case
    exact hh.eventually_isGoodPrice_of_one_lt hr₀ hc1 hc2 H
  · -- `r₀.1 > 1`, `r₀.2 > 1`: no intersections nearby
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hc1,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hc2] with r hc1' hc2'
    simp [IsGoodPrice, hh.levelIntersections_eq_empty_of_one_lt hc1' hc2']

end IsPosNeoclassical

/-! ### Separation by rays -/

/-- Families of prices near a family in `ℝ²₊₊` stay in `ℝ²₊₊`. -/
theorem eventually_mem_orthant {T : ℕ} {P₀ : Fin T → ℝ × ℝ} (hP₀ : ∀ t, P₀ t ∈ orthant) :
    ∀ᶠ P in 𝓝 P₀, ∀ t, P t ∈ orthant :=
  eventually_all.mpr fun t => (continuous_apply t).continuousAt (isOpen_orthant.mem_nhds (hP₀ t))

namespace IsPosNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

/-- Homogeneity along a ray: if `y` lies on the ray of `x ∈ ℝ²₊₊`, then `y = (y₂ / x₂) • x`. -/
theorem apply_hadamard_of_cross_eq {p x y : ℝ × ℝ} (hp : p ∈ quadrant) (hx : x ∈ orthant)
    (hy : y ∈ quadrant) (hc : x.1 * y.2 = x.2 * y.1) :
    h (hadamard p y) = y.2 / x.2 * h (hadamard p x) := by
  have hpy : hadamard p y = (y.2 / x.2) • hadamard p x := by
    ext <;> simp <;> field_simp [(mem_orthant.mp hx).2.ne']; linear_combination -p.1 * hc
  rcases (div_nonneg (mem_quadrant.mp hy).2 (mem_orthant.mp hx).2.le).eq_or_lt with hc0 | hc0
  · rw [hpy, ← hc0, zero_smul, hh.map_zero, zero_mul]
  · rw [hpy, hh.homogeneous _ hc0 _ (hadamard_mem_quadrant hp (orthant_subset_quadrant hx))]

/-- General position in terms of good prices and separation by rays of pairs with a common
index: a triple point `x` of the curves `r, s, t` is a point of the pairs `(r, s)` and `(r, t)`
on one ray; conversely two points of these pairs on one ray lie on the curve `r`, hence
coincide by homogeneity (`apply_hadamard_of_cross_eq`) and give a triple point. -/
theorem generalPosition_iff {T : ℕ} {P : Fin T → ℝ × ℝ} :
    GeneralPosition h P ↔ (∀ t, P t ∈ orthant) ∧
      (∀ s t, s ≠ t → IsGoodPrice h (hadamard (hinv (P s)) (P t))) ∧
      ∀ r s t, r ≠ s → s ≠ t → r ≠ t → RaySep h P r s t := by
  constructor
  · intro GP
    refine ⟨GP.mem_orthant, fun s t hst => (pairGood_iff (GP.mem_orthant s)).mp
      ⟨GP.finite s t hst, GP.transversal s t hst⟩, fun r s t hrs hst hrt x hx y hy hc => ?_⟩
    -- `y = (y₂ / x₂) • x` on the curve of `p_r` forces `y = x`, a triple point
    have hxo := (GP.transversal r s hrs x hx).1
    have hy2 := hh.apply_hadamard_of_cross_eq (orthant_subset_quadrant (GP.mem_orthant r)) hxo
      hy.1 hc
    rw [hx.2.1, hy.2.1, mul_one, eq_comm, div_eq_one_iff_eq (mem_orthant.mp hxo).2.ne'] at hy2
    have hyx : y = x :=
      Prod.ext (mul_left_cancel₀ (mem_orthant.mp hxo).2.ne' (by rw [← hc, hy2]; ring)) hy2
    exact GP.no_triple r s t hrs hst hrt x hx (hyx ▸ hy.2.2)
  · rintro ⟨hO, hGood, hRS⟩
    have hPG := fun s t hst => (pairGood_iff (hO s)).mpr (hGood s t hst)
    exact ⟨hO, fun s t hst => (hPG s t hst).1, fun s t hst => (hPG s t hst).2,
      fun r s t hrs hst hrt x hx heq =>
        hRS r s t hrs hst hrt x hx x ⟨hx.1, hx.2.1, heq⟩ (mul_comm _ _)⟩

/-- **Separation by rays is open**: intersection points stay bounded for nearby prices and their
limits are intersection points, so a sequence of bad families has a bad limit. -/
theorem eventually_raySep {T : ℕ} {P₀ : Fin T → ℝ × ℝ} (hP₀ : ∀ t, P₀ t ∈ orthant)
    {r s t : Fin T} (H : RaySep h P₀ r s t) : ∀ᶠ P in 𝓝 P₀, RaySep h P r s t := by
  by_contra hcontra
  -- near `P₀` the coordinates of `p_u` stay above half of their values at `P₀`
  have hnear : ∀ u, ∀ᶠ P in 𝓝 P₀, (P₀ u).1 / 2 ≤ (P u).1 ∧ (P₀ u).2 / 2 ≤ (P u).2 := fun u =>
    (((continuous_apply u).fst.tendsto P₀).eventually_const_le (half_lt_self (hP₀ u).1)).and
      (((continuous_apply u).snd.tendsto P₀).eventually_const_le (half_lt_self (hP₀ u).2))
  -- a sequence of bad families `Q n → P₀` with bad points `x n`, `y n`
  obtain ⟨Q, hQ, hQbad⟩ := exists_seq_forall_of_frequently
    ((not_eventually.mp hcontra).and_eventually ((eventually_mem_orthant hP₀).and
      (hnear r)))
  choose x hx y hy hxy using fun n => by
    have := (hQbad n).1; simp only [RaySep, not_forall, not_not, exists_prop] at this; exact this
  -- the bad points lie in a compact box (`linear_le`): pass to a convergent subsequence
  have hbox : ∀ {a b : ℝ} {p q z : ℝ × ℝ}, 0 < a → 0 < b → a ≤ p.1 ∧ b ≤ p.2 →
      z ∈ pairIntersections h p q →
        z ∈ Icc 0 (1 / (a * h (1, 0))) ×ˢ Icc 0 (1 / (b * h (0, 1))) := by
    rintro a b p q z ha hb hp ⟨hz, hz1, -⟩
    obtain ⟨h1, h2⟩ := mem_quadrant.mp hz
    have hl := hh.linear_le (hadamard_mem_quadrant (p := p) ⟨ha.le.trans hp.1, hb.le.trans hp.2⟩ hz)
    rw [hz1, hadamard_fst, hadamard_snd] at hl
    have := hh.pos_fst; have := hh.pos_snd
    refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩ <;> rw [le_div_iff₀ (by positivity)] <;>
      nlinarith [mul_nonneg (sub_nonneg.2 hp.1) h1, mul_nonneg (sub_nonneg.2 hp.2) h2,
        mul_nonneg (ha.le.trans hp.1) h1, mul_nonneg (hb.le.trans hp.2) h2]
  have hK := fun n => Set.mk_mem_prod
    (hbox (half_pos (hP₀ r).1) (half_pos (hP₀ r).2) (hQbad n).2.2 (hx n))
    (hbox (half_pos (hP₀ r).1) (half_pos (hP₀ r).2) (hQbad n).2.2 (hy n))
  obtain ⟨⟨x₀, y₀⟩, -, φ, hφ, hlim⟩ :=
    ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)).tendsto_subseq hK
  -- the intersection points and the cross equation pass to the limit
  have hq : IsClosed quadrant := isClosed_Ici.prod isClosed_Ici
  have hcl : IsClosed (quadrant ×ˢ quadrant ∩ {z : (ℝ × ℝ) × (ℝ × ℝ) | h (hadamard z.1 z.2) = 1}) :=
    (hh.continuousOn.comp (by unfold hadamard; fun_prop) fun z hz => hadamard_mem_quadrant hz.1
      hz.2).preimage_isClosed_of_isClosed (hq.prod hq) isClosed_singleton
  have hpair : ∀ u v z z₀, Tendsto z atTop (𝓝 z₀) →
      (∀ n, z n ∈ pairIntersections h (Q (φ n) u) (Q (φ n) v)) →
      z₀ ∈ pairIntersections h (P₀ u) (P₀ v) := fun u v z z₀ hz hzn => by
    have hcurve := fun w (hw : ∀ n, h (hadamard (Q (φ n) w) (z n)) = 1) => hcl.mem_of_tendsto
      ((((continuous_apply w).tendsto P₀).comp (hQ.comp hφ.tendsto_atTop)).prodMk_nhds hz)
      (.of_forall fun n => ⟨⟨orthant_subset_quadrant ((hQbad (φ n)).2.1 w), (hzn n).1⟩, hw n⟩)
    have hu := hcurve u fun n => (hzn n).2.1
    exact ⟨hu.1.2, hu.2, (hcurve v fun n => (hzn n).2.2).2⟩
  have hc : (x₀, y₀) ∈ {z : (ℝ × ℝ) × (ℝ × ℝ) | z.1.1 * z.2.2 = z.1.2 * z.2.1} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).mem_of_tendsto hlim (.of_forall fun n => hxy (φ n))
  exact H x₀ (hpair r s _ _ ((continuous_fst.tendsto _).comp hlim) fun n => hx (φ n))
    y₀ (hpair r t _ _ ((continuous_snd.tendsto _).comp hlim) fun n => hy (φ n)) hc

/-- **Separation by rays is dense.** Scale `p_t` by `λ ≠ 1` near `1`: each of the finitely many
points of `(r, s)` is on a ray with a point of `(r, t)` for one `λ`. -/
theorem exists_raySep_near {T : ℕ} {W : Set (Fin T → ℝ × ℝ)} (hW : IsOpen W)
    {P₀ : Fin T → ℝ × ℝ} (hP₀ : P₀ ∈ W) (hO : ∀ t, P₀ t ∈ orthant) {r s t : Fin T}
    (hst : s ≠ t) (hrt : r ≠ t) (hG : IsGoodPrice h (hadamard (hinv (P₀ r)) (P₀ s))) :
    ∃ P ∈ W, RaySep h P r s t := by
  obtain ⟨hFfin, htrF⟩ := (pairGood_iff (hO r)).mpr hG
  -- the bad scalings `λ = h (p_r ∘ x) / h (p_t ∘ x)`, `x` an intersection point of `(r, s)`
  set B : Set ℝ := (fun x => h (hadamard (P₀ r) x) / h (hadamard (P₀ t) x)) ''
    pairIntersections h (P₀ r) (P₀ s)
  -- scale `p_t` by some `λ ≠ 1` near `1` outside `B`
  have hev : ∀ᶠ lam in 𝓝 (1 : ℝ),
      Function.update P₀ t (lam • P₀ t) ∈ W ∧ 0 < lam ∧ lam ∉ B \ {1} :=
    ((continuous_const.update t (continuous_id.smul continuous_const)).continuousAt.eventually_mem
      (by simpa using hW.mem_nhds hP₀)).and ((lt_mem_nhds one_pos).and
        ((hFfin.image _).diff.isClosed.isOpen_compl.mem_nhds fun h1 => h1.2 rfl))
  obtain ⟨lam, ⟨hlW, hl0, hlB⟩, hl1⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (s := {1}ᶜ))).exists
  refine ⟨_, hlW, fun x hx y hy hc => ?_⟩
  simp only [Function.update_of_ne hrt, Function.update_of_ne hst, Function.update_self] at hx hy
  -- along the ray of `x`: `1 = c a = c λ b`, `c = y₂ / x₂`, hence `λ = a / b ∈ B`
  have hA := hh.apply_hadamard_of_cross_eq (orthant_subset_quadrant (hO r)) (htrF x hx).1 hy.1 hc
  have hB := hh.apply_hadamard_of_cross_eq
    (quadrant_smul hl0.le (orthant_subset_quadrant (hO t))) (htrF x hx).1 hy.1 hc
  rw [hy.2.1] at hA
  rw [hy.2.2, show hadamard (lam • P₀ t) x = lam • hadamard (P₀ t) x by ext <;> simp [mul_assoc],
    hh.homogeneous lam hl0 _ (hadamard_mem_quadrant (orthant_subset_quadrant (hO t)) hx.1)] at hB
  have hc0 : y.2 / x.2 ≠ 0 := fun h0 => by simp [h0] at hA
  have hb : h (hadamard (P₀ t) x) ≠ 0 := fun h0 => by simp [h0] at hB
  exact hlB ⟨⟨x, hx, (div_eq_iff hb).mpr (mul_left_cancel₀ hc0 (hA.symm.trans hB))⟩, hl1⟩

end IsPosNeoclassical

/-! ### Main results -/

/-- An abstract density argument: if each condition `C i` is open near the points of `A ∩ C i`
and every open set meeting `A` contains a point of `A ∩ C i`, then every open set meeting `A`
contains a point of `A` satisfying all the finitely many conditions. -/
theorem exists_mem_inter_iInter {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    {A : Set X} {C : ι → Set X} (hC : ∀ i, ∀ x ∈ A ∩ C i, ∀ᶠ y in 𝓝 x, y ∈ C i)
    (hD : ∀ i, ∀ W : Set X, IsOpen W → (W ∩ A).Nonempty → (W ∩ A ∩ C i).Nonempty)
    {W : Set X} (hW : IsOpen W) (hne : (W ∩ A).Nonempty) : (W ∩ A ∩ ⋂ i, C i).Nonempty := by
  classical
  have := Fintype.ofFinite ι
  suffices key : ∀ F : Finset ι, ∀ W : Set X, IsOpen W → (W ∩ A).Nonempty →
      (W ∩ A ∩ ⋂ i ∈ F, C i).Nonempty by simpa using key Finset.univ W hW hne
  intro F
  induction F using Finset.induction_on with
  | empty => intro W _ hne; simpa using hne
  | insert i F _ ih =>
    -- a point of `W ∩ A ∩ C i`, then the induction hypothesis in `W ∩ interior (C i)`
    intro W hW hne
    obtain ⟨x, ⟨hxW, hxA⟩, hxC⟩ := hD i W hW hne
    obtain ⟨y, ⟨⟨hyW, hyi⟩, hyA⟩, hyF⟩ := ih (W ∩ interior (C i)) (hW.inter isOpen_interior)
      ⟨x, ⟨hxW, mem_interior_iff_mem_nhds.mpr (hC i x ⟨hxA, hxC⟩)⟩, hxA⟩
    refine ⟨y, ⟨hyW, hyA⟩, ?_⟩
    rw [Finset.set_biInter_insert]
    exact ⟨interior_subset hyi, hyF⟩

namespace IsPosNeoclassical

variable {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
include hh

/-- A good pair stays good for nearby prices: `Q ↦ q_s⁻¹ ∘ q_t` is continuous. -/
theorem eventually_pairGood {T : ℕ} {P₀ : Fin T → ℝ × ℝ} (hP₀ : ∀ t, P₀ t ∈ orthant)
    {s t : Fin T} (H : IsGoodPrice h (hadamard (hinv (P₀ s)) (P₀ t))) :
    ∀ᶠ P in 𝓝 P₀, IsGoodPrice h (hadamard (hinv (P s)) (P t)) := by
  have hs : ContinuousAt (fun Q : Fin T → ℝ × ℝ => hinv (Q s)) P₀ :=
    (continuousOn_hinv.continuousAt (isOpen_orthant.mem_nhds (hP₀ s))).tendsto.comp
      (continuous_apply s).continuousAt
  have ht : ContinuousAt (fun Q : Fin T → ℝ × ℝ => Q t) P₀ := (continuous_apply t).continuousAt
  exact ((hs.fst.mul ht.fst).prodMk (hs.snd.mul ht.snd)).eventually
    (hh.eventually_isGoodPrice (hadamard_mem_orthant (hinv_mem_orthant (hP₀ s)) (hP₀ t)) H)

/-- Families in `(ℝ²₊₊)^T` with all pairs good form an open set. -/
theorem eventually_pairsGood {T : ℕ} {P₀ : Fin T → ℝ × ℝ} (hP₀ : ∀ t, P₀ t ∈ orthant)
    (H : ∀ s t, s ≠ t → IsGoodPrice h (hadamard (hinv (P₀ s)) (P₀ t))) :
    ∀ᶠ P in 𝓝 P₀, (∀ t, P t ∈ orthant) ∧
      ∀ s t, s ≠ t → IsGoodPrice h (hadamard (hinv (P s)) (P t)) :=
  (eventually_mem_orthant hP₀).and <| by
    simpa only [eventually_all] using fun s t hst => hh.eventually_pairGood hP₀ (H s t hst)

/-- Moving `p_t` to `p_s ∘ q` with `q` given by lemma 2.9 makes the pair `(s, t)` good. -/
theorem exists_pairGood_near {T : ℕ} {W : Set (Fin T → ℝ × ℝ)} (hW : IsOpen W)
    {P₀ : Fin T → ℝ × ℝ} (hP₀ : P₀ ∈ W) (hO : ∀ t, P₀ t ∈ orthant) {s t : Fin T} (hst : s ≠ t) :
    ∃ P ∈ W, (∀ r, P r ∈ orthant) ∧ IsGoodPrice h (hadamard (hinv (P s)) (P t)) := by
  classical
  -- `F q` replaces `p_t` by `p_s ∘ q`, and `F (p_s⁻¹ ∘ p_t) = P₀`
  set F : ℝ × ℝ → Fin T → ℝ × ℝ := fun q => Function.update P₀ t (hadamard (P₀ s) q) with hF
  have hFc : Continuous F := continuous_const.update t
    ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hq₀ := hadamard_mem_orthant (hinv_mem_orthant (hO s)) (hO t)
  have hFq₀ : F (hadamard (hinv (P₀ s)) (P₀ t)) ∈ W := by
    simpa only [hF, hadamard_hadamard_hinv (hO s), Function.update_eq_self] using hP₀
  -- lemma 2.9 gives a good price `q` with `F q ∈ W`
  obtain ⟨V, -, ⟨q, hqV⟩, hVU, hVgood⟩ := hh.exists_open_finite_levelIntersections
    ((hW.preimage hFc).inter isOpen_orthant) ⟨_, ⟨hFq₀, hq₀⟩, hq₀⟩
  obtain ⟨⟨hqW, hqo⟩, -⟩ := hVU hqV
  refine ⟨F q, hqW, fun r => ?_, ?_⟩
  · rcases eq_or_ne r t with rfl | hrt
    · simpa only [hF, Function.update_self] using hadamard_mem_orthant (hO s) hqo
    · simpa only [hF, Function.update_of_ne hrt] using hO r
  · simpa only [hF, Function.update_of_ne hst, Function.update_self,
      hadamard_hinv_hadamard (hO s)] using hVgood q hqV

/-- **Stability of general position** (proposition 2.10 of the notes). If `(h, P)` is in general
position, then so is `(h, Q)` for every `Q` in some open neighbourhood of `P`.

Proof: by `generalPosition_iff` general position is a finite conjunction of conditions on
`P`, each of them open: good prices form an open set (`eventually_isGoodPrice`) and
`Q ↦ q_s⁻¹ ∘ q_t` is continuous; separation by rays is open (`eventually_raySep`). -/
theorem generalPosition_stable {T : ℕ} {P : Fin T → ℝ × ℝ} (hP : GeneralPosition h P) :
    ∃ V : Set (Fin T → ℝ × ℝ), IsOpen V ∧ P ∈ V ∧ ∀ Q ∈ V, GeneralPosition h Q := by
  obtain ⟨hO, hG, hR⟩ := hh.generalPosition_iff.mp hP
  have hR' : ∀ᶠ Q in 𝓝 P, ∀ r s t, r ≠ s → s ≠ t → r ≠ t → RaySep h Q r s t := by
    simpa only [eventually_all] using
      fun r s t hrs hst hrt => hh.eventually_raySep hO (hR r s t hrs hst hrt)
  obtain ⟨V, hVsub, hVo, hPV⟩ := eventually_nhds_iff.mp ((hh.eventually_pairsGood hO hG).and hR')
  exact ⟨V, hVo, hPV, fun Q hQ =>
    hh.generalPosition_iff.mpr ⟨(hVsub Q hQ).1.1, (hVsub Q hQ).1.2, (hVsub Q hQ).2⟩⟩

/-- **Density of general position** (proposition 2.11 of the notes). Every nonempty open set
`U ⊆ (ℝ²₊₊)^T` of prices contains `P` with `(h, P)` in general position.

Proof: each condition of `generalPosition_iff` is open and dense relative to a set, so their
finite intersection meets `U` (`exists_mem_inter_iInter`). First the pairs, relative to
`(ℝ²₊₊)^T`: moving `p_t` to `p_s ∘ q` with `q` given by lemma 2.9 makes the pair `(s, t)` good
(`exists_pairGood_near`). Then the rays, relative to the families with all pairs good: scaling
one curve of a triple moves its intersection points along their rays (`exists_raySep_near`). -/
theorem exists_generalPosition {T : ℕ} {U : Set (Fin T → ℝ × ℝ)} (hU : IsOpen U)
    (hUo : U ⊆ {P | ∀ t, P t ∈ orthant}) (hne : U.Nonempty) :
    ∃ P ∈ U, GeneralPosition h P := by
  obtain ⟨P₀, hP₀U⟩ := hne
  -- step 1: all pairs good, relative to `(ℝ²₊₊)^T`
  obtain ⟨P₁, ⟨hP₁U, hP₁O⟩, hP₁G⟩ := exists_mem_inter_iInter
    (A := {P : Fin T → ℝ × ℝ | ∀ t, P t ∈ orthant})
    (C := fun i : {i : Fin T × Fin T // i.1 ≠ i.2} =>
      {P | IsGoodPrice h (hadamard (hinv (P i.1.1)) (P i.1.2))})
    (fun _ _ hP => hh.eventually_pairGood hP.1 hP.2)
    (fun i W hW ⟨P, hPW, hPO⟩ => by
      obtain ⟨Q, hQW, hQO, hQG⟩ := hh.exists_pairGood_near hW hPW hPO i.2
      exact ⟨Q, ⟨hQW, hQO⟩, hQG⟩) hU ⟨P₀, hP₀U, hUo hP₀U⟩
  -- step 2: separation by rays, relative to the open set `A` of families with all pairs good
  set A : Set (Fin T → ℝ × ℝ) :=
    {P | (∀ t, P t ∈ orthant) ∧ ∀ s t, s ≠ t → IsGoodPrice h (hadamard (hinv (P s)) (P t))}
  have hA : IsOpen A := isOpen_iff_mem_nhds.mpr fun P hP => hh.eventually_pairsGood hP.1 hP.2
  obtain ⟨P, ⟨hPU, hPA⟩, hPR⟩ := exists_mem_inter_iInter (A := A)
    (C := fun i : {i : Fin T × Fin T × Fin T // i.1 ≠ i.2.1 ∧ i.2.1 ≠ i.2.2 ∧ i.1 ≠ i.2.2} =>
      {P | RaySep h P i.1.1 i.1.2.1 i.1.2.2})
    (fun _ _ hP => hh.eventually_raySep hP.1.1 hP.2)
    (fun i W hW ⟨P, hPW, hPA⟩ => by
      obtain ⟨Q, ⟨hQW, hQA⟩, hQR⟩ :=
        hh.exists_raySep_near (hW.inter hA) ⟨hPW, hPA⟩ hPA.1 i.2.2.1 i.2.2.2 (hPA.2 _ _ i.2.1)
      exact ⟨Q, ⟨hQW, hQA⟩, hQR⟩)
    hU ⟨P₁, hP₁U, hP₁O, fun s t hst => mem_iInter.mp hP₁G ⟨(s, t), hst⟩⟩
  exact ⟨P, hPU, hh.generalPosition_iff.mpr
    ⟨hPA.1, hPA.2, fun r s t hrs hst hrt => mem_iInter.mp hPR ⟨(r, s, t), hrs, hst, hrt⟩⟩⟩

end IsPosNeoclassical

end NeoTiling
