import Mathlib

/-!
# Neoclassical functions of two variables

Informal definition (notes, Definition "Neoclassical functions", specialised to `n = 2`):
a function `f : ℝ₊² → ℝ₊` is *neoclassical* if it is continuous, concave and
homogeneous of degree 1.

We model `ℝ₊²` as the closed nonnegative quadrant `quadrant ⊆ ℝ × ℝ` and a function
`ℝ₊² → ℝ₊` as a function `f : ℝ × ℝ → ℝ` together with the requirement that `f` is
nonnegative on the quadrant. Only the values of `f` on the quadrant matter.
-/

open Real

namespace NeoTiling

/-- The closed nonnegative quadrant `ℝ₊² = {(x, y) | 0 ≤ x, 0 ≤ y}`. -/
def quadrant : Set (ℝ × ℝ) := Set.Ici 0 ×ˢ Set.Ici 0

/-- `f : ℝ × ℝ → ℝ` is *neoclassical* if, viewed as a function `ℝ₊² → ℝ₊`, it is
continuous, concave and (positively) homogeneous of degree 1. -/
structure IsNeoclassical (f : ℝ × ℝ → ℝ) : Prop where
  /-- `f` takes values in `ℝ₊` on the quadrant. -/
  nonneg : ∀ p ∈ quadrant, 0 ≤ f p
  /-- `f` is continuous on the closed quadrant (boundary included). -/
  continuousOn : ContinuousOn f quadrant
  /-- `f` is concave on the quadrant. -/
  concaveOn : ConcaveOn ℝ quadrant f
  /-- `f (t • p) = t * f p` for every `t > 0` and every `p` in the quadrant. -/
  homogeneous : ∀ t : ℝ, 0 < t → ∀ p ∈ quadrant, f (t • p) = t * f p

/-- The Euclidean norm `(x, y) ↦ √(x² + y²)`. -/
noncomputable def euclid (p : ℝ × ℝ) : ℝ := √(p.1 ^ 2 + p.2 ^ 2)

/-- The geometric mean `(x, y) ↦ √(x·y)`. Since `Real.sqrt` is `0` on nonpositive
arguments, this is already the extension by `0` to the boundary of the quadrant. -/
noncomputable def geomMean (p : ℝ × ℝ) : ℝ := √(p.1 * p.2)

/-- `geomMean` vanishes on the boundary of the quadrant: this is the extension by
continuity mentioned in the informal statement. -/
theorem geomMean_eq_zero_of_boundary (p : ℝ × ℝ) (h : p.1 = 0 ∨ p.2 = 0) :
    geomMean p = 0 := by
  unfold geomMean
  rcases h with h | h <;> simp [h]

/-- `√(x² + y²)` is not neoclassical: concavity fails at the midpoint of `(1, 0)` and
`(0, 1)`, where the function takes the value `√(1/2) < 1`. -/
theorem not_isNeoclassical_euclid : ¬ IsNeoclassical euclid := by
  intro h
  have hx : ((1 : ℝ), (0 : ℝ)) ∈ quadrant := by simp [quadrant]
  have hy : ((0 : ℝ), (1 : ℝ)) ∈ quadrant := by simp [quadrant]
  have key := h.concaveOn.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [euclid, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at key
  norm_num at key
  -- `key : 1 ≤ (√2)⁻¹`, which contradicts `1 < √2`.
  have h2 : (1 : ℝ) < √2 := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
    simpa using this
  have hlt : (√2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
  linarith

/-- Two-variable AM–GM in the form needed for the concavity of `geomMean`:
`2 √(x₁x₂) √(y₁y₂) ≤ x₁y₂ + y₁x₂`. -/
lemma two_mul_sqrt_mul_sqrt_le {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    2 * (√(x₁ * x₂) * √(y₁ * y₂)) ≤ x₁ * y₂ + y₁ * x₂ := by
  have h1 : √(x₁ * x₂) * √(y₁ * y₂) = √(x₁ * y₂) * √(y₁ * x₂) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  calc 2 * (√(x₁ * x₂) * √(y₁ * y₂)) = 2 * √(x₁ * y₂) * √(y₁ * x₂) := by rw [h1]; ring
    _ ≤ √(x₁ * y₂) ^ 2 + √(y₁ * x₂) ^ 2 := two_mul_le_add_sq _ _
    _ = x₁ * y₂ + y₁ * x₂ := by
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

/-- The concavity inequality for the geometric mean, for arbitrary nonnegative weights
(the constraint `a + b = 1` is not needed). -/
lemma geomMean_concave_aux {x₁ x₂ y₁ y₂ a b : ℝ} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * √(x₁ * x₂) + b * √(y₁ * y₂) ≤ √((a * x₁ + b * y₁) * (a * x₂ + b * y₂)) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have hs := Real.sq_sqrt (mul_nonneg hx₁ hx₂)
  have ht := Real.sq_sqrt (mul_nonneg hy₁ hy₂)
  have key := two_mul_sqrt_mul_sqrt_le hx₁ hx₂ hy₁ hy₂
  have e : (a * √(x₁ * x₂) + b * √(y₁ * y₂)) ^ 2
      = a ^ 2 * √(x₁ * x₂) ^ 2 + (a * b) * (2 * (√(x₁ * x₂) * √(y₁ * y₂)))
        + b ^ 2 * √(y₁ * y₂) ^ 2 := by ring
  rw [e, hs, ht]
  nlinarith [mul_le_mul_of_nonneg_left key (mul_nonneg ha hb)]

/-- `√(x·y)`, extended by `0` to the boundary, is neoclassical. -/
theorem isNeoclassical_geomMean : IsNeoclassical geomMean := by
  constructor
  · intro p _
    exact Real.sqrt_nonneg _
  · unfold geomMean
    fun_prop
  · refine ⟨(convex_Ici 0).prod (convex_Ici 0), ?_⟩
    rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩ a b ha hb _
    simp only [Set.mem_Ici] at hx₁ hx₂ hy₁ hy₂
    simp only [geomMean, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk]
    exact geomMean_concave_aux hx₁ hx₂ hy₁ hy₂ ha hb
  · intro t ht p _
    simp only [geomMean, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [show t * p.1 * (t * p.2) = t ^ 2 * (p.1 * p.2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]

/-!
## A twisted geometric mean

`twist (x, y) = √(x·y) · exp(¼ sin ln(x / y))`. This is the function `h` from the notes.
It is neoclassical, but unlike `geomMean` its level curves are not smooth deformations of
hyperbolas: the exponential factor oscillates along rays.

The proof of concavity does not go through the Hessian. Instead we use homogeneity to
reduce to the one-variable function `twistPhi u = twist (u, 1)` and show that
`twistPhi` is concave on `[0, ∞)` because its derivative is antitone.
-/

/-- `(x, y) ↦ √(x·y) · exp(¼ sin ln(x / y))`. Since `Real.sqrt`, `Real.log` are total and
`√(x·y) = 0` on the boundary of the quadrant, this is already extended by `0` there. -/
noncomputable def twist (p : ℝ × ℝ) : ℝ :=
  √(p.1 * p.2) * exp (1 / 4 * sin (log (p.1 / p.2)))

/-- `u ↦ √u · exp(¼ sin ln u)`, the restriction of `twist` to the line `y = 1`. -/
noncomputable def twistPhi (u : ℝ) : ℝ := √u * exp (1 / 4 * sin (log u))

/-- `twistPhi' u = twistPsi (log u)` for `u > 0`. -/
noncomputable def twistPsi (v : ℝ) : ℝ :=
  exp (-(v / 2) + 1 / 4 * sin v) * (1 / 2 + 1 / 4 * cos v)

theorem twist_nonneg (p : ℝ × ℝ) : 0 ≤ twist p := by
  unfold twist
  positivity

/-- The oscillating factor is bounded by `exp (1/4)`. -/
theorem twist_le (p : ℝ × ℝ) : twist p ≤ exp (1 / 4) * geomMean p := by
  unfold twist geomMean
  rw [mul_comm (exp (1 / 4))]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  have := Real.sin_le_one (log (p.1 / p.2))
  linarith

theorem twist_eq_zero_of_boundary (p : ℝ × ℝ) (h : p.1 = 0 ∨ p.2 = 0) : twist p = 0 := by
  unfold twist
  rcases h with h | h <;> simp [h]

theorem twistPhi_eq (u : ℝ) : twistPhi u = twist (u, 1) := by
  simp [twistPhi, twist]

/-- Homogeneity written as a reduction to one variable, valid on the whole closed quadrant
(for `p.2 = 0` both sides vanish). -/
theorem twist_eq_mul_twistPhi {p : ℝ × ℝ} (h2 : 0 ≤ p.2) :
    twist p = p.2 * twistPhi (p.1 / p.2) := by
  unfold twist twistPhi
  rcases h2.eq_or_lt with h2 | h2
  · simp [← h2]
  · have : √(p.1 * p.2) = p.2 * √(p.1 / p.2) := by
      rw [← Real.sqrt_sq h2.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h2.le]
      congr 1
      field_simp
    rw [this]
    ring

/-- Derivative of `twistPhi` on `(0, ∞)`. -/
theorem hasDerivAt_twistPhi {u : ℝ} (hu : 0 < u) :
    HasDerivAt twistPhi (twistPsi (log u)) u := by
  have hsqrt := Real.hasDerivAt_sqrt hu.ne'
  have hexp := (((Real.hasDerivAt_log hu.ne').sin).const_mul (1 / 4)).exp
  have h := hsqrt.mul hexp
  refine h.congr_deriv ?_
  -- Write `√u = exp (log u / 2)` and clear denominators.
  have hs : √u = exp (log u / 2) :=
    (Real.sqrt_eq_iff_mul_self_eq hu.le (exp_pos _).le).mpr
      (by rw [← Real.exp_add, add_halves, Real.exp_log hu])
  have hss : exp (log u / 2) * exp (log u / 2) = u := by
    rw [← Real.exp_add, add_halves, Real.exp_log hu]
  unfold twistPsi
  rw [show -(log u / 2) + 1 / 4 * sin (log u) = 1 / 4 * sin (log u) - log u / 2 by ring,
    Real.exp_sub, hs]
  field_simp
  linear_combination (2 * cos (log u)) * hss

theorem deriv_twistPhi {u : ℝ} (hu : 0 < u) : deriv twistPhi u = twistPsi (log u) :=
  (hasDerivAt_twistPhi hu).deriv

/-- `twistPsi` is antitone: its derivative is `-exp(…) (1 + sin v)(3 + sin v) / 16 ≤ 0`.
This is the one-variable shadow of the Hessian computation in the notes. -/
theorem twistPsi_antitone : Antitone twistPsi := by
  apply antitone_of_deriv_nonpos
  · unfold twistPsi
    fun_prop
  · intro v
    have hA : HasDerivAt (fun v : ℝ => -(v / 2) + 1 / 4 * sin v) (-(1 / 2) + 1 / 4 * cos v) v := by
      have := ((hasDerivAt_id v).div_const 2).neg.add ((Real.hasDerivAt_sin v).const_mul (1 / 4))
      simpa using this
    have hB : HasDerivAt (fun v : ℝ => 1 / 2 + 1 / 4 * cos v) (1 / 4 * -sin v) v :=
      ((Real.hasDerivAt_cos v).const_mul (1 / 4)).const_add (1 / 2)
    have h : HasDerivAt twistPsi
        (exp (-(v / 2) + 1 / 4 * sin v) * (-(1 / 2) + 1 / 4 * cos v) * (1 / 2 + 1 / 4 * cos v)
          + exp (-(v / 2) + 1 / 4 * sin v) * (1 / 4 * -sin v)) v := hA.exp.mul hB
    rw [h.deriv]
    set A := -(v / 2) + 1 / 4 * sin v
    have hc : cos v ^ 2 = 1 - sin v ^ 2 := Real.cos_sq' v
    have key : exp A * (-(1 / 2) + 1 / 4 * cos v) * (1 / 2 + 1 / 4 * cos v)
        + exp A * (1 / 4 * -sin v) = -(exp A * ((sin v + 1) * (sin v + 3))) / 16 := by
      linear_combination (exp A / 16) * hc
    rw [key]
    have h1 : 0 ≤ sin v + 1 := by linarith [Real.neg_one_le_sin v]
    have h3 : 0 ≤ sin v + 3 := by linarith [Real.neg_one_le_sin v]
    have : 0 ≤ exp A * ((sin v + 1) * (sin v + 3)) :=
      mul_nonneg (exp_pos _).le (mul_nonneg h1 h3)
    linarith

/-- Continuity on the closed quadrant. In the interior `twist` is a composition of
continuous functions; on the boundary it is squeezed between `0` and `exp (1/4) * geomMean`. -/
theorem twist_continuousOn : ContinuousOn twist quadrant := by
  intro p hp
  by_cases h : p.1 = 0 ∨ p.2 = 0
  · -- boundary point: squeeze
    rw [ContinuousWithinAt, twist_eq_zero_of_boundary p h]
    have hc : Continuous (fun q : ℝ × ℝ => exp (1 / 4) * geomMean q) := by
      unfold geomMean
      fun_prop
    have hup : Filter.Tendsto (fun q : ℝ × ℝ => exp (1 / 4) * geomMean q)
        (nhdsWithin p quadrant) (nhds 0) := by
      have := hc.continuousWithinAt (s := quadrant) (x := p)
      rwa [ContinuousWithinAt, geomMean_eq_zero_of_boundary p h, mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Filter.Eventually.of_forall twist_nonneg) (Filter.Eventually.of_forall twist_le)
  · -- interior point
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    have hne : p.1 / p.2 ≠ 0 := div_ne_zero h1 h2
    apply ContinuousAt.continuousWithinAt
    unfold twist
    have hdiv : ContinuousAt (fun q : ℝ × ℝ => q.1 / q.2) p := by
      fun_prop (disch := assumption)
    have hlog : ContinuousAt (fun q : ℝ × ℝ => log (q.1 / q.2)) p := hdiv.log hne
    have hsin : ContinuousAt (fun q : ℝ × ℝ => sin (log (q.1 / q.2))) p :=
      ContinuousAt.comp (f := fun q : ℝ × ℝ => log (q.1 / q.2))
        Real.continuous_sin.continuousAt hlog
    have hsqrt : ContinuousAt (fun q : ℝ × ℝ => √(q.1 * q.2)) p := by fun_prop
    exact hsqrt.mul (hsin.const_mul (1 / 4)).rexp

theorem twistPhi_continuousOn : ContinuousOn twistPhi (Set.Ici 0) := by
  have : twistPhi = fun u => twist (u, 1) := funext twistPhi_eq
  rw [this]
  refine twist_continuousOn.comp (by fun_prop) ?_
  intro u hu
  exact ⟨hu, Set.mem_Ici.mpr zero_le_one⟩

theorem twistPhi_differentiableOn : DifferentiableOn ℝ twistPhi (interior (Set.Ici 0)) := by
  rw [interior_Ici]
  intro u hu
  exact (hasDerivAt_twistPhi hu).differentiableAt.differentiableWithinAt

theorem twistPhi_concaveOn : ConcaveOn ℝ (Set.Ici 0) twistPhi := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) twistPhi_continuousOn
    twistPhi_differentiableOn ?_
  rw [interior_Ici]
  intro u hu v hv huv
  rw [deriv_twistPhi hu, deriv_twistPhi hv]
  exact twistPsi_antitone (Real.log_le_log hu huv)

theorem twistPhi_monotoneOn : MonotoneOn twistPhi (Set.Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) twistPhi_continuousOn
    twistPhi_differentiableOn ?_
  rw [interior_Ici]
  intro u hu
  rw [deriv_twistPhi hu]
  unfold twistPsi
  have := Real.neg_one_le_cos (log u)
  exact mul_nonneg (exp_pos _).le (by linarith)

/-- `y * (x / y) ≤ x` for `x ≥ 0` (with equality unless `y = 0`). -/
theorem mul_div_self_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : y * (x / y) ≤ x := by
  by_cases hy : y = 0
  · simp [hy, hx]
  · rw [mul_div_cancel₀ x hy]

/-- Concavity of `twist` on the closed quadrant, by the perspective argument. -/
theorem twist_concaveOn : ConcaveOn ℝ quadrant twist := by
  refine ⟨(convex_Ici 0).prod (convex_Ici 0), ?_⟩
  rintro ⟨p₁, p₂⟩ ⟨hp₁, hp₂⟩ ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩ a b ha hb hab
  simp only [Set.mem_Ici] at hp₁ hp₂ hq₁ hq₂
  simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk]
  rw [twist_eq_mul_twistPhi hp₂, twist_eq_mul_twistPhi hq₂,
    twist_eq_mul_twistPhi (by positivity)]
  simp only
  set y := a * p₂ + b * q₂ with hy
  rcases (by positivity : 0 ≤ y).eq_or_lt with hy0 | hy0
  · -- degenerate case: both `a * p₂` and `b * q₂` vanish
    have h1 : a * p₂ = 0 := by nlinarith [mul_nonneg ha hp₂, mul_nonneg hb hq₂]
    have h2 : b * q₂ = 0 := by nlinarith [mul_nonneg ha hp₂, mul_nonneg hb hq₂]
    rw [show a * (p₂ * twistPhi (p₁ / p₂)) + b * (q₂ * twistPhi (q₁ / q₂))
        = (a * p₂) * twistPhi (p₁ / p₂) + (b * q₂) * twistPhi (q₁ / q₂) by ring, h1, h2, ← hy0]
    simp
  · set l := a * p₂ / y with hl
    set m := b * q₂ / y with hm
    have hl0 : 0 ≤ l := by positivity
    have hm0 : 0 ≤ m := by positivity
    have hlm : l + m = 1 := by
      rw [hl, hm, ← add_div, hy, div_self hy0.ne']
    have jensen := twistPhi_concaveOn.2 (Set.mem_Ici.mpr (by positivity : 0 ≤ p₁ / p₂))
      (Set.mem_Ici.mpr (by positivity : 0 ≤ q₁ / q₂)) hl0 hm0 hlm
    simp only [smul_eq_mul] at jensen
    have hle : l * (p₁ / p₂) + m * (q₁ / q₂) ≤ (a * p₁ + b * q₁) / y := by
      rw [hl, hm, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
      apply div_le_div_of_nonneg_right _ hy0.le
      have e1 := mul_le_mul_of_nonneg_left (mul_div_self_le_of_nonneg hp₁ p₂) ha
      have e2 := mul_le_mul_of_nonneg_left (mul_div_self_le_of_nonneg hq₁ q₂) hb
      nlinarith [e1, e2]
    have mono := twistPhi_monotoneOn (Set.mem_Ici.mpr (by positivity))
      (Set.mem_Ici.mpr (by positivity)) hle
    calc a * (p₂ * twistPhi (p₁ / p₂)) + b * (q₂ * twistPhi (q₁ / q₂))
        = y * (l * twistPhi (p₁ / p₂) + m * twistPhi (q₁ / q₂)) := by
          rw [hl, hm]
          field_simp
      _ ≤ y * twistPhi (l * (p₁ / p₂) + m * (q₁ / q₂)) :=
          mul_le_mul_of_nonneg_left jensen hy0.le
      _ ≤ y * twistPhi ((a * p₁ + b * q₁) / y) := mul_le_mul_of_nonneg_left mono hy0.le

/-- `√(x·y) · exp(¼ sin ln(x / y))` is neoclassical. -/
theorem isNeoclassical_twist : IsNeoclassical twist := by
  constructor
  · intro p _
    exact twist_nonneg p
  · exact twist_continuousOn
  · exact twist_concaveOn
  · intro t ht p _
    simp only [twist, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [mul_div_mul_left _ _ ht.ne',
      show t * p.1 * (t * p.2) = t ^ 2 * (p.1 * p.2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq ht.le]
    ring

end NeoTiling
