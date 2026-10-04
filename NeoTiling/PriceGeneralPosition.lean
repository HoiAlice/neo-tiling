import NeoTiling.Solvability

/-!
# General position of prices

Notes, section "Разрешимость в общем положении": `def:prices-gp` (`PricesGeneralPosition`) and
`prop:prices-gp` (`pricesGeneralPosition_iff`): prices are in general position iff `(h, P)` is in
general position for some strictly positive neoclassical `h`.

* Necessity (`GeneralPosition.pricesGeneralPosition`): an equal coordinate gives a common axis
  point of two curves; two proportional incomparable pairs give two intersection points on a ray.
* Sufficiency (`PricesGeneralPosition.exists_generalPosition_near`): polygonal functions
  `polyMin ξ = min_j ⟨ξ_j, ·⟩`. Inscribed polygons with short edges (`exists_startLines`) have no
  line shared by two curves at a common point (`NoSharedLine`, an open condition); generic lines
  (`GenericLines`, dense) then give general position (`generalPosition_polyMin`).
-/

open Set Filter Topology

namespace NeoTiling

/-! ### Prices in general position -/

/-- Prices `p, q` are *incomparable* (crossing): `(p₁ - q₁)(p₂ - q₂) < 0`. -/
def Crossing (p q : ℝ × ℝ) : Prop := (p.1 - q.1) * (p.2 - q.2) < 0

theorem Crossing.symm {p q : ℝ × ℝ} (h : Crossing p q) : Crossing q p := by
  unfold Crossing at *; nlinarith

/-- **General position of prices** (notes, `def:prices-gp`): the prices lie in `ℝ²₊₊`, their
first coordinates are pairwise distinct, so are the second ones, and for no `μ > 1` the set
`P ∩ μ P` contains two incomparable prices. -/
structure PricesGeneralPosition {T : ℕ} (P : Fin T → ℝ × ℝ) : Prop where
  mem_orthant : ∀ t, P t ∈ orthant
  fst_injective : Function.Injective fun t => (P t).1
  snd_injective : Function.Injective fun t => (P t).2
  /-- no `μ > 1` such that `P ∩ μ P` contains two incomparable prices -/
  no_crossing_dilate : ∀ μ > (1 : ℝ), ∀ s t s' t', P s = μ • P s' → P t = μ • P t' →
    ¬ Crossing (P s) (P t)

/-- Two different incomparable pairs of prices in general position are not proportional:
`μ = 1` gives the same pair, `μ > 1` and `μ < 1` contradict condition 2. -/
theorem PricesGeneralPosition.not_dilate {T : ℕ} {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) {s t s' t' : Fin T} (hd : PairsDiffer s t s' t')
    (hc : Crossing (P s) (P t)) (hc' : Crossing (P s') (P t')) {μ : ℝ}
    (hs : P s' = μ • P s) (ht : P t' = μ • P t) : False := by
  have hμ : 0 < μ := pos_of_mul_pos_left (show 0 < μ * (P s).1 by
    simpa [hs] using (hP.mem_orthant s').1) (mem_Ioi.1 (hP.mem_orthant s).1).le
  rcases lt_trichotomy μ 1 with h | rfl | h
  · exact hP.no_crossing_dilate μ⁻¹ ((one_lt_inv₀ hμ).mpr h) s t s' t'
      ((eq_inv_smul_iff₀ hμ.ne').2 hs.symm) ((eq_inv_smul_iff₀ hμ.ne').2 ht.symm) hc
  · exact hd.2.2 (.inl ⟨hP.fst_injective (by simp [hs]), hP.fst_injective (by simp [ht])⟩)
  · exact hP.no_crossing_dilate μ h s' t' s t hs ht hc'

/-! ### Curves of two prices -/

/-- Common points of the curves of two prices with distinct coordinates lie in `ℝ²₊₊` (on an axis
`h (p ∘ x) = p₁ x₁ h (1, 0)`), and the prices cross (`levelIntersections_eq_empty_of_one_lt`). -/
theorem IsPosNeoclassical.mem_orthant_crossing {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    {p q : ℝ × ℝ} (hp : p ∈ orthant) (hq : q ∈ orthant) (h1 : p.1 ≠ q.1) (h2 : p.2 ≠ q.2)
    {x : ℝ × ℝ} (hx : x ∈ pairIntersections h p q) : x ∈ orthant ∧ Crossing p q := by
  obtain ⟨y, hy, -⟩ := (pairIntersections_eq_image hp).subset hx; obtain ⟨hxq, hgp, hgq⟩ := hx
  obtain ⟨hx1, hx2⟩ := mem_quadrant.mp hxq; obtain ⟨hp1, hp2⟩ := mem_orthant.mp hp
  obtain ⟨hq1, hq2⟩ := mem_orthant.mp hq; simp only [hadamard, hinv, one_div_mul_eq_div] at hy
  refine ⟨?_, not_le.1 fun hnc => ?_⟩; rotate_left; rcases h1.lt_or_gt with h1' | h1'
  · exact (hh.levelIntersections_eq_empty_of_one_lt ((one_lt_div hp1).2 h1')
      ((one_lt_div hp2).2 (h2.lt_of_le (by nlinarith)))).subset hy
  · exact (hh.levelIntersections_eq_empty_of_lt_one (mem_orthant.2 ⟨div_pos hq1 hp1, div_pos hq2
      hp2⟩) ((div_lt_one hp1).2 h1') ((div_lt_one hp2).2 (h2.lt_of_le' (by nlinarith)))).subset hy
  refine mem_orthant.2 ⟨hx1.lt_of_ne fun e => h2 ?_, hx2.lt_of_ne fun e => h1 ?_⟩ <;>
    simp only [hadamard, ← e, mul_zero, mul_assoc, hh.fst_axis, hh.snd_axis, mul_nonneg,
      hx1, hx2, hp1.le, hq1.le, hp2.le, hq2.le] at hgp hgq <;>
    exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hgp) (hgp.trans hgq.symm)

/-- **Incomparable prices have crossing curves.** Along the segment `v ω = (1 - ω, ω)` the values
`h (p ∘ v ω)` and `h (q ∘ v ω)` change order (intermediate value theorem), and at a point of
equality `v ω / h (p ∘ v ω)` lies on both curves. -/
theorem IsPosNeoclassical.pairIntersections_nonempty {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    {p q : ℝ × ℝ} (hp : p ∈ orthant) (hq : q ∈ orthant) (hc : Crossing p q) :
    (pairIntersections h p q).Nonempty := by
  wlog hlt : p.1 < q.1 generalizing p q with H
  · exact pairIntersections_comm h p q ▸ H hq hp hc.symm
      ((not_lt.1 hlt).lt_of_ne fun e => by simp [Crossing, e] at hc)
  obtain ⟨hp1, hp2⟩ := mem_orthant.mp hp; obtain ⟨hq1, hq2⟩ := mem_orthant.mp hq
  have hw {r : ℝ × ℝ} (hr : r ∈ orthant) {ω : ℝ} (hω : ω ∈ Icc (0 : ℝ) 1) :
      hadamard r (1 - ω, ω) ∈ quadrant :=
    hadamard_mem_quadrant (orthant_subset_quadrant hr) (mk_mem_quadrant (sub_nonneg.2 hω.2) hω.1)
  have hC {r} (hr : r ∈ orthant) : ContinuousOn (fun ω => h (hadamard r (1 - ω, ω))) (Icc 0 1) :=
    hh.continuousOn.comp (by simp only [hadamard_mk]; fun_prop) fun _ => hw hr
  obtain ⟨ω, hω, hFG⟩ := isPreconnected_Icc.intermediate_value₂ (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one) (hC hp) (hC hq)
    (by simp [hh.fst_axis hp1.le, hh.fst_axis hq1.le]; nlinarith [hh.pos_fst])
    (by simp [hh.snd_axis hp2.le, hh.snd_axis hq2.le]; rw [Crossing] at hc; nlinarith [hh.pos_snd])
  have hpos : 0 < h (hadamard p (1 - ω, ω)) := hh.pos _ (hw hp hω) fun e => by
    simp [Prod.ext_iff, hp1.ne', hp2.ne'] at e; linarith
  refine ⟨(h (hadamard p (1 - ω, ω)))⁻¹ • (1 - ω, ω), quadrant_smul (inv_pos.2 hpos).le
    (mem_quadrant_of_hadamard_mem hp (hw hp hω)), ?_, ?_⟩ <;> rw [hadamard_smul, hh.homogeneous _
      (inv_pos.2 hpos), inv_mul_eq_one₀ hpos.ne'] <;> first | rfl | exact hFG | exact hw ‹_› hω

/-- **Necessity** (notes, `prop:prices-gp`): if `(h, P)` is in general position, then so is `P`.
Distinct coordinates: `p_s⁻¹ ∘ p_t` is a good price (`pairGood_iff`), so its coordinates are not
`1` (`ne_one_of_isGoodPrice`). If `μ > 1`, `p_s = μ p_{s'}`, `p_t = μ p_{t'}` and `p_s, p_t` are
incomparable, the curves `s', t'` meet at some `x` (`pairIntersections_nonempty`); then
`x / μ ≠ x` is an intersection point of the curves `s, t` on the same ray. -/
theorem GeneralPosition.pricesGeneralPosition {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    {T : ℕ} {P : Fin T → ℝ × ℝ} (hG : GeneralPosition h P) : PricesGeneralPosition P := by
  have hO := hG.mem_orthant
  have hne : ∀ s t, s ≠ t → 1 / (P s).1 * (P t).1 ≠ 1 ∧ 1 / (P s).2 * (P t).2 ≠ 1 := fun s t hst =>
    hh.ne_one_of_isGoodPrice ((pairGood_iff (hO s)).mp ⟨hG.finite s t hst, hG.transversal s t hst⟩)
  refine ⟨hO, fun s t he => by_contra fun hst => (hne s t hst).1 ?_,
    fun s t he => by_contra fun hst => (hne s t hst).2 ?_, fun μ hμ s t s' t' hs ht hc => ?_⟩
  · rw [← show (P s).1 = (P t).1 from he, one_div_mul_cancel (hO s).1.ne']
  · rw [← show (P s).2 = (P t).2 from he, one_div_mul_cancel (hO s).2.ne']
  have hμ0 : 0 < μ := one_pos.trans hμ
  have hst : s ≠ t := by rintro rfl; simp [Crossing] at hc
  have hs't' : s' ≠ t' := by rintro rfl; rw [hs.trans ht.symm] at hc; simp [Crossing] at hc
  have hc' : Crossing (P s') (P t') := by
    rw [hs, ht] at hc; simp only [Crossing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hc ⊢
    nlinarith [mul_pos hμ0 hμ0]
  obtain ⟨x, hx⟩ := hh.pairIntersections_nonempty (hO s') (hO t') hc'
  have hxo := (hG.transversal s' t' hs't' x hx).1
  obtain ⟨hx1, hx2⟩ := NeoTiling.mem_orthant.mp hxo
  have hμx : ∀ p : ℝ × ℝ, hadamard (μ • p) (μ⁻¹ • x) = hadamard p x := fun p => by
    ext <;> simp [hadamard] <;> field_simp
  refine hG.rays s t s' t' hst hs't' (μ⁻¹ • x) ⟨quadrant_smul (inv_pos.mpr hμ0).le
    (orthant_subset_quadrant hxo), by rw [hs, hμx]; exact hx.2.1, by rw [ht, hμx]; exact hx.2.2⟩
    x hx (fun e => ?_) ⟨x.1 / x.2, div_pos hx1 hx2, by simp; field_simp, by field_simp⟩
  have := congrArg Prod.fst e
  simp only [Prod.smul_fst, smul_eq_mul] at this
  nlinarith [inv_lt_one_of_one_lt₀ hμ]

/-! ### Polygonal functions -/

section Polygonal

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The determinant of two vectors of `ℝ²`. -/
def det2 (v w : ℝ × ℝ) : ℝ := v.1 * w.2 - v.2 * w.1

theorem ip_hadamard (a p x : ℝ × ℝ) : ip a (hadamard p x) = ip (hadamard a p) x := by
  simp only [ip, hadamard]; ring

/-- The polygonal function `z ↦ min_j ⟨ξ_j, z⟩`. -/
noncomputable def polyMin (ξ : ι → ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => ip (ξ j) z

theorem polyMin_le (ξ : ι → ℝ × ℝ) (z : ℝ × ℝ) (j : ι) : polyMin ξ z ≤ ip (ξ j) z :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem le_polyMin {ξ : ι → ℝ × ℝ} {z : ℝ × ℝ} {c : ℝ} (H : ∀ j, c ≤ ip (ξ j) z) :
    c ≤ polyMin ξ z :=
  Finset.le_inf' _ _ fun j _ => H j

theorem exists_ip_eq_polyMin (ξ : ι → ℝ × ℝ) (z : ℝ × ℝ) : ∃ j, ip (ξ j) z = polyMin ξ z := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun j => ip (ξ j) z)
  exact ⟨j, hj.symm⟩

theorem continuous_polyMin : Continuous fun q : (ι → ℝ × ℝ) × (ℝ × ℝ) => polyMin q.1 q.2 := by
  unfold polyMin
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro j _
  simp only [ip]
  fun_prop

theorem polyMin_hadamard (ξ : ι → ℝ × ℝ) (p x : ℝ × ℝ) :
    polyMin ξ (hadamard p x) = polyMin (fun j => hadamard (ξ j) p) x := by
  simp only [polyMin, ip_hadamard]

theorem polyMin_eq_of_lt {ξ : ι → ℝ × ℝ} {z : ℝ × ℝ} {j : ι}
    (h : ∀ l, l ≠ j → ip (ξ j) z < ip (ξ l) z) : polyMin ξ z = ip (ξ j) z :=
  (polyMin_le ξ z j).antisymm (le_polyMin fun l => by
    rcases eq_or_ne l j with rfl | hl
    exacts [le_rfl, (h l hl).le])

theorem isPosNeoclassical_polyMin {ξ : ι → ℝ × ℝ} (hξ : ∀ j, ξ j ∈ orthant) :
    IsPosNeoclassical (polyMin ξ) := by
  have h (i) : 0 < ip (ξ i) (1, 0) ∧ 0 < ip (ξ i) (0, 1) := by simpa [ip] using mem_orthant.1 (hξ i)
  have ha := (exists_ip_eq_polyMin ξ (1, 0)).elim fun i hi => hi ▸ (h i).1
  have hb := (exists_ip_eq_polyMin ξ (0, 1)).elim fun i hi => hi ▸ (h i).2
  have hlin : ∀ p ∈ quadrant, polyMin ξ (1, 0) * p.1 + polyMin ξ (0, 1) * p.2 ≤ polyMin ξ p :=
    fun p hp => le_polyMin fun j => by
      have := polyMin_le ξ (1, 0) j; have := polyMin_le ξ (0, 1) j
      simp only [ip, mem_quadrant] at *; nlinarith
  refine isPosNeoclassical_iff_exists_linear_le.mpr ⟨⟨fun p hp => le_trans (by
    obtain ⟨h1, h2⟩ := mem_quadrant.mp hp; positivity) (hlin p hp),
    (continuous_polyMin.comp (continuous_const.prodMk continuous_id)).continuousOn,
    ⟨(convex_Ici 0).prod (convex_Ici 0), fun x _ y _ s t hs ht _ => le_polyMin fun j => ?_⟩,
    fun τ hτ p _ => ?_⟩, _, _, ha, hb, hlin⟩
  · have := polyMin_le ξ x j; have := polyMin_le ξ y j
    simp [ip] at *; nlinarith
  · rw [polyMin, polyMin, Finset.comp_inf'_eq_inf'_comp _ _ fun x y => mul_min_of_nonneg x y hτ.le]
    simp [ip, mul_add, mul_left_comm]

/-- Near a point where a single line is active, `polyMin` is linear, so its only supergradient
is the gradient of that line (test the supergradient inequality at `x + δ (b_j - ξ)`). -/
theorem superdiff_polyMin_subset {b : ι → ℝ × ℝ} {x : ℝ × ℝ} (hx : x ∈ orthant) {j : ι}
    (hj : ∀ l, l ≠ j → ip (b j) x < ip (b l) x) : superdiff (polyMin b) x ⊆ {b j} := by
  intro η hη
  set y := fun δ : ℝ => x + δ • (b j - η)
  have hc : ∀ c, ContinuousAt (fun δ => ip c (y δ)) 0 := fun c => by simp only [ip, y]; fun_prop
  have hev : ∀ᶠ δ in 𝓝 0, y δ ∈ orthant ∧ ∀ l, l ≠ j → ip (b j) (y δ) < ip (b l) (y δ) :=
    ((ContinuousAt.eventually_mem (by fun_prop)
      (isOpen_orthant.mem_nhds (by simpa [y] using hx))).and
      (eventually_all.mpr fun l => by
        by_cases hl : l = j
        · exact .of_forall fun _ h => absurd hl h
        · exact ((hc _).eventually_lt (hc _) (by simpa [y] using hj l hl)).mono fun _ h _ => h))
  obtain ⟨δ, hδ, hδo, hδlt⟩ := hev.exists_gt
  have h1 := hη _ (orthant_subset_quadrant hδo)
  rw [polyMin_eq_of_lt hδlt, polyMin_eq_of_lt hj, add_sub_cancel_left] at h1
  have h0 : ((b j).1 - η.1) ^ 2 + ((b j).2 - η.2) ^ 2 ≤ 0 := by simp [ip, y] at h1; nlinarith
  exact Prod.ext (by nlinarith [sq_nonneg ((b j).2 - η.2)])
    (by nlinarith [sq_nonneg ((b j).1 - η.1)])

end Polygonal

/-! ### Lines in general position

With `a_{j t} = ξ_j ∘ p_t`, the curve `t` of `polyMin ξ` is `min_j ⟨a_{j t}, x⟩ = 1`. -/

section Lines

variable {ι : Type*} {T : ℕ}

/-- Vectors orthogonal to two points of `ℝ²₊₊` on one ray are parallel:
`det (D, D') ⟨x, y⟩ = 0` is a linear combination of the hypotheses. -/
theorem det2_eq_zero_of_ip_eq_zero {D D' x y : ℝ × ℝ} (hx : x ∈ orthant) (hy : y ∈ orthant)
    (hxy : x.1 * y.2 = x.2 * y.1) (hD : ip D x = 0) (hD' : ip D' y = 0) : det2 D D' = 0 := by
  have h := mul_pos (mem_orthant.1 hx).2 (mem_orthant.1 hy).2
  unfold det2 ip at *
  exact mul_right_cancel₀ h.ne'
    (by linear_combination D.1 * x.2 * hD' - D'.1 * y.2 * hD + D.1 * D'.1 * hxy)

/-- For `s ≠ t` the system `⟨p_s, y⟩ = ⟨p_t, y⟩ = 1` has at most one solution: two solutions
would make `p_s, p_t` parallel, hence equal. -/
theorem subsingleton_solutions {p q : ℝ × ℝ} (hpq : p ≠ q) :
    {y : ℝ × ℝ | ip p y = 1 ∧ ip q y = 1}.Subsingleton := by
  rintro y ⟨h1, h2⟩ y' ⟨h1', h2'⟩
  unfold ip at *
  by_cases hd : p.1 * q.2 - p.2 * q.1 = 0
  · exact absurd (Prod.ext (by linear_combination q.1 * h1 - p.1 * h2 + y.2 * hd)
      (by linear_combination q.2 * h1 - p.2 * h2 - y.1 * hd)) hpq
  · refine Prod.ext (mul_left_cancel₀ hd ?_) (mul_left_cancel₀ hd ?_)
    · linear_combination q.2 * h1 - p.2 * h2 - q.2 * h1' + p.2 * h2'
    · linear_combination p.1 * h2 - q.1 * h1 - p.1 * h2' + q.1 * h1'

theorem ip_sub (a b x : ℝ × ℝ) : ip (a - b) x = ip a x - ip b x := by
  simp only [ip, Prod.fst_sub, Prod.snd_sub]; ring

/-- The difference `a_{j t} - a_{j' t'}` of the coefficient vectors `a_{j t} = ξ_j ∘ p_t`, as a
linear function of `ξ`. -/
noncomputable def coefDiff (P : Fin T → ℝ × ℝ) (a b : ι × Fin T) :
    (ι → ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ where
  toFun ξ := hadamard (ξ a.1) (P a.2) - hadamard (ξ b.1) (P b.2)
  map_add' ξ ζ := by ext <;> simp [hadamard] <;> ring
  map_smul' c ξ := by ext <;> simp [hadamard] <;> ring

@[simp] theorem coefDiff_apply (P : Fin T → ℝ × ℝ) (a b : ι × Fin T) (ξ : ι → ℝ × ℝ) :
    coefDiff P a b ξ = hadamard (ξ a.1) (P a.2) - hadamard (ξ b.1) (P b.2) := rfl

/-- **Generic lines**: a determinant `det (a_α - a_β, a_γ - a_δ)` of differences of coefficient
vectors vanishes at `ξ` only if it vanishes identically in `ξ`. -/
def GenericLines (ξ : ι → ℝ × ℝ) (P : Fin T → ℝ × ℝ) : Prop :=
  ∀ a b c d : ι × Fin T, (∃ ζ, det2 (coefDiff P a b ζ) (coefDiff P c d ζ) ≠ 0) →
    det2 (coefDiff P a b ξ) (coefDiff P c d ξ) ≠ 0

/-- **Two different pairs of crossing prices.** For lines `j ≠ k` and `j' ≠ k'` the determinant
`det (a_{j s} - a_{k t}, a_{j' s'} - a_{k' t'})` does not vanish identically in `ξ`: if
`{j', k'} ⊄ {j, k}`, take `ζ = (1, 0)` at `j`, `(0, 1)` at the new line and `0` elsewhere;
otherwise its values at four choices of `(ζ_j, ζ_k)` make the pairs proportional, excluded by
`not_dilate`. -/
theorem PricesGeneralPosition.exists_det2_ne_zero {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) {s t s' t' : Fin T} (hd : PairsDiffer s t s' t')
    (hc : Crossing (P s) (P t)) (hc' : Crossing (P s') (P t')) {j k j' k' : ι} (hjk : j ≠ k)
    (hj'k' : j' ≠ k') :
    ∃ ζ : ι → ℝ × ℝ, det2 (coefDiff P (j, s) (k, t) ζ) (coefDiff P (j', s') (k', t') ζ) ≠ 0 := by
  classical
  wlog h : (j' ≠ j ∧ j' ≠ k) ∨ (j' = j ∧ k' = k) generalizing s' t' j' k'
  · obtain ⟨ζ, hζ⟩ := this ⟨hd.1, hd.2.1.symm, fun h => hd.2.2 h.symm⟩ hc'.symm hj'k'.symm
      (by grind)
    refine ⟨ζ, fun e => hζ ?_⟩
    simp only [coefDiff_apply, det2, Prod.fst_sub, Prod.snd_sub] at e ⊢
    linear_combination -e
  obtain ⟨hs1, hs2⟩ := NeoTiling.mem_orthant.mp (hP.mem_orthant s)
  rcases h with h | ⟨rfl, rfl⟩
  · refine ⟨Pi.single j (1, 0) + Pi.single j' (0, 1), ?_⟩
    simp only [coefDiff_apply, det2, hadamard, Pi.add_apply, Pi.single_apply, if_neg h.1.symm,
      if_neg h.2.symm, if_neg hjk.symm, if_neg h.1, if_neg hj'k'.symm]
    split_ifs <;> simp [hs1.ne', (NeoTiling.mem_orthant.mp (hP.mem_orthant s')).2.ne']
  by_contra H
  push_neg at H
  have e1 := H (Pi.single j' (1, 1))
  have e3 := H (Pi.single j' (1, 0) + Pi.single k' (0, 1))
  have e4 := H (Pi.single j' (0, 1) + Pi.single k' (1, 0))
  simp [det2, hadamard, hjk, hjk.symm] at e1 e3 e4
  refine hP.not_dilate hd hc hc' (μ := (P s').1 / (P s).1) (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> field_simp
  · linear_combination e1
  · exact mul_left_cancel₀ hs2.ne' (by linear_combination (P s).1 * e4 + (P t).1 * e1)
  · linear_combination -e3

/-- Coefficient vectors of two different curves differ: for one line by injectivity of
`ξ_j ∘ ·`, for lines `j ≠ k` by genericity (witness `ζ_j = (1, 0)`, `ζ_k = (0, 1)`). -/
theorem GenericLines.coef_ne {ξ : ι → ℝ × ℝ} {P : Fin T → ℝ × ℝ} (hG : GenericLines ξ P)
    (hP : PricesGeneralPosition P) (hξ : ∀ j, ξ j ∈ orthant) {s t : Fin T} (hst : s ≠ t)
    (j k : ι) : hadamard (ξ j) (P s) ≠ hadamard (ξ k) (P t) := fun heq => by
  classical
  rcases eq_or_ne j k with rfl | hjk
  · exact hst (hP.fst_injective (congrArg Prod.fst (hadamard_injective (hξ j) heq)))
  apply hG (j, s) (k, t) (j, s) (j, t) ⟨Pi.single j (1, 0) + Pi.single k (0, 1), ?_⟩ <;>
    first | (simp [det2, heq]; done) | simp [det2, hadamard, hjk, hjk.symm,
      (mem_Ioi.1 (hP.mem_orthant t).2).ne', sub_ne_zero.2 (hP.fst_injective.ne hst)]

variable [Fintype ι] [Nonempty ι] {ξ : ι → ℝ × ℝ} {P : Fin T → ℝ × ℝ}

/-- **No line is shared by two curves at one point.** If the line `j` meets the curves `s ≠ t`
of `g = polyMin ξ` at a common point `x`, then `y = ξ_j ∘ x` solves `⟨p_s, y⟩ = ⟨p_t, y⟩ = 1`,
and `x = ξ_j⁻¹ ∘ y` is off one of the curves `g (p ∘ x) = 1`. (Stated in `y`, the condition is
visibly open in `ξ`, `eventually_noSharedLine`.) -/
def NoSharedLine (ξ : ι → ℝ × ℝ) (P : Fin T → ℝ × ℝ) : Prop :=
  ∀ j s t, s ≠ t → ∀ y ∈ quadrant, ip (P s) y = 1 → ip (P t) y = 1 →
    polyMin ξ (hadamard (P s) (hadamard (hinv (ξ j)) y)) < 1 ∨
      polyMin ξ (hadamard (P t) (hadamard (hinv (ξ j)) y)) < 1

/-- At a common point of the curves `s ≠ t` the lines active for them are different. -/
theorem NoSharedLine.ne (hS : NoSharedLine ξ P) (hξ : ∀ j, ξ j ∈ orthant) {s t : Fin T}
    (hst : s ≠ t) {x : ℝ × ℝ} (hx : x ∈ pairIntersections (polyMin ξ) (P s) (P t)) {j k : ι}
    (hj : ip (hadamard (ξ j) (P s)) x = 1) (hk : ip (hadamard (ξ k) (P t)) x = 1) : j ≠ k := by
  rintro rfl
  have e (p) : ip p (hadamard (ξ j) x) = ip (hadamard (ξ j) p) x := by unfold ip hadamard; ring
  have := hS j s t hst _ (hadamard_mem_quadrant (orthant_subset_quadrant (hξ j)) hx.1)
    (e _ ▸ hj) (e _ ▸ hk)
  rw [hadamard_hinv_hadamard (hξ j)] at this
  rcases this with h | h <;> linarith [hx.2.1, hx.2.2]

/-- **Active lines** at a common point `x` of the curves `s ≠ t` of `polyMin ξ`: `x ∈ ℝ²₊₊` and the
prices cross (`mem_orthant_crossing`); lines `j ≠ k` are active for `s` and `t`
(`NoSharedLine.ne`); `j` is the only line active for `s` (a second one would be concurrent with
`j` and `k`, which genericity excludes), so `a_{j s}` is the only supergradient of
`polyMin ξ (p_s ∘ ·)` at `x` (`superdiff_polyMin_subset`). -/
theorem exists_active (hξ : ∀ j, ξ j ∈ orthant) (hP : PricesGeneralPosition P)
    (hS : NoSharedLine ξ P) (hG : GenericLines ξ P) {s t : Fin T} (hst : s ≠ t) {x : ℝ × ℝ}
    (hx : x ∈ pairIntersections (polyMin ξ) (P s) (P t)) :
    x ∈ orthant ∧ Crossing (P s) (P t) ∧ ∃ j k, j ≠ k ∧ ip (hadamard (ξ j) (P s)) x = 1 ∧
      ip (hadamard (ξ k) (P t)) x = 1 ∧
      superdiff (fun y => polyMin ξ (hadamard (P s) y)) x ⊆ {hadamard (ξ j) (P s)} := by
  classical
  obtain ⟨hxo, hxc⟩ := (isPosNeoclassical_polyMin hξ).mem_orthant_crossing (hP.mem_orthant s)
    (hP.mem_orthant t) (hP.fst_injective.ne hst) (hP.snd_injective.ne hst) hx
  obtain ⟨j, hj⟩ := exists_ip_eq_polyMin ξ (hadamard (P s) x)
  obtain ⟨k, hk⟩ := exists_ip_eq_polyMin ξ (hadamard (P t) x)
  rw [ip_hadamard, hx.2.1] at hj
  rw [ip_hadamard, hx.2.2] at hk
  have hjk := hS.ne hξ hst hx hj hk
  refine ⟨hxo, hxc, j, k, hjk, hj, hk, ?_⟩
  rw [show (fun y => polyMin ξ (hadamard (P s) y)) = _ from funext (polyMin_hadamard ξ (P s))]
  refine superdiff_polyMin_subset hxo fun l hlj => hj ▸ lt_of_le_of_ne ?_ fun heq => ?_
  · simpa [ip_hadamard, hx.2.1] using polyMin_le ξ (hadamard (P s) x) l
  have hlk := hS.ne hξ hst hx heq.symm hk
  obtain ⟨hs1, hs2⟩ := mem_orthant.mp (hP.mem_orthant s)
  refine hG (j, s) (k, t) (l, s) (k, t) ⟨Pi.single j (1, 0) + Pi.single l (0, 1), ?_⟩
    (det2_eq_zero_of_ip_eq_zero hxo hxo (mul_comm _ _) (by simp [ip_sub, hj, hk])
      (by simp [ip_sub, ← heq, hk]))
  simp [det2, hadamard, hlj, hjk.symm, hlk.symm, Ne.symm hlj, hs1.ne', hs2.ne']

/-- **General position of a polygonal function** (through `generalPosition_iff`). By
`exists_active`, intersection points of the curves `s, t` lie on two lines `(j, s)`, `(k, t)`
with different coefficient vectors (`coef_ne`), so each pair of lines contributes at most one
point (`subsingleton_solutions`), and the superdifferentials are the different points `a_{j s}`,
`a_{k t}`. Two intersection points `x, y` of different pairs on one ray make
`a_{j s} - a_{k t}` and `a_{j' s'} - a_{k' t'}` parallel (`det2_eq_zero_of_ip_eq_zero`), which
genericity excludes (`exists_det2_ne_zero`). -/
theorem generalPosition_polyMin (hξ : ∀ j, ξ j ∈ orthant) (hP : PricesGeneralPosition P)
    (hS : NoSharedLine ξ P) (hG : GenericLines ξ P) : GeneralPosition (polyMin ξ) P := by
  refine (isPosNeoclassical_polyMin hξ).generalPosition_iff.mpr
    ⟨hP.mem_orthant, fun s t hst => (pairGood_iff (hP.mem_orthant s)).mp ⟨?_, fun x hx => ?_⟩, ?_⟩
  · refine (Set.finite_iUnion fun j => Set.finite_iUnion fun k =>
      (subsingleton_solutions (hG.coef_ne hP hξ hst j k)).finite).subset fun z hz => ?_
    obtain ⟨-, -, j, k, -, hj, hk, -⟩ := exists_active hξ hP hS hG hst hz
    exact mem_iUnion₂.mpr ⟨j, k, hj, hk⟩
  · obtain ⟨hxo, -, j, -, -, -, -, hsupS⟩ := exists_active hξ hP hS hG hst hx
    obtain ⟨-, -, j₂, -, -, -, -, hsupT⟩ := exists_active hξ hP hS hG hst.symm
      (pairIntersections_comm (polyMin ξ) (P s) (P t) ▸ hx)
    exact ⟨hxo, Disjoint.mono hsupS hsupT (disjoint_singleton.mpr (hG.coef_ne hP hξ hst j j₂))⟩
  · intro s t s' t' hd x hx y hy hxy
    obtain ⟨hxo, hxc, j, k, hjk, hj, hk, -⟩ := exists_active hξ hP hS hG hd.1 hx
    obtain ⟨hyo, hyc, j', k', hjk', hj', hk', -⟩ := exists_active hξ hP hS hG hd.2.1 hy
    exact hG (j, s) (k, t) (j', s') (k', t') (hP.exists_det2_ne_zero hd hxc hyc hjk hjk')
      (det2_eq_zero_of_ip_eq_zero hxo hyo hxy (by simp [ip_sub, hj, hk])
        (by simp [ip_sub, hj', hk']))

end Lines

/-! ### Generic lines are dense -/

section Generic

variable {ι : Type*}

/-- **A quadratic form vanishes nowhere densely.** If `det (L₁ ζ, L₂ ζ) ≠ 0` for some `ζ`, then
along every line `ξ + l ζ` the determinant is a polynomial of degree `2` in `l` with leading
coefficient `det (L₁ ζ, L₂ ζ)`, so it vanishes at finitely many `l` only. -/
theorem dense_det2_ne_zero {L₁ L₂ : (ι → ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ}
    (h : ∃ ζ, det2 (L₁ ζ) (L₂ ζ) ≠ 0) : Dense {ξ | det2 (L₁ ξ) (L₂ ξ) ≠ 0} := by
  obtain ⟨ζ, hζ⟩ := h
  refine dense_iff_inter_open.2 fun U hU ⟨ξ₀, hξ₀⟩ => ?_
  open Polynomial in
  let p : ℝ[X] := C (det2 (L₁ ξ₀) (L₂ ξ₀)) + C (det2 (L₁ ξ₀) (L₂ ζ) + det2 (L₁ ζ) (L₂ ξ₀)) * X +
    C (det2 (L₁ ζ) (L₂ ζ)) * X ^ 2
  have hp0 : p ≠ 0 := fun h0 => hζ (by simpa [p] using congrArg (Polynomial.coeff · 2) h0)
  have hU' : {l : ℝ | ξ₀ + l • ζ ∈ U} ∈ 𝓝 0 := (Continuous.continuousAt (by fun_prop))
    |>.preimage_mem_nhds (hU.mem_nhds (by simpa using hξ₀))
  obtain ⟨l, hlU, hlr⟩ :=
    ((infinite_of_mem_nhds 0 hU').diff (Polynomial.finite_setOf_isRoot hp0)).nonempty
  refine ⟨_, hlU, fun h0 => hlr ?_⟩
  simp only [map_add, map_smul, det2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at h0
  simp [p, det2]
  linear_combination h0

/-- **Generic lines exist in every nonempty open set**: finitely many dense open conditions
(`dense_det2_ne_zero`, Baire). -/
theorem exists_genericLines [Fintype ι] {T : ℕ} {P : Fin T → ℝ × ℝ} {V : Set (ι → ℝ × ℝ)}
    (hV : IsOpen V) (hne : V.Nonempty) : ∃ ξ ∈ V, GenericLines ξ P := by
  classical
  let D (q : (ι × Fin T) × (ι × Fin T) × (ι × Fin T) × (ι × Fin T)) (ξ : ι → ℝ × ℝ) :=
    det2 (coefDiff P q.1 q.2.1 ξ) (coefDiff P q.2.2.1 q.2.2.2 ξ)
  have hD q : Continuous (D q) := by simp only [D, coefDiff_apply, det2, hadamard]; fun_prop
  obtain ⟨ξ, hξ, hξV⟩ := (dense_iInter_of_isOpen (f := fun i : {q // ∃ ζ, D q ζ ≠ 0} =>
    {ξ | D i ξ ≠ 0}) (fun i => isOpen_ne.preimage (hD i)) fun i => dense_det2_ne_zero i.2)
    |>.exists_mem_open hV hne
  exact ⟨ξ, hξV, fun a b c d hζ => mem_iInter.mp hξ ⟨(a, b, c, d), hζ⟩⟩

end Generic

/-! ### No shared line is an open condition -/

/-- **`NoSharedLine` is open**: for each line `j` and pair `s ≠ t` the condition is required at
most at one point `y`, and is an open condition on `ξ` there (`continuous_polyMin`,
`continuousOn_hinv`). -/
theorem eventually_noSharedLine {ι : Type*} [Fintype ι] [Nonempty ι] {T : ℕ}
    {P : Fin T → ℝ × ℝ} (hP : PricesGeneralPosition P) {ξ₀ : ι → ℝ × ℝ}
    (hξ₀ : ∀ j, ξ₀ j ∈ orthant) (hS : NoSharedLine ξ₀ P) : ∀ᶠ ξ in 𝓝 ξ₀, NoSharedLine ξ P := by
  have hF (p : ℝ × ℝ) (j : ι) (y : ℝ × ℝ) : ContinuousAt
      (fun ξ : ι → ℝ × ℝ => polyMin ξ (hadamard p (hadamard (hinv (ξ j)) y))) ξ₀ :=
    continuous_polyMin.continuousAt.comp₂ continuousAt_id <| ContinuousAt.comp
      (by unfold hadamard; fun_prop : Continuous fun q => hadamard p (hadamard q y)).continuousAt
      ((continuousOn_hinv.continuousAt (isOpen_orthant.mem_nhds (hξ₀ j))).comp
        (f := fun ξ : ι → ℝ × ℝ => ξ j) (continuous_apply j).continuousAt)
  simp only [NoSharedLine, eventually_all]
  intro j s t hst
  filter_upwards [((subsingleton_solutions (hP.fst_injective.ne hst <| congrArg Prod.fst ·)).anti
    inter_subset_left).finite.eventually_all.2 fun y hy =>
    (((hF (P s) j y).min (hF (P t) j y)).eventually_lt continuousAt_const
    (min_lt_iff.2 (hS j s t hst y hy.2 hy.1.1 hy.1.2))).mono fun _ => min_lt_iff.1]
    with ξ hξ y hyq hys hyt
  exact hξ y ⟨⟨hys, hyt⟩, hyq⟩


/-! ### Starting lines: chords of a strictly concave function -/

/-- The chord of `H` over `[a, b]`, as an affine function. -/
noncomputable def chord (H : ℝ → ℝ) (a b τ : ℝ) : ℝ := ((b - τ) * H a + (τ - a) * H b) / (b - a)

/-- For `0 ≤ a < b ≤ 1` and strictly concave `H`: on `[a, b]` the chord is between
`min (H a) (H b)` and `H`; off `[a, b]` it is strictly above `H`. -/
theorem chord_spec {H : ℝ → ℝ} (hH : StrictConcaveOn ℝ (Icc 0 1) H) {a b τ : ℝ}
    (haI : a ∈ Icc (0 : ℝ) 1) (hbI : b ∈ Icc (0 : ℝ) 1) (hab : a < b) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    (τ ∈ Icc a b → min (H a) (H b) ≤ chord H a b τ ∧ chord H a b τ ≤ H τ) ∧
      (τ ∉ Icc a b → H τ < chord H a b τ) := by
  have three : ∀ {x y z : ℝ}, x ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 1 → x < y → y < z →
      (z - y) * H x + (y - x) * H z < (z - x) * H y := fun hx hz hxy hyz => by
    have := hH.slope_anti_adjacent hx hz hxy hyz
    rw [div_lt_div_iff₀ (by linarith) (by linarith)] at this; nlinarith
  have hba : 0 < b - a := by linarith
  simp only [chord, le_div_iff₀ hba, div_le_iff₀ hba, lt_div_iff₀ hba, mem_Icc, not_and_or, not_le]
  refine ⟨fun ⟨h1, h2⟩ => ⟨by nlinarith [min_le_left (H a) (H b), min_le_right (H a) (H b)], ?_⟩,
    fun h => ?_⟩
  · rcases h1.eq_or_lt with rfl | h1 <;> rcases h2.eq_or_lt with rfl | h2 <;>
      first | nlinarith | nlinarith [three haI hbI h1 h2]
  · rcases h with h | h <;> [nlinarith [three hτ hbI h hab]; nlinarith [three haI hτ hab h]]

/-- The `k`-th node `k / (n + 1)` of the uniform partition of `[0, 1]` into `n + 1` pieces. -/
noncomputable def node (n k : ℕ) : ℝ := k / (n + 1)

/-- The `k`-th piece `[node k, node (k + 1)]` lies in `[0, 1]` and has length `1 / (n + 1)`. -/
theorem node_piece (n : ℕ) (k : Fin (n + 1)) : node n k ∈ Icc (0 : ℝ) 1 ∧
    node n (k + 1) ∈ Icc (0 : ℝ) 1 ∧ node n k < node n (k + 1) ∧
      node n (k + 1) - node n k = 1 / (n + 1) := by
  have := k.isLt; unfold node; push_cast
  exact ⟨⟨by positivity, div_le_one_of_le₀ (by norm_cast; omega) (by positivity)⟩,
    ⟨by positivity, div_le_one_of_le₀ (by norm_cast) (by positivity)⟩, by gcongr; linarith, by ring⟩

/-- The line `⟨ℓ, (1 - τ, τ)⟩ = chord` of the chord of `H` over the `k`-th piece. -/
noncomputable def chordLine (H : ℝ → ℝ) (n : ℕ) (k : Fin (n + 1)) : ℝ × ℝ :=
  (chord H (node n k) (node n (k + 1)) 0, chord H (node n k) (node n (k + 1)) 1)

theorem ip_chordLine (H : ℝ → ℝ) (n : ℕ) (k : Fin (n + 1)) (τ : ℝ) :
    ip (chordLine H n k) (1 - τ, τ) = chord H (node n k) (node n (k + 1)) τ := by
  simp only [ip, chordLine, chord]; ring

/-- The point of direction `(1 - τ, τ)` on the curve `H = 1`, a vertex of the polygon. -/
noncomputable def vertex (H : ℝ → ℝ) (τ : ℝ) : ℝ × ℝ := (H τ)⁻¹ • (1 - τ, τ)

/-- A nonzero point of the quadrant is a positive multiple of `(1 - τ, τ)`, `τ ∈ [0, 1]`. -/
theorem eq_smul_segment {z : ℝ × ℝ} (hz : z ∈ quadrant) (hz0 : z ≠ 0) :
    ∃ c > (0 : ℝ), ∃ τ ∈ Icc (0 : ℝ) 1, z = c • (1 - τ, τ) := by
  obtain ⟨h1, h2⟩ := mem_quadrant.mp hz
  have hc : 0 < z.1 + z.2 := by
    by_contra! h; exact hz0 (Prod.ext (by simp; linarith) (by simp; linarith))
  exact ⟨_, hc, z.2 / (z.1 + z.2), ⟨by positivity, div_le_one_of_le₀ (by linarith) hc.le⟩,
    by ext <;> simp <;> field_simp; ring⟩

section Chords

variable {H : ℝ → ℝ} (hH : StrictConcaveOn ℝ (Icc 0 1) H) (hpos : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < H τ)
  {n : ℕ}
include hH hpos

theorem chordLine_mem_orthant (k : Fin (n + 1)) : chordLine H n k ∈ orthant := by
  obtain ⟨ha, hb, hab, -⟩ := node_piece n k
  have key : ∀ τ ∈ Icc (0 : ℝ) 1, 0 < chord H (node n k) (node n (k + 1)) τ := fun τ hτ => by
    have := chord_spec hH ha hb hab hτ
    by_cases h : τ ∈ Icc (node n k) (node n (k + 1))
    exacts [(lt_min (hpos _ ha) (hpos _ hb)).trans_le (this.1 h).1, (hpos τ hτ).trans (this.2 h)]
  exact mem_orthant.mpr ⟨key 0 ⟨le_rfl, zero_le_one⟩, key 1 ⟨zero_le_one, le_rfl⟩⟩

omit hpos in
/-- The polygon lies below `H` on the segment (`τ` lies in the piece `⌊τ (n + 1)⌋`), and a line
active at `(1 - τ, τ)` is the chord of a piece containing `τ` (`chord_spec`). -/
theorem polyMin_chordLine {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    polyMin (chordLine H n) (1 - τ, τ) ≤ H τ ∧ ∀ k : Fin (n + 1),
      ip (chordLine H n k) (1 - τ, τ) = polyMin (chordLine H n) (1 - τ, τ) →
        τ ∈ Icc (node n k) (node n (k + 1)) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  set k₀ : Fin (n + 1) := ⟨min ⌊τ * (n + 1)⌋₊ n, by omega⟩
  obtain ⟨ha, hb, hab, -⟩ := node_piece n k₀
  have hle : polyMin (chordLine H n) (1 - τ, τ) ≤ H τ := by
    refine (polyMin_le _ _ k₀).trans ((ip_chordLine H n k₀ τ).trans_le
      ((chord_spec hH ha hb hab hτ).1 ⟨?_, ?_⟩).2) <;>
      simp only [k₀, node, div_le_iff₀ hN, le_div_iff₀ hN, ← min_add_add_right] <;> push_cast
    exacts [(min_le_left _ _).trans (Nat.floor_le (mul_nonneg hτ.1 hN.le)),
      le_min (Nat.lt_floor_add_one _).le (by nlinarith [hτ.2])]
  refine ⟨hle, fun k hk => by_contra fun h => ?_⟩
  obtain ⟨ha, hb, hab, -⟩ := node_piece n k
  have := (chord_spec hH ha hb hab hτ).2 h
  rw [ip_chordLine] at hk; linarith

/-- **Edges.** A point `z = c (1 - τ, τ)` of `polyMin = 1` on the line `k` lies on the edge
`[v_a, v_b]` over the `k`-th piece: `τ ∈ [a, b]` (`polyMin_chordLine`), `z = θ_a v_a + θ_b v_b`,
`θ_a = c (b - τ) H a / (b - a)`, `θ_b = c (τ - a) H b / (b - a)`, `θ_a + θ_b = c chord τ = 1`. -/
theorem mem_segment_of_active {k : Fin (n + 1)} {z : ℝ × ℝ} (hz : z ∈ quadrant)
    (h1 : ip (chordLine H n k) z = 1) (h2 : polyMin (chordLine H n) z = 1) :
    z ∈ segment ℝ (vertex H (node n k)) (vertex H (node n (k + 1))) := by
  obtain ⟨c, hc, τ, hτ, rfl⟩ := eq_smul_segment hz (by rintro rfl; simp [ip] at h1)
  rw [(isPosNeoclassical_polyMin (chordLine_mem_orthant hH hpos)).homogeneous c hc _
    (mk_mem_quadrant (by linarith [hτ.2]) hτ.1)] at h2
  replace h1 : c * ip (chordLine H n k) (1 - τ, τ) = 1 := by convert h1 using 1; simp [ip]; ring
  obtain ⟨ha, hb, hab, -⟩ := node_piece n k
  obtain ⟨hτa, hτb⟩ := (polyMin_chordLine hH hτ).2 k (mul_left_cancel₀ hc.ne' (h1.trans h2.symm))
  rw [ip_chordLine] at h1
  have hba : 0 < node n (k + 1) - node n k := by linarith
  have := hpos _ ha; have := hpos _ hb
  refine ⟨c * (node n (k + 1) - τ) * H (node n k) / (node n (k + 1) - node n k),
    c * (τ - node n k) * H (node n (k + 1)) / (node n (k + 1) - node n k),
    div_nonneg (by have := sub_nonneg.2 hτb; positivity) hba.le,
    div_nonneg (by have := sub_nonneg.2 hτa; positivity) hba.le, by rw [← h1, chord]; ring, ?_⟩
  ext <;> simp [vertex] <;> field_simp <;> ring

/-- **Short edges give `NoSharedLine`.** If the line `j` were active at `z = p_s ∘ x` and
`w = p_t ∘ x`, both would lie on the edge `[v_a, v_b]` (`mem_segment_of_active`), so
`ρ z_i ≤ |z_i - w_i| < ρ / (2M)` for both `i`, but `z₁ + z₂ ≥ 1 / M` on the edge. -/
theorem noSharedLine_chordLine {T : ℕ} {P : Fin T → ℝ × ℝ} {ρ M : ℝ}
    (hP : ∀ t, P t ∈ orthant)
    (hρ : ∀ s t, s ≠ t → ρ * (P s).1 ≤ |(P s).1 - (P t).1| ∧ ρ * (P s).2 ≤ |(P s).2 - (P t).2|)
    (hM : ∀ τ ∈ Icc (0 : ℝ) 1, H τ ≤ M)
    (hN : ∀ k : Fin (n + 1),
      dist (vertex H (node n k)) (vertex H (node n (k + 1))) < ρ / (2 * M)) :
    NoSharedLine (chordLine H n) P := by
  intro j s t hst y hy hys hyt
  by_contra! hcon
  obtain ⟨hξ1, hξ2⟩ := mem_orthant.mp (chordLine_mem_orthant hH hpos j)
  set x := hadamard (hinv (chordLine H n j)) y
  have hx : x ∈ quadrant := hadamard_mem_quadrant
    (orthant_subset_quadrant (hinv_mem_orthant (chordLine_mem_orthant hH hpos j))) hy
  have hseg : ∀ u, u ∈ orthant → ip u y = 1 → 1 ≤ polyMin (chordLine H n) (hadamard u x) →
      hadamard u x ∈ segment ℝ (vertex H (node n j)) (vertex H (node n (j + 1))) := by
    intro u hu h1 h2
    have h1' : ip (chordLine H n j) (hadamard u x) = 1 := by
      rw [← h1]; simp only [x, ip, hadamard, hinv]; field_simp
    exact mem_segment_of_active hH hpos (hadamard_mem_quadrant (orthant_subset_quadrant hu) hx)
      h1' (le_antisymm (h1' ▸ polyMin_le _ _ j) h2)
  have hz := hseg _ (hP s) hys hcon.1
  have hw := hseg _ (hP t) hyt hcon.2
  have hM0 : 0 < M := (hpos 0 ⟨le_rfl, zero_le_one⟩).trans_le (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hρ0 : 0 < ρ := (div_pos_iff_of_pos_right (by linarith)).mp (dist_nonneg.trans_lt (hN j))
  have hzw : dist (hadamard (P s) x) (hadamard (P t) x) < ρ / (2 * M) := by
    rw [← convexHull_pair] at hz hw
    have := Metric.dist_le_diam_of_mem (isBounded_convexHull.2 (toFinite _).isBounded) hz hw
    rw [convexHull_diam, Metric.diam_pair] at this; exact this.trans_lt (hN j)
  have key : ∀ ps pt xi : ℝ, ρ * ps ≤ |ps - pt| → 0 ≤ xi →
      dist (ps * xi) (pt * xi) < ρ / (2 * M) → ps * xi < 1 / (2 * M) := by
    intro ps pt xi hp hxi h1
    rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg hxi] at h1
    rw [← mul_lt_mul_iff_right₀ hρ0, mul_one_div, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hp hxi).trans_lt h1
  have := key _ _ _ (hρ s t hst).1 (mem_quadrant.mp hx).1 ((le_max_left _ _).trans_lt hzw)
  have := key _ _ _ (hρ s t hst).2 (mem_quadrant.mp hx).2 ((le_max_right _ _).trans_lt hzw)
  have hv : ∀ τ ∈ Icc (0 : ℝ) 1, vertex H τ ∈ {v : ℝ × ℝ | 1 / M ≤ v.1 + v.2} := fun τ hτ => by
    simpa [vertex, ← mul_add] using inv_anti₀ (hpos τ hτ) (hM τ hτ)
  obtain ⟨ha, hb, hab, -⟩ := node_piece n j
  have := (convex_halfSpace_ge (𝕜 := ℝ) ⟨fun _ _ => by simp; ring, fun _ _ => by simp; ring⟩
    (1 / M)).segment_subset (hv _ ha) (hv _ hb) hz
  have : 1 / (2 * M) + 1 / (2 * M) = 1 / M := by field_simp; ring
  simp only [mem_setOf_eq, hadamard_fst, hadamard_snd] at *; linarith

end Chords

/-- Distinct prices in general position differ in each coordinate by a fixed fraction `ρ`. -/
theorem PricesGeneralPosition.exists_rho {T : ℕ} {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) : ∃ ρ > 0, ∀ s t, s ≠ t →
      ρ * (P s).1 ≤ |(P s).1 - (P t).1| ∧ ρ * (P s).2 ≤ |(P s).2 - (P t).2| := by
  have key : ∀ c d : ℝ, c ≠ d → ∀ᶠ ρ in 𝓝 (0 : ℝ), ρ * c ≤ |c - d| := fun c d h =>
    (Tendsto.eventually_lt_const (by simpa [sub_eq_zero] using h)
      ((continuous_mul_right c).tendsto 0)).mono fun _ => le_of_lt
  exact (eventually_all.2 fun s : Fin T => eventually_all.2 fun t : Fin T =>
    eventually_imp_distrib_left.2 fun hst => (key _ _ (hP.fst_injective.ne hst)).and
      (key _ _ (hP.snd_injective.ne hst))).exists_gt

/-- Uniform continuity: for large `n`, `f` varies by `< ε` on `[0, 1]` at distance `1 / (n + 1)`. -/
theorem eventually_dist_lt {E : Type*} [PseudoMetricSpace E] {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |a - b| ≤ 1 / (n + 1) →
      dist (f a) (f b) < ε := by
  obtain ⟨δ, hδ, H⟩ :=
    Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [eventually_ge_atTop N] with n hn a ha b hb hab
  exact H a ha b hb (hab.trans_lt (lt_of_le_of_lt (by gcongr) hN))

/-- The restriction of `h` to the segment `(1 - τ, τ)` plus `ε τ (1 - τ)`. -/
noncomputable def segFun (h : ℝ × ℝ → ℝ) (ε τ : ℝ) : ℝ := h (1 - τ, τ) + ε * (τ * (1 - τ))

/-- For `ε > 0`, `segFun h ε` is strictly concave, continuous, positive and `ε`-close to `h`. -/
theorem IsPosNeoclassical.segFun_spec {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h) {ε : ℝ}
    (hε : 0 < ε) : StrictConcaveOn ℝ (Icc 0 1) (segFun h ε) ∧
      ContinuousOn (segFun h ε) (Icc 0 1) ∧ ∀ τ ∈ Icc (0 : ℝ) 1,
        0 < segFun h ε τ ∧ |segFun h ε τ - h (1 - τ, τ)| ≤ ε := by
  have hq : ∀ τ ∈ Icc (0 : ℝ) 1, ((1 : ℝ) - τ, τ) ∈ quadrant := fun τ hτ =>
    mk_mem_quadrant (by linarith [hτ.2]) hτ.1
  refine ⟨⟨convex_Icc 0 1, fun x hx y hy hxy a b ha hb hab => ?_⟩,
    (hh.continuousOn.comp (by fun_prop) hq).add (by fun_prop), fun τ hτ => ?_⟩
  · have hc := hh.concaveOn.2 (hq x hx) (hq y hy) ha.le hb.le hab
    rw [show a • (1 - x, x) + b • (1 - y, y) = (1 - (a • x + b • y), a • x + b • y) by
      ext <;> simp; linarith] at hc
    simp only [smul_eq_mul, segFun] at hc ⊢
    nlinarith [mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)),
      (by linear_combination (-(a*x^2+b*y^2)) * hab :
        (a*x+b*y)*(1-(a*x+b*y)) - (a*(x*(1-x))+b*(y*(1-y))) = a*b*(x-y)^2)]
  · have := mul_nonneg hε.le (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2))
    refine ⟨add_pos_of_pos_of_nonneg (hh.pos _ (hq τ hτ) (by simp [Prod.ext_iff]; intro; linarith
      [hτ.1])) this, ?_⟩
    rw [segFun, add_sub_cancel_left, abs_of_nonneg this]
    exact mul_le_of_le_one_right hε.le (by nlinarith [hτ.2, sq_nonneg τ])

/-- **Starting lines** in `ℝ²₊₊` with `NoSharedLine` and polygon `η`-close to `h` on `Z`: chords of
`H = segFun h ε` over `n + 1` pieces, `0 < H ≤ M`. For large `n` the ends of each edge are
`ρ / (2M)`-close (`noSharedLine_chordLine`) and `|polyMin - H| < ε` on the segment; by homogeneity
`|polyMin ξ z - h z| < 2 (z₁ + z₂) ε`. -/
theorem IsPosNeoclassical.exists_startLines {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    {T : ℕ} {P : Fin T → ℝ × ℝ} (hP : PricesGeneralPosition P) (Z : Finset (ℝ × ℝ))
    (hZ : ∀ z ∈ Z, z ∈ orthant) {η : ℝ × ℝ → ℝ} (hη : ∀ z ∈ Z, 0 < η z) :
    ∃ (n : ℕ) (ξ : Fin (n + 1) → ℝ × ℝ), (∀ j, ξ j ∈ orthant) ∧ NoSharedLine ξ P ∧
      ∀ z ∈ Z, |polyMin ξ z - h z| < η z := by
  obtain ⟨ρ, hρ0, hρ⟩ := hP.exists_rho
  obtain ⟨e, he0, he1⟩ := (Z.eventually_all.2 fun z hz => Tendsto.eventually_lt_const
    (by simpa using hη z hz) ((by fun_prop : Continuous fun e : ℝ => (z.1 + z.2) * (2 * e)).tendsto
      0)).exists_gt
  obtain ⟨hH, hHc, hHτ⟩ := hh.segFun_spec he0
  have hpos := fun τ hτ => (hHτ τ hτ).1
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hHc
  replace hM : ∀ τ ∈ Icc (0 : ℝ) 1, segFun h e τ ≤ M := fun τ hτ => hM (mem_image_of_mem _ hτ)
  have hM0 : 0 < M := (hpos 0 ⟨le_rfl, zero_le_one⟩).trans_le (hM 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨n, evV, evH⟩ := ((eventually_dist_lt ((hHc.inv₀ fun τ hτ => (hpos τ hτ).ne').smul
    (by fun_prop : Continuous fun τ : ℝ => ((1 : ℝ) - τ, τ)).continuousOn)
    (by positivity : 0 < ρ / (2 * M))).and (eventually_dist_lt hHc he0)).exists
  refine ⟨n, chordLine (segFun h e) n, chordLine_mem_orthant hH hpos,
    noSharedLine_chordLine hH hpos hP.mem_orthant hρ hM fun k => ?_, fun z hz => ?_⟩
  · exact evV _ (node_piece n k).1 _ (node_piece n k).2.1 (by rw [abs_sub_comm,
      (node_piece n k).2.2.2, abs_of_pos (by positivity)])
  obtain ⟨c, hc, τ, hτ, rfl⟩ := eq_smul_segment (orthant_subset_quadrant (hZ z hz))
    (by rintro rfl; exact lt_irrefl _ (mem_orthant.mp (hZ _ hz)).1)
  have hu : ((1 : ℝ) - τ, τ) ∈ quadrant := mk_mem_quadrant (by linarith [hτ.2]) hτ.1
  rw [(isPosNeoclassical_polyMin (chordLine_mem_orthant hH hpos)).homogeneous c hc _ hu,
    hh.homogeneous c hc _ hu, ← mul_sub, abs_mul, abs_of_pos hc]
  refine (mul_lt_mul_of_pos_left ?_ hc).trans (by simpa [← mul_add] using he1 _ hz)
  obtain ⟨k, hk⟩ := exists_ip_eq_polyMin (chordLine (segFun h e) n) (1 - τ, τ)
  obtain ⟨ha, hb, hab, hd⟩ := node_piece n k
  have hm := (polyMin_chordLine hH hτ).2 k hk
  have hmin := ((chord_spec hH ha hb hab hτ).1 hm).1
  rw [ip_chordLine] at hk
  have h1 := abs_lt.1 (evH _ ha τ hτ (abs_le.2 ⟨by linarith [hm.1, hm.2], by linarith [hm.1]⟩))
  have h2 := abs_lt.1 (evH _ hb τ hτ (abs_le.2 ⟨by linarith [hm.2], by linarith [hm.1, hm.2]⟩))
  have h3 := (polyMin_chordLine hH hτ (n := n)).1
  have h4 := abs_le.mp (hHτ τ hτ).2
  rw [abs_lt]
  rcases min_choice (segFun h e (node n k)) (segFun h e (node n (k + 1))) with h | h <;>
    rw [h] at hmin <;> constructor <;> linarith

/-! ### Main results -/

/-- **Approximation in general position.** For prices in general position, a strictly positive
neoclassical `h` is approximated at finitely many points of `ℝ²₊₊` by strictly positive
neoclassical `g` with `(g, P)` in general position. Proof: starting lines `ξ⁰`
(`exists_startLines`); a neighbourhood of `ξ⁰` keeps the lines in `ℝ²₊₊`, `NoSharedLine`
(`eventually_noSharedLine`) and the approximation; generic lines there
(`exists_genericLines`) give general position (`generalPosition_polyMin`). -/
theorem PricesGeneralPosition.exists_generalPosition_near {T : ℕ} {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    (Z : Finset (ℝ × ℝ)) (hZ : ∀ z ∈ Z, z ∈ orthant) {η : ℝ × ℝ → ℝ}
    (hη : ∀ z ∈ Z, 0 < η z) :
    ∃ g, IsPosNeoclassical g ∧ GeneralPosition g P ∧ ∀ z ∈ Z, |g z - h z| < η z := by
  obtain ⟨n, ξ₀, hξ₀, hS₀, hclose⟩ := hh.exists_startLines hP Z hZ hη
  have hall : ∀ᶠ ξ in 𝓝 ξ₀, (∀ j, ξ j ∈ orthant) ∧ NoSharedLine ξ P ∧
      ∀ z ∈ Z, |polyMin ξ z - h z| < η z := by
    refine (eventually_all.mpr fun j => (continuous_apply j).continuousAt
      (isOpen_orthant.mem_nhds (hξ₀ j))).and ((eventually_noSharedLine hP hξ₀ hS₀).and
      (Z.eventually_all.mpr fun z hz => ?_))
    have hc : Continuous fun ξ : Fin (n + 1) → ℝ × ℝ => |polyMin ξ z - h z| :=
      ((continuous_polyMin.comp (continuous_id.prodMk continuous_const)).sub
        continuous_const).abs
    exact hc.continuousAt.eventually_lt_const (hclose z hz)
  obtain ⟨V, hVsub, hVo, hξ₀V⟩ := mem_nhds_iff.mp hall
  obtain ⟨ξ, hξV, hG⟩ := exists_genericLines hVo ⟨ξ₀, hξ₀V⟩
  obtain ⟨hξo, hξS, hξZ⟩ := hVsub hξV
  exact ⟨polyMin ξ, isPosNeoclassical_polyMin hξo, generalPosition_polyMin hξo hP hξS hG, hξZ⟩

/-- **Proposition `prop:prices-gp`.** Prices are in general position iff `(h, P)` is in general
position for some strictly positive neoclassical `h`. -/
theorem pricesGeneralPosition_iff {T : ℕ} {P : Fin T → ℝ × ℝ} :
    PricesGeneralPosition P ↔ ∃ h, IsPosNeoclassical h ∧ GeneralPosition h P := by
  refine ⟨fun hP => ?_, fun ⟨h, hh, hG⟩ => hG.pricesGeneralPosition hh⟩
  have h₀ : IsPosNeoclassical (polyMin fun _ : Fin 1 => ((1 : ℝ), (1 : ℝ))) :=
    isPosNeoclassical_polyMin fun _ => mem_orthant.mpr ⟨one_pos, one_pos⟩
  obtain ⟨g, hg, hgP, -⟩ := hP.exists_generalPosition_near h₀ ∅ (by simp) (η := fun _ => 1)
    (by simp)
  exact ⟨g, hg, hgP⟩

end NeoTiling
