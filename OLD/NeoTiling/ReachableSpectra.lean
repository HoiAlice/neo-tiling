import NeoTiling.RegularSolvability

/-!
# Reachable spectra

Notes, section "Алгоритм регулярной разрешимости". An index `t` *covers* the pair `s, r`
(`Covers`) if `p_t ∈ conv {p_s, p_r} + ℝ²₊`; a set `S ⊆ [T]` is a *reachable spectrum*
(`IsReachable`) if no `t ∈ S` covers a pair `s, r ∉ S`; `Sp(P)` is `reachableSpectra P`.

Main results:

General position of the prices is needed only in `thm:admissible-cone` and the remark after it,
through `lem:gp-approx`; all lemmas before hold for any positive prices.

* `IsNeoclassical.spectrum_subset_reachableSpectra`: `Sp(h, P) ⊆ Sp(P)` for every `h ∈ Φ₂`
  (concavity and monotonicity, `IsNeoclassical.one_le_of_covers`).
* `IsReachable.exists_polyMin`: every `S ∈ Sp(P)` is in `Sp(h, P)` for a polygonal
  `h = min_k ⟨ξ_k, ·⟩ ∈ Φ̂₂`; the vectors `ξ_t = c_t (σ_t, 1)` come from
  `IsReachable.exists_slope` and `IsReachable.exists_vector`.
* `exists_polyMin_patch` (`lem:patch`): one polygonal `h` for finitely many reachable spectra,
  copies of the vectors transported to the points `x_i = (α_i, α_i⁻¹)`.
* `Realizes.mem_span_reachableSpectra`, `NeoSolvable.mem_span_reachableSpectra`: the direction
  `→` of `thm:admissible-cone`, for any positive prices.
* `PricesGeneralPosition.regularlySolvable_iff_mem_span_reachableSpectra` and
  `PricesGeneralPosition.neoSolvable_iff_mem_span_reachableSpectra` (`thm:admissible-cone`):
  for prices in general position the solvable outputs form `cone {1_S | S ∈ Sp(P)}`.
* `PricesGeneralPosition.exists_spectrum_eq_reachableSpectra` (the remark): one `h` in general
  position with `P` has `Sp(h, P) = Sp(P)`.

The algorithm built on `thm:admissible-cone` is implemented in `code/solvability/`
(CLI `code/solve.py`).
-/

open Set Filter Topology

namespace NeoTiling

variable {T : ℕ} {P : Fin T → ℝ × ℝ}

/-! ### Reachable spectra -/

/-- **Definition "Достижимые спектры"**: `t` *covers* the pair `s, r` if
`p_t ∈ conv {p_s, p_r} + ℝ²₊`, i.e. some point `q` of the segment `[p_s, p_r]` satisfies
`q ≤ p_t` coordinatewise (the order on `ℝ × ℝ` is the product order). `s = r` is allowed. -/
def Covers (P : Fin T → ℝ × ℝ) (t s r : Fin T) : Prop :=
  ∃ q ∈ segment ℝ (P s) (P r), q ≤ P t

/-- **Definition "Достижимые спектры"**: `S` is a *reachable spectrum* at prices `P` if no index
`t ∈ S` covers a pair of indices `s, r ∉ S`. -/
def IsReachable (P : Fin T → ℝ × ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∀ s ∉ S, ∀ r ∉ S, ¬ Covers P t s r

/-- **Definition "Достижимые спектры"**: the family `Sp(P)` of reachable spectra. -/
def reachableSpectra (P : Fin T → ℝ × ℝ) : Set (Finset (Fin T)) := {S | IsReachable P S}

/-! ### `Sp(h, P) ⊆ Sp(P)` -/

/-- The step `A_t ⊆ A_s ∪ A_r` of the lemma `Sp(h, P) ⊆ Sp(P)`: if `t` covers `s, r` and `x` is
(weakly) outside the curves `s` and `r`, then it is (weakly) outside the curve `t`, by concavity
and monotonicity of `h`. -/
theorem IsNeoclassical.one_le_of_covers {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
    (hP : ∀ t, P t ∈ orthant) {x : ℝ × ℝ} (hx : x ∈ quadrant) {t s r : Fin T}
    (hc : Covers P t s r) (hs : 1 ≤ h (hadamard (P s) x)) (hr : 1 ≤ h (hadamard (P r) x)) :
    1 ≤ h (hadamard (P t) x) := by
  obtain ⟨q, ⟨a, b, ha, hb, hab, rfl⟩, hq⟩ := hc
  have hu := hadamard_mem_quadrant (orthant_subset_quadrant (hP s)) hx
  have hv := hadamard_mem_quadrant (orthant_subset_quadrant (hP r)) hx
  have e : a • hadamard (P s) x + b • hadamard (P r) x = hadamard (a • P s + b • P r) x := by
    ext <;> simp [hadamard] <;> ring
  have hconc := hh.concaveOn.2 hu hv ha hb hab
  have hqx := hh.concaveOn.1 hu hv ha hb hab
  rw [e] at hconc hqx
  have hxq := mem_quadrant.mp hx
  have hq' := Prod.le_def.1 hq
  have hd : hadamard (P t) x - hadamard (a • P s + b • P r) x ∈ quadrant := mem_quadrant.2
    ⟨by simp only [hadamard, Prod.fst_sub]; nlinarith [mul_nonneg (sub_nonneg.2 hq'.1) hxq.1],
      by simp only [hadamard, Prod.snd_sub]; nlinarith [mul_nonneg (sub_nonneg.2 hq'.2) hxq.2]⟩
  have hmono := hh.mono hqx hd
  rw [add_sub_cancel] at hmono
  simp only [smul_eq_mul] at hconc
  nlinarith

/-- **Lemma "`Sp(h, P) ⊆ Sp(P)`"** for every `h ∈ Φ₂` and any positive prices:
if `S ∈ Sp(h, P)` and `t ∈ S` covered `s, r ∉ S`, then `A_t ⊆ A_s ∪ A_r` would force `s` or `r`
into `S`. -/
theorem IsNeoclassical.spectrum_subset_reachableSpectra {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
    (hP : ∀ t, P t ∈ orthant) : spectrum h P ⊆ reachableSpectra P := by
  intro S ⟨x, hx⟩
  obtain ⟨hxo, hspec⟩ := interior_subset hx
  intro t ht s hs r hr hc
  have h1 := hh.one_le_of_covers hP (orthant_subset_quadrant hxo) hc
    (not_lt.mp fun h => hs ((hspec s).2 h)) (not_lt.mp fun h => hr ((hspec r).2 h))
  linarith [(hspec t).1 ht]

/-! ### One reachable spectrum -/

/-- Strict inequalities at a point `x` put `S` into the spectrum: `x` lies in the interior of the
chamber `R_S` (`mem_interior_specRegion`). -/
theorem mem_spectrum_of_lt_of_lt {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g orthant)
    (hP : ∀ t, P t ∈ orthant) {S : Finset (Fin T)} {x : ℝ × ℝ} (hx : x ∈ orthant)
    (hlt : ∀ t ∈ S, g (hadamard (P t) x) < 1) (hgt : ∀ t ∉ S, 1 < g (hadamard (P t) x)) :
    S ∈ spectrum g P := by
  refine ⟨x, mem_interior_specRegion hg hP ⟨hx, fun t => ⟨hlt t, fun h => by_contra fun ht =>
    (hgt t ht).not_gt h⟩⟩ fun t => ?_⟩
  by_cases ht : t ∈ S
  · exact (hlt t ht).ne
  · exact (hgt t ht).ne'

/-- `∅ ∈ Sp(h, P)` for every `h ∈ Φ̂₂` (used in `lem:patch`): far along the diagonal all values
`h (p_t ∘ x)` exceed `1`. -/
theorem IsPosNeoclassical.empty_mem_spectrum {h : ℝ × ℝ → ℝ} (hh : IsPosNeoclassical h)
    (hP : ∀ t, P t ∈ orthant) : ∅ ∈ spectrum h P := by
  have hpos (t) : 0 < h (P t) := hh.pos _ (orthant_subset_quadrant (hP t))
    fun e => (mem_orthant.1 (hP t)).1.ne' (congrArg Prod.fst e)
  obtain ⟨c, hc, hc0⟩ := ((eventually_all.2 fun t => eventually_gt_atTop (1 / h (P t))).and
    (eventually_gt_atTop 0)).exists
  have h1 : ((1 : ℝ), (1 : ℝ)) ∈ orthant := mem_orthant.2 ⟨one_pos, one_pos⟩
  refine mem_spectrum_of_lt_of_lt (hh.continuousOn.mono orthant_subset_quadrant) hP
    (smul_mem_orthant hc0 h1) (by simp) fun t _ => ?_
  have e : hadamard (P t) (c • ((1 : ℝ), (1 : ℝ))) = c • P t := by
    rw [hadamard_smul]; simp [hadamard]
  rw [e, hh.homogeneous c hc0 _ (orthant_subset_quadrant (hP t))]
  exact (div_lt_iff₀ (hpos t)).1 (hc t)

/-- Proof of the second lemma, first step: for `t ∈ S ∈ Sp(P)` and `s ∉ S`, `t` does not cover
the pair `s, s`, so `p_s ≰ p_t`: `p¹_s > p¹_t` or `p²_s > p²_t`. -/
theorem IsReachable.lt_or_lt {S : Finset (Fin T)} (hS : IsReachable P S) {t : Fin T}
    (ht : t ∈ S) {s : Fin T} (hs : s ∉ S) : (P t).1 < (P s).1 ∨ (P t).2 < (P s).2 := by
  by_contra hcon
  push_neg at hcon
  exact hS t ht s hs s hs ⟨P s, left_mem_segment ℝ _ _, Prod.le_def.2 hcon⟩

/-- Proof of the second lemma, the slope bounds: for `t ∈ S ∈ Sp(P)` and `r, s ∉ S` with
`p¹_r > p¹_t > p¹_s`, every lower bound for `σ_t` is below every upper bound,
`(p²_t - p²_r) / (p¹_r - p¹_t) < (p²_s - p²_t) / (p¹_t - p¹_s)`. The point
`q = λ p_s + (1 - λ) p_r`, `λ = (p¹_r - p¹_t) / (p¹_r - p¹_s)`, of the segment has `q¹ = p¹_t`, and
`t` does not cover `s, r`, so `q² > p²_t`. -/
theorem IsReachable.slope_lt {S : Finset (Fin T)} (hS : IsReachable P S) {t : Fin T}
    (ht : t ∈ S) {s r : Fin T} (hs : s ∉ S) (hr : r ∉ S) (hst : (P s).1 < (P t).1)
    (htr : (P t).1 < (P r).1) :
    ((P t).2 - (P r).2) / ((P r).1 - (P t).1) < ((P s).2 - (P t).2) / ((P t).1 - (P s).1) := by
  by_contra hcon
  push_neg at hcon
  set d1 : ℝ := (P t).1 - (P s).1 with hd1def
  set d2 : ℝ := (P r).1 - (P t).1 with hd2def
  have hd1 : 0 < d1 := sub_pos.2 hst
  have hd2 : 0 < d2 := sub_pos.2 htr
  rw [div_le_div_iff₀ hd1 hd2] at hcon
  -- `q = λ p_s + (1 - λ) p_r` with `λ = d2 / (d1 + d2)` has `q¹ = p¹_t` and `q² ≤ p²_t`
  set μ : ℝ := d2 / (d1 + d2) with hμdef
  have hne : d1 + d2 ≠ 0 := by positivity
  have h1μ : 1 - μ = d1 / (d1 + d2) := by rw [hμdef]; field_simp; ring
  have hts : (P t).1 = (P s).1 + d1 := by rw [hd1def]; ring
  have htr' : (P r).1 = (P t).1 + d2 := by rw [hd2def]; ring
  have hq1 : (μ • P s + (1 - μ) • P r).1 = (P t).1 := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hμdef]
    rw [hts, htr']; field_simp; ring
  have hq2 : (μ • P s + (1 - μ) • P r).2 ≤ (P t).2 := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [h1μ, hμdef]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_le_iff₀ (by positivity)]
    nlinarith [hcon]
  exact hS t ht s hs r hr ⟨_, ⟨μ, 1 - μ, div_nonneg hd2.le (by positivity),
    h1μ ▸ div_nonneg hd1.le (by positivity), by ring, rfl⟩, Prod.le_def.2 ⟨hq1.le, hq2⟩⟩

/-- Proof of the second lemma, the slope `σ_t > 0`: `σ_t (p¹_s - p¹_t) + (p²_s - p²_t) > 0`, i.e.
`⟨(σ_t, 1), p_t⟩ < ⟨(σ_t, 1), p_s⟩`, for all `s ∉ S`. Take `σ_t` above `0` and all lower bounds
and below all upper bounds (`IsReachable.slope_lt`). -/
theorem IsReachable.exists_slope {S : Finset (Fin T)} (hS : IsReachable P S) {t : Fin T}
    (ht : t ∈ S) : ∃ σ : ℝ, 0 < σ ∧ ∀ s ∉ S, ip (σ, 1) (P t) < ip (σ, 1) (P s) := by
  classical
  -- `A`: lower bounds `L a` for `σ`; `B`: upper bounds `U b`
  set A := Finset.univ.filter fun a : Fin T => a ∉ S ∧ (P t).1 < (P a).1
  set B := Finset.univ.filter fun b : Fin T => b ∉ S ∧ (P b).1 < (P t).1
  set L : Fin T → ℝ := fun a => ((P t).2 - (P a).2) / ((P a).1 - (P t).1) with hL
  set U : Fin T → ℝ := fun b => ((P b).2 - (P t).2) / ((P t).1 - (P b).1) with hU
  -- `lo = max (0, L a)`, `hi = min (lo + 2, U b)`, and `lo < hi`
  set lo := (insert 0 (A.image L)).max' (Finset.insert_nonempty _ _)
  have hlo0 : 0 ≤ lo := Finset.le_max' _ 0 (Finset.mem_insert_self _ _)
  have hloA : ∀ a ∈ A, L a ≤ lo := fun a ha =>
    Finset.le_max' _ (L a) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem L ha))
  have hUlo : ∀ b ∈ B, lo < U b := by
    intro b hb
    obtain ⟨-, hbS, hblt⟩ := Finset.mem_filter.1 hb
    refine (Finset.max'_lt_iff _ _).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · have := (hS.lt_or_lt ht hbS).resolve_left (not_lt.2 hblt.le)
      exact div_pos (by linarith) (by linarith)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨-, haS, halt⟩ := Finset.mem_filter.1 ha
      exact hS.slope_lt ht hbS haS hblt halt
  set hi := (insert (lo + 2) (B.image U)).min' (Finset.insert_nonempty _ _)
  have hlohi : lo < hi := by
    refine (Finset.lt_min'_iff _ _).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · linarith
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      exact hUlo b hb
  have hhiB : ∀ b ∈ B, hi ≤ U b := fun b hb =>
    Finset.min'_le _ (U b) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem U hb))
  refine ⟨(lo + hi) / 2, by linarith, fun s hs => ?_⟩
  simp only [ip]
  rcases lt_trichotomy (P t).1 (P s).1 with hts | hts | hts
  · have h' : L s < (lo + hi) / 2 := by
      linarith [hloA s (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hts⟩)]
    rw [hL, div_lt_iff₀ (by linarith)] at h'
    nlinarith
  · have := (hS.lt_or_lt ht hs).resolve_left hts.not_lt
    rw [hts]; linarith
  · have h' : (lo + hi) / 2 < U s := by
      linarith [hhiB s (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, hts⟩)]
    rw [hU, lt_div_iff₀ (by linarith)] at h'
    nlinarith

/-- Proof of the second lemma, the vector `ξ_t = c_t (σ_t, 1) ∈ ℝ²₊₊` with
`⟨ξ_t, p_t⟩ < 1 < ⟨ξ_t, p_s⟩` for all `s ∉ S`: `c_t = 2 / (⟨(σ_t, 1), p_t⟩ + m)`, `m` the minimum
of `⟨(σ_t, 1), p_s⟩` over `s ∉ S` (`IsReachable.exists_slope`). -/
theorem IsReachable.exists_vector (hP : ∀ t, P t ∈ orthant) {S : Finset (Fin T)}
    (hS : IsReachable P S) {t : Fin T} (ht : t ∈ S) :
    ∃ ξ : ℝ × ℝ, ξ ∈ orthant ∧ ip ξ (P t) < 1 ∧ ∀ s ∉ S, 1 < ip ξ (P s) := by
  classical
  obtain ⟨σ, hσ, hσt⟩ := hS.exists_slope ht
  set a : ℝ := ip (σ, 1) (P t) with ha
  have ha0 : 0 < a := by
    have := mem_orthant.1 (hP t); simp only [ha, ip]; nlinarith
  -- `m = min (2a, ⟨(σ, 1), p_s⟩ for s ∉ S)`, so `a < m ≤ ⟨(σ, 1), p_s⟩`
  set F : Finset ℝ := insert (2 * a) ((Finset.univ.filter (· ∉ S)).image fun s => ip (σ, 1) (P s))
  set m : ℝ := F.min' (Finset.insert_nonempty _ _)
  have hmF : ∀ s ∉ S, m ≤ ip (σ, 1) (P s) := fun s hs => F.min'_le _ (Finset.mem_insert_of_mem
    (Finset.mem_image.2 ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, hs⟩, rfl⟩))
  have ham : a < m := by
    rcases Finset.mem_insert.1 (F.min'_mem (Finset.insert_nonempty _ _)) with h | h
    · rw [show m = 2 * a from h]; linarith
    · obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 h
      rw [show m = ip (σ, 1) (P s) from hse.symm]; exact hσt s (Finset.mem_filter.1 hs).2
  have hpos : 0 < a + m := by linarith
  -- `ξ_t = c_t (σ_t, 1)` with `c_t = 2 / (a + m)`
  have e (p : ℝ × ℝ) : ip (2 / (a + m) * σ, 2 / (a + m)) p = 2 * ip (σ, 1) p / (a + m) := by
    simp only [ip]; ring
  refine ⟨(2 / (a + m) * σ, 2 / (a + m)), mem_orthant.2 ⟨by positivity, by positivity⟩, ?_,
    fun s hs => ?_⟩
  · rw [e, ← ha, div_lt_one hpos]; linarith
  · rw [e, lt_div_iff₀ hpos]; linarith [hmF s hs]

/-- **Lemma: every `S ∈ Sp(P)` lies in `Sp(h, P)` for a polygonal `h = min_k ⟨ξ_k, ·⟩ ∈ Φ̂₂`**
for any positive prices. Proof: `h = min_{t ∈ S} ⟨ξ_t, ·⟩` with the vectors of
`IsReachable.exists_vector`; at `x = (1, 1)`, `h (p_t) < 1` for `t ∈ S` and `h (p_s) > 1` for
`s ∉ S` (`mem_spectrum_of_lt_of_lt`). For `S = ∅` any `h ∈ Φ̂₂` works
(`IsPosNeoclassical.empty_mem_spectrum`). -/
theorem IsReachable.exists_polyMin (hP : ∀ t, P t ∈ orthant) {S : Finset (Fin T)}
    (hS : IsReachable P S) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (ξ : K → ℝ × ℝ),
      (∀ k, ξ k ∈ orthant) ∧ S ∈ spectrum (polyMin ξ) P := by
  classical
  have h1 : ((1 : ℝ), (1 : ℝ)) ∈ orthant := mem_orthant.2 ⟨one_pos, one_pos⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨Unit, inferInstance, inferInstance, fun _ => (1, 1), fun _ => h1,
      (isPosNeoclassical_polyMin fun _ => h1).empty_mem_spectrum hP⟩
  have : Nonempty S := hne.to_subtype
  choose ξ hξ hlt hgt using fun t : S => hS.exists_vector hP t.2
  have e (t : Fin T) : hadamard (P t) (1, 1) = P t := by simp [hadamard]
  refine ⟨S, inferInstance, inferInstance, ξ, hξ, mem_spectrum_of_lt_of_lt
    ((isPosNeoclassical_polyMin hξ).continuousOn.mono orthant_subset_quadrant) hP h1
    (fun t ht => ?_) fun s hs => ?_⟩
  · rw [e]; exact (polyMin_le ξ _ ⟨t, ht⟩).trans_lt (hlt _)
  · obtain ⟨j, hj⟩ := exists_ip_eq_polyMin ξ (hadamard (P s) (1, 1))
    rw [← hj, e]; exact hgt j s hs

/-! ### Patching -/

/-- In `lem:patch`, the transported vector `ξ̃ = (ξ¹ α⁻¹, ξ² α)` at the point `p ∘ (α, α⁻¹)` gives
the value of `ξ` at `p`. -/
theorem ip_transport_self {α : ℝ} (hα : α ≠ 0) (ξ p : ℝ × ℝ) :
    ip (ξ.1 * α⁻¹, ξ.2 * α) (hadamard p (α, α⁻¹)) = ip ξ p := by
  simp only [ip, hadamard]
  field_simp

/-- In `lem:patch`, a vector transported to `(α, α⁻¹)` is large at another point `(β, β⁻¹)`:
if `β ≥ M α` or `α ≥ M β`, then
`⟨ξ̃, p ∘ (β, β⁻¹)⟩ = ξ¹ p¹ β / α + ξ² p² α / β ≥ M min (ξ¹ p¹, ξ² p²)`. -/
theorem le_ip_transport {α β M : ℝ} (hα : 0 < α) (hβ : 0 < β) (hM : 0 ≤ M)
    (hαβ : M * α ≤ β ∨ M * β ≤ α) {ξ p : ℝ × ℝ} (hξ : ξ ∈ orthant) (hp : p ∈ orthant) :
    M * min (ξ.1 * p.1) (ξ.2 * p.2) ≤ ip (ξ.1 * α⁻¹, ξ.2 * α) (hadamard p (β, β⁻¹)) := by
  obtain ⟨hξ1, hξ2⟩ := mem_orthant.1 hξ
  obtain ⟨hp1, hp2⟩ := mem_orthant.1 hp
  have e : ip (ξ.1 * α⁻¹, ξ.2 * α) (hadamard p (β, β⁻¹)) =
      β / α * (ξ.1 * p.1) + α / β * (ξ.2 * p.2) := by simp only [ip, hadamard]; ring
  have h1 : 0 < β / α * (ξ.1 * p.1) := by positivity
  have h2 : 0 < α / β * (ξ.2 * p.2) := by positivity
  rw [e]
  rcases hαβ with h | h
  · have := mul_le_mul_of_nonneg_right ((le_div_iff₀ hα).2 h) (mul_pos hξ1 hp1).le
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left (ξ.1 * p.1) (ξ.2 * p.2)) hM]
  · have := mul_le_mul_of_nonneg_right ((le_div_iff₀ hβ).2 h) (mul_pos hξ2 hp2).le
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right (ξ.1 * p.1) (ξ.2 * p.2)) hM]

/-- **Lemma `lem:patch` (склейка)**: for `S_1, …, S_k ∈ Sp(P)` one polygonal
`h = min_k ⟨ξ_k, ·⟩ ∈ Φ̂₂` has `S_1, …, S_k ∈ Sp(h, P)`, for any positive prices.

Proof: vectors `ξ_{i,t}`, `t ∈ S_i`, from `IsReachable.exists_vector`; `M ≥ 1` with
`M min (ξ¹_{i,t} p¹_s, ξ²_{i,t} p²_s) > 1` for all `i, t, s`; `α_i = M^i`, `x_i = (α_i, α_i⁻¹)`
and `h = min_{i, t ∈ S_i} ⟨ξ̃_{i,t}, ·⟩` with `ξ̃_{i,t} = (ξ¹_{i,t} α_i⁻¹, ξ²_{i,t} α_i)`. At
`p_t ∘ x_i` the vectors of copy `i` give `⟨ξ_{i,t}, p_t⟩` (`ip_transport_self`), those of the
other copies give `> 1` (`le_ip_transport`), so `x_i` is in the chamber `R_{S_i}`
(`mem_spectrum_of_lt_of_lt`). An empty `S_i` needs no separate treatment as long as some vector
exists; if there are none, all `S_i` are empty and `∅ ∈ Sp(h, P)` for every `h ∈ Φ̂₂`
(`IsPosNeoclassical.empty_mem_spectrum`). -/
theorem exists_polyMin_patch (hP : ∀ t, P t ∈ orthant) {k : ℕ} (S : Fin k → Finset (Fin T))
    (hS : ∀ i, IsReachable P (S i)) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (ξ : K → ℝ × ℝ),
      (∀ j, ξ j ∈ orthant) ∧ ∀ i, S i ∈ spectrum (polyMin ξ) P := by
  classical
  -- the vectors are indexed by the pairs `(i, t)` with `t ∈ S_i`
  by_cases hK : ∃ i, ∃ t, t ∈ S i
  swap
  · -- no vectors: all `S_i` are empty
    push_neg at hK
    have h1 : ((1 : ℝ), (1 : ℝ)) ∈ orthant := mem_orthant.2 ⟨one_pos, one_pos⟩
    refine ⟨Unit, inferInstance, inferInstance, fun _ => (1, 1), fun _ => h1, fun i => ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem.2 (hK i)]
    exact (isPosNeoclassical_polyMin fun _ => h1).empty_mem_spectrum hP
  set K := {p : Fin k × Fin T // p.2 ∈ S p.1}
  obtain ⟨i₀, t₀, h₀⟩ := hK
  have : Nonempty K := ⟨⟨(i₀, t₀), h₀⟩⟩
  -- `ξ_{i,t}` from the one-set lemma
  choose η hηo hηt hηs using fun j : K => (hS j.1.1).exists_vector hP j.2
  -- `M ≥ 1` with `M min (ξ¹_{i,t} p¹_s, ξ²_{i,t} p²_s) > 1`
  obtain ⟨M, hM, hM1⟩ := ((eventually_all.2 fun j : K => eventually_all.2 fun s : Fin T =>
    eventually_gt_atTop (1 / min ((η j).1 * (P s).1) ((η j).2 * (P s).2))).and
      (eventually_ge_atTop 1)).exists
  have hMsep (j : K) (s : Fin T) : 1 < M * min ((η j).1 * (P s).1) ((η j).2 * (P s).2) := by
    obtain ⟨h1, h2⟩ := mem_orthant.1 (hηo j)
    obtain ⟨h3, h4⟩ := mem_orthant.1 (hP s)
    exact (div_lt_iff₀ (lt_min (mul_pos h1 h3) (mul_pos h2 h4))).1 (hM j s)
  have hM0 : 0 < M := one_pos.trans_le hM1
  -- `α_i = M^i`, `x_i = (α_i, α_i⁻¹)`, `ξ̃_{i,t} = (ξ¹_{i,t} α_i⁻¹, ξ²_{i,t} α_i)`
  set α : Fin k → ℝ := fun i => M ^ (i : ℕ) with hα
  have hα0 (i) : 0 < α i := pow_pos hM0 _
  set ξ : K → ℝ × ℝ := fun j => ((η j).1 * (α j.1.1)⁻¹, (η j).2 * α j.1.1)
  have hξo (j) : ξ j ∈ orthant := by
    obtain ⟨h1, h2⟩ := mem_orthant.1 (hηo j)
    exact mem_orthant.2 ⟨mul_pos h1 (inv_pos.2 (hα0 _)), mul_pos h2 (hα0 _)⟩
  refine ⟨K, inferInstance, inferInstance, ξ, hξo, fun i => mem_spectrum_of_lt_of_lt
    ((isPosNeoclassical_polyMin hξo).continuousOn.mono orthant_subset_quadrant) hP
    (x := (α i, (α i)⁻¹)) (mem_orthant.2 ⟨hα0 i, inv_pos.2 (hα0 i)⟩) (fun t ht => ?_)
    fun s hs => ?_⟩
  · -- `t ∈ S_i`: the own vector `ξ̃_{i,t}` gives `⟨ξ_{i,t}, p_t⟩ < 1`
    exact (polyMin_le ξ _ ⟨(i, t), ht⟩).trans_lt
      ((ip_transport_self (hα0 i).ne' _ _).trans_lt (hηt ⟨(i, t), ht⟩))
  · -- `s ∉ S_i`: own vectors by the choice of `ξ_{i,t}`, other copies by the choice of `M`
    obtain ⟨⟨⟨i', t'⟩, h'⟩, hj⟩ := exists_ip_eq_polyMin ξ (hadamard (P s) (α i, (α i)⁻¹))
    rw [← hj]
    by_cases hii : i' = i
    · subst hii
      exact (ip_transport_self (hα0 i').ne' _ _).symm ▸ hηs ⟨(i', t'), h'⟩ s hs
    · have hαβ : M * α i' ≤ α i ∨ M * α i ≤ α i' := by
        simp only [hα, ← pow_succ']
        rcases lt_or_gt_of_ne (Fin.val_injective.ne hii) with h | h
        · exact .inl (pow_le_pow_right₀ hM1 h)
        · exact .inr (pow_le_pow_right₀ hM1 h)
      exact (hMsep _ s).trans_le
        (le_ip_transport (hα0 i') (hα0 i) hM0.le hαβ (hηo ⟨(i', t'), h'⟩) (hP s))

/-! ### The cone of reachable spectra -/

/-- **Direction `→` of `thm:admissible-cone`**, without general position: an output realized by a
neoclassical `h` at positive prices lies in `cone {1_S | S ∈ Sp(P)}` (`lem:signature-points` and
`Sp(h, P) ⊆ Sp(P)`). -/
theorem Realizes.mem_span_reachableSpectra {h : ℝ × ℝ → ℝ} {y : Fin T → ℝ}
    (hR : Realizes h P y) (hh : IsNeoclassical h) (hP : ∀ t, P t ∈ orthant) (hy : ∀ t, 0 ≤ y t) :
    y ∈ PointedCone.span ℝ
      ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) '' reachableSpectra P) := by
  rw [hh.realizes_iff_mem_span hP hy] at hR
  exact Submodule.span_mono (image_mono (hh.spectrum_subset_reachableSpectra hP)) hR

/-- A neoclassically solvable output at positive prices lies in `cone {1_S | S ∈ Sp(P)}`;
general position of `P` is not needed. -/
theorem NeoSolvable.mem_span_reachableSpectra {y : Fin T → ℝ} (hN : NeoSolvable P y)
    (hP : ∀ t, P t ∈ orthant) (hy : ∀ t, 0 ≤ y t) :
    y ∈ PointedCone.span ℝ
      ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) '' reachableSpectra P) := by
  obtain ⟨h, hh, hev⟩ := hN
  exact hev.self_of_nhds.mem_span_reachableSpectra hh hP hy


/-- For prices in general position some `h ∈ Φ̂₂` in general position with `P` has
`Sp(P) ⊆ Sp(h, P)`: `lem:patch` for the whole finite family `Sp(P)`, then `lem:gp-approx`
(`PricesGeneralPosition.exists_spectrum_subset`). -/
theorem PricesGeneralPosition.exists_reachableSpectra_subset (hP : PricesGeneralPosition P) :
    ∃ h, IsPosNeoclassical h ∧ GeneralPosition h P ∧ reachableSpectra P ⊆ spectrum h P := by
  classical
  set 𝒮 := Finset.univ.filter fun S : Finset (Fin T) => IsReachable P S
  obtain ⟨K, _, _, ξ, hξ, hspec⟩ :=
    exists_polyMin_patch hP.mem_orthant (fun i => (𝒮.equivFin.symm i : Finset (Fin T)))
      fun i => (Finset.mem_filter.1 (𝒮.equivFin.symm i).2).2
  obtain ⟨g, hg, hgP, hsub⟩ :=
    hP.exists_spectrum_subset (isPosNeoclassical_polyMin hξ).toIsNeoclassical
  refine ⟨g, hg, hgP, fun S hS => hsub ?_⟩
  simpa using hspec (𝒮.equivFin ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩⟩)

/-- **Theorem `thm:admissible-cone`**: for prices in general position, outputs `y ≥ 0` are
regularly solvable iff `y ∈ cone {1_S | S ∈ Sp(P)}`.

Proof: `→` holds without general position (`Realizes.mem_span_reachableSpectra`); `←` by the same lemma for the `h` in general position with
`Sp(P) ⊆ Sp(h, P)` (`lem:patch` and `lem:gp-approx`,
`PricesGeneralPosition.exists_reachableSpectra_subset`). -/
theorem PricesGeneralPosition.regularlySolvable_iff_mem_span_reachableSpectra
    (hP : PricesGeneralPosition P) {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) :
    RegularlySolvable P y ↔ y ∈ PointedCone.span ℝ
      ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) '' reachableSpectra P) := by
  constructor
  · rintro ⟨h, hh, -, hreal⟩
    exact hreal.mem_span_reachableSpectra hh.toIsNeoclassical hP.mem_orthant hy
  · intro hmem
    obtain ⟨h, hh, hhP, hsub⟩ := hP.exists_reachableSpectra_subset
    exact ⟨h, hh, hhP, (hh.toIsNeoclassical.realizes_iff_mem_span hP.mem_orthant hy).2
      (Submodule.span_mono (image_mono hsub) hmem)⟩

/-- **Theorem `thm:admissible-cone`**, neoclassical form: for prices in general position,
outputs `y ≥ 0` are neoclassically solvable iff `y ∈ cone {1_S | S ∈ Sp(P)}`
(`thm:regular-solvability`, `PricesGeneralPosition.neoSolvable_iff_regularlySolvable`). -/
theorem PricesGeneralPosition.neoSolvable_iff_mem_span_reachableSpectra
    (hP : PricesGeneralPosition P) {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) :
    NeoSolvable P y ↔ y ∈ PointedCone.span ℝ
      ((fun S : Finset (Fin T) => (S : Set (Fin T)).indicator 1) '' reachableSpectra P) := by
  rw [hP.neoSolvable_iff_regularlySolvable, hP.regularlySolvable_iff_mem_span_reachableSpectra hy]

/-- **Remark after `thm:admissible-cone`**: for prices in general position some `h ∈ Φ̂₂` in
general position with `P` has `Sp(h, P) = Sp(P)`, so every regularly solvable output is realized
by this one `h` (only the measure depends on `y`). -/
theorem PricesGeneralPosition.exists_spectrum_eq_reachableSpectra (hP : PricesGeneralPosition P) :
    ∃ h, IsPosNeoclassical h ∧ GeneralPosition h P ∧ spectrum h P = reachableSpectra P := by
  obtain ⟨h, hh, hhP, hsub⟩ := hP.exists_reachableSpectra_subset
  exact ⟨h, hh, hhP, (hh.toIsNeoclassical.spectrum_subset_reachableSpectra hP.mem_orthant).antisymm
    hsub⟩

end NeoTiling
