import NeoTiling.GeneralPosition

/-!
# Neoclassical solvability

Notes, section 1, definition `def:neo-solvability`: demand sets (`demandSet`), realization
(`Realizes`) and neoclassical solvability (`NeoSolvable`).

Realization depends only on the signs of `h (p_t ∘ x) - 1` at finitely many points
(`SignaturePoints`): the unit level curves are null, so a realization yields signature points
(`exists_signaturePoints`), and signature points are always realized (`SignaturePoints.realizes`).
Main results: `IsNeoclassical.eventually_realizes` and `neoSolvable_iff_exists_pos`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace NeoTiling

/-! ### Definitions -/

/-- The demand set `A = {x ∈ ℝ²₊₊ | h (p ∘ x) < 1}` of the price `p`. -/
def demandSet (h : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ orthant ∧ h (hadamard p x) < 1}

/-- `h` realizes outputs `y` at prices `P`: some measure absolutely continuous w.r.t. Lebesgue
gives mass `y t` to the demand set of `P t`. -/
def Realizes (h : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ μ : Measure (ℝ × ℝ), μ ≪ volume ∧ ∀ t, μ (demandSet h (P t)) = ENNReal.ofReal (y t)

/-- **Neoclassical solvability** (notes, `def:neo-solvability`): one neoclassical `h` realizes
`y` at all prices near `P`. -/
def NeoSolvable {T : ℕ} (P : Fin T → ℝ × ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ h : ℝ × ℝ → ℝ, IsNeoclassical h ∧ ∀ᶠ Q in 𝓝 P, Realizes h Q y

/-- *Signature points*: finitely many points of `ℝ²₊₊` off all curves `g (p_t ∘ x) = 1`, with
masses `m`, such that the mass of the points inside `A_t` is `y_t` for every `t`. -/
def SignaturePoints (g : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) (y : Fin T → ℝ)
    (s : Finset (ℝ × ℝ)) (m : ℝ × ℝ → ℝ≥0∞) : Prop :=
  (∀ x ∈ s, x ∈ orthant ∧ ∀ t, g (hadamard (P t) x) ≠ 1) ∧
    ∀ t, ∑ x ∈ s with g (hadamard (P t) x) < 1, m x = ENNReal.ofReal (y t)

/-- The signature of `x`: the set of `t` with `g (p_t ∘ x) < 1`. Its fibres in `ℝ²₊₊` are the
sign regions of the curves. -/
noncomputable def signature (g : ℝ × ℝ → ℝ) {T : ℕ} (P : Fin T → ℝ × ℝ) (x : ℝ × ℝ) :
    Finset (Fin T) :=
  {t | g (hadamard (P t) x) < 1}

/-! ### Level curves are null -/

/-- `hadamard p` commutes with scalar multiplication. -/
theorem hadamard_smul (p x : ℝ × ℝ) (c : ℝ) : hadamard p (c • x) = c • hadamard p x := by
  ext <;> simp [hadamard] <;> ring

/-- The orthant is closed under multiplication by a positive scalar. -/
theorem smul_mem_orthant {c : ℝ} (hc : 0 < c) {x : ℝ × ℝ} (hx : x ∈ orthant) : c • x ∈ orthant :=
  mem_orthant.mpr ⟨by simpa using mul_pos hc (mem_orthant.mp hx).1,
    by simpa using mul_pos hc (mem_orthant.mp hx).2⟩

/-- The unit level set of `h (p ∘ ·)` in `ℝ²₊₊` is Lebesgue null: the level sets for `c > 0` are
its dilations by `c`, pairwise disjoint, so only countably many of them have positive measure. -/
theorem IsNeoclassical.volume_levelSet_eq_zero {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
    {p : ℝ × ℝ} (hp : p ∈ orthant) :
    volume {x | x ∈ orthant ∧ h (hadamard p x) = 1} = 0 := by
  by_contra hne
  have hcont : ContinuousOn (fun x => h (hadamard p x)) orthant := hh.continuousOn.comp
    (by unfold hadamard; fun_prop) fun x hx => orthant_subset_quadrant (hadamard_mem_orthant hp hx)
  refine absurd ((Measure.countable_meas_level_set_pos₀ (μ := volume.restrict orthant)
    (hcont.aemeasurable isOpen_orthant.measurableSet).nullMeasurable).mono (s₁ := Ioi 0)
    fun c (hc : 0 < c) => ?_)
    fun H => by simpa using H.measure_zero volume
  -- the level `c` is the dilation by `c` of the level `1`
  have hset : {x | h (hadamard p x) = c} ∩ orthant =
      c • {x | x ∈ orthant ∧ h (hadamard p x) = 1} := by
    ext x
    have ho : x ∈ orthant ↔ c⁻¹ • x ∈ orthant := ⟨smul_mem_orthant (inv_pos.2 hc), fun h' => by
      simpa [smul_smul, hc.ne'] using smul_mem_orthant hc h'⟩
    rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_inter_iff, and_comm, ho]
    refine and_congr_right fun hx => ?_
    rw [mem_setOf_eq, hadamard_smul, hh.homogeneous _ (inv_pos.2 hc) _ (orthant_subset_quadrant
      (hadamard_mem_orthant hp (ho.2 hx))), inv_mul_eq_one₀ hc.ne', eq_comm]
  rw [mem_setOf_eq, Measure.restrict_apply' isOpen_orthant.measurableSet, hset,
    Measure.addHaar_smul_of_nonneg volume hc.le]
  exact ENNReal.mul_pos (by simpa using hc.ne') hne

/-! ### Signature points -/

section Signature

variable {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g orthant) {T : ℕ} {P : Fin T → ℝ × ℝ}
  (hP : ∀ t, P t ∈ orthant)
include hg hP

/-- `μ (A_t)` is the sum of the masses of the sign regions inside `A_t`. -/
theorem measure_demandSet_eq_sum (μ : Measure (ℝ × ℝ)) (t : Fin T) :
    μ (demandSet g (P t)) = ∑ S with t ∈ S, μ (orthant ∩ signature g P ⁻¹' {S}) := by
  have hU (u : Fin T) : MeasurableSet (orthant ∩ {x | g (hadamard (P u) x) < 1}) :=
    (ContinuousOn.isOpen_inter_preimage (hg.comp (by unfold hadamard; fun_prop)
      fun x hx => hadamard_mem_orthant (hP u) hx) isOpen_orthant isOpen_Iio).measurableSet
  rw [← measure_biUnion_finset (fun S _ S' _ hne => disjoint_left.2 fun x h h' =>
    hne (h.2.symm.trans h'.2)) fun S _ => ?_]
  · congr 1; ext x; simp [demandSet, signature, and_comm]
  convert isOpen_orthant.measurableSet.inter (MeasurableSet.iInter fun u =>
    measurableSet_setOf.2 ((measurable_const (a := u ∈ S)).iff (measurable_mem.2 (hU u))))
    using 1
  ext x; simp +contextual [signature, Finset.ext_iff, eq_comm]

/-- A realization at `P` with null curves yields signature points: one point off the curves in
each sign region of positive mass, carrying that mass. -/
theorem exists_signaturePoints
    (hnull : ∀ t, volume {x | x ∈ orthant ∧ g (hadamard (P t) x) = 1} = 0)
    {y : Fin T → ℝ} (hR : Realizes g P y) :
    ∃ (s : Finset (ℝ × ℝ)) (m : ℝ × ℝ → ℝ≥0∞), SignaturePoints g P y s m := by
  obtain ⟨μ, hμ, hy⟩ := hR
  classical
  set G : Finset (Finset (Fin T)) := {S | μ (orthant ∩ signature g P ⁻¹' {S}) ≠ 0}
  have hex (S) (hS : S ∈ G) :
      ∃ x ∈ orthant ∩ signature g P ⁻¹' {S}, ∀ t, g (hadamard (P t) x) ≠ 1 := by
    have hN := hμ (measure_iUnion_null hnull)
    obtain ⟨x, hx, hx'⟩ := nonempty_of_measure_ne_zero
      ((measure_diff_null hN).symm ▸ (Finset.mem_filter.1 hS).2)
    exact ⟨x, hx, fun t e => hx' (mem_iUnion.2 ⟨t, hx.1, e⟩)⟩
  choose! xS hxS hxne using hex
  have hσ (S) (hS : S ∈ G) : signature g P (xS S) = S := (hxS S hS).2
  refine ⟨G.image xS, fun x => μ (orthant ∩ signature g P ⁻¹' {signature g P x}),
    by simpa using fun S hS => ⟨(hxS S hS).1, hxne S hS⟩, fun t => ?_⟩
  rw [← hy t, measure_demandSet_eq_sum hg hP, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_image fun S hS S' hS' e => by rw [← hσ S hS, e, hσ S' hS'],
    ← Finset.sum_subset (Finset.subset_univ G) fun S _ hS => by simp_all [G]]
  exact Finset.sum_congr rfl fun S hS =>
    if_congr (by simpa [signature] using Finset.ext_iff.1 (hσ S hS) t) (by rw [hσ S hS]) rfl

omit hg hP in
/-- A value closer to `b` than `b` is to `1` lies on the same side of `1` as `b`. -/
theorem lt_one_iff_of_abs_sub_lt {a b : ℝ} (H : |a - b| < |b - 1|) :
    (a < 1 ↔ b < 1) ∧ a ≠ 1 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 H
  rcases abs_cases (b - 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at h1 h2 <;>
    exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, fun _ => by linarith⟩

omit hg hP in
/-- **Signatures depend only on signs.** Signature points of `g` at `P` are signature points of
`g'` at `Q` if every value `g' (q_t ∘ x)`, `x ∈ s`, is closer to `g (p_t ∘ x)` than this value
is to `1`. -/
theorem SignaturePoints.of_abs_sub_lt {y : Fin T → ℝ} {s : Finset (ℝ × ℝ)} {m : ℝ × ℝ → ℝ≥0∞}
    (H : SignaturePoints g P y s m) {g' : ℝ × ℝ → ℝ} {Q : Fin T → ℝ × ℝ}
    (hQ : ∀ x ∈ s, ∀ t, |g' (hadamard (Q t) x) - g (hadamard (P t) x)| <
      |g (hadamard (P t) x) - 1|) :
    SignaturePoints g' Q y s m := by
  have hs := fun x hx t => lt_one_iff_of_abs_sub_lt (hQ x hx t)
  refine ⟨fun x hx => ⟨(H.1 x hx).1, fun t => (hs x hx t).2⟩, fun t => ?_⟩
  rw [Finset.filter_congr fun x hx => (hs x hx t).1]
  exact H.2 t

omit hg hP in
/-- Signature points persist along any family of functions and prices whose values at the
finitely many points `q_t ∘ x`, `x ∈ s`, converge to those of `g` at `P`. -/
theorem SignaturePoints.eventually_of_tendsto {y : Fin T → ℝ} {s : Finset (ℝ × ℝ)}
    {m : ℝ × ℝ → ℝ≥0∞} (H : SignaturePoints g P y s m) {α : Type*} {l : Filter α}
    {G : α → ℝ × ℝ → ℝ} {Q : α → Fin T → ℝ × ℝ}
    (hl : ∀ x ∈ s, ∀ t, Tendsto (fun a => G a (hadamard (Q a t) x)) l
      (𝓝 (g (hadamard (P t) x)))) :
    ∀ᶠ a in l, SignaturePoints (G a) (Q a) y s m :=
  (s.eventually_all.2 fun x hx => eventually_all.2 fun t => Metric.tendsto_nhds.1 (hl x hx t) _
    (abs_pos.2 (sub_ne_zero.2 ((H.1 x hx).2 t)))).mono fun _ ha => H.of_abs_sub_lt ha

/-- Signature points at `P` stay signature points at nearby prices. -/
theorem SignaturePoints.eventually {y : Fin T → ℝ} {s : Finset (ℝ × ℝ)} {m : ℝ × ℝ → ℝ≥0∞}
    (H : SignaturePoints g P y s m) : ∀ᶠ Q in 𝓝 P, SignaturePoints g Q y s m :=
  H.eventually_of_tendsto (G := fun _ => g) (Q := id) fun x hx t =>
    ((hg.continuousAt (isOpen_orthant.mem_nhds (hadamard_mem_orthant (hP t) (H.1 x hx).1))).comp
      (f := fun Q : Fin T → ℝ × ℝ => hadamard (Q t) x) (by unfold hadamard; fun_prop)).tendsto

omit hg hP in
/-- Signature points stay signature points for `g + ε (x₁ + x₂)` with small `ε > 0`. -/
theorem SignaturePoints.exists_add_linear {y : Fin T → ℝ} {s : Finset (ℝ × ℝ)}
    {m : ℝ × ℝ → ℝ≥0∞} (H : SignaturePoints g P y s m) :
    ∃ ε > 0, SignaturePoints (fun z => g z + ε * (z.1 + z.2)) P y s m :=
  ((H.eventually_of_tendsto (Q := fun _ => P) (G := fun ε z => g z + ε * (z.1 + z.2))
    fun _ _ _ => ((Continuous.tendsto' (continuous_const.add (continuous_id.mul continuous_const))
      0 _ (by simp)).mono_left nhdsWithin_le_nhds)).and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists.imp fun _ h => ⟨h.2, h.1⟩

/-- Signature points are realized: put mass `m x` uniformly on a small ball around `x` on which
no sign `g (p_t ∘ ·) - 1` changes. -/
theorem SignaturePoints.realizes {y : Fin T → ℝ} {s : Finset (ℝ × ℝ)} {m : ℝ × ℝ → ℝ≥0∞}
    (H : SignaturePoints g P y s m) : Realizes g P y := by
  have hex (x) (hx : x ∈ s) : ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ orthant ∧
      ∀ t, (g (hadamard (P t) z) < 1 ↔ g (hadamard (P t) x) < 1) :=
    Metric.eventually_nhds_iff_ball.1 <| (isOpen_orthant.eventually_mem (H.1 x hx).1).and <|
      eventually_all.2 fun t => (Metric.tendsto_nhds.1 ((hg.continuousAt (isOpen_orthant.mem_nhds
        (hadamard_mem_orthant (hP t) (H.1 x hx).1))).comp (f := hadamard (P t))
        (by unfold hadamard; fun_prop)) _ (abs_pos.2 (sub_ne_zero.2 ((H.1 x hx).2 t)))).mono
        fun _ hz => (lt_one_iff_of_abs_sub_lt hz).1
  choose! r hr hrz using hex
  refine ⟨∑ x ∈ s, (m x / volume (Metric.ball x (r x))) • volume.restrict (Metric.ball x (r x)),
    fun A hA => by simp [fun B => Measure.absolutelyContinuous_of_le
      (Measure.restrict_le_self (s := B)) hA], fun t => ?_⟩
  rw [Measure.finset_sum_apply, ← H.2 t, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_ball]
  split_ifs with hlt
  · rw [(inter_eq_right (s := demandSet g (P t))).2 fun z hz =>
      ⟨(hrz x hx z hz).1, ((hrz x hx z hz).2 t).2 hlt⟩,
      ENNReal.div_mul_cancel (Metric.measure_ball_pos volume x (hr x hx)).ne' measure_ball_ne_top]
  · rw [(eq_empty_iff_forall_notMem (s := demandSet g (P t) ∩ _)).2 fun z hz =>
      hlt (((hrz x hx z hz.2).2 t).1 hz.1.2),
      measure_empty, mul_zero]

end Signature

/-! ### Solvability -/

/-- `h + ε (x₁ + x₂)` is strictly positive neoclassical for `ε > 0`. -/
theorem IsNeoclassical.isPosNeoclassical_add_linear {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h)
    {ε : ℝ} (hε : 0 < ε) : IsPosNeoclassical (fun z => h z + ε * (z.1 + z.2)) := by
  rw [isPosNeoclassical_iff_exists_linear_le]
  have hlin : ConcaveOn ℝ quadrant (fun z : ℝ × ℝ => ε * (z.1 + z.2)) := by
    refine ⟨hh.concaveOn.1, fun p _ q _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
    nlinarith [hab]
  refine ⟨⟨fun p hp => ?_, hh.continuousOn.add (by fun_prop), hh.concaveOn.add hlin,
    fun t ht p hp => ?_⟩, ε, ε, hε, hε, fun p hp => ?_⟩
  · have := hh.nonneg p hp
    obtain ⟨h1, h2⟩ := mem_quadrant.mp hp
    positivity
  · simp only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd]
    rw [hh.homogeneous t ht p hp]; ring
  · nlinarith [hh.nonneg p hp]

/-- **Realization at `P` gives realization near `P`.** The curves are null
(`volume_levelSet_eq_zero`), so a realization yields signature points
(`exists_signaturePoints`); they stay signature points near `P` (`SignaturePoints.eventually`)
and are realized there (`SignaturePoints.realizes`). -/
theorem IsNeoclassical.eventually_realizes {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h) {T : ℕ}
    {P : Fin T → ℝ × ℝ} (hP : ∀ t, P t ∈ orthant) {y : Fin T → ℝ} (hR : Realizes h P y) :
    ∀ᶠ Q in 𝓝 P, Realizes h Q y := by
  have hg : ContinuousOn h orthant := hh.continuousOn.mono orthant_subset_quadrant
  obtain ⟨s, m, H⟩ :=
    exists_signaturePoints hg hP (fun t => hh.volume_levelSet_eq_zero (hP t)) hR
  filter_upwards [H.eventually hg hP, eventually_mem_orthant hP] with Q hQ hQo
  exact hQ.realizes hg hQo

/-- **Solvability with a strictly positive `h`.** Outputs are solvable iff some strictly positive
neoclassical `h` realizes them at `P`. Proof: take signature points of a realizing `h`; they stay
signature points for `h + ε (x₁ + x₂)`, `ε > 0` small, which is strictly positive. -/
theorem neoSolvable_iff_exists_pos {T : ℕ} {P : Fin T → ℝ × ℝ} (hP : ∀ t, P t ∈ orthant)
    {y : Fin T → ℝ} :
    NeoSolvable P y ↔ ∃ h, IsPosNeoclassical h ∧ Realizes h P y := by
  refine ⟨fun ⟨h, hh, hev⟩ => ?_, fun ⟨h, hh, hR⟩ =>
    ⟨h, hh.toIsNeoclassical, hh.toIsNeoclassical.eventually_realizes hP hR⟩⟩
  obtain ⟨s, m, H⟩ := exists_signaturePoints (hh.continuousOn.mono orthant_subset_quadrant) hP
    (fun t => hh.volume_levelSet_eq_zero (hP t)) hev.self_of_nhds
  obtain ⟨ε, hε, Hε⟩ := H.exists_add_linear
  have hpos := hh.isPosNeoclassical_add_linear hε
  exact ⟨_, hpos, Hε.realizes (hpos.continuousOn.mono orthant_subset_quadrant) hP⟩

end NeoTiling
