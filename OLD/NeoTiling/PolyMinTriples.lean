import NeoTiling.PriceGeneralPosition

/-!
# Generic triples

The genericity condition `GenericLines` (all quadruples of coefficient vectors) is used in
`generalPosition_polyMin` only on determinants `det (a_α - a_β, a_α - a_γ)`. Here the weaker
condition `GenericTriples` on such triples is shown to suffice
(`generalPosition_polyMin_of_triples`).
-/

namespace NeoTiling

section Triples

variable {ι : Type*} {T : ℕ}

/-- Generic triples: a determinant `det (a_α - a_β, a_α - a_γ)` of differences of coefficient
vectors `a_{(j,t)} = ξ_j ∘ p_t` vanishes at `ξ` only if it vanishes identically in `ξ`. -/
def GenericTriples (ξ : ι → ℝ × ℝ) (P : Fin T → ℝ × ℝ) : Prop :=
  ∀ α β γ : ι × Fin T, (∃ ζ, det2 (coefDiff P α β ζ) (coefDiff P α γ ζ) ≠ 0) →
    det2 (coefDiff P α β ξ) (coefDiff P α γ ξ) ≠ 0

/-- Generic lines are in particular generic triples. -/
theorem GenericLines.genericTriples {ξ : ι → ℝ × ℝ} {P : Fin T → ℝ × ℝ}
    (hG : GenericLines ξ P) : GenericTriples ξ P :=
  fun α β γ => hG α β α γ

/-- `GenericLines.coef_ne` under generic triples. -/
theorem GenericTriples.coef_ne {ξ : ι → ℝ × ℝ} {P : Fin T → ℝ × ℝ} (hG : GenericTriples ξ P)
    (hP : PricesGeneralPosition P) (hξ : ∀ j, ξ j ∈ orthant) {s t : Fin T} (hst : s ≠ t)
    (j k : ι) : hadamard (ξ j) (P s) ≠ hadamard (ξ k) (P t) := fun heq => by
  classical
  rcases eq_or_ne j k with rfl | hjk
  · exact hst (hP.fst_injective (congrArg Prod.fst (hadamard_injective (hξ j) heq)))
  apply hG (j, s) (k, t) (j, t) ⟨Pi.single j (1, 0) + Pi.single k (0, 1), ?_⟩ <;>
    first | (simp [det2, heq]; done) | simp [det2, hadamard, hjk, hjk.symm,
      (Set.mem_Ioi.1 (hP.mem_orthant t).2).ne', sub_ne_zero.2 (hP.fst_injective.ne hst)]

/-- **When the triple determinant is not identically zero.** For pairwise distinct `α, β, γ` and
prices in general position, `det (a_α - a_β, a_α - a_γ)` vanishes identically in `ξ` iff the
three line indices coincide and the three prices are collinear. If the indices coincide, the
determinant is `ζ₁ ζ₂ det (p_α - p_β, p_α - p_γ)`; otherwise a witness `ζ` supported on two lines
with values `(1, 0)`, `(0, 1)` gives a nonzero determinant. -/
theorem exists_det2_coefDiff_ne_zero_iff [DecidableEq ι] {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) {α β γ : ι × Fin T} (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hβγ : β ≠ γ) :
    (∃ ζ : ι → ℝ × ℝ, det2 (coefDiff P α β ζ) (coefDiff P α γ ζ) ≠ 0) ↔
      ¬ (α.1 = β.1 ∧ α.1 = γ.1 ∧ det2 (P α.2 - P β.2) (P α.2 - P γ.2) = 0) := by
  obtain ⟨a, r⟩ := α; obtain ⟨b, s⟩ := β; obtain ⟨c, t⟩ := γ
  have hO := fun t => mem_orthant.1 (hP.mem_orthant t)
  have h1 {u v : Fin T} (h : u ≠ v) := hP.fst_injective.ne h
  have h2 {u v : Fin T} (h : u ≠ v) := hP.snd_injective.ne h
  constructor
  · rintro ⟨ζ, hζ⟩ ⟨rfl, rfl, hd⟩
    apply hζ
    simp only [coefDiff_apply, det2, hadamard, Prod.fst_sub, Prod.snd_sub] at hd ⊢
    linear_combination (ζ a).1 * (ζ a).2 * hd
  intro H
  simp only at H
  by_cases hab : a = b <;> by_cases hac : a = c
  · subst hab hac
    refine ⟨Pi.single a (1, 1), fun h => H ⟨rfl, rfl, ?_⟩⟩
    simpa [det2, hadamard] using h
  · subst hab
    have hrs : r ≠ s := fun h => hαβ (by rw [h])
    exact ⟨Pi.single a (1, 0) + Pi.single c (0, 1), by
      simp [det2, hadamard, hac, Ne.symm hac, (hO t).2.ne', sub_ne_zero.2 (h1 hrs)]⟩
  · subst hac
    have hrt : r ≠ t := fun h => hαγ (by rw [h])
    exact ⟨Pi.single a (1, 0) + Pi.single b (0, 1), by
      simp [det2, hadamard, hab, Ne.symm hab, (hO s).2.ne', sub_ne_zero.2 (h1 hrt)]⟩
  by_cases hbc : b = c
  · subst hbc
    have hst : s ≠ t := fun h => hβγ (by rw [h])
    exact ⟨Pi.single a (1, 0) + Pi.single b (0, 1), by
      simp only [coefDiff_apply, det2, hadamard, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hab, Pi.single_eq_of_ne' hab]
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
      intro h; apply (hO r).1.ne' ∘ (mul_eq_zero.1 · |>.resolve_right (sub_ne_zero.2 (h2 hst)))
      simp at h; linear_combination h⟩
  exact ⟨Pi.single b (1, 0) + Pi.single c (0, 1), by
    simp [det2, hadamard, hab, hac, hbc, Ne.symm hbc,
      (hO s).1.ne', (hO t).2.ne']⟩

variable [Fintype ι] [Nonempty ι] {ξ : ι → ℝ × ℝ} {P : Fin T → ℝ × ℝ}

/-- `exists_active` under generic triples: the triple is `α = (k,t)`, `β = (j,s)`,
`γ = (l,s)`. -/
theorem exists_active_of_triples (hξ : ∀ j, ξ j ∈ orthant) (hP : PricesGeneralPosition P)
    (hS : NoSharedLine ξ P) (hG : GenericTriples ξ P) {s t : Fin T} (hst : s ≠ t) {x : ℝ × ℝ}
    (hx : x ∈ pairIntersections (polyMin ξ) (P s) (P t)) :
    x ∈ orthant ∧ ∃ j k, ip (hadamard (ξ j) (P s)) x = 1 ∧ ip (hadamard (ξ k) (P t)) x = 1 ∧
      superdiff (fun y => polyMin ξ (hadamard (P s) y)) x ⊆ {hadamard (ξ j) (P s)} := by
  classical
  have hxo := (isPosNeoclassical_polyMin hξ).mem_orthant_of_mem_pairIntersections
    (hP.mem_orthant s) (hP.mem_orthant t) (hP.fst_injective.ne hst) (hP.snd_injective.ne hst) hx
  obtain ⟨j, hj⟩ := exists_ip_eq_polyMin ξ (hadamard (P s) x)
  obtain ⟨k, hk⟩ := exists_ip_eq_polyMin ξ (hadamard (P t) x)
  rw [ip_hadamard, hx.2.1] at hj
  rw [ip_hadamard, hx.2.2] at hk
  have hjk := hS.ne hξ hst hx hj hk
  refine ⟨hxo, j, k, hj, hk, ?_⟩
  rw [show (fun y => polyMin ξ (hadamard (P s) y)) = _ from funext (polyMin_hadamard ξ (P s))]
  refine superdiff_polyMin_subset hxo fun l hlj => hj ▸ lt_of_le_of_ne ?_ fun heq => ?_
  · simpa [ip_hadamard, hx.2.1] using polyMin_le ξ (hadamard (P s) x) l
  have hlk := hS.ne hξ hst hx heq.symm hk
  obtain ⟨hs1, hs2⟩ := mem_orthant.mp (hP.mem_orthant s)
  refine hG (k, t) (j, s) (l, s) ⟨Pi.single j (1, 0) + Pi.single l (0, 1), ?_⟩
    (det2_eq_zero_of_ip_eq_zero hxo (by simp [ip_sub, hj, hk])
      (by simp [ip_sub, ← heq, hk]))
  simp [det2, hadamard, hlj, hjk, hlk, Ne.symm hlj, hs1.ne', hs2.ne']

/-- **General position of a polygonal function under generic triples**: the proof of
`generalPosition_polyMin`, which uses genericity only on triples. -/
theorem generalPosition_polyMin_of_triples (hξ : ∀ j, ξ j ∈ orthant)
    (hP : PricesGeneralPosition P) (hS : NoSharedLine ξ P) (hG : GenericTriples ξ P) :
    GeneralPosition (polyMin ξ) P := by
  classical
  refine ⟨hP.mem_orthant, fun s t hst => ?_, fun s t hst x hx => ?_,
    fun r s t hrs hst hrt x hx ht => ?_⟩
  · refine (Set.finite_iUnion fun j => Set.finite_iUnion fun k => (subsingleton_solutions
      (hG.coef_ne hP hξ hst j k)).finite).subset fun z hz => ?_
    obtain ⟨-, j, k, hj, hk, -⟩ := exists_active_of_triples hξ hP hS hG hst hz
    exact Set.mem_iUnion₂.mpr ⟨j, k, hj, hk⟩
  · obtain ⟨hxo, j, -, -, -, hsupS⟩ := exists_active_of_triples hξ hP hS hG hst hx
    obtain ⟨-, j₂, -, -, -, hsupT⟩ := exists_active_of_triples hξ hP hS hG hst.symm
      (pairIntersections_comm (polyMin ξ) (P s) (P t) ▸ hx)
    exact ⟨hxo, Disjoint.mono hsupS hsupT
      (Set.disjoint_singleton.mpr (hG.coef_ne hP hξ hst j j₂))⟩
  obtain ⟨hxo, j, k, hj, hk, -⟩ := exists_active_of_triples hξ hP hS hG hrs hx
  obtain ⟨l, hl⟩ := exists_ip_eq_polyMin ξ (hadamard (P t) x)
  rw [ip_hadamard, ht] at hl
  have hjk := hS.ne hξ hrs hx hj hk
  have hjl := hS.ne hξ hrt ⟨hx.1, hx.2.1, ht⟩ hj hl
  have hkl := hS.ne hξ hst ⟨hx.1, hx.2.2, ht⟩ hk hl
  obtain ⟨hr1, -⟩ := mem_orthant.mp (hP.mem_orthant r)
  obtain ⟨-, hs2⟩ := mem_orthant.mp (hP.mem_orthant s)
  refine hG (j, r) (k, s) (l, t) ⟨Pi.single j (1, 0) + Pi.single k (0, 1), ?_⟩
    (det2_eq_zero_of_ip_eq_zero hxo (by simp [ip_sub, hj, hk])
      (by simp [ip_sub, hj, hl]))
  simp [det2, hadamard, hjk, hjk.symm, hjl.symm, hkl.symm, hr1.ne', hs2.ne']

end Triples

end NeoTiling
