import Algorithms.Cuts

/-!
# Blocking in the plane, and the minimal perturbation for a general cost

Part of `poly-hardness/` (not part of the `NeoTiling` library). Check with
`lake env lean poly-hardness/lean/PolyHardness/Blocking.lean` from the repository root.

`IsBlocked Q t R` (from `Algorithms/Cuts.lean`): some nonzero `ξ ≥ 0` has `⟨ξ, q_r - q_t⟩ ≥ 0`
for all `r ∈ R`. In the plane a witness is a point of a segment, so blocking is decided by pairs.

* `isBlocked_iff_pairs`: `t` is blocked by `R` iff it is blocked by every pair `{r, s} ⊆ R`
  (Helly's theorem on a segment).
* `isBlocked_pair_iff`: `t` is blocked by `{r, s}` iff `q_t` is weakly left of both, or weakly
  below both, or below a point of the segment `[q_r, q_s]` of a non-increasing segment.
* `IsBlocked.mono`: blocking survives lowering `q_t` and raising the `q_r`.
* `exists_pair_cover`: a set that is not weakly reachable has a point strictly covered by at most
  two points of its complement.
* `exists_min_cost`: for a cost `Σ φ(log(q/p))` with `φ` continuous and coercive, the minimum over
  weakly solvable prices is attained.
-/

namespace NeoTiling.PolyHardness

open Finset

variable {T : ℕ} {Q : Fin T → Fin 2 → ℝ}

/-- `q_t` lies below a point of the segment from `q_r` (upper left) to `q_s` (lower right). -/
def Mixed (Q : Fin T → Fin 2 → ℝ) (t r s : Fin T) : Prop :=
  Q r 0 ≤ Q s 0 ∧ Q s 1 ≤ Q r 1 ∧
    ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧ ∀ i, Q t i ≤ μ * Q r i + (1 - μ) * Q s i

/-- In the plane a blocking witness can be normalized to `ξ = (θ, 1 - θ)` with `θ ∈ [0, 1]`. -/
theorem isBlocked_two_iff (t : Fin T) (R : Finset (Fin T)) :
    IsBlocked Q t R ↔ ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      ∀ r ∈ R, 0 ≤ θ * (Q r 0 - Q t 0) + (1 - θ) * (Q r 1 - Q t 1) := by
  constructor
  · -- `θ := ξ₀ / (ξ₀ + ξ₁)`
    rintro ⟨ξ, hξ, hne, h⟩
    have h0 : 0 ≤ ξ 0 := hξ 0
    have h1 : 0 ≤ ξ 1 := hξ 1
    have hs : 0 < ξ 0 + ξ 1 := by
      by_contra hc
      exact hne (funext fun i => by fin_cases i <;> simp <;> linarith)
    refine ⟨ξ 0 / (ξ 0 + ξ 1), ⟨div_nonneg h0 hs.le, (div_le_one hs).2 (by linarith)⟩,
      fun r hr => ?_⟩
    have := h r hr
    simp [dotProduct, Fin.sum_univ_two] at this
    have e : 1 - ξ 0 / (ξ 0 + ξ 1) = ξ 1 / (ξ 0 + ξ 1) := by field_simp; ring
    rw [e, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    exact div_nonneg (by linarith) hs.le
  · -- `ξ := (θ, 1 - θ)`
    rintro ⟨θ, ⟨h0, h1⟩, h⟩
    refine ⟨![θ, 1 - θ], fun i => by fin_cases i <;> simp <;> linarith, fun hc => ?_,
      fun r hr => ?_⟩
    · have a := congrFun hc 0
      have b := congrFun hc 1
      simp at a b
      linarith
    · simpa [dotProduct, Fin.sum_univ_two] using h r hr

/-- **Helly on a segment.** In the plane `t` is blocked by `R` iff it is blocked by every pair of
points of `R`. (Normalize `ξ = (θ, 1 - θ)`: each `r` allows a closed interval of `θ ∈ [0, 1]`,
and intervals that meet pairwise have a common point.) -/
theorem isBlocked_iff_pairs (t : Fin T) (R : Finset (Fin T)) :
    IsBlocked Q t R ↔ ∀ r ∈ R, ∀ s ∈ R, IsBlocked Q t {r, s} := by
  constructor
  · rintro h r hr s hs
    obtain ⟨ξ, h0, hne, hξ⟩ := h
    exact ⟨ξ, h0, hne, fun u hu => hξ u (by rcases mem_insert.mp hu with rfl | hu <;> simp_all)⟩
  · intro h
    simp only [isBlocked_two_iff] at h ⊢
    rcases R.eq_empty_or_nonempty with rfl | ⟨r₀, hr₀⟩
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    -- the admissible `θ` for `r`: a segment cut by a half-line
    let F : Fin T → Set ℝ := fun r =>
      Set.Icc 0 1 ∩ {θ | 0 ≤ θ * (Q r 0 - Q t 0) + (1 - θ) * (Q r 1 - Q t 1)}
    have hconv : ∀ r ∈ R, Convex ℝ (F r) := fun r _ =>
      (convex_Icc 0 1).inter fun x hx y hy a b ha hb hab => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx hy ⊢
        have e : 1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by linear_combination -hab
        have := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
        rw [e]; linarith
    -- at most two of them meet: they lie in a pair
    have hI : ∀ I ⊆ R, #I ≤ Module.finrank ℝ ℝ + 1 → (⋂ i ∈ I, F i).Nonempty := by
      intro I hIR hcard
      rw [Module.finrank_self] at hcard
      obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ R, ∃ b ∈ R, I ⊆ {a, b} := by
        interval_cases h : #I
        · rw [card_eq_zero.mp h]; exact ⟨r₀, hr₀, r₀, hr₀, by simp⟩
        · obtain ⟨c, rfl⟩ := card_eq_one.mp h
          have hc := hIR (mem_singleton_self c)
          exact ⟨c, hc, c, hc, by simp⟩
        · obtain ⟨c, d, -, rfl⟩ := card_eq_two.mp h
          exact ⟨c, hIR (by simp), d, hIR (by simp), Subset.rfl⟩
      obtain ⟨θ, hθ, hθ'⟩ := h a ha b hb
      exact ⟨θ, Set.mem_iInter₂.mpr fun i hi => ⟨hθ, hθ' i (hab hi)⟩⟩
    -- Helly's theorem on the line
    obtain ⟨θ, hθ⟩ := Convex.helly_theorem' hconv hI
    simp only [Set.mem_iInter] at hθ
    exact ⟨θ, (hθ r₀ hr₀).1, fun r hr => (hθ r hr).2⟩

/-- Blocking by a pair in coordinates: `ξ = (a, b)`. -/
theorem isBlocked_pair_coord (t r s : Fin T) :
    IsBlocked Q t {r, s} ↔ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ (a ≠ 0 ∨ b ≠ 0) ∧
      0 ≤ a * (Q r 0 - Q t 0) + b * (Q r 1 - Q t 1) ∧
      0 ≤ a * (Q s 0 - Q t 0) + b * (Q s 1 - Q t 1) := by
  constructor
  · rintro ⟨ξ, h0, hne, h⟩
    refine ⟨ξ 0, ξ 1, h0 0, h0 1, ?_, ?_, ?_⟩
    · by_contra hc
      push_neg at hc
      exact hne (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    · simpa [dotProduct, Fin.sum_univ_two] using h r (by simp)
    · simpa [dotProduct, Fin.sum_univ_two] using h s (by simp)
  · rintro ⟨a, b, ha, hb, hne, h1, h2⟩
    refine ⟨![a, b], fun i => by fin_cases i <;> simpa, ?_, ?_⟩
    · intro h; rcases hne with h' | h'
      · exact h' (by simpa using congrFun h 0)
      · exact h' (by simpa using congrFun h 1)
    · intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · simpa [dotProduct, Fin.sum_univ_two] using h1
      · rw [Finset.mem_singleton.1 hu]; simpa [dotProduct, Fin.sum_univ_two] using h2

/-- A crossing pair `p = q_r - q_t`, `q = q_s - q_t` (`0 ≤ p₁`, `q₁ < 0`) admitting a witness
`(a, b)` has `det(q, p) ≥ 0`: `p₁ ⟨ξ, q⟩ - q₁ ⟨ξ, p⟩ = a det(q, p)` and `a > 0`. -/
theorem cross_ineq {a b p0 p1 q0 q1 : ℝ} (ha : 0 ≤ a) (hpos : 0 < a ∨ 0 < b)
    (hp : 0 ≤ a * p0 + b * p1) (hq : 0 ≤ a * q0 + b * q1) (h1 : 0 ≤ p1) (h3 : q1 < 0) :
    0 ≤ q0 * p1 - p0 * q1 := by
  have ha' : 0 < a := by
    rcases hpos with h | h
    · exact h
    · by_contra hc
      have : a = 0 := le_antisymm (not_lt.1 hc) ha
      subst this; nlinarith
  have : 0 ≤ a * (q0 * p1 - p0 * q1) := by
    nlinarith [mul_nonneg h1 hq, mul_nonneg (neg_nonneg.2 h3.le) hp]
  exact nonneg_of_mul_nonneg_right this ha'

/-- A crossing pair with `det ≥ 0` gives a mixed point: `μ = (X_s - X_t) / (X_s - X_r)`. -/
theorem Mixed.of_cross {t r s : Fin T} (h1 : Q r 0 < Q t 0) (h2 : Q t 0 ≤ Q s 0)
    (h3 : Q s 1 < Q t 1) (h4 : Q t 1 ≤ Q r 1)
    (h5 : 0 ≤ (Q s 0 - Q t 0) * (Q r 1 - Q t 1) + (Q t 0 - Q r 0) * (Q s 1 - Q t 1)) :
    Mixed Q t r s := by
  have hD : 0 < Q s 0 - Q r 0 := by linarith
  refine ⟨by linarith, by linarith, (Q s 0 - Q t 0) / (Q s 0 - Q r 0),
    div_nonneg (by linarith) hD.le, (div_le_one hD).2 (by linarith), ?_⟩
  intro i
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [← sub_nonneg]
    have : (Q s 0 - Q t 0) / (Q s 0 - Q r 0) * Q r 0
        + (1 - (Q s 0 - Q t 0) / (Q s 0 - Q r 0)) * Q s 0 - Q t 0 = 0 := by field_simp; ring
    linarith
  · simp only [Fin.mk_one]
    rw [← sub_nonneg]
    have : (Q s 0 - Q t 0) / (Q s 0 - Q r 0) * Q r 1
        + (1 - (Q s 0 - Q t 0) / (Q s 0 - Q r 0)) * Q s 1 - Q t 1 =
        ((Q s 0 - Q t 0) * (Q r 1 - Q t 1) + (Q t 0 - Q r 0) * (Q s 1 - Q t 1))
          / (Q s 0 - Q r 0) := by field_simp; ring
    rw [this]
    exact div_nonneg h5 hD.le

/-- A mixed pair blocks `t`, with `ξ = (Y_r - Y_s, X_s - X_r)` (or `(1, 0)` if `q_r = q_s`). -/
theorem Mixed.isBlocked {t r s : Fin T} (h : Mixed Q t r s) : IsBlocked Q t {r, s} := by
  obtain ⟨hx, hy, μ, hμ0, hμ1, hq⟩ := h
  rw [isBlocked_pair_coord]
  have q0 := hq 0
  have q1 := hq 1
  by_cases hz : Q r 1 - Q s 1 = 0 ∧ Q s 0 - Q r 0 = 0
  · refine ⟨1, 0, by norm_num, le_rfl, Or.inl one_ne_zero, ?_, ?_⟩
    · nlinarith
    · nlinarith
  · refine ⟨Q r 1 - Q s 1, Q s 0 - Q r 0, by linarith, by linarith, ?_, ?_, ?_⟩
    · by_contra hc; push_neg at hc; exact hz hc
    · nlinarith [mul_le_mul_of_nonneg_left q0 (sub_nonneg.2 hy),
        mul_le_mul_of_nonneg_left q1 (sub_nonneg.2 hx)]
    · nlinarith [mul_le_mul_of_nonneg_left q0 (sub_nonneg.2 hy),
        mul_le_mul_of_nonneg_left q1 (sub_nonneg.2 hx)]

/-- **Blocking by a pair.** (→): split on the signs of the coordinates of `q_r - q_t` and
`q_s - q_t`; both negative is impossible, so the remaining cases are a common coordinate or a
crossing, where `cross_ineq` and `Mixed.of_cross` give a mixed point. -/
theorem isBlocked_pair_iff (t r s : Fin T) :
    IsBlocked Q t {r, s} ↔
      (Q t 0 ≤ Q r 0 ∧ Q t 0 ≤ Q s 0) ∨ (Q t 1 ≤ Q r 1 ∧ Q t 1 ≤ Q s 1) ∨
        Mixed Q t r s ∨ Mixed Q t s r := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hne, h1, h2⟩ := isBlocked_pair_coord t r s |>.1 h
    have pos : 0 < a ∨ 0 < b := by
      rcases hne with h | h
      · exact Or.inl (lt_of_le_of_ne ha (Ne.symm h))
      · exact Or.inr (lt_of_le_of_ne hb (Ne.symm h))
    -- the two crossings
    have hx1 : Q r 0 < Q t 0 → Q t 1 ≤ Q r 1 → Q t 0 ≤ Q s 0 → Q s 1 < Q t 1 → Mixed Q t r s :=
      fun a0 a1 b0 b1 => Mixed.of_cross a0 b0 b1 a1 (by
        nlinarith [cross_ineq ha pos h1 h2 (by linarith : 0 ≤ Q r 1 - Q t 1)
          (by linarith : Q s 1 - Q t 1 < 0)])
    have hx2 : Q s 0 < Q t 0 → Q t 1 ≤ Q s 1 → Q t 0 ≤ Q r 0 → Q r 1 < Q t 1 → Mixed Q t s r :=
      fun b0 b1 a0 a1 => Mixed.of_cross b0 a0 a1 b1 (by
        nlinarith [cross_ineq ha pos h2 h1 (by linarith : 0 ≤ Q s 1 - Q t 1)
          (by linarith : Q r 1 - Q t 1 < 0)])
    -- split on the signs of the four coordinates
    rcases lt_or_ge (Q r 0) (Q t 0) with a0 | a0 <;>
      rcases lt_or_ge (Q r 1) (Q t 1) with a1 | a1 <;>
      rcases lt_or_ge (Q s 0) (Q t 0) with b0 | b0 <;>
      rcases lt_or_ge (Q s 1) (Q t 1) with b1 | b1
    all_goals first
      | (exfalso; rcases pos with p | p <;> nlinarith)
      | exact Or.inl ⟨by linarith, by linarith⟩
      | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inr (Or.inr (Or.inl (hx1 ‹_› ‹_› ‹_› ‹_›)))
      | exact Or.inr (Or.inr (Or.inr (hx2 ‹_› ‹_› ‹_› ‹_›)))
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | h | h)
    · exact (isBlocked_pair_coord t r s).2 ⟨1, 0, by norm_num, le_rfl, Or.inl one_ne_zero,
        by linarith, by linarith⟩
    · exact (isBlocked_pair_coord t r s).2 ⟨0, 1, le_rfl, by norm_num, Or.inr one_ne_zero,
        by linarith, by linarith⟩
    · exact h.isBlocked
    · rw [Finset.pair_comm]; exact h.isBlocked

/-- **Monotonicity.** Lowering `q_t` and raising the points of `R` keeps `t` blocked. -/
theorem IsBlocked.mono {d : ℕ} {Q Q' : Fin T → Fin d → ℝ} {t : Fin T} {R : Finset (Fin T)}
    (h : IsBlocked Q t R) (ht : ∀ i, Q' t i ≤ Q t i) (hR : ∀ r ∈ R, ∀ i, Q r i ≤ Q' r i) :
    IsBlocked Q' t R := by
  obtain ⟨ξ, h0, hne, hξ⟩ := h
  refine ⟨ξ, h0, hne, fun r hr => (hξ r hr).trans ?_⟩
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (h0 i)
  simp only [Pi.sub_apply]; linarith [hR r hr i, ht i]

/-- **Pair covers.** If `S` is not weakly reachable, some `t ∈ S` is not blocked by a set of at
most two points outside `S`. -/
theorem exists_pair_cover {S : Finset (Fin T)} (h : ¬ IsWeakReachable Q S) :
    ∃ t ∈ S, ∃ R : Finset (Fin T), R ⊆ univ \ S ∧ R.card ≤ 2 ∧ ¬ IsBlocked Q t R := by
  by_contra hcon
  push_neg at hcon
  refine h fun t ht => ?_
  by_contra hb
  -- `t` has no weak witness: it is not blocked by the complement of `S`
  have hnb : ¬ IsBlocked Q t (univ \ S) := by
    rintro ⟨ξ, h0, hne, hξ⟩
    exact hb ⟨ξ, h0, hne, fun s hs => hξ s (by simp [hs])⟩
  -- hence not by some pair in it
  rw [isBlocked_iff_pairs] at hnb
  push_neg at hnb
  obtain ⟨r, hr, s, hs, hn⟩ := hnb
  exact hn (hcon t ht {r, s}
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption) Finset.card_le_two)

/-- The cost `Σ_{t,i} φ(log(q_t^i / p_t^i))`. -/
noncomputable def logCost (φ : ℝ → ℝ) (P Q : Fin T → Fin 2 → ℝ) : ℝ :=
  ∑ t, ∑ i, φ (Real.log (Q t i / P t i))

/-- **The minimum is attained for every coercive cost.** Let `φ` be continuous, nonnegative and
`φ u → ∞` as `|u| → ∞`. Then among positive prices `Q` at which `y ≥ 0` is weakly solvable some
`Q` minimizes `logCost φ P Q`. (The sublevel set lies in a box `p e^{-M} ≤ q ≤ p e^{M}`, the
weakly solvable prices form a closed set by definition, and the hyperbola prices of
`Algorithms/Perturbation.lean` show the set is nonempty.) -/
theorem exists_min_cost {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφ : Filter.Tendsto φ (Filter.cocompact ℝ) Filter.atTop)
    {P : Fin T → Fin 2 → ℝ} (hP : ∀ t, P t ∈ orthant 2) {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) :
    ∃ Q : Fin T → Fin 2 → ℝ, (∀ t, Q t ∈ orthant 2) ∧ WeakSolvable Q y ∧
      ∀ Q' : Fin T → Fin 2 → ℝ, (∀ t, Q' t ∈ orthant 2) → WeakSolvable Q' y →
        logCost φ P Q ≤ logCost φ P Q' := by
  obtain ⟨Q₀, hQ₀, hw₀, -⟩ := exists_weak_totalPert_eq (le_refl 2) hP hy (κ := 1) one_pos
  set c₀ := logCost φ P Q₀
  -- far from `0`, `φ` exceeds `c₀`
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 (hφ.eventually_gt_atTop c₀)
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
  have hfar : ∀ u, M < |u| → c₀ < φ u := fun u hu =>
    hKs fun huK => by simpa using (not_lt.2 (mem_closedBall_zero_iff.1 (hM huK))) hu
  -- positive prices of cost `≤ c₀` lie in the box `p e^{-M} ≤ q ≤ p e^M`
  set B : Set (Fin T → Fin 2 → ℝ) := Set.pi Set.univ fun t => Set.pi Set.univ fun i =>
    Set.Icc (P t i * Real.exp (-M)) (P t i * Real.exp M)
  have hBc : IsCompact B := isCompact_univ_pi fun t => isCompact_univ_pi fun i => isCompact_Icc
  have hBpos : ∀ Q ∈ B, ∀ t, Q t ∈ orthant 2 := fun Q hQ t i =>
    (mul_pos (hP t i) (Real.exp_pos _)).trans_le (hQ t (Set.mem_univ _) i (Set.mem_univ _)).1
  have hbox : ∀ Q', (∀ t, Q' t ∈ orthant 2) → logCost φ P Q' ≤ c₀ → Q' ∈ B := by
    intro Q' hQ' hle t _ i _
    have hterm : φ (Real.log (Q' t i / P t i)) ≤ c₀ :=
      ((Finset.single_le_sum (f := fun j => φ (Real.log (Q' t j / P t j)))
        (fun j _ => hφ0 _) (mem_univ i)).trans
      (Finset.single_le_sum (f := fun s => ∑ j, φ (Real.log (Q' s j / P s j)))
        (fun s _ => Finset.sum_nonneg fun j _ => hφ0 _) (mem_univ t))).trans hle
    have habs : |Real.log (Q' t i / P t i)| ≤ M := not_lt.1 fun h => (hfar _ h).not_ge hterm
    have hp := hP t i
    have hr : 0 < Q' t i / P t i := div_pos (hQ' t i) hp
    obtain ⟨h1, h2⟩ := abs_le.1 habs
    constructor
    · rw [mul_comm, ← le_div_iff₀ hp]
      exact (Real.le_log_iff_exp_le hr).1 h1
    · rw [mul_comm, ← div_le_iff₀ hp]
      exact (Real.log_le_iff_le_exp hr).1 h2
  have hc₀B : Q₀ ∈ B := hbox Q₀ hQ₀ le_rfl
  -- the cost is continuous at positive prices
  have hcont : ContinuousOn (logCost φ P) {Q | ∀ t, Q t ∈ orthant 2} := by
    unfold logCost
    refine continuousOn_finset_sum _ fun t _ => continuousOn_finset_sum _ fun i _ => ?_
    refine hφc.comp_continuousOn
      (ContinuousOn.log ?_ fun Q hQ => (div_pos (hQ t i) (hP t i)).ne')
    exact (continuous_apply i |>.comp (continuous_apply t)).continuousOn.div_const _
  -- minimize over the compact set of weakly solvable prices in the box
  have hKc : IsCompact (closure {Q : Fin T → Fin 2 → ℝ | (∀ t, Q t ∈ orthant 2) ∧
      NeoSolvable Q y} ∩ B) := hBc.inter_left isClosed_closure
  obtain ⟨Q, ⟨hw, hQB⟩, hmin⟩ := hKc.exists_isMinOn ⟨Q₀, hw₀, hc₀B⟩
    (hcont.mono fun Q hQ => hBpos Q hQ.2)
  refine ⟨Q, hBpos Q hQB, hw, fun Q' hQ' hw' => ?_⟩
  by_cases h : logCost φ P Q' ≤ c₀
  · exact isMinOn_iff.1 hmin _ ⟨hw', hbox Q' hQ' h⟩
  · exact (isMinOn_iff.1 hmin _ ⟨hw₀, hc₀B⟩).trans (not_le.1 h).le

end NeoTiling.PolyHardness
