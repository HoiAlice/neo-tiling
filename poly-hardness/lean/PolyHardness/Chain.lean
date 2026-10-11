import NeoTiling.Closure

/-!
# Reachable sets in the plane are cut out by convex chains

Part of `poly-hardness/` (not part of the `NeoTiling` library).

Weak reachability (witnesses with `⟨ξ, p_s - p_t⟩ ≥ 0`) and reachability (`> 0`) are treated at
once: `Ok b u` is `0 < u` for `b = true` and `0 ≤ u` for `b = false`, and `IsReachableB b` is
reachability with `Ok b` witnesses, so `IsReachableB false = IsWeakReachable` and
`IsReachableB true = IsReachable`.

For prices `P : Fin T → Fin 2 → ℝ` write `X t = P t 0`, `Y t = P t 1`. A *chain*
`v 0, …, v k` has `X` strictly increasing, `Y` strictly decreasing and strictly convex turns. It
describes the closed region `C(V) = conv(V) + ℝ²₊` (`InHull`) and its interior (`InInt`). The
*forbidden region* is `InInt` for weak and `InHull` for strict reachability.
* `isReachableB_iff_chain`: `S` is (weakly) reachable iff `S = univ` or some chain has its
  vertices outside `S`, every point outside `C(V)` in `S` and every forbidden point outside `S`.
  Corollaries `isWeakReachable_iff_chain`, `isReachable_iff_chain`.
* `inHull_iff_of_piece`, `inHull_iff_of_left`, `inHull_iff_of_right`: *locality*. The status of
  a point depends only on the vertical slab of the chain containing it.
-/

namespace NeoTiling.PolyHardness

open Finset

/-! ## Weak and strict at once -/

/-- `Ok b u`: `0 < u` if `b` (strict), `0 ≤ u` otherwise. -/
def Ok (b : Bool) (u : ℝ) : Prop := if b then 0 < u else 0 ≤ u

/-- Reachability with `Ok b` witnesses: every `t ∈ S` has a nonzero `ξ ≥ 0` with
`Ok b ⟨ξ, p_s - p_t⟩` for all `s ∉ S`. -/
def IsReachableB {d T : ℕ} (b : Bool) (P : Fin T → Fin d → ℝ) (S : Finset (Fin T)) : Prop :=
  ∀ t ∈ S, ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∉ S, Ok b (ξ ⬝ᵥ (P s - P t))

section OkLemmas

variable {b : Bool} {u v : ℝ}

theorem Ok.nonneg (h : Ok b u) : 0 ≤ u := by
  cases b <;> simp only [Ok] at h <;> simp_all [le_of_lt]

theorem Ok.add_nonneg (h : Ok b u) (hv : 0 ≤ v) : Ok b (u + v) := by
  cases b <;> simp [Ok] at h ⊢ <;> linarith

theorem Ok.mul_pos {c : ℝ} (hc : 0 < c) (h : Ok b u) : Ok b (c * u) := by
  cases b <;> simp [Ok, hc] at h ⊢ <;> exact h

/-- `Ok b x` and `Ok (!b) y` cannot hold together with `x + y ≤ 0`. -/
theorem Ok.false_of_add_nonpos {x y : ℝ} (hx : Ok b x) (hy : Ok (!b) y)
    (h : x + y ≤ 0) : False := by
  cases b <;> simp only [Ok, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true,
    if_false] at hx hy <;> linarith

theorem isReachableB_false_iff {d T : ℕ} {P : Fin T → Fin d → ℝ} {S : Finset (Fin T)} :
    IsReachableB false P S ↔ IsWeakReachable P S := Iff.rfl

theorem isReachableB_true_iff {d T : ℕ} {P : Fin T → Fin d → ℝ} {S : Finset (Fin T)} :
    IsReachableB true P S ↔ IsReachable P S := Iff.rfl
end OkLemmas

/-! ## Part I: the plane -/

section Plane

variable {T : ℕ} (P : Fin T → Fin 2 → ℝ)

/-- Orientation of the triple `(a, b, q)`: positive iff `q` is strictly to the left of the
directed line `a → b` (above it when `X a < X b`). -/
def cross (a b q : Fin T) : ℝ :=
  (P b 0 - P a 0) * (P q 1 - P a 1) - (P b 1 - P a 1) * (P q 0 - P a 0)

/-- A strictly convex lower-left chain `v 0, …, v k`. -/
structure IsChain (v : ℕ → Fin T) (k : ℕ) : Prop where
  xlt : ∀ j < k, P (v j) 0 < P (v (j + 1)) 0
  ylt : ∀ j < k, P (v (j + 1)) 1 < P (v j) 1
  convex : ∀ j, j + 1 < k → 0 < cross P (v j) (v (j + 1)) (v (j + 2))

/-- `q` lies in the closed region `C(V)`. -/
def InHull (v : ℕ → Fin T) (k : ℕ) (q : Fin T) : Prop :=
  P (v 0) 0 ≤ P q 0 ∧ P (v k) 1 ≤ P q 1 ∧ ∀ j < k, 0 ≤ cross P (v j) (v (j + 1)) q

/-- `q` lies in the interior of `C(V)`. -/
def InInt (v : ℕ → Fin T) (k : ℕ) (q : Fin T) : Prop :=
  P (v 0) 0 < P q 0 ∧ P (v k) 1 < P q 1 ∧ ∀ j < k, 0 < cross P (v j) (v (j + 1)) q

variable {P}

/-! ### Existence of the hull chain (gift wrapping) -/

/-- Algebra for the gift-wrapping step: if `a` is above the line `v₀ w`, `w` above the line
`a b`, `X v₀ < X w < X a < X b` and `Y b < Y a`, then `v₀` is above the line `a b`. -/
theorem cross_nonneg_left {v₀ w a b : Fin T} (h0w : P v₀ 0 < P w 0) (hwa : P w 0 < P a 0)
    (hab : P a 0 < P b 0) (_hyab : P b 1 < P a 1) (ha : 0 ≤ cross P v₀ w a)
    (hw : 0 ≤ cross P a b w) : 0 ≤ cross P a b v₀ := by
  have key : (P a 0 - P w 0) * cross P a b v₀
      = (P a 0 - P v₀ 0) * cross P a b w + (P b 0 - P a 0) * cross P v₀ w a := by
    unfold cross; ring
  have h1 : 0 < P a 0 - P w 0 := by linarith
  have h2 : 0 < P a 0 - P v₀ 0 := by linarith
  have h3 : 0 < P b 0 - P a 0 := by linarith
  have : 0 ≤ (P a 0 - P w 0) * cross P a b v₀ := by
    rw [key]; positivity
  exact nonneg_of_mul_nonneg_right this h1

/-- Algebra for the gift-wrapping step: if `f = cross P a b` is nonnegative at `v₀` and `w`,
the normal of `a b` is nonnegative, and `s` lies in `conv{v₀, w} + ℝ²₊` (`X s ≥ X v₀`,
`Y s ≥ Y w`, `s` above the line `v₀ w`), then `f s ≥ 0`. -/
theorem cross_nonneg_of_above {v₀ w a b s : Fin T} (h0w : P v₀ 0 < P w 0)
    (_hyw : P w 1 < P v₀ 1) (hab : P a 0 < P b 0) (hyab : P b 1 < P a 1)
    (h0 : 0 ≤ cross P a b v₀) (hw : 0 ≤ cross P a b w) (hxs : P v₀ 0 ≤ P s 0)
    (hys : P w 1 ≤ P s 1) (hs : 0 ≤ cross P v₀ w s) : 0 ≤ cross P a b s := by
  have h3 : 0 < P b 0 - P a 0 := by linarith
  rcases le_or_gt (P w 0) (P s 0) with hx | hx
  · have key : cross P a b s - cross P a b w
        = (P b 0 - P a 0) * (P s 1 - P w 1) + (P a 1 - P b 1) * (P s 0 - P w 0) := by
      unfold cross; ring
    have : 0 ≤ (P b 0 - P a 0) * (P s 1 - P w 1) + (P a 1 - P b 1) * (P s 0 - P w 0) := by
      have : 0 < P a 1 - P b 1 := by linarith
      have : 0 ≤ P s 1 - P w 1 := by linarith
      have : 0 ≤ P s 0 - P w 0 := by linarith
      positivity
    linarith
  · have key : (P w 0 - P v₀ 0) * cross P a b s
        = (P w 0 - P s 0) * cross P a b v₀ + (P s 0 - P v₀ 0) * cross P a b w
          + (P b 0 - P a 0) * cross P v₀ w s := by
      unfold cross; ring
    have h1 : 0 < P w 0 - P v₀ 0 := by linarith
    have : 0 ≤ (P w 0 - P v₀ 0) * cross P a b s := by
      rw [key]
      have : 0 < P w 0 - P s 0 := by linarith
      have : 0 ≤ P s 0 - P v₀ 0 := by linarith
      positivity
    exact nonneg_of_mul_nonneg_right this h1

/-- `X` is strictly increasing along a chain. -/
private lemma x_mono {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {i j : ℕ} (hij : i < j)
    (hj : j ≤ k) : P (v i) 0 < P (v j) 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · exact (ih h (by omega)).trans (hc.xlt j (by omega))
    · subst h; exact hc.xlt i (by omega)

/-- **Hull chain.** Every nonempty `U` has a chain with vertices in `U`, starting at a given
lexicographic minimum `v₀` of `U`, whose region contains all of `U`. Proof by strong induction on
`#U`: if no point of `U` is below `v₀`, the chain is `v₀` alone. Otherwise pick `w` below `v₀` of
least slope `(Y w - Y v₀)/(X w - X v₀)`, farthest among ties; `w` is the lexicographic minimum of
`U' = {s ∈ U | Y s ≤ Y w}`, apply induction to `U'` and prepend `v₀`. Points of `U \ U'` satisfy
the later edge inequalities by `cross_nonneg_left` and `cross_nonneg_of_above`. -/
theorem exists_hull_chain (U : Finset (Fin T)) (v₀ : Fin T) (hv₀ : v₀ ∈ U)
    (hmin : ∀ s ∈ U, P v₀ 0 ≤ P s 0 ∧ (P s 0 = P v₀ 0 → P v₀ 1 ≤ P s 1)) :
    ∃ (v : ℕ → Fin T) (k : ℕ), IsChain P v k ∧ v 0 = v₀ ∧ (∀ i ≤ k, v i ∈ U) ∧
      ∀ s ∈ U, InHull P v k s := by
  classical
  induction h : U.card using Nat.strong_induction_on generalizing U v₀ with
  | _ n ih =>
  by_cases hU' : U.filter (fun s => P s 1 < P v₀ 1) = ∅
  · refine ⟨fun _ => v₀, 0, ⟨by simp, by simp, by simp⟩, rfl, fun _ _ => hv₀, fun s hs => ?_⟩
    refine ⟨(hmin s hs).1, ?_, by simp⟩
    have : s ∉ U.filter (fun s => P s 1 < P v₀ 1) := by rw [hU']; simp
    simp only [mem_filter, not_and, not_lt] at this
    exact this hs
  set U' := U.filter (fun s => P s 1 < P v₀ 1) with hU'def
  have hne : U'.Nonempty := nonempty_iff_ne_empty.mpr hU'
  have hU'x : ∀ s ∈ U', P v₀ 0 < P s 0 := by
    intro s hs
    rw [mem_filter] at hs
    rcases (hmin s hs.1).1.lt_or_eq with h | h
    · exact h
    · exact absurd ((hmin s hs.1).2 h.symm) (not_le.mpr hs.2)
  set σ : Fin T → ℝ := fun s => (P s 1 - P v₀ 1) / (P s 0 - P v₀ 0) with hσ
  obtain ⟨w₁, hw₁, hw₁min⟩ := U'.exists_min_image σ hne
  have hne2 : (U'.filter (fun s => σ s = σ w₁)).Nonempty := ⟨w₁, mem_filter.mpr ⟨hw₁, rfl⟩⟩
  obtain ⟨w, hw, hwmax⟩ :=
    (U'.filter (fun s => σ s = σ w₁)).exists_max_image (fun s => P s 0) hne2
  rw [mem_filter] at hw
  obtain ⟨hwU', hσw⟩ := hw
  have hwmin : ∀ s ∈ U', σ w ≤ σ s := fun s hs => hσw ▸ hw₁min s hs
  have hwtie : ∀ s ∈ U', σ s = σ w → P s 0 ≤ P w 0 :=
    fun s hs he => hwmax s (mem_filter.mpr ⟨hs, he.trans hσw⟩)
  have hwU : w ∈ U := (mem_filter.mp hwU').1
  have hwy : P w 1 < P v₀ 1 := (mem_filter.mp hwU').2
  have hwx : P v₀ 0 < P w 0 := hU'x w hwU'
  have hσneg : σ w < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have F1 : ∀ s, P v₀ 0 < P s 0 →
      cross P v₀ w s = (P w 0 - P v₀ 0) * (P s 0 - P v₀ 0) * (σ s - σ w) := by
    intro s hs
    have h1 : P s 0 - P v₀ 0 ≠ 0 := by linarith
    have h2 : P w 0 - P v₀ 0 ≠ 0 := by linarith
    simp only [hσ, cross]
    field_simp
  have F2 : ∀ s ∈ U, 0 ≤ cross P v₀ w s := by
    intro s hs
    rcases (hmin s hs).1.lt_or_eq with hx | hx
    · rw [F1 s hx]
      apply mul_nonneg (mul_nonneg (by linarith) (by linarith))
      by_cases hsU' : s ∈ U'
      · linarith [hwmin s hsU']
      · have : P v₀ 1 ≤ P s 1 := by simpa [U', hs] using hsU'
        have : 0 ≤ σ s := div_nonneg (by linarith) (by linarith)
        linarith
    · have hy := (hmin s hs).2 hx.symm
      have e : P s 0 - P v₀ 0 = 0 := by linarith
      simp only [cross, e, mul_zero, sub_zero]
      exact mul_nonneg (by linarith) (by linarith)
  set U'' := U.filter (fun s => P s 1 ≤ P w 1) with hU''def
  have hU''sub : ∀ s ∈ U'', s ∈ U' := by
    intro s hs; rw [mem_filter] at hs ⊢; exact ⟨hs.1, lt_of_le_of_lt hs.2 hwy⟩
  have hU''U : ∀ s ∈ U'', s ∈ U := fun s hs => (mem_filter.mp hs).1
  have hcard : U''.card < n := by
    rw [← h]; apply card_lt_card
    refine ⟨filter_subset _ _, fun hsub => ?_⟩
    have := hsub hv₀; rw [mem_filter] at this; linarith [this.2]
  have hwU'' : w ∈ U'' := mem_filter.mpr ⟨hwU, le_rfl⟩
  have hwmin'' : ∀ s ∈ U'', P w 0 ≤ P s 0 ∧ (P s 0 = P w 0 → P w 1 ≤ P s 1) := by
    intro s hs
    have hsU' := hU''sub s hs
    have hsx := hU'x s hsU'
    have hsy : P s 1 ≤ P w 1 := (mem_filter.mp hs).2
    have hσs := hwmin s hsU'
    have hc : 0 ≤ cross P v₀ w s := by
      rw [F1 s hsx]
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    simp only [cross] at hc
    constructor
    · by_contra hlt; push_neg at hlt
      nlinarith [mul_nonneg (sub_nonneg.2 hwx.le) (sub_nonneg.2 hsy),
        mul_pos (sub_pos.2 hwy) (sub_pos.2 hlt)]
    · intro he; by_contra hlt; push_neg at hlt; rw [he] at hc
      nlinarith [mul_pos (sub_pos.2 hwx) (sub_pos.2 hlt)]
  obtain ⟨v', k', hc', hv'0, hv'U, hv'H⟩ := ih _ hcard U'' w hwU'' hwmin'' rfl
  obtain ⟨v, hv0, hvs⟩ : ∃ v : ℕ → Fin T, v 0 = v₀ ∧ ∀ j, v (j + 1) = v' j :=
    ⟨fun i => match i with | 0 => v₀ | j + 1 => v' j, rfl, fun _ => rfl⟩
  have hconv0 : 0 < k' → 0 < cross P v₀ w (v' 1) := by
    intro hk
    have hbU'' := hv'U 1 hk
    have hbU' := hU''sub _ hbU''
    have hbx : P w 0 < P (v' 1) 0 := by have := hc'.xlt 0 hk; rwa [hv'0] at this
    have hσb := hwmin _ hbU'
    have hne : σ (v' 1) ≠ σ w := fun he => absurd (hwtie _ hbU' he) (not_le.mpr hbx)
    rw [F1 _ (by linarith)]
    exact mul_pos (mul_pos (by linarith) (by linarith))
      (by linarith [lt_of_le_of_ne hσb (Ne.symm hne)])
  refine ⟨v, k' + 1, ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩, hv0, ?_, ?_⟩
  · rcases j with _ | j
    · rw [hv0, hvs, hv'0]; exact hwx
    · rw [hvs, hvs]; exact hc'.xlt j (by omega)
  · rcases j with _ | j
    · rw [hv0, hvs, hv'0]; exact hwy
    · rw [hvs, hvs]; exact hc'.ylt j (by omega)
  · rcases j with _ | j
    · show 0 < cross P (v 0) (v (0 + 1)) (v (1 + 1))
      rw [hv0, hvs, hvs, hv'0]; exact hconv0 (by omega)
    · show 0 < cross P (v (j + 1)) (v ((j + 1) + 1)) (v ((j + 2) + 1))
      rw [hvs, hvs, hvs]; exact hc'.convex j (by omega)
  · intro i hi
    rcases i with _ | i
    · rw [hv0]; exact hv₀
    · rw [hvs]; exact hU''U _ (hv'U i (by omega))
  · intro s hs
    refine ⟨by rw [hv0]; exact (hmin s hs).1, ?_, ?_⟩
    · rw [hvs]
      by_cases hsU'' : s ∈ U''
      · exact (hv'H s hsU'').2.1
      · have : P w 1 < P s 1 := by simpa [U'', hs] using hsU''
        have := (mem_filter.mp (hv'U k' le_rfl)).2
        linarith
    · intro j hj
      rcases j with _ | j
      · rw [hv0, hvs, hv'0]; exact F2 s hs
      · rw [hvs, hvs]
        by_cases hsU'' : s ∈ U''
        · exact (hv'H s hsU'').2.2 j (by omega)
        · have hys : P w 1 < P s 1 := by simpa [U'', hs] using hsU''
          have hj' : j < k' := by omega
          have hab := hc'.xlt j hj'
          have hyab := hc'.ylt j hj'
          have hw' : 0 ≤ cross P (v' j) (v' (j + 1)) w := (hv'H w hwU'').2.2 j hj'
          have h0 : 0 ≤ cross P (v' j) (v' (j + 1)) v₀ := by
            rcases j with _ | j
            · have := hconv0 (by omega)
              have e : cross P w (v' 1) v₀ = cross P v₀ w (v' 1) := by unfold cross; ring
              rw [hv'0]
              show 0 ≤ cross P w (v' 1) v₀
              linarith
            · have hxa : P w 0 < P (v' (j + 1)) 0 := by
                rw [← hv'0]; exact x_mono hc' (by omega) (by omega)
              exact cross_nonneg_left hwx hxa hab hyab
                (F2 _ (hU''U _ (hv'U _ (by omega)))) hw'
          exact cross_nonneg_of_above hwx hwy hab hyab h0 hw' (hmin s hs).1 hys.le (F2 s hs)

/-! ### Locality: the status of a point is decided by its slab -/

/-- Along a strictly convex chain the slopes increase: for `j ≤ i < k`,
`(X_{j+1} - X_j)(Y_{i+1} - Y_i) - (Y_{j+1} - Y_j)(X_{i+1} - X_i) ≥ 0`. -/
theorem slope_mono {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {i j : ℕ} (hji : j ≤ i)
    (hik : i < k) :
    0 ≤ (P (v (j + 1)) 0 - P (v j) 0) * (P (v (i + 1)) 1 - P (v i) 1) -
      (P (v (j + 1)) 1 - P (v j) 1) * (P (v (i + 1)) 0 - P (v i) 0) := by
  induction i, hji using Nat.le_induction with
  | base => apply le_of_eq; ring
  | succ i hji ih =>
    have h1 := ih (by omega)
    have h2 := hc.convex i hik
    have hxi := hc.xlt i (by omega)
    have hxi1 := hc.xlt (i + 1) hik
    have hxj := hc.xlt j (by omega)
    unfold cross at h2
    have key : (P (v (i + 1)) 0 - P (v i) 0) *
        ((P (v (j + 1)) 0 - P (v j) 0) * (P (v (i + 1 + 1)) 1 - P (v (i + 1)) 1) -
          (P (v (j + 1)) 1 - P (v j) 1) * (P (v (i + 1 + 1)) 0 - P (v (i + 1)) 0)) =
        (P (v (i + 1 + 1)) 0 - P (v (i + 1)) 0) *
          ((P (v (j + 1)) 0 - P (v j) 0) * (P (v (i + 1)) 1 - P (v i) 1) -
            (P (v (j + 1)) 1 - P (v j) 1) * (P (v (i + 1)) 0 - P (v i) 0)) +
        (P (v (j + 1)) 0 - P (v j) 0) *
          ((P (v (i + 1)) 0 - P (v i) 0) * (P (v (i + 2)) 1 - P (v i) 1) -
            (P (v (i + 1)) 1 - P (v i) 1) * (P (v (i + 2)) 0 - P (v i) 0)) := by
      ring
    have h3 : 0 ≤ (P (v (i + 1)) 0 - P (v i) 0) *
        ((P (v (j + 1)) 0 - P (v j) 0) * (P (v (i + 1 + 1)) 1 - P (v (i + 1)) 1) -
          (P (v (j + 1)) 1 - P (v j) 1) * (P (v (i + 1 + 1)) 0 - P (v (i + 1)) 0)) := by
      rw [key]
      have := mul_nonneg (sub_nonneg.2 hxi1.le) h1
      have := mul_nonneg (sub_nonneg.2 hxj.le) h2.le
      positivity
    exact nonneg_of_mul_nonneg_right h3 (sub_pos.2 hxi)

private theorem xmono {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {j i : ℕ} (hji : j ≤ i)
    (hik : i ≤ k) : P (v j) 0 ≤ P (v i) 0 := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ i hji ih => exact (ih (by omega)).trans (hc.xlt i (by omega)).le

private theorem ymono {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {j i : ℕ} (hji : j ≤ i)
    (hik : i ≤ k) : P (v i) 1 ≤ P (v j) 1 := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ i hji ih => exact (hc.ylt i (by omega)).le.trans (ih (by omega))

private theorem cross_vertex_nonneg {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {j i : ℕ}
    (hj : j < k) (hi : i ≤ k) : 0 ≤ cross P (v j) (v (j + 1)) (v i) := by
  by_cases hji : j + 1 ≤ i
  · induction i, hji using Nat.le_induction with
    | base => apply le_of_eq; unfold cross; ring
    | succ l hl ih =>
      have h1 := ih (by omega)
      have h2 := slope_mono hc (show j ≤ l by omega) (show l < k by omega)
      have : cross P (v j) (v (j + 1)) (v (l + 1)) =
          cross P (v j) (v (j + 1)) (v l) +
          ((P (v (j + 1)) 0 - P (v j) 0) * (P (v (l + 1)) 1 - P (v l) 1) -
            (P (v (j + 1)) 1 - P (v j) 1) * (P (v (l + 1)) 0 - P (v l) 0)) := by
        unfold cross; ring
      rw [this]; linarith
  · have hij : i ≤ j + 1 := by omega
    have key : ∀ d l : ℕ, l + d = j + 1 → 0 ≤ cross P (v j) (v (j + 1)) (v l) := by
      intro d
      induction d with
      | zero =>
        intro l hl
        have : l = j + 1 := by omega
        subst this
        apply le_of_eq; unfold cross; ring
      | succ d ih =>
        intro l hl
        have h1 := ih (l + 1) (by omega)
        have h2 := slope_mono hc (show l ≤ j by omega) hj
        have : cross P (v j) (v (j + 1)) (v l) =
            cross P (v j) (v (j + 1)) (v (l + 1)) +
            ((P (v (l + 1)) 0 - P (v l) 0) * (P (v (j + 1)) 1 - P (v j) 1) -
              (P (v (l + 1)) 1 - P (v l) 1) * (P (v (j + 1)) 0 - P (v j) 0)) := by
          unfold cross; ring
        rw [this]; linarith
    exact key (j + 1 - i) i (by omega)

/-- Every vertex of a strictly convex chain lies in its region. -/
theorem inHull_vertex {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {i : ℕ} (hi : i ≤ k) :
    InHull P v k (v i) :=
  ⟨xmono hc (Nat.zero_le i) hi, ymono hc hi le_rfl, fun _ hj => cross_vertex_nonneg hc hj hi⟩

/-- **Edge slab.** For `X (v j) < X q ≤ X (v (j+1))` the point is in `C(V)` (in its interior)
iff it is on or above (strictly above) the line of the edge `j`. -/
theorem inHull_iff_of_piece {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {j : ℕ} (hj : j < k)
    {q : Fin T} (hq1 : P (v j) 0 < P q 0) (hq2 : P q 0 ≤ P (v (j + 1)) 0) :
    (InHull P v k q ↔ 0 ≤ cross P (v j) (v (j + 1)) q) ∧
      (InInt P v k q ↔ 0 < cross P (v j) (v (j + 1)) q) := by
  have hL : 0 < P (v (j + 1)) 0 - P (v j) 0 := sub_pos.2 (hc.xlt j hj)
  have hlam : 0 ≤ P (v (j + 1)) 0 - P q 0 := sub_nonneg.2 hq2
  have hmu : 0 < P q 0 - P (v j) 0 := sub_pos.2 hq1
  have hf : ∀ i, (P (v (j + 1)) 0 - P (v j) 0) * cross P (v i) (v (i + 1)) q =
      (P (v (j + 1)) 0 - P q 0) * cross P (v i) (v (i + 1)) (v j) +
      (P q 0 - P (v j) 0) * cross P (v i) (v (i + 1)) (v (j + 1)) +
      cross P (v j) (v (j + 1)) q * (P (v (i + 1)) 0 - P (v i) 0) := by
    intro i; unfold cross; ring
  have hy1 := ymono hc (show j ≤ k by omega) le_rfl
  have hy2 := ymono hc (show j + 1 ≤ k by omega) le_rfl
  have hx0 := xmono hc (Nat.zero_le j) hj.le
  refine ⟨⟨fun h => h.2.2 j hj, fun hcr => ⟨by linarith, ?_, ?_⟩⟩,
    ⟨fun h => h.2.2 j hj, fun hcr => ⟨by linarith, ?_, ?_⟩⟩⟩
  · by_contra hlt
    push_neg at hlt
    have hyq : (P (v (j + 1)) 0 - P (v j) 0) * P q 1 =
        (P (v (j + 1)) 0 - P q 0) * P (v j) 1 + (P q 0 - P (v j) 0) * P (v (j + 1)) 1 +
          cross P (v j) (v (j + 1)) q := by unfold cross; ring
    nlinarith [mul_nonneg hlam (sub_nonneg.2 hy1), mul_pos hmu (sub_pos.2 hlt)]
  · intro i hi
    have a1 := cross_vertex_nonneg hc hi hj.le
    have a2 := cross_vertex_nonneg hc hi (show j + 1 ≤ k by omega)
    have hx := hc.xlt i hi
    have h0 : 0 ≤ (P (v (j + 1)) 0 - P (v j) 0) * cross P (v i) (v (i + 1)) q := by
      rw [hf i]
      have := mul_nonneg hlam a1
      have := mul_nonneg hmu.le a2
      have := mul_nonneg hcr (sub_nonneg.2 hx.le)
      linarith
    exact nonneg_of_mul_nonneg_right h0 hL
  · by_contra hlt
    push_neg at hlt
    have hyq : (P (v (j + 1)) 0 - P (v j) 0) * P q 1 =
        (P (v (j + 1)) 0 - P q 0) * P (v j) 1 + (P q 0 - P (v j) 0) * P (v (j + 1)) 1 +
          cross P (v j) (v (j + 1)) q := by unfold cross; ring
    nlinarith [mul_nonneg hlam (sub_nonneg.2 hy1), mul_nonneg hmu.le (sub_nonneg.2 hy2),
      mul_pos hL hcr]
  · intro i hi
    have a1 := cross_vertex_nonneg hc hi hj.le
    have a2 := cross_vertex_nonneg hc hi (show j + 1 ≤ k by omega)
    have hx := hc.xlt i hi
    have h0 : 0 < (P (v (j + 1)) 0 - P (v j) 0) * cross P (v i) (v (i + 1)) q := by
      rw [hf i]
      have := mul_nonneg hlam a1
      have := mul_nonneg hmu.le a2
      have := mul_pos hcr (sub_pos.2 hx)
      linarith
    exact pos_of_mul_pos_right h0 hL.le

/-- **Left slab.** For `X q ≤ X (v 0)` the point is never interior, and it is in `C(V)` iff it
is on the vertical ray above `v 0`. -/
theorem inHull_iff_of_left {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {q : Fin T}
    (hq : P q 0 ≤ P (v 0) 0) :
    (InHull P v k q ↔ P q 0 = P (v 0) 0 ∧ P (v 0) 1 ≤ P q 1) ∧ ¬ InInt P v k q := by
  refine ⟨⟨fun h => ⟨le_antisymm hq h.1, ?_⟩, fun ⟨hxq, hy⟩ => ⟨hxq.ge, ?_, ?_⟩⟩,
    fun h => absurd h.1 (not_lt.2 hq)⟩
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact h.2.1
    · have h0 := h.2.2 0 hk
      have hx := hc.xlt 0 hk
      have heq : P q 0 = P (v 0) 0 := le_antisymm hq h.1
      unfold cross at h0
      rw [heq] at h0
      by_contra hlt
      push_neg at hlt
      nlinarith [mul_pos (sub_pos.2 hx) (sub_pos.2 hlt)]
  · exact (ymono hc (Nat.zero_le k) le_rfl).trans hy
  · intro i hi
    have hy' := sub_nonneg.2 hy
    have a1 := cross_vertex_nonneg hc hi (show 0 ≤ k by omega)
    have hx := hc.xlt i hi
    have hxy := hc.ylt i hi
    have : cross P (v i) (v (i + 1)) q = cross P (v i) (v (i + 1)) (v 0) +
        ((P (v (i + 1)) 0 - P (v i) 0) * (P q 1 - P (v 0) 1) -
          (P (v (i + 1)) 1 - P (v i) 1) * (P q 0 - P (v 0) 0)) := by
      unfold cross; ring
    have hyy := mul_nonneg (sub_nonneg.2 hx.le) (sub_nonneg.2 hy')
    rw [this, hxq]; nlinarith

/-- **Right slab.** For `X q > X (v k)` the point is in `C(V)` (interior) iff `Y q ≥ Y (v k)`
(`>`). -/
theorem inHull_iff_of_right {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {q : Fin T}
    (hq : P (v k) 0 < P q 0) :
    (InHull P v k q ↔ P (v k) 1 ≤ P q 1) ∧ (InInt P v k q ↔ P (v k) 1 < P q 1) := by
  have hx0 := xmono hc (Nat.zero_le k) le_rfl
  have hf : ∀ i, cross P (v i) (v (i + 1)) q = cross P (v i) (v (i + 1)) (v k) +
      ((P (v (i + 1)) 0 - P (v i) 0) * (P q 1 - P (v k) 1) -
        (P (v (i + 1)) 1 - P (v i) 1) * (P q 0 - P (v k) 0)) := by
    intro i; unfold cross; ring
  refine ⟨⟨fun h => h.2.1, fun hy => ⟨by linarith, hy, ?_⟩⟩,
    ⟨fun h => h.2.1, fun hy => ⟨by linarith, hy, ?_⟩⟩⟩
  · intro i hi
    have a1 := cross_vertex_nonneg hc hi le_rfl
    have := mul_nonneg (sub_nonneg.2 (hc.xlt i hi).le) (sub_nonneg.2 hy)
    have := mul_nonneg (sub_nonneg.2 (hc.ylt i hi).le) (sub_nonneg.2 hq.le)
    rw [hf i]; nlinarith
  · intro i hi
    have a1 := cross_vertex_nonneg hc hi le_rfl
    have := mul_nonneg (sub_nonneg.2 (hc.xlt i hi).le) (sub_nonneg.2 hy.le)
    have := mul_pos (sub_pos.2 (hc.ylt i hi)) (sub_pos.2 hq)
    rw [hf i]; nlinarith


/-! ### The characterization, weak and strict at once -/

/-- The forbidden region for points of `S`: the interior of `C(V)` for weak reachability, all of
`C(V)` for strict reachability. -/
def Forbidden (P : Fin T → Fin 2 → ℝ) (b : Bool) (v : ℕ → Fin T) (k : ℕ) (q : Fin T) : Prop :=
  if b then InHull P v k q else InInt P v k q

/-- A point that is not forbidden violates one of the inequalities of `C(V)` in the `Ok b`
sense. -/
theorem ok_of_not_forbidden {b : Bool} {v : ℕ → Fin T} {k : ℕ} {q : Fin T}
    (h : ¬ Forbidden P b v k q) :
    Ok b (P (v 0) 0 - P q 0) ∨ Ok b (P (v k) 1 - P q 1) ∨
      ∃ j < k, Ok b (- cross P (v j) (v (j + 1)) q) := by
  cases b
  · simp only [Forbidden, Bool.false_eq_true, if_false, InInt] at h
    simp only [Ok, Bool.false_eq_true, if_false]
    by_contra hcon
    push_neg at hcon
    exact h ⟨by linarith [hcon.1], by linarith [hcon.2.1],
      fun j hj => by linarith [hcon.2.2 j hj]⟩
  · simp only [Forbidden, if_true, InHull] at h
    simp only [Ok, if_true]
    by_contra hcon
    push_neg at hcon
    exact h ⟨by linarith [hcon.1], by linarith [hcon.2.1],
      fun j hj => by linarith [hcon.2.2 j hj]⟩

/-- A forbidden point satisfies the inequalities of `C(V)` in the opposite sense: `Ok b` of
`X q - X (v 0)`, `Y q - Y (v k)` and of every `cross`. -/
theorem ok_of_forbidden {b : Bool} {v : ℕ → Fin T} {k : ℕ} {q : Fin T}
    (h : Forbidden P b v k q) :
    InHull P v k q ∧ Ok (!b) (P q 0 - P (v 0) 0) ∧ Ok (!b) (P q 1 - P (v k) 1) ∧
      ∀ j < k, Ok (!b) (cross P (v j) (v (j + 1)) q) := by
  cases b
  · simp only [Forbidden, Bool.false_eq_true, if_false] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [Ok, Bool.not_false, if_true]
    exact ⟨⟨h0.le, h1.le, fun j hj => (h2 j hj).le⟩, by linarith, by linarith, h2⟩
  · simp only [Forbidden, if_true] at h
    obtain ⟨h0, h1, h2⟩ := h
    simp only [Ok, Bool.not_true, Bool.false_eq_true, if_false]
    exact ⟨⟨h0, h1, h2⟩, by linarith, by linarith, h2⟩

/-- **Soundness.** If every point outside `S` is in `C(V)` and no point of `S` is forbidden,
then `S` is (weakly) reachable: the inequality of `C(V)` that `t ∈ S` violates gives the witness
`(1,0)`, `(0,1)` or the edge normal `(Y a - Y b, X b - X a)`. -/
theorem isReachableB_of_chain {b : Bool} {v : ℕ → Fin T} {k : ℕ}
    (hc : IsChain P v k) {S : Finset (Fin T)}
    (hout : ∀ q, ¬ InHull P v k q → q ∈ S) (hfor : ∀ q, Forbidden P b v k q → q ∉ S) :
    IsReachableB b P S := by
  intro t ht
  have hs : ∀ s, s ∉ S → InHull P v k s := fun s hs => by
    by_contra h
    exact hs (hout s h)
  rcases ok_of_not_forbidden (fun h => hfor t h ht) with h | h | ⟨j, hj, h⟩
  · refine ⟨![1, 0], ?_, ?_, fun s hs' => ?_⟩
    · intro i; fin_cases i <;> simp
    · intro h0; have := congrFun h0 0; simp at this
    · have := (hs s hs').1
      have e : ![(1 : ℝ), 0] ⬝ᵥ (P s - P t) = (P (v 0) 0 - P t 0) + (P s 0 - P (v 0) 0) := by
        simp [dotProduct, Fin.sum_univ_two]
      rw [e]
      exact h.add_nonneg (by linarith)
  · refine ⟨![0, 1], ?_, ?_, fun s hs' => ?_⟩
    · intro i; fin_cases i <;> simp
    · intro h0; have := congrFun h0 1; simp at this
    · have := (hs s hs').2.1
      have e : ![(0 : ℝ), 1] ⬝ᵥ (P s - P t) = (P (v k) 1 - P t 1) + (P s 1 - P (v k) 1) := by
        simp [dotProduct, Fin.sum_univ_two]
      rw [e]
      exact h.add_nonneg (by linarith)
  · have hx := hc.xlt j hj
    have hy := hc.ylt j hj
    refine ⟨![P (v j) 1 - P (v (j + 1)) 1, P (v (j + 1)) 0 - P (v j) 0], ?_, ?_,
      fun s hs' => ?_⟩
    · intro i; fin_cases i <;> simp <;> linarith
    · intro h0; have := congrFun h0 1; simp at this; linarith
    · have e : ![P (v j) 1 - P (v (j + 1)) 1, P (v (j + 1)) 0 - P (v j) 0] ⬝ᵥ (P s - P t) =
          - cross P (v j) (v (j + 1)) t + cross P (v j) (v (j + 1)) s := by
        simp [dotProduct, Fin.sum_univ_two, cross]; ring
      rw [e]
      exact h.add_nonneg ((hs s hs').2.2 j hj)

/-- **Forbidden points are covered by the vertices.** For every nonzero `ξ ≥ 0` some vertex
fails `Ok b ⟨ξ, p_v - p_q⟩`. Left of `v 0` or right of `v k` the point dominates a vertex;
in the slab of an edge `j`, with `λ = X (v (j+1)) - X q ≥ 0`, `μ = X q - X (v j) > 0`,
`λ ⟨ξ, p_{v j} - p_q⟩ + μ ⟨ξ, p_{v (j+1)} - p_q⟩ = - ξ₁ cross (v j) (v (j+1)) q`. -/
theorem exists_not_ok_of_forbidden {b : Bool} {v : ℕ → Fin T} {k : ℕ}
    (hc : IsChain P v k) {q : Fin T} (hq : Forbidden P b v k q)
    {ξ : Fin 2 → ℝ} (hξ0 : 0 ≤ ξ) (hξ : ξ ≠ 0) :
    ∃ i ≤ k, ¬ Ok b (ξ ⬝ᵥ (P (v i) - P q)) := by
  obtain ⟨hH, hX, hY, hC⟩ := ok_of_forbidden hq
  have a0 : 0 ≤ ξ 0 := hξ0 0
  have a1 : 0 ≤ ξ 1 := hξ0 1
  -- if `ξ 1 = 0` then `ξ 0 > 0`
  have h10 : ξ 1 = 0 → 0 < ξ 0 := fun h1 => by
    rcases a0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hξ; funext i; fin_cases i
      · simp [← h]
      · simp [h1]
  have dot : ∀ i, ξ ⬝ᵥ (P (v i) - P q) =
      ξ 0 * (P (v i) 0 - P q 0) + ξ 1 * (P (v i) 1 - P q 1) := by
    intro i; simp [dotProduct, Fin.sum_univ_two]
  by_contra hcon
  push_neg at hcon
  by_cases hXk : P (v k) 0 < P q 0
  · have d := hcon k le_rfl
    rw [dot] at d
    rcases a1.lt_or_eq with h1 | h1
    · exact d.false_of_add_nonpos (Ok.mul_pos h1 hY) (by nlinarith)
    · have := d.nonneg
      rw [← h1] at this
      nlinarith [h10 h1.symm]
  push_neg at hXk
  by_cases hX0 : P q 0 ≤ P (v 0) 0
  · obtain ⟨heq, hy⟩ := (inHull_iff_of_left hc hX0).1.1 hH
    have d := hcon 0 (Nat.zero_le _)
    rw [dot, heq] at d
    exact d.false_of_add_nonpos hX (by rw [heq]; nlinarith)
  push_neg at hX0
  have hex : ∃ i, P q 0 ≤ P (v i) 0 := ⟨k, hXk⟩
  classical
  have hi0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    linarith
  obtain ⟨j, hj0⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hj : Nat.find hex = j + 1 := hj0
  have hjk : j + 1 ≤ k := by rw [← hj]; exact Nat.find_min' hex hXk
  have h1 : P q 0 ≤ P (v (j + 1)) 0 := by rw [← hj]; exact Nat.find_spec hex
  have h2 : P (v j) 0 < P q 0 := by
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    push_neg at this; exact this
  have dA := hcon j (by omega)
  have dB := hcon (j + 1) hjk
  rw [dot] at dA dB
  have key : (P q 0 - P (v j) 0) *
        (ξ 0 * (P (v (j + 1)) 0 - P q 0) + ξ 1 * (P (v (j + 1)) 1 - P q 1)) +
      (P (v (j + 1)) 0 - P q 0) * (ξ 0 * (P (v j) 0 - P q 0) + ξ 1 * (P (v j) 1 - P q 1)) +
      ξ 1 * cross P (v j) (v (j + 1)) q = 0 := by
    unfold cross; ring
  have hsum := (Ok.mul_pos (sub_pos.2 h2) dB).add_nonneg
    (mul_nonneg (sub_nonneg.2 h1) dA.nonneg)
  rcases a1.lt_or_eq with ha1 | ha1
  · exact hsum.false_of_add_nonpos (Ok.mul_pos ha1 (hC j (by omega))) key.le
  · have := dA.nonneg
    rw [← ha1] at this
    nlinarith [h10 ha1.symm]

/-- **(Weakly) reachable sets in the plane.** `S` is reachable with `Ok b` witnesses iff
`S = univ` or there is a strictly convex chain with vertices outside `S`, every point outside
`C(V)` in `S` and every forbidden point outside `S`. -/
theorem isReachableB_iff_chain (b : Bool) (S : Finset (Fin T)) :
    IsReachableB b P S ↔ S = univ ∨ ∃ (v : ℕ → Fin T) (k : ℕ), IsChain P v k ∧
      (∀ i ≤ k, v i ∉ S) ∧ (∀ q, ¬ InHull P v k q → q ∈ S) ∧
      (∀ q, Forbidden P b v k q → q ∉ S) := by
  constructor
  · intro h
    by_cases hS : S = univ
    · exact Or.inl hS
    right
    have hne : (univ \ S).Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hn
      exact hS (Finset.eq_univ_of_forall fun x => hn (Finset.mem_univ x))
    obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image (univ \ S) (fun s => P s 0) hne
    obtain ⟨v₀, hv₀, hv₀min⟩ := Finset.exists_min_image
      ((univ \ S).filter (fun s => P s 0 = P a 0)) (fun s => P s 1)
      ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
    rw [Finset.mem_filter] at hv₀
    have hmin : ∀ s ∈ univ \ S, P v₀ 0 ≤ P s 0 ∧ (P s 0 = P v₀ 0 → P v₀ 1 ≤ P s 1) := by
      intro s hs
      refine ⟨by rw [hv₀.2]; exact hamin s hs, fun he => ?_⟩
      exact hv₀min s (Finset.mem_filter.2 ⟨hs, by rw [he, hv₀.2]⟩)
    obtain ⟨v, k, hc, hv0, hvU, hall⟩ := exists_hull_chain (univ \ S) v₀ hv₀.1 hmin
    refine ⟨v, k, hc, fun i hi => ?_, fun q hq => ?_, fun q hq hqS => ?_⟩
    · have := hvU i hi
      simpa using this
    · by_contra hqS
      exact hq (hall q (by simpa using hqS))
    · obtain ⟨ξ, hξ0, hξ, hξS⟩ := h q hqS
      obtain ⟨i, hi, hlt⟩ := exists_not_ok_of_forbidden hc hq hξ0 hξ
      have hvi : v i ∉ S := by simpa using hvU i hi
      exact hlt (hξS (v i) hvi)
  · rintro (rfl | ⟨v, k, hc, _, hout, hfor⟩)
    · intro t _
      refine ⟨![1,1], ?_, ?_, fun s hs => absurd (Finset.mem_univ s) hs⟩
      · intro i; fin_cases i <;> simp
      · intro h0; have := congrFun h0 0; simp at this
    · exact isReachableB_of_chain hc hout hfor

/-- **Weakly reachable sets in the plane** (`b = false`): the forbidden region is the interior;
points on the boundary of `C(V)` other than the vertices are free. -/
theorem isWeakReachable_iff_chain (S : Finset (Fin T)) :
    IsWeakReachable P S ↔ S = univ ∨ ∃ (v : ℕ → Fin T) (k : ℕ), IsChain P v k ∧
      (∀ i ≤ k, v i ∉ S) ∧ (∀ q, ¬ InHull P v k q → q ∈ S) ∧ (∀ q, InInt P v k q → q ∉ S) := by
  rw [← isReachableB_false_iff, isReachableB_iff_chain]
  simp [Forbidden]

/-- **Reachable sets in the plane** (`b = true`): the forbidden region is all of `C(V)`, so `S` is
exactly the set of points outside `C(V)`. -/
theorem isReachable_iff_chain (S : Finset (Fin T)) :
    IsReachable P S ↔ S = univ ∨ ∃ (v : ℕ → Fin T) (k : ℕ), IsChain P v k ∧
      ∀ q, (q ∈ S ↔ ¬ InHull P v k q) := by
  rw [← isReachableB_true_iff, isReachableB_iff_chain]
  simp only [Forbidden, if_true]
  constructor
  · rintro (h | ⟨v, k, hc, _, hout, hfor⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, k, hc, fun q => ⟨fun hq hh => hfor q hh hq, fun hq => hout q hq⟩⟩
  · rintro (h | ⟨v, k, hc, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨v, k, hc, fun i hi hS => ?_, fun q hq => (h q).2 hq,
        fun q hq hqS => (h q).1 hqS hq⟩
      exact (h _).1 hS (inHull_vertex hc hi)

end Plane

end NeoTiling.PolyHardness
