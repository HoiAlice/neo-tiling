import NeoTiling.Perturbation.Box

/-!
# Least relative price perturbation: reduction to one box query

Prices `P t ∈ ℝ^d_{>0}`, outputs `y ≥ 0`. New prices are written `Q t = P t ∘ (1 + ε t)` with
`ε > -1`, `ε = relDev P Q`, and cost the weighted l_p norm `‖c ∘ ε‖_p` (`1 ≤ p < ∞`), through its
`p`-th power `lpPow p c ε`.

* `exists_weakSolvable_iff_boxFeasible`: a cost is achievable by some `Q` at which `y` is weakly
  solvable iff it is achievable by relative half-widths `0 ≤ α < 1`, `β ≥ 0` whose box
  `[P (1 - α), P (1 + β)]` passes ONE box query (`BoxFeasible`), at cost `lpPow p c (max α β)`.
  The feasible half-widths form an upward closed set (`BoxFeasible.mono`).
* `exists_oneSigned_le`: optimal prices can be taken to move every year in one direction.
* `le_sum_of_conv_lt`, `le_of_lt`: necessary conditions; dominance `Q s < Q t` forces
  `y t ≤ y s`.
* `BoxFeasible.restrict`: a NO on a subset of the years is a NO on all of them.
* `not_boxCone_of_certificate`: the NO certificate of the box query.
* `separated_bound`: the packing bound behind the termination of the algorithm.
-/

namespace NeoTiling.L1Perturbation

open NeoTiling

variable {d T : ℕ}

/-- Relative deviation `q / p - 1` of `q` from `p`. -/
noncomputable def relDev (p q : Fin d → ℝ) : Fin d → ℝ := fun i => q i / p i - 1

/-- The box `[P (1 - α), P (1 + β)]` passes the box query: its `2T` corners carry a vector `w` of
the cone of weakly reachable spectra with `w (lower corner) ≥ y ≥ w (upper corner)`. -/
def BoxFeasible (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) (α β : Fin T → Fin d → ℝ) : Prop :=
  ∃ w ∈ indicatorCone (weakReachableSpectra
      (Fin.append (fun t i => P t i * (1 - α t i)) (fun t i => P t i * (1 + β t i)))),
    (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)

/-- The `p`-th power of the weighted l_p norm of a `T × d` matrix: `∑_t ∑_i (c t i |x t i|)^p`. -/
noncomputable def lpPow (p : ℝ) (c : Fin T → Fin d → ℝ) (x : Fin T → Fin d → ℝ) : ℝ :=
  ∑ t, ∑ i, (c t i * |x t i|) ^ p

/-- The coordinatewise larger of the two half-widths. -/
def maxHW (α β : Fin T → Fin d → ℝ) : Fin T → Fin d → ℝ := fun t i => max (α t i) (β t i)

/-- `lpPow` is monotone in the absolute values of the entries. -/
theorem lpPow_mono {p : ℝ} (hp : 0 ≤ p) {c : Fin T → Fin d → ℝ} (hc : ∀ t i, 0 ≤ c t i)
    {x x' : Fin T → Fin d → ℝ} (h : ∀ t i, |x t i| ≤ |x' t i|) : lpPow p c x ≤ lpPow p c x' :=
  Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ => Real.rpow_le_rpow
    (mul_nonneg (hc t i) (abs_nonneg _)) (mul_le_mul_of_nonneg_left (h t i) (hc t i)) hp

/-- With `e = q / p - 1`, the box `[p (1 - e⁻), p (1 + e⁺)]` contains `q`, and `e⁻ < 1`. -/
private theorem mem_relBox {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    max (-(q / p - 1)) 0 < 1 ∧ p * (1 - max (-(q / p - 1)) 0) ≤ q ∧
      q ≤ p * (1 + max (q / p - 1) 0) := by
  have hr : 0 < q / p := div_pos hq hp
  have hq' : p * (1 + (q / p - 1)) = q := by field_simp; ring
  rcases le_total (q / p - 1) 0 with h | h
  · rw [max_eq_left (by linarith : 0 ≤ -(q / p - 1)), max_eq_right h, sub_neg_eq_add]
    exact ⟨by linarith, hq'.le, by nlinarith⟩
  · rw [max_eq_right (by linarith : -(q / p - 1) ≤ 0), max_eq_left h]
    exact ⟨one_pos, by nlinarith, hq'.ge⟩

/-- `max e⁻ e⁺ ≤ |e|`. -/
theorem max_negPart_posPart_le (e : ℝ) : max (max (-e) 0) (max e 0) ≤ |e| :=
  max_le (max_le (neg_le_abs _) (abs_nonneg _)) (max_le (le_abs_self _) (abs_nonneg _))

/-- If `y` is weakly solvable at positive `Q`, the box with half-widths `ε⁻, ε⁺`,
`ε = relDev P Q`, passes the box query: it contains `Q` (`box_iff`). -/
theorem boxFeasible_of_weakSolvable (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ}
    (hP : ∀ t, P t ∈ orthant d) {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {Q : Fin T → Fin d → ℝ}
    (hQ : ∀ t, Q t ∈ orthant d) (hws : WeakSolvable Q y) :
    BoxFeasible P y (fun t i => max (-relDev (P t) (Q t) i) 0)
      (fun t i => max (relDev (P t) (Q t) i) 0) := by
  refine (BoxPerturbation.box_iff hd _ _ y (fun t i => ?_) (fun t i => ?_) hy).1
    ⟨Q, fun t i => (mem_relBox (hP t i) (hQ t i)).2, hws⟩
  · exact mul_nonneg (hP t i).le (sub_nonneg.2 (mem_relBox (hP t i) (hQ t i)).1.le)
  · obtain ⟨-, h1, h2⟩ := mem_relBox (hP t i) (hQ t i)
    exact h1.trans h2

/-- **Prices in a feasible box.** If the box with half-widths `α, β ≥ 0`, `α < 1`, passes the box
query, some positive `Q` with weakly solvable `y` moves every year in one direction, has
`|relDev P Q| ≤ max α β` coordinatewise, and lies in the box: `-α ≤ relDev P Q ≤ β`.

Proof. `path_of_corners` on the path `P (1 - α (1 - 2 s))` for `s ≤ 1/2`, `P (1 + β (2 s - 1))`
for `s ≥ 1/2`: continuous, from the lower to the upper corner through `P` at `s = 1/2`, positive
since `α < 1`. -/
theorem exists_oneSigned_of_boxFeasible (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ}
    (hP : ∀ t, P t ∈ orthant d) {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {α β : Fin T → Fin d → ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hα1 : ∀ t i, α t i < 1) (h : BoxFeasible P y α β) :
    ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
      (∀ t, (∀ i, Q t i ≤ P t i) ∨ (∀ i, P t i ≤ Q t i)) ∧
      (∀ t i, |relDev (P t) (Q t) i| ≤ maxHW α β t i) ∧
      ∀ t i, -α t i ≤ relDev (P t) (Q t) i ∧ relDev (P t) (Q t) i ≤ β t i := by
  have hpos : ∀ t i, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      0 < 1 - α t i * max (1 - 2 * r) 0 + β t i * max (2 * r - 1) 0 := by
    intro t i r hr
    have h1 : max (1 - 2 * r) 0 ≤ 1 := max_le (by linarith [hr.1]) zero_le_one
    have := mul_le_mul_of_nonneg_left h1 (hα t i)
    have := mul_nonneg (hβ t i) (le_max_right (2 * r - 1) 0)
    linarith [hα1 t i]
  obtain ⟨s, hs, hws⟩ := PricePerturbation.path_of_corners hd (fun t i => P t i * (1 - α t i))
    (fun t i => P t i * (1 + β t i))
    (fun t r i => P t i * (1 - α t i * max (1 - 2 * r) 0 + β t i * max (2 * r - 1) 0))
    (fun t => by fun_prop) (fun t => by funext i; norm_num) (fun t => by funext i; norm_num)
    (fun t r hr i => mul_nonneg (hP t i).le (hpos t i r hr).le) y hy h
  refine ⟨fun t i => P t i * (1 - α t i * max (1 - 2 * s t) 0 + β t i * max (2 * s t - 1) 0),
    fun t i => mul_pos (hP t i) (hpos t i _ (hs t)), hws, fun t => ?_, fun t i => ?_,
    fun t i => ?_⟩
  · obtain ⟨h0, h1⟩ := hs t
    rcases le_total (s t) (1 / 2) with hc | hc
    · refine Or.inl fun i => ?_
      beta_reduce
      rw [max_eq_right (by linarith : 2 * s t - 1 ≤ 0), mul_zero, add_zero]
      nlinarith [hP t i, mul_nonneg (hα t i) (le_max_right (1 - 2 * s t) 0)]
    · refine Or.inr fun i => ?_
      beta_reduce
      rw [max_eq_right (by linarith : 1 - 2 * s t ≤ 0), mul_zero, sub_zero]
      nlinarith [hP t i, mul_nonneg (hβ t i) (le_max_right (2 * s t - 1) 0)]
  · obtain ⟨h0, h1⟩ := hs t
    have ha : 0 ≤ α t i := hα t i
    have hb : 0 ≤ β t i := hβ t i
    have hma := le_max_left (α t i) (β t i)
    have hmb := le_max_right (α t i) (β t i)
    simp only [relDev, maxHW]
    rw [mul_div_cancel_left₀ _ (hP t i).ne', abs_le]
    rcases le_total (s t) (1 / 2) with hc | hc
    · rw [max_eq_right (by linarith : 2 * s t - 1 ≤ 0),
        max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * s t)]
      constructor <;> nlinarith
    · rw [max_eq_right (by linarith : 1 - 2 * s t ≤ 0),
        max_eq_left (by linarith : (0 : ℝ) ≤ 2 * s t - 1)]
      constructor <;> nlinarith
  · obtain ⟨h0, h1⟩ := hs t
    have ha : 0 ≤ α t i := hα t i
    have hb : 0 ≤ β t i := hβ t i
    simp only [relDev]
    rw [mul_div_cancel_left₀ _ (hP t i).ne']
    rcases le_total (s t) (1 / 2) with hc | hc
    · rw [max_eq_right (by linarith : 2 * s t - 1 ≤ 0),
        max_eq_left (by linarith : (0 : ℝ) ≤ 1 - 2 * s t)]
      constructor <;> nlinarith
    · rw [max_eq_right (by linarith : 1 - 2 * s t ≤ 0),
        max_eq_left (by linarith : (0 : ℝ) ≤ 2 * s t - 1)]
      constructor <;> nlinarith

/-- **Reduction to one box query.** For `d ≥ 2`, `1 ≤ p` and weights `c ≥ 0`: some positive `Q`
with weakly solvable `y` has `lpPow p c (relDev P Q) ≤ C` iff some half-widths `0 ≤ α < 1`,
`β ≥ 0` pass the box query with `lpPow p c (max α β) ≤ C`.

Proof. `→`: `α = ε⁻`, `β = ε⁺` for `ε = relDev P Q`, so `max α β = |ε|`; the box
`[P (1 - α), P (1 + β)]` contains `Q`, so it passes the query by `box_iff`. `←`:
`exists_oneSigned_of_boxFeasible` gives `Q` in the box, so `|relDev P Q| ≤ max α β`
coordinatewise, and `lpPow` is monotone. -/
theorem exists_weakSolvable_iff_boxFeasible (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 1 ≤ p)
    (c : Fin T → Fin d → ℝ) (hc : ∀ t i, 0 ≤ c t i) (C : ℝ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        lpPow p c (fun t => relDev (P t) (Q t)) ≤ C) ↔
      ∃ α β : Fin T → Fin d → ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (∀ t i, α t i < 1) ∧ BoxFeasible P y α β ∧
        lpPow p c (maxHW α β) ≤ C := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  constructor
  · rintro ⟨Q, hQ, hws, hC⟩
    refine ⟨fun t i => max (-relDev (P t) (Q t) i) 0, fun t i => max (relDev (P t) (Q t) i) 0,
      fun t i => le_max_right _ _, fun t i => le_max_right _ _,
      fun t i => (mem_relBox (hP t i) (hQ t i)).1, boxFeasible_of_weakSolvable hd hP hy hQ hws,
      (lpPow_mono hp0 hc fun t i => ?_).trans hC⟩
    rw [abs_of_nonneg ((le_max_right _ _).trans (le_max_left _ _))]
    exact max_negPart_posPart_le _
  · rintro ⟨α, β, hα, hβ, hα1, hbox, hC⟩
    obtain ⟨Q, hQ, hws, -, hle, -⟩ := exists_oneSigned_of_boxFeasible hd hP hy hα hβ hα1 hbox
    exact ⟨Q, hQ, hws, (lpPow_mono hp0 hc fun t i => (hle t i).trans (le_abs_self _)).trans hC⟩

/-- **One-signed solutions.** For every positive `Q` at which `y` is weakly solvable there is a
positive `Q'` at which `y` is weakly solvable, moving every year in one direction, with
`|relDev P Q'| ≤ |relDev P Q|` coordinatewise (so every cost monotone in the absolute
deviations, e.g. `lpPow p c`, does not increase).

Proof. The box with half-widths `ε⁻, ε⁺`, `ε = relDev P Q`, contains `Q` and passes the query;
`exists_oneSigned_of_boxFeasible` gives `Q'` with `|relDev P Q'| ≤ max ε⁻ ε⁺ = |ε|`. -/
theorem exists_oneSigned_le (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {Q : Fin T → Fin d → ℝ} (hQ : ∀ t, Q t ∈ orthant d)
    (hws : WeakSolvable Q y) :
    ∃ Q' : Fin T → Fin d → ℝ, (∀ t, Q' t ∈ orthant d) ∧ WeakSolvable Q' y ∧
      (∀ t, (∀ i, Q' t i ≤ P t i) ∨ (∀ i, P t i ≤ Q' t i)) ∧
      ∀ t i, |relDev (P t) (Q' t) i| ≤ |relDev (P t) (Q t) i| := by
  obtain ⟨Q', hQ', hws', hos, hle, -⟩ := exists_oneSigned_of_boxFeasible hd hP hy
    (fun t i => le_max_right _ _) (fun t i => le_max_right _ _)
    (fun t i => (mem_relBox (hP t i) (hQ t i)).1) (boxFeasible_of_weakSolvable hd hP hy hQ hws)
  exact ⟨Q', hQ', hws', hos, fun t i => (hle t i).trans (max_negPart_posPart_le _)⟩

/-- **Monotonicity.** Larger half-widths (with `α' ≤ 1`, so the lower corners stay
nonnegative) keep the box query feasible: `box_iff` twice, a point of the smaller box lies in the
larger one. -/
theorem BoxFeasible.mono (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {α β α' β' : Fin T → Fin d → ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (h : BoxFeasible P y α β) (hαα' : α ≤ α') (hββ' : β ≤ β')
    (hα' : ∀ t i, α' t i ≤ 1) : BoxFeasible P y α' β' := by
  have hL : ∀ a : Fin T → Fin d → ℝ, (∀ t i, a t i ≤ 1) → ∀ t,
      0 ≤ fun i => P t i * (1 - a t i) := fun a ha t i =>
    mul_nonneg (hP t i).le (by linarith [ha t i])
  have hLU : ∀ a b : Fin T → Fin d → ℝ, 0 ≤ a → 0 ≤ b → ∀ t i,
      P t i * (1 - a t i) ≤ P t i * (1 + b t i) := fun a b ha hb t i => by
    have h1 : (0 : ℝ) ≤ a t i := ha t i
    have h2 : (0 : ℝ) ≤ b t i := hb t i
    exact mul_le_mul_of_nonneg_left (by linarith) (hP t i).le
  obtain ⟨Q, hQ, hws⟩ := (BoxPerturbation.box_iff hd _ _ y
    (hL α fun t i => (hαα' t i).trans (hα' t i)) (hLU α β hα hβ) hy).2 h
  refine (BoxPerturbation.box_iff hd _ _ y (hL α' hα')
    (hLU α' β' (hα.trans hαα') (hβ.trans hββ')) hy).1 ⟨Q, fun t i => ⟨?_, ?_⟩, hws⟩
  · exact (mul_le_mul_of_nonneg_left (by linarith [hαα' t i]) (hP t i).le).trans (hQ t i).1
  · exact (hQ t i).2.trans (mul_le_mul_of_nonneg_left (by linarith [hββ' t i]) (hP t i).le)

/-- **Deleting years.** A feasible box stays feasible for any subset of the years (given by an
embedding `e`): a weakly reachable set of all corners, intersected with the corners of the kept
years, is weakly reachable there (same witnesses), and the cone vector restricts. -/
theorem BoxFeasible.restrict {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ} {α β : Fin T → Fin d → ℝ}
    {k : ℕ} (e : Fin k ↪ Fin T) (h : BoxFeasible P y α β) :
    BoxFeasible (fun j => P (e j)) (fun j => y (e j)) (fun j => α (e j)) (fun j => β (e j)) := by
  classical
  obtain ⟨w, hw, hlo, hhi⟩ := h
  set W := Fin.append (fun t i => P t i * (1 - α t i)) (fun t i => P t i * (1 + β t i)) with hW
  -- the corners of the kept years, as indices among all corners
  let g : Fin (k + k) → Fin (T + T) :=
    Fin.append (fun j => Fin.castAdd T (e j)) (fun j => Fin.natAdd T (e j))
  have hg : Fin.append (fun j i => P (e j) i * (1 - α (e j) i))
      (fun j i => P (e j) i * (1 + β (e j) i)) = fun r => W (g r) := by
    funext r
    refine Fin.addCases (fun j => ?_) (fun j => ?_) r <;>
      simp only [g, W, Fin.append_left, Fin.append_right]
  -- restriction maps the cone of all corners into the cone of the kept corners
  have hcone : ∀ x ∈ indicatorCone (weakReachableSpectra W),
      (fun r => x (g r)) ∈ indicatorCone (weakReachableSpectra (fun r => W (g r))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      refine Submodule.subset_span ⟨Finset.univ.filter (fun r => g r ∈ S), ?_, ?_⟩
      · intro t ht
        rw [Finset.mem_filter] at ht
        obtain ⟨ξ, h0, hne, hξ⟩ := hS (g t) ht.2
        exact ⟨ξ, h0, hne, fun s hs => hξ (g s) (by simpa using hs)⟩
      · funext r; simp [Set.indicator_apply]
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  unfold BoxFeasible
  rw [hg]
  refine ⟨fun r => w (g r), hcone w hw, fun j => ?_, fun j => ?_⟩
  · simpa only [g, Fin.append_left] using hlo (e j)
  · simpa only [g, Fin.append_right] using hhi (e j)

/-! ### Necessary conditions: covers and dominance -/

/-- A weakly reachable `S ∋ t` meets `A` when a convex combination of the prices of `A` is
strictly below `Q t`: otherwise the witness `ξ` of `t` gives `0 ≤ ⟨ξ, ∑ μ_s Q s - Q t⟩ < 0`. -/
theorem meets_of_conv_lt {Q : Fin T → Fin d → ℝ} {t : Fin T} {A : Finset (Fin T)}
    (μ : Fin T → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμA : ∀ s ∉ A, μ s = 0)
    (hμ1 : ∑ s, μ s = 1) (hlt : ∀ i, ∑ s, μ s * Q s i < Q t i)
    {S : Finset (Fin T)} (hS : IsWeakReachable Q S) (htS : t ∈ S) : ∃ s ∈ A, s ∈ S := by
  by_contra hno
  push_neg at hno
  obtain ⟨ξ, hξ0, hξne, hξ⟩ := hS t htS
  have h1 : 0 ≤ ∑ s, μ s * (ξ ⬝ᵥ (Q s - Q t)) := by
    refine Finset.sum_nonneg fun s _ => ?_
    by_cases hs : s ∈ A
    · exact mul_nonneg (hμ0 s) (hξ s (hno s hs))
    · simp [hμA s hs]
  have h2 : ∑ s, μ s * (ξ ⬝ᵥ (Q s - Q t)) = ∑ i, ξ i * (∑ s, μ s * Q s i - Q t i) := by
    have e : ∀ i, ∑ s, μ s * (ξ i * (Q s i - Q t i)) =
        ξ i * (∑ s, μ s * Q s i - Q t i) := by
      intro i
      have : ∑ s, μ s * (ξ i * (Q s i - Q t i)) =
          ξ i * ∑ s, μ s * Q s i - (∑ s, μ s) * (ξ i * Q t i) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, hμ1]; ring
    simp only [dotProduct, Pi.sub_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => e i
  obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra h; push_neg at h; exact hξne (funext h)
  have hip : 0 < ξ i := lt_of_le_of_ne (hξ0 i) (Ne.symm hi)
  have h3 : ∑ j, ξ j * (∑ s, μ s * Q s j - Q t j) < 0 := by
    refine Finset.sum_neg' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · exact mul_nonpos_of_nonneg_of_nonpos (hξ0 j) (by linarith [hlt j])
    · exact mul_neg_of_pos_of_neg hip (by linarith [hlt i])
  linarith

/-- **Cover condition.** If a convex combination of the prices of the years in `A` is strictly
below `Q t` in every coordinate and `y` is weakly solvable at `Q`, then `y t ≤ ∑_{s ∈ A} y s`.

Proof. By `weakSolvable_iff`, `y` is in the cone of weakly reachable spectra. A weakly reachable
`S ∋ t` meets `A` (`meets_of_conv_lt`). So the linear functional `x ↦ ∑_{s ∈ A} x s - x t` is
`≥ 0` on the generators, hence on the cone. -/
theorem le_sum_of_conv_lt (hd : 2 ≤ d) {Q : Fin T → Fin d → ℝ} (hQ : ∀ t, 0 ≤ Q t)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) (hws : WeakSolvable Q y) {t : Fin T}
    {A : Finset (Fin T)} (μ : Fin T → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμA : ∀ s ∉ A, μ s = 0)
    (hμ1 : ∑ s, μ s = 1) (hlt : ∀ i, ∑ s, μ s * Q s i < Q t i) :
    y t ≤ ∑ s ∈ A, y s := by
  classical
  rw [weakSolvable_iff hd hQ hy] at hws
  suffices H : ∀ x ∈ indicatorCone (weakReachableSpectra Q), x t ≤ ∑ s ∈ A, x s from H y hws
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    beta_reduce
    by_cases htS : t ∈ S
    · obtain ⟨s, hsA, hsS⟩ := meets_of_conv_lt μ hμ0 hμA hμ1 hlt hS htS
      have h1 : ((S : Set (Fin T)).indicator (1 : Fin T → ℝ)) t = 1 := by simp [htS]
      rw [h1]
      calc (1 : ℝ) = ((S : Set (Fin T)).indicator (1 : Fin T → ℝ)) s := by simp [hsS]
        _ ≤ _ := Finset.single_le_sum (f := fun s => ((S : Set (Fin T)).indicator (1 : Fin T → ℝ)) s)
            (fun r _ => by simp only [Set.indicator_apply]; split_ifs <;> norm_num) hsA
    · have h1 : ((S : Set (Fin T)).indicator (1 : Fin T → ℝ)) t = 0 := by simp [htS]
      rw [h1]
      exact Finset.sum_nonneg fun r _ => by simp only [Set.indicator_apply]; split_ifs <;> norm_num
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [Pi.add_apply, Finset.sum_add_distrib]; linarith
  | smul a x _ hx =>
    change (a : ℝ) * x t ≤ ∑ s ∈ A, (a : ℝ) * x s
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hx a.2

/-- **Dominance.** If `Q s < Q t` in every coordinate and `y` is weakly solvable at `Q`, then
`y t ≤ y s` (`le_sum_of_conv_lt` with `A = {s}`). -/
theorem le_of_lt (hd : 2 ≤ d) {Q : Fin T → Fin d → ℝ} (hQ : ∀ t, 0 ≤ Q t) {y : Fin T → ℝ}
    (hy : ∀ t, 0 ≤ y t) (hws : WeakSolvable Q y) {s t : Fin T} (hst : ∀ i, Q s i < Q t i) :
    y t ≤ y s := by
  classical
  have := le_sum_of_conv_lt hd hQ hy hws (t := t) (A := {s}) (Pi.single s 1)
    (fun r => by by_cases h : r = s <;> simp [Pi.single_apply, h])
    (fun r hr => by simp at hr; simp [hr])
    (by simp) (fun i => by simpa [Pi.single_apply] using hst i)
  simpa using this

/-! ### The NO certificate of the box query -/

/-- **NO certificate.** Let `C` be a finite set of covers `(r, A)`: a convex combination of the
corners of `A` is strictly below the corner `r`. If `λ` has `∑_{r ∈ S} λ r ≥ 0` on every `S` that
respects `C` (contains a point of `A` whenever it contains `r`), `λ ≤ 0` on the lower corners and
`∑ (-λ_lower) y > ∑ (λ_upper)⁺ y`, then no `w` of the cone meets the bounds of the box query.

Proof. Weakly reachable sets respect `C` (`meets_of_conv_lt`), so `w ↦ ∑ λ w` and the coordinates
are `≥ 0` on the cone. For `w` with `w_lower ≥ y ≥ w_upper ≥ 0` this sum is
`≤ ∑ λ_lower y + ∑ (λ_upper)⁺ y < 0`. -/
theorem not_boxCone_of_certificate {W : Fin (T + T) → Fin d → ℝ} (y : Fin T → ℝ)
    (C : Finset (Fin (T + T) × Finset (Fin (T + T))))
    (hcov : ∀ e ∈ C, ∃ μ : Fin (T + T) → ℝ, (∀ s, 0 ≤ μ s) ∧ (∀ s ∉ e.2, μ s = 0) ∧
      ∑ s, μ s = 1 ∧ ∀ i, ∑ s, μ s * W s i < W e.1 i)
    (lam : Fin (T + T) → ℝ)
    (hF2 : ∀ S : Finset (Fin (T + T)), (∀ e ∈ C, e.1 ∈ S → ∃ s ∈ e.2, s ∈ S) →
      0 ≤ ∑ r ∈ S, lam r)
    (hlo : ∀ t, lam (Fin.castAdd T t) ≤ 0)
    (hF1 : 0 < ∑ t, (-lam (Fin.castAdd T t)) * y t - ∑ t, max (lam (Fin.natAdd T t)) 0 * y t) :
    ¬ ∃ w ∈ indicatorCone (weakReachableSpectra W),
      (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  classical
  rintro ⟨w, hw, hlow, hupp⟩
  have key : ∀ x ∈ indicatorCone (weakReachableSpectra W), 0 ≤ ∑ r, lam r * x r ∧ 0 ≤ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      refine ⟨?_, fun r => ?_⟩
      · have : ∑ r, lam r * (S : Set (Fin (T + T))).indicator 1 r = ∑ r ∈ S, lam r := by
          simp [Set.indicator_apply]
        rw [this]
        refine hF2 S fun e he h1 => ?_
        obtain ⟨μ, h0, hA, h1', hlt⟩ := hcov e he
        exact meets_of_conv_lt μ h0 hA h1' hlt hS h1
      · simp only [Set.indicator_apply]; split_ifs <;> norm_num
    | zero => simp
    | add x z _ _ hx hz =>
      refine ⟨?_, add_nonneg hx.2 hz.2⟩
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; linarith [hx.1, hz.1]
    | smul a x _ hx =>
      refine ⟨?_, fun r => mul_nonneg a.2 (hx.2 r)⟩
      change 0 ≤ ∑ r, lam r * ((a : ℝ) * x r)
      have : ∑ r, lam r * ((a : ℝ) * x r) = (a : ℝ) * ∑ r, lam r * x r := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      rw [this]; exact mul_nonneg a.2 hx.1
  obtain ⟨h1, h0⟩ := key w hw
  rw [Fin.sum_univ_add] at h1
  have hc := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) =>
    mul_le_mul_of_nonpos_left (hlow t) (hlo t)
  have hn := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) =>
    (mul_le_mul_of_nonneg_right (le_max_left (lam (Fin.natAdd T t)) 0) (h0 (Fin.natAdd T t))).trans
      (mul_le_mul_of_nonneg_left (hupp t) (le_max_right (lam (Fin.natAdd T t)) 0))
  simp only [neg_mul, Finset.sum_neg_distrib] at hF1
  linarith

/-! ### Termination of the exact algorithm -/

/-- **Packing bound.** Points of `[0, M]^n` such that every later point exceeds every earlier one
by `τ > 0` in some coordinate are at most `(⌊M / τ⌋ + 1)^n` many: the cells
`⌊z / τ⌋` are pairwise different. -/
theorem separated_bound {n K : ℕ} {M τ : ℝ} (hτ : 0 < τ) (z : Fin K → Fin n → ℝ)
    (hz : ∀ k j, 0 ≤ z k j ∧ z k j ≤ M) (hsep : ∀ k l, k < l → ∃ j, z k j + τ ≤ z l j) :
    K ≤ (⌊M / τ⌋₊ + 1) ^ n := by
  have hlt : ∀ k j, ⌊z k j / τ⌋₊ < ⌊M / τ⌋₊ + 1 := fun k j =>
    Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (hz k j).2 hτ.le))
  let f : Fin K → (Fin n → Fin (⌊M / τ⌋₊ + 1)) := fun k j => ⟨⌊z k j / τ⌋₊, hlt k j⟩
  have key : ∀ k l, k < l → f k ≠ f l := by
    intro k l hkl heq
    obtain ⟨j, hj⟩ := hsep k l hkl
    have h := congrArg (fun g => (g j : ℕ)) heq
    simp only [f] at h
    have h3 : z k j / τ + 1 ≤ z l j / τ := by
      rw [div_add_one hτ.ne']; exact div_le_div_of_nonneg_right hj hτ.le
    have h4 : ⌊z k j / τ⌋₊ + 1 ≤ ⌊z l j / τ⌋₊ := by
      rw [← Nat.floor_add_one (div_nonneg (hz k j).1 hτ.le)]
      exact Nat.floor_le_floor h3
    omega
  have hinj : Function.Injective f := by
    intro k l h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact key k l h' h
    · exact key l k h' h.symm
  have := Fintype.card_le_of_injective f hinj
  simpa [Fintype.card_fun, Fintype.card_fin] using this

end NeoTiling.L1Perturbation
