import NeoTiling.Perturbation.Hex
import NeoTiling.Perturbation.Box

/-!
# Least l_p perturbation of log prices: reduction to boxes, one-signedness, dominance

Prices `P t ∈ ℝ^d_{>0}`, outputs `y ≥ 0`. New prices `Q` cost one weighted l_p norm (`1 ≤ p ≤ ∞`)
of the whole vector `log Q - log P`; more generally `N t (log Q t - log P t)` per year with `N t`
monotone in absolute values (`AbsMono`) and the year costs combined monotonically.

* `exists_weakSolvable_iff_boxFeasible` (`_lp`, `_linf`): a cost is achievable by some `Q` at
  which `y` is weakly solvable iff it is achievable by log half-widths `α, β ≥ 0` whose box
  `[P e^{-α}, P e^{β}]` passes ONE box query, at cost `N t (α t + β t)`. The feasible half-widths
  form an upward closed set (`BoxFeasible.mono`).
* `exists_oneSigned`, `exists_oneSigned_le`, `exists_lt_of_mixed_lp`: optimal prices move every
  year in one direction (strictly forced for `p < ∞`).
* `le_sum_of_conv_lt`, `le_of_lt`: necessary conditions; dominance `Q s < Q t` forces `y t ≤ y s`.
  In log coordinates these are linear disjunctions: the dominance relaxation is a mixed-integer
  program.
* `BoxFeasible.restrict`: a NO on a subset of the years is a NO on all of them (with
  `BoxFeasible.mono`: validity of the box cuts of the exact algorithm).
* `separated_bound`: the packing bound behind its finite termination.
-/

namespace NeoTiling.L1Perturbation

open NeoTiling Real

variable {d T : ℕ}

/-- Log deviation of `q` from `p`. -/
noncomputable def logDev (p q : Fin d → ℝ) : Fin d → ℝ := fun i => log (q i) - log (p i)

/-- `N` is monotone in the absolute values of the coordinates. -/
def AbsMono (N : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ u v : Fin d → ℝ, (∀ i, |u i| ≤ |v i|) → N u ≤ N v

/-- The box with log half-widths `α` (down) and `β` (up) passes the box query: the `2T` corners
`P t ∘ e^{-α t}`, `P t ∘ e^{β t}` carry a vector `w` of the cone of weakly reachable spectra with
`w (lower corner) ≥ y ≥ w (upper corner)`. -/
def BoxFeasible (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) (α β : Fin T → Fin d → ℝ) : Prop :=
  ∃ w ∈ indicatorCone (weakReachableSpectra
      (Fin.append (fun t i => P t i * exp (-α t i)) (fun t i => P t i * exp (β t i)))),
    (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)

/-- The box `[min p q, max p q]` written with log half-widths `(log p - log q)⁺`, `(log q - log p)⁺`
contains `q`. -/
theorem box_contains_aux {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p * exp (-max (log p - log q) 0) ≤ q ∧ q ≤ p * exp (max (log q - log p) 0) := by
  rcases le_total (log p - log q) 0 with h | h
  · have h2 : 0 ≤ log q - log p := by linarith
    rw [max_eq_right h, max_eq_left h2]
    have : log p ≤ log q := by linarith
    have hpq : p ≤ q := (Real.log_le_log_iff hp hq).1 this
    refine ⟨by simpa using hpq, ?_⟩
    have : q = p * exp (log q - log p) := by
      rw [Real.exp_sub, Real.exp_log hp, Real.exp_log hq]; field_simp
    exact this.le
  · have h2 : log q - log p ≤ 0 := by linarith
    rw [max_eq_left h, max_eq_right h2]
    have : log q ≤ log p := by linarith
    have hqp : q ≤ p := (Real.log_le_log_iff hq hp).1 this
    refine ⟨?_, by simpa using hqp⟩
    have : q = p * exp (-(log p - log q)) := by
      rw [Real.exp_neg, Real.exp_sub, Real.exp_log hp, Real.exp_log hq]; field_simp
    exact this.ge

/-- **Reduction to boxes.** For every vector of year budgets `c`: some positive `Q` with weakly
solvable `y` and year costs `N t (log Q t - log P t) ≤ c t` exists iff some half-widths
`α, β ≥ 0` pass the box query with `N t (α t + β t) ≤ c t`.

Proof. `→`: `α = (log P - log Q)⁺`, `β = (log Q - log P)⁺`; the box contains `Q`, so `box_iff`
gives the corner condition; `α + β = |log Q - log P|`. `←`: `path_of_corners` on the log-linear
segments `s ↦ P ∘ exp (-α + s (α + β))`; the point has `|log q - log p| ≤ α + β`
coordinatewise. -/
theorem exists_weakSolvable_iff_boxFeasible (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    (N : Fin T → (Fin d → ℝ) → ℝ) (hN : ∀ t, AbsMono (N t)) (c : Fin T → ℝ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        ∀ t, N t (logDev (P t) (Q t)) ≤ c t) ↔
      ∃ α β : Fin T → Fin d → ℝ, 0 ≤ α ∧ 0 ≤ β ∧ BoxFeasible P y α β ∧
        ∀ t, N t (α t + β t) ≤ c t := by
  constructor
  · rintro ⟨Q, hQ, hws, hc⟩
    refine ⟨fun t i => max (log (P t i) - log (Q t i)) 0,
      fun t i => max (log (Q t i) - log (P t i)) 0, fun t i => le_max_right _ _,
      fun t i => le_max_right _ _, ?_, fun t => ?_⟩
    · refine (BoxPerturbation.box_iff hd _ _ y (fun t i => mul_pos (hP t i) (exp_pos _))
        (fun t i => ?_) hy).1 ⟨Q, fun t i => box_contains_aux (hP t i) (hQ t i), hws⟩
      exact (mul_le_mul_of_nonneg_left (exp_le_exp.2 (by
        have := le_max_right (log (P t i) - log (Q t i)) 0
        have := le_max_right (log (Q t i) - log (P t i)) 0
        linarith)) (hP t i).le)
    · refine (hN t _ _ fun i => ?_).trans (hc t)
      simp only [Pi.add_apply, logDev]
      rcases le_total (log (P t i) - log (Q t i)) 0 with h | h
      · have h2 : 0 ≤ log (Q t i) - log (P t i) := by linarith
        rw [max_eq_right h, max_eq_left h2, zero_add, abs_of_nonneg h2]
      · rw [max_eq_left h, max_eq_right (by linarith : log (Q t i) - log (P t i) ≤ 0)]
        rw [add_zero, abs_of_nonneg h, abs_of_nonpos (by linarith)]; linarith
  · rintro ⟨α, β, hα, hβ, hbox, hc⟩
    obtain ⟨s, hs, hws⟩ := PricePerturbation.path_of_corners hd
      (fun t i => P t i * exp (-α t i)) (fun t i => P t i * exp (β t i))
      (fun t s i => P t i * exp (-α t i + s * (α t i + β t i)))
      (fun t => by fun_prop)
      (fun t => by funext i; simp)
      (fun t => by funext i; simp only; congr 2; ring)
      (fun t s _ i => (mul_pos (hP t i) (exp_pos _)).le) y hy hbox
    refine ⟨fun t i => P t i * exp (-α t i + s t * (α t i + β t i)),
      fun t i => mul_pos (hP t i) (exp_pos _), hws, fun t => ?_⟩
    refine (hN t _ _ fun i => ?_).trans (hc t)
    have h1 : logDev (P t) (fun i => P t i * exp (-α t i + s t * (α t i + β t i))) i =
        -α t i + s t * (α t i + β t i) := by
      simp only [logDev]
      rw [Real.log_mul (hP t i).ne' (exp_pos _).ne', Real.log_exp]; ring
    rw [h1]
    obtain ⟨hs0, hs1⟩ := hs t
    have ha : 0 ≤ α t i := hα t i
    have hb : 0 ≤ β t i := hβ t i
    simp only [Pi.add_apply]
    rw [abs_of_nonneg (by linarith : 0 ≤ α t i + β t i), abs_le]
    constructor <;> nlinarith

/-- **Monotonicity.** Larger half-widths keep the box query feasible (`box_iff` twice: a point of
the smaller box lies in the larger one). -/
theorem BoxFeasible.mono (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {α β α' β' : Fin T → Fin d → ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (h : BoxFeasible P y α β) (hαα' : α ≤ α') (hββ' : β ≤ β') :
    BoxFeasible P y α' β' := by
  have hLU : ∀ a b : Fin T → Fin d → ℝ, 0 ≤ a → 0 ≤ b → ∀ t i,
      P t i * exp (-a t i) ≤ P t i * exp (b t i) := fun a b ha hb t i =>
    mul_le_mul_of_nonneg_left (exp_le_exp.2 (by
      have h1 : 0 ≤ a t i := ha t i
      have h2 : 0 ≤ b t i := hb t i
      linarith)) (hP t i).le
  obtain ⟨Q, hQ, hws⟩ := (BoxPerturbation.box_iff hd (fun t i => P t i * exp (-α t i))
    (fun t i => P t i * exp (β t i)) y (fun t i => mul_pos (hP t i) (exp_pos _))
    (hLU α β hα hβ) hy).2 h
  refine (BoxPerturbation.box_iff hd (fun t i => P t i * exp (-α' t i))
    (fun t i => P t i * exp (β' t i)) y (fun t i => mul_pos (hP t i) (exp_pos _))
    (hLU α' β' (hα.trans hαα') (hβ.trans hββ')) hy).1 ⟨Q, fun t i => ⟨?_, ?_⟩, hws⟩
  · exact (mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg (hαα' t i))) (hP t i).le).trans
      (hQ t i).1
  · exact (hQ t i).2.trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 (hββ' t i)) (hP t i).le)

/-- **One-signed solution.** A feasible box gives a feasible `Q` that moves every year in one
direction, with year cost at most `max (N α) (N β)`.

Proof. `path_of_corners` on the path `P ∘ e^{-α (1 - 2 s)}` for `s ≤ 1/2`,
`P ∘ e^{β (2 s - 1)}` for `s ≥ 1/2` (continuous, through `P` at `s = 1/2`). -/
theorem exists_oneSigned (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) (N : Fin T → (Fin d → ℝ) → ℝ)
    (hN : ∀ t, AbsMono (N t)) {α β : Fin T → Fin d → ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : BoxFeasible P y α β) :
    ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
      ∀ t, ((∀ i, Q t i ≤ P t i) ∨ (∀ i, P t i ≤ Q t i)) ∧
        N t (logDev (P t) (Q t)) ≤ max (N t (α t)) (N t (β t)) := by
  obtain ⟨s, hs, hws⟩ := PricePerturbation.path_of_corners hd (fun t i => P t i * exp (-α t i))
    (fun t i => P t i * exp (β t i))
    (fun t r i => P t i * exp (-α t i * max (1 - 2 * r) 0 + β t i * max (2 * r - 1) 0))
    (fun t => by fun_prop)
    (fun t => by funext i; norm_num)
    (fun t => by funext i; norm_num)
    (fun t r _ i => (mul_pos (hP t i) (exp_pos _)).le) y hy h
  refine ⟨fun t i => P t i * exp (-α t i * max (1 - 2 * s t) 0 + β t i * max (2 * s t - 1) 0),
    fun t i => mul_pos (hP t i) (exp_pos _), hws, fun t => ?_⟩
  obtain ⟨h0, h1⟩ := hs t
  have hld : logDev (P t) (fun i => P t i * exp (-α t i * max (1 - 2 * s t) 0 +
      β t i * max (2 * s t - 1) 0)) =
      fun i => -α t i * max (1 - 2 * s t) 0 + β t i * max (2 * s t - 1) 0 := by
    funext i
    simp only [logDev]
    rw [Real.log_mul (hP t i).ne' (exp_pos _).ne', Real.log_exp]; ring
  rw [hld]
  have hαt : ∀ i, 0 ≤ α t i := fun i => hα t i
  have hβt : ∀ i, 0 ≤ β t i := fun i => hβ t i
  rcases le_total (s t) (1 / 2) with hc | hc
  · have ha : max (1 - 2 * s t) 0 = 1 - 2 * s t := max_eq_left (by linarith)
    have hb : max (2 * s t - 1) 0 = 0 := max_eq_right (by linarith)
    simp only [ha, hb, mul_zero, add_zero]
    refine ⟨Or.inl fun i => ?_, le_max_of_le_left (hN t _ _ fun i => ?_)⟩
    · have : -α t i * (1 - 2 * s t) ≤ 0 := by nlinarith [hαt i]
      calc _ ≤ P t i * 1 := mul_le_mul_of_nonneg_left (by simpa using this) (hP t i).le
        _ = _ := mul_one _
    · rw [abs_of_nonneg (hαt i), abs_le]; constructor <;> nlinarith [hαt i]
  · have ha : max (1 - 2 * s t) 0 = 0 := max_eq_right (by linarith)
    have hb : max (2 * s t - 1) 0 = 2 * s t - 1 := max_eq_left (by linarith)
    simp only [ha, hb, mul_zero, zero_add]
    refine ⟨Or.inr fun i => ?_, le_max_of_le_right (hN t _ _ fun i => ?_)⟩
    · have : 0 ≤ β t i * (2 * s t - 1) := by nlinarith [hβt i]
      calc P t i = P t i * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using this) (hP t i).le
    · rw [abs_of_nonneg (hβt i), abs_le]; constructor <;> nlinarith [hβt i]

/-- From any feasible `Q`: a feasible one-signed `Q'` whose year cost is at most
`max (N u⁻) (N u⁺) ≤ N u`, `u = log Q t - log P t`. -/
theorem exists_oneSigned_le (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) (N : Fin T → (Fin d → ℝ) → ℝ)
    (hN : ∀ t, AbsMono (N t)) {Q : Fin T → Fin d → ℝ} (hQ : ∀ t, Q t ∈ orthant d)
    (hws : WeakSolvable Q y) :
    ∃ Q' : Fin T → Fin d → ℝ, (∀ t, Q' t ∈ orthant d) ∧ WeakSolvable Q' y ∧
      ∀ t, ((∀ i, Q' t i ≤ P t i) ∨ (∀ i, P t i ≤ Q' t i)) ∧
        N t (logDev (P t) (Q' t)) ≤
          max (N t fun i => max (-logDev (P t) (Q t) i) 0) (N t fun i => max (logDev (P t) (Q t) i) 0) ∧
        N t (logDev (P t) (Q' t)) ≤ N t (logDev (P t) (Q t)) := by
  -- the box with half-widths `u⁻, u⁺` contains `Q`, so it passes the box query
  have hbox : BoxFeasible P y (fun t i => max (-logDev (P t) (Q t) i) 0)
      (fun t i => max (logDev (P t) (Q t) i) 0) := by
    refine (BoxPerturbation.box_iff hd
      (fun t i => P t i * exp (-max (-logDev (P t) (Q t) i) 0))
      (fun t i => P t i * exp (max (logDev (P t) (Q t) i) 0)) y
      (fun t i => mul_pos (hP t i) (exp_pos _))
      (fun t i => mul_le_mul_of_nonneg_left (exp_le_exp.2 (by
        linarith [le_max_right (-logDev (P t) (Q t) i) 0, le_max_right (logDev (P t) (Q t) i) 0]))
        (hP t i).le) hy).1 ⟨Q, fun t i => ?_, hws⟩
    simpa only [logDev, neg_sub] using box_contains_aux (hP t i) (hQ t i)
  obtain ⟨Q', hQ', hws', hres⟩ := exists_oneSigned hd hP hy N hN
    (fun t i => le_max_right _ _) (fun t i => le_max_right _ _) hbox
  refine ⟨Q', hQ', hws', fun t => ⟨(hres t).1, (hres t).2, ((hres t).2).trans ?_⟩⟩
  refine max_le (hN t _ _ fun i => ?_) (hN t _ _ fun i => ?_)
  · rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (neg_le_abs _) (abs_nonneg _)
  · rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)

/-- A weakly reachable `S ∋ t` meets `A` when a convex combination of the prices of `A` is
strictly below `Q t`. -/
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
`S ∋ t` meets `A`: otherwise the witness `ξ` of `t` gives `0 ≤ ⟨ξ, ∑ λ_s Q s - Q t⟩ < 0`. So the
linear functional `x ↦ ∑_{s ∈ A} x s - x t` is `≥ 0` on the generators, hence on the cone. -/
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

/-! ### Validity of the cuts and termination of the exact algorithm -/

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

/-- **Deleting years.** A feasible box stays feasible for any subset of the years (given by an
embedding `e`): a weakly reachable set of all corners, intersected with the corners of the kept
years, is weakly reachable there (same witnesses), and the cone vector restricts. -/
theorem BoxFeasible.restrict {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ} {α β : Fin T → Fin d → ℝ}
    {k : ℕ} (e : Fin k ↪ Fin T) (h : BoxFeasible P y α β) :
    BoxFeasible (fun j => P (e j)) (fun j => y (e j)) (fun j => α (e j)) (fun j => β (e j)) := by
  classical
  obtain ⟨w, hw, hlo, hhi⟩ := h
  set W := Fin.append (fun t i => P t i * exp (-α t i)) (fun t i => P t i * exp (β t i)) with hW
  -- the corners of the kept years, as indices among all corners
  let g : Fin (k + k) → Fin (T + T) :=
    Fin.append (fun j => Fin.castAdd T (e j)) (fun j => Fin.natAdd T (e j))
  have hg : Fin.append (fun j i => P (e j) i * exp (-α (e j) i))
      (fun j i => P (e j) i * exp (β (e j) i)) = fun r => W (g r) := by
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

/-! ### One l_p norm of the whole vector of log deviations -/

/-- The `p`-th power of the weighted l_p norm of a `T × d` matrix:
`∑_t ∑_i (c t i * |x t i|)^p`. -/
noncomputable def lpPow (p : ℝ) (c : Fin T → Fin d → ℝ) (x : Fin T → Fin d → ℝ) : ℝ :=
  ∑ t, ∑ i, (c t i * |x t i|) ^ p

/-- The cost `v ↦ ∑_i (c i * |v i|)^p` is monotone in absolute values. -/
theorem absMono_lp {p : ℝ} (hp : 0 ≤ p) {c : Fin d → ℝ} (hc : ∀ i, 0 ≤ c i) :
    AbsMono (fun v : Fin d → ℝ => ∑ i, (c i * |v i|) ^ p) := fun _ _ huv =>
  Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (mul_nonneg (hc i) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (huv i) (hc i)) hp

/-- **Reduction for one l_p norm** (`1 ≤ p < ∞`, weights `c ≥ 0`): some positive `Q` with weakly
solvable `y` has `∑_{t,i} (c |log Q - log P|)^p ≤ C` iff some half-widths `α, β ≥ 0` pass the box
query with `∑_{t,i} (c (α + β))^p ≤ C`. Since `x ↦ x^(1/p)` is monotone, the least l_p norms
agree. Proof: `exists_weakSolvable_iff_boxFeasible` with the year costs
`N t v = ∑_i (c t i * |v i|)^p` (monotone in absolute values) and the budgets of the given side. -/
theorem exists_weakSolvable_iff_boxFeasible_lp (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 1 ≤ p)
    (c : Fin T → Fin d → ℝ) (hc : ∀ t i, 0 ≤ c t i) (C : ℝ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        lpPow p c (fun t => logDev (P t) (Q t)) ≤ C) ↔
      ∃ α β : Fin T → Fin d → ℝ, 0 ≤ α ∧ 0 ≤ β ∧ BoxFeasible P y α β ∧
        lpPow p c (α + β) ≤ C := by
  have hN := fun t => absMono_lp (by linarith : (0 : ℝ) ≤ p) (hc t)
  constructor
  · rintro ⟨Q, hQ, hws, hC⟩
    obtain ⟨α, β, hα, hβ, hbox, hb⟩ := (exists_weakSolvable_iff_boxFeasible hd P hP y hy _ hN
      (fun t => ∑ i, (c t i * |logDev (P t) (Q t) i|) ^ p)).1 ⟨Q, hQ, hws, fun t => le_rfl⟩
    exact ⟨α, β, hα, hβ, hbox, by unfold lpPow; exact (Finset.sum_le_sum fun t _ => hb t).trans hC⟩
  · rintro ⟨α, β, hα, hβ, hbox, hC⟩
    obtain ⟨Q, hQ, hws, hb⟩ := (exists_weakSolvable_iff_boxFeasible hd P hP y hy _ hN
      (fun t => ∑ i, (c t i * |(α + β) t i|) ^ p)).2 ⟨α, β, hα, hβ, hbox, fun t => le_rfl⟩
    exact ⟨Q, hQ, hws, by unfold lpPow; exact (Finset.sum_le_sum fun t _ => hb t).trans hC⟩

/-- **Reduction for the l_∞ norm** (largest weighted log deviation over all years and prices):
the same equivalence with `max_{t,i} c |x|` (`exists_weakSolvable_iff_boxFeasible` with the
year cost `N t v = 0` if `c t i * |v i| ≤ C` for all `i` and `1` otherwise, which is monotone in
absolute values, and all year budgets `0`). -/
theorem exists_weakSolvable_iff_boxFeasible_linf (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    (c : Fin T → Fin d → ℝ) (hc : ∀ t i, 0 ≤ c t i) (C : ℝ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        ∀ t i, c t i * |logDev (P t) (Q t) i| ≤ C) ↔
      ∃ α β : Fin T → Fin d → ℝ, 0 ≤ α ∧ 0 ≤ β ∧ BoxFeasible P y α β ∧
        ∀ t i, c t i * (α t i + β t i) ≤ C := by
  classical
  -- year cost `0` if every weighted deviation is at most `C`, else `1`; budgets `0`
  let N : Fin T → (Fin d → ℝ) → ℝ := fun t v => if ∀ i, c t i * |v i| ≤ C then 0 else 1
  have hN : ∀ t, AbsMono (N t) := by
    intro t u v huv
    by_cases hv : ∀ i, c t i * |v i| ≤ C
    · have hu : ∀ i, c t i * |u i| ≤ C := fun i =>
        (mul_le_mul_of_nonneg_left (huv i) (hc t i)).trans (hv i)
      simp only [N, if_pos hu, if_pos hv, le_refl]
    · simp only [N, if_neg hv]; split_ifs <;> norm_num
  have hN0 : ∀ t v, N t v ≤ 0 ↔ ∀ i, c t i * |v i| ≤ C := by
    intro t v; simp only [N]; split_ifs with h <;> simp [h]
  have key := exists_weakSolvable_iff_boxFeasible hd P hP y hy N hN (fun _ => 0)
  simp only [hN0] at key
  rw [key]
  refine exists_congr fun α => exists_congr fun β => ?_
  constructor
  · rintro ⟨hα, hβ, hbox, h⟩
    refine ⟨hα, hβ, hbox, fun t i => ?_⟩
    have := h t i
    rwa [Pi.add_apply, abs_of_nonneg (add_nonneg (hα t i) (hβ t i))] at this
  · rintro ⟨hα, hβ, hbox, h⟩
    refine ⟨hα, hβ, hbox, fun t i => ?_⟩
    rw [Pi.add_apply, abs_of_nonneg (add_nonneg (hα t i) (hβ t i))]
    exact h t i

/-- **One-signedness for one l_p norm** (`1 ≤ p < ∞`, weights `c > 0`): if a year of a feasible `Q`
moves some price up and some price down, another feasible `Q'` has a strictly smaller
`∑_{t,i} (c |log Q - log P|)^p`. So every optimum of the l_p problem is one-signed. Proof:
`exists_oneSigned_le` with `N t v = ∑_i (c t i * |v i|)^p`; this `N t` is additive over the
coordinates, so `max (N u⁻) (N u⁺) < N u⁻ + N u⁺ = N u` when both parts are nonzero, and the other
years do not increase. -/
theorem exists_lt_of_mixed_lp (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 1 ≤ p) {c : Fin T → Fin d → ℝ}
    (hc : ∀ t i, 0 < c t i) {Q : Fin T → Fin d → ℝ} (hQ : ∀ t, Q t ∈ orthant d)
    (hws : WeakSolvable Q y) {t : Fin T} {i j : Fin d} (hi : Q t i < P t i) (hj : P t j < Q t j) :
    ∃ Q' : Fin T → Fin d → ℝ, (∀ t, Q' t ∈ orthant d) ∧ WeakSolvable Q' y ∧
      lpPow p c (fun t => logDev (P t) (Q' t)) < lpPow p c (fun t => logDev (P t) (Q t)) := by
  have hp0 : 0 < p := by linarith
  let N : Fin T → (Fin d → ℝ) → ℝ := fun t v => ∑ i, (c t i * |v i|) ^ p
  have hN : ∀ t, AbsMono (N t) := fun t => absMono_lp hp0.le fun i => (hc t i).le
  obtain ⟨Q', hQ', hws', hres⟩ := exists_oneSigned_le hd hP hy N hN hQ hws
  refine ⟨Q', hQ', hws', ?_⟩
  obtain ⟨u, hu⟩ : ∃ u, u = logDev (P t) (Q t) := ⟨_, rfl⟩
  -- `N` splits over the negative and positive parts
  have hsplit : N t u = N t (fun k => max (-u k) 0) + N t (fun k => max (u k) 0) := by
    simp only [N, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases le_total 0 (u k) with h | h
    · rw [max_eq_right (by linarith : -u k ≤ 0), max_eq_left h, abs_zero, mul_zero,
        Real.zero_rpow hp0.ne', zero_add]
    · rw [max_eq_left (by linarith : 0 ≤ -u k), max_eq_right h, abs_zero, mul_zero,
        Real.zero_rpow hp0.ne', add_zero, abs_neg]
  have hui : u i < 0 := by
    rw [hu]; simp only [logDev]; linarith [Real.log_lt_log (hQ t i) hi]
  have huj : 0 < u j := by
    rw [hu]; simp only [logDev]; linarith [Real.log_lt_log (hP t j) hj]
  have hpos : ∀ (w : Fin d → ℝ) (k : Fin d), w k ≠ 0 → 0 < N t w := fun w k hk =>
    Finset.sum_pos' (fun l _ => Real.rpow_nonneg (mul_nonneg (hc t l).le (abs_nonneg _)) _)
      ⟨k, Finset.mem_univ _, Real.rpow_pos_of_pos (mul_pos (hc t k) (abs_pos.2 hk)) _⟩
  have h1 := hpos (fun k => max (-u k) 0) i (by simp only; exact (lt_max_of_lt_left (by linarith)).ne')
  have h2 := hpos (fun k => max (u k) 0) j (by simp only; exact (lt_max_of_lt_left huj).ne')
  have hlt : N t (logDev (P t) (Q' t)) < N t (logDev (P t) (Q t)) := by
    refine ((hres t).2.1).trans_lt ?_
    rw [← hu, hsplit]
    exact max_lt (by linarith) (by linarith)
  unfold lpPow
  exact Finset.sum_lt_sum (fun s _ => (hres s).2.2) ⟨t, Finset.mem_univ _, hlt⟩

/-! ### Relative price errors -/

/-- Relative deviation of `q` from `p`. -/
noncomputable def relDev (p q : Fin d → ℝ) : Fin d → ℝ := fun i => q i / p i - 1

/-- With log half-widths `-log (1 - a)` and `log (1 + b)` the box corners are `P (1 - a)` and
`P (1 + b)`. -/
theorem boxFeasible_rel_iff (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) {a b : Fin T → Fin d → ℝ}
    (ha : ∀ t i, a t i < 1) (hb : 0 ≤ b) :
    BoxFeasible P y (fun t i => -log (1 - a t i)) (fun t i => log (1 + b t i)) ↔
      ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t i => P t i * (1 - a t i)) (fun t i => P t i * (1 + b t i)))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  have h1 : (fun t i => P t i * exp (-(-log (1 - a t i)))) = fun t i => P t i * (1 - a t i) := by
    funext t i; rw [neg_neg, exp_log (by linarith [ha t i])]
  have h2 : (fun t i => P t i * exp (log (1 + b t i))) = fun t i => P t i * (1 + b t i) := by
    funext t i
    have hbi : 0 ≤ b t i := hb t i
    rw [exp_log (by linarith)]
  unfold BoxFeasible; rw [h1, h2]

/-- **Reduction to boxes for relative errors.** Some positive `Q` with weakly solvable `y` and year
costs `N t (Q t / P t - 1) ≤ c t` exists iff some relative half-widths `0 ≤ a < 1`, `b ≥ 0` pass
the box query with corners `P (1 - a)`, `P (1 + b)` and `N t (a t + b t) ≤ c t`.

Proof. `→`: `a = (1 - Q/P)⁺`, `b = (Q/P - 1)⁺`; the box contains `Q`, so `box_iff` gives the corner
condition; `|Q/P - 1| ≤ a + b`. `←`: `path_of_corners` on the price-linear segments
`s ↦ P (1 - a + s (a + b))`; the point has relative deviation `-a + s (a + b)`. -/
theorem exists_weakSolvable_iff_boxFeasible_rel (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    (N : Fin T → (Fin d → ℝ) → ℝ) (hN : ∀ t, AbsMono (N t)) (c : Fin T → ℝ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        ∀ t, N t (relDev (P t) (Q t)) ≤ c t) ↔
      ∃ a b : Fin T → Fin d → ℝ, 0 ≤ a ∧ (∀ t i, a t i < 1) ∧ 0 ≤ b ∧
        BoxFeasible P y (fun t i => -log (1 - a t i)) (fun t i => log (1 + b t i)) ∧
        ∀ t, N t (a t + b t) ≤ c t := by
  constructor
  · rintro ⟨Q, hQ, hws, hc⟩
    have hr : ∀ t i, 0 < Q t i / P t i := fun t i => div_pos (hQ t i) (hP t i)
    have ha1 : ∀ t i, max (1 - Q t i / P t i) 0 < 1 := fun t i =>
      max_lt (by linarith [hr t i]) one_pos
    have hb : (0 : Fin T → Fin d → ℝ) ≤ fun t i => max (Q t i / P t i - 1) 0 :=
      fun t i => le_max_right _ _
    refine ⟨fun t i => max (1 - Q t i / P t i) 0, fun t i => max (Q t i / P t i - 1) 0,
      fun t i => le_max_right _ _, ha1, hb, ?_, fun t => ?_⟩
    · refine (boxFeasible_rel_iff P y ha1 hb).2 ((BoxPerturbation.box_iff hd _ _ y
        (fun t i => mul_pos (hP t i) (by linarith [ha1 t i])) (fun t i => ?_) hy).1
        ⟨Q, fun t i => ?_, hws⟩)
      · have h1 := le_max_right (1 - Q t i / P t i) 0
        have h2 := le_max_right (Q t i / P t i - 1) 0
        exact mul_le_mul_of_nonneg_left (by linarith) (hP t i).le
      · have hq : P t i * (Q t i / P t i) = Q t i := by field_simp [(hP t i).ne']
        constructor
        · calc _ ≤ P t i * (1 - (1 - Q t i / P t i)) := mul_le_mul_of_nonneg_left
                (by linarith [le_max_left (1 - Q t i / P t i) 0]) (hP t i).le
            _ = P t i * (Q t i / P t i) := by ring
            _ = Q t i := hq
        · calc Q t i = P t i * (Q t i / P t i) := hq.symm
            _ = P t i * (1 + (Q t i / P t i - 1)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left
                (by linarith [le_max_left (Q t i / P t i - 1) 0]) (hP t i).le
    · refine (hN t _ _ fun i => ?_).trans (hc t)
      simp only [Pi.add_apply, relDev]
      rw [abs_of_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))]
      rcases le_total (Q t i / P t i) 1 with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonpos (by linarith)]
        linarith
      · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonneg (by linarith)]
        linarith
  · rintro ⟨a, b, ha, ha1, hb, hbox, hc⟩
    have hpos : ∀ t i (s : ℝ), 0 ≤ s → 0 < 1 - a t i + s * (a t i + b t i) := by
      intro t i s hs
      have ha' : 0 ≤ a t i := ha t i
      have hb' : 0 ≤ b t i := hb t i
      nlinarith [ha1 t i]
    obtain ⟨s, hs, hws⟩ := PricePerturbation.path_of_corners hd
      (fun t i => P t i * (1 - a t i)) (fun t i => P t i * (1 + b t i))
      (fun t s i => P t i * (1 - a t i + s * (a t i + b t i)))
      (fun t => by fun_prop)
      (fun t => by funext i; simp)
      (fun t => by funext i; simp only; congr 1; ring)
      (fun t s hs i => mul_nonneg (hP t i).le (hpos t i s hs.1).le)
      y hy ((boxFeasible_rel_iff P y ha1 hb).1 hbox)
    refine ⟨fun t i => P t i * (1 - a t i + s t * (a t i + b t i)),
      fun t i => mul_pos (hP t i) (hpos t i _ (hs t).1),
      hws, fun t => ?_⟩
    refine (hN t _ _ fun i => ?_).trans (hc t)
    have h1 : relDev (P t) (fun i => P t i * (1 - a t i + s t * (a t i + b t i))) i =
        -a t i + s t * (a t i + b t i) := by
      simp only [relDev]; field_simp [(hP t i).ne']; ring
    rw [h1]
    obtain ⟨hs0, hs1⟩ := hs t
    have ha' : 0 ≤ a t i := ha t i
    have hb' : 0 ≤ b t i := hb t i
    simp only [Pi.add_apply]
    rw [abs_of_nonneg (by linarith : 0 ≤ a t i + b t i), abs_le]
    constructor <;> nlinarith

/-- **Reduction for one l_p norm of relative errors**: `exists_weakSolvable_iff_boxFeasible_rel`
with the year costs `N t v = ∑_i (c t i * |v i|)^p`, as in `exists_weakSolvable_iff_boxFeasible_lp`. -/
theorem exists_weakSolvable_iff_boxFeasible_rel_lp (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 1 ≤ p)
    (c : Fin T → Fin d → ℝ) (hc : ∀ t i, 0 ≤ c t i) (C : ℝ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        lpPow p c (fun t => relDev (P t) (Q t)) ≤ C) ↔
      ∃ a b : Fin T → Fin d → ℝ, 0 ≤ a ∧ (∀ t i, a t i < 1) ∧ 0 ≤ b ∧
        BoxFeasible P y (fun t i => -log (1 - a t i)) (fun t i => log (1 + b t i)) ∧
        lpPow p c (a + b) ≤ C := by
  have hN := fun t => absMono_lp (by linarith : (0 : ℝ) ≤ p) (hc t)
  constructor
  · rintro ⟨Q, hQ, hws, hC⟩
    obtain ⟨a, b, ha, ha1, hb, hbox, hab⟩ := (exists_weakSolvable_iff_boxFeasible_rel hd P hP y hy
      _ hN (fun t => ∑ i, (c t i * |relDev (P t) (Q t) i|) ^ p)).1 ⟨Q, hQ, hws, fun t => le_rfl⟩
    exact ⟨a, b, ha, ha1, hb, hbox,
      by unfold lpPow; exact (Finset.sum_le_sum fun t _ => hab t).trans hC⟩
  · rintro ⟨a, b, ha, ha1, hb, hbox, hC⟩
    obtain ⟨Q, hQ, hws, hab⟩ := (exists_weakSolvable_iff_boxFeasible_rel hd P hP y hy _ hN
      (fun t => ∑ i, (c t i * |(a + b) t i|) ^ p)).2 ⟨a, b, ha, ha1, hb, hbox, fun t => le_rfl⟩
    exact ⟨Q, hQ, hws, by unfold lpPow; exact (Finset.sum_le_sum fun t _ => hab t).trans hC⟩

/-! ### The NO certificate of the box query -/

/-- **NO certificate.** Let `C` be a finite set of covers `(r, A)`: a convex combination of the
corners of `A` is strictly below the corner `r`. If `λ` has `∑_{r ∈ S} λ r ≥ 0` on every `S` that
respects `C` (contains a point of `A` whenever it contains `r`), `λ ≤ 0` on the lower corners and
`∑ (-λ_lower) y > ∑ (λ_upper)⁺ y`, then no `w` of the cone meets the bounds of the box query.

Proof. Weakly reachable sets respect `C` (`meets_of_conv_lt`), so `w ↦ ∑ λ w` and the coordinates
are `≥ 0` on the cone. For `w` with `w_lower ≥ y ≥ w_upper ≥ 0` this sum is
`≤ ∑ λ_lower y + ∑ (λ_upper)⁺ y < 0`. -/
theorem not_boxCone_of_certificate (hd : 2 ≤ d) {W : Fin (T + T) → Fin d → ℝ}
    (hW : ∀ r, 0 ≤ W r) (y : Fin T → ℝ) (C : Finset (Fin (T + T) × Finset (Fin (T + T))))
    (hcov : ∀ e ∈ C, ∃ μ : Fin (T + T) → ℝ, (∀ s, 0 ≤ μ s) ∧ (∀ s ∉ e.2, μ s = 0) ∧
      ∑ s, μ s = 1 ∧ ∀ i, ∑ s, μ s * W s i < W e.1 i)
    (lam : Fin (T + T) → ℝ)
    (hF2 : ∀ S : Finset (Fin (T + T)), (∀ e ∈ C, e.1 ∈ S → ∃ s ∈ e.2, s ∈ S) →
      0 ≤ ∑ r ∈ S, lam r)
    (hlo : ∀ t, lam (Fin.castAdd T t) ≤ 0)
    (hF1 : 0 < ∑ t, (-lam (Fin.castAdd T t)) * y t - ∑ t, max (lam (Fin.natAdd T t)) 0 * y t)
    (hy : ∀ t, 0 ≤ y t) :
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

end NeoTiling.L1Perturbation
