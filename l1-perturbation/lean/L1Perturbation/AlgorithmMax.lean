import L1Perturbation.Algorithm

/-!
# The polyblock algorithm with the cost `g (lpPow p c (max α β))`

A second instantiation of the polyblock theorem (`boxRun_correct`), with the cost the code uses:
the coordinatewise maximum of the two half-widths instead of their sum. A point of the box
`[P e^{-α}, P e^{β}]` has `|log Q - log P| ≤ max α β`, so this cost still bounds the cost of the
prices found, and it is at most the cost `g (lpPow p c (α + β))` used for the lower bound.

For `g = (·)^(1/p)` this cost satisfies `f (z + a • 1) ≤ f z + a * ‖c‖_p` (Minkowski), so the
`Problem.shift` constant is `L = ‖c‖_p`, not `2 ‖c‖_p`; the step length
`τ = (UB - LB) / (2 ‖c‖_p)` of the implementation is the model's `τ` with `L = ‖c‖_p`. The
Minkowski bound is the `Problem.f_shift` field and is supplied by the user.
-/

namespace NeoTiling.L1Perturbation.Polyblock

open Real

variable {d T : ℕ}

/-- **Prices in a feasible box.** If the box with half-widths `α, β ≥ 0` passes the box query,
some positive `Q` with weakly solvable `y` has `lpPow p c (log Q - log P) ≤ lpPow p c (max α β)`.

Proof. `path_of_corners` on the segments `s ↦ P ∘ exp (-α + s (α + β))` gives `Q` with
`-α ≤ log Q - log P ≤ β`, so `|log Q - log P| ≤ max α β`; `lpPow` is monotone in absolute
values. -/
theorem exists_of_boxFeasible_max (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ}
    (hP : ∀ t, P t ∈ orthant d) {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 0 ≤ p)
    {c : Fin T → Fin d → ℝ} (hc : ∀ t i, 0 ≤ c t i) {α β : Fin T → Fin d → ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hbox : BoxFeasible P y α β) :
    ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
      lpPow p c (fun t => logDev (P t) (Q t)) ≤ lpPow p c (fun t i => max (α t i) (β t i)) := by
  obtain ⟨s, hs, hws⟩ := PricePerturbation.path_of_corners hd
    (fun t i => P t i * exp (-α t i)) (fun t i => P t i * exp (β t i))
    (fun t s i => P t i * exp (-α t i + s * (α t i + β t i)))
    (fun t => by fun_prop)
    (fun t => by funext i; simp)
    (fun t => by funext i; simp only; congr 2; ring)
    (fun t s _ i => (mul_pos (hP t i) (exp_pos _)).le) y hy hbox
  refine ⟨fun t i => P t i * exp (-α t i + s t * (α t i + β t i)),
    fun t i => mul_pos (hP t i) (exp_pos _), hws, ?_⟩
  unfold lpPow
  refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ => ?_
  refine Real.rpow_le_rpow (mul_nonneg (hc t i) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left ?_ (hc t i)) hp
  have h1 : logDev (P t) (fun i => P t i * exp (-α t i + s t * (α t i + β t i))) i =
      -α t i + s t * (α t i + β t i) := by
    simp only [logDev]
    rw [Real.log_mul (hP t i).ne' (exp_pos _).ne', Real.log_exp]; ring
  show |logDev (P t) (fun i => P t i * exp (-α t i + s t * (α t i + β t i))) i| ≤
    |max (α t i) (β t i)|
  rw [h1]
  obtain ⟨hs0, hs1⟩ := hs t
  have ha : 0 ≤ α t i := hα t i
  have hb : 0 ≤ β t i := hβ t i
  have hma := le_max_left (α t i) (β t i)
  have hmb := le_max_right (α t i) (β t i)
  rw [abs_of_nonneg (ha.trans hma), abs_le]
  constructor <;> nlinarith

/-- **(C') The algorithm with the cost `g (lpPow p c (max α β))`.** As `boxRun_correct`, but the
cost of the half-widths `z = (α, β)` is `f z = g (∑ (c max (α, β))^p)` (the cost of the code).
After any number of steps `UB` is attained by prices `Q` at which `y` is weakly solvable, and
`LB` is at most the cost of every such `Q`.

Proof. `UB`: `exists_of_boxFeasible_max` at the best point. `LB`: for `Q`,
`exists_weakSolvable_iff_boxFeasible_lp` gives feasible `α, β ≥ 0` with
`lpPow (α + β) ≤ lpPow (log Q - log P)`; `max α β ≤ α + β`, so `f (α, β)` is at most the cost
of `Q`; then `opt_le`, using `hM` if `(α, β)` leaves the box. -/
theorem boxRunMax_correct (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 1 ≤ p) (c : Fin T → Fin d → ℝ)
    (hc : ∀ t i, 0 ≤ c t i) {g : ℝ → ℝ} (hg : Monotone g)
    (Pr : Problem ((Fin T × Fin d) ⊕ (Fin T × Fin d)))
    (hH : ∀ z ∈ box Pr.M, z ∈ Pr.H ↔ BoxFeasible P y (alphaOf z) (betaOf z))
    (hf : ∀ z, Pr.f z = g (lpPow p c (fun t i => max (alphaOf z t i) (betaOf z t i))))
    (hM : ∀ z, 0 ≤ z → (∃ j, Pr.M < z j) → Pr.f Pr.top ≤ Pr.f z) (ε : ℝ) (n : ℕ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        g (lpPow p c (fun t => logDev (P t) (Q t))) ≤ (Pr.run ε n).UB) ∧
      ∀ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) → WeakSolvable Q y →
        (Pr.run ε n).LB ≤ g (lpPow p c (fun t => logDev (P t) (Q t))) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  obtain ⟨hLB, -, ⟨hbH, hbb⟩, hUB⟩ := Pr.run_correct ε n
  set b := (Pr.run ε n).best
  refine ⟨?_, fun Q hQ hws => ?_⟩
  · obtain ⟨Q, hQ, hws, hle⟩ := exists_of_boxFeasible_max hd hP hy hp0 hc
      (fun _ _ => (hbb _).1) (fun _ _ => (hbb _).1) ((hH b hbb).1 hbH)
    exact ⟨Q, hQ, hws, (hg hle).trans (hf b ▸ hUB).le⟩
  · obtain ⟨α, β, hα, hβ, hfeas, hle⟩ :=
      (exists_weakSolvable_iff_boxFeasible_lp hd P hP y hy hp c hc _).1 ⟨Q, hQ, hws, le_rfl⟩
    let z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ :=
      Sum.elim (fun ti => α ti.1 ti.2) (fun ti => β ti.1 ti.2)
    have hz0 : 0 ≤ z := by
      rintro (⟨t, i⟩ | ⟨t, i⟩)
      exacts [hα t i, hβ t i]
    have hmax : lpPow p c (fun t i => max (alphaOf z t i) (betaOf z t i)) ≤ lpPow p c (α + β) := by
      unfold lpPow
      refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ => ?_
      refine Real.rpow_le_rpow (mul_nonneg (hc t i) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ?_ (hc t i)) hp0
      have ha : 0 ≤ α t i := hα t i
      have hb : 0 ≤ β t i := hβ t i
      simp only [alphaOf, betaOf, z, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
      rw [abs_of_nonneg (ha.trans (le_max_left _ _)), abs_of_nonneg (add_nonneg ha hb)]
      exact max_le (by linarith) (by linarith)
    have hfz : Pr.f z ≤ g (lpPow p c (fun t => logDev (P t) (Q t))) := by
      rw [hf]; exact hg (hmax.trans hle)
    have hfeas' : BoxFeasible P y (alphaOf z) (betaOf z) := hfeas
    refine hLB.trans ?_
    by_cases hzb : z ∈ box Pr.M
    · exact (Pr.opt_le ((hH z hzb).2 hfeas') hzb).trans hfz
    · have : ∃ j, Pr.M < z j := by
        by_contra h; push_neg at h; exact hzb fun j => ⟨hz0 j, h j⟩
      exact (Pr.opt_le Pr.top_mem Pr.top_box).trans ((hM z hz0 this).trans hfz)

end NeoTiling.L1Perturbation.Polyblock
