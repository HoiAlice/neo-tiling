import NeoTiling.Perturbation.Hex

namespace NeoTiling.PricePerturbation

open NeoTiling Real

variable {d T : ℕ}

/-- Distance between normalized prices `a = (x₁/x_{d+1}, …, x_d/x_{d+1})` and
`b = (y₁/y_{d+1}, …, y_d/y_{d+1})` induced by the log-`ℓ¹` distance of the `(d+1)`-tuples after
optimal rescaling: `inf_s (∑ᵢ |uᵢ + s| + |s|)` with `uᵢ = log aᵢ - log bᵢ`. -/
noncomputable def projDist (a b : Fin d → ℝ) : ℝ :=
  ⨅ s : ℝ, (∑ i, |log (a i) - log (b i) + s|) + |s|

theorem projDist_bddBelow (a b : Fin d → ℝ) :
    BddBelow (Set.range fun s : ℝ => (∑ i, |log (a i) - log (b i) + s|) + |s|) :=
  ⟨0, by rintro _ ⟨s, rfl⟩; positivity⟩

/-- Rescaling: `projDist (c • p) p ≤ |log c|` (take `s = -log c`). -/
theorem projDist_smul_le {c : ℝ} (hc : 0 < c) {p : Fin d → ℝ} (hp : p ∈ orthant d) :
    projDist (c • p) p ≤ |log c| := by
  have h : ∀ i, log ((c • p) i) - log (p i) + -log c = 0 := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, Real.log_mul hc.ne' (hp i).ne']; ring
  refine (ciInf_le (projDist_bddBelow _ _) (-log c)).trans_eq ?_
  simp only [h, abs_zero, Finset.sum_const_zero, zero_add, abs_neg]

/-- Each coordinate log-difference is bounded by `projDist`. -/
theorem abs_log_sub_le_projDist (q p : Fin d → ℝ) (i : Fin d) :
    |log (q i) - log (p i)| ≤ projDist q p := by
  refine le_ciInf fun s => ?_
  have h1 : |log (q i) - log (p i)| ≤ |log (q i) - log (p i) + s| + |s| := by
    simpa using abs_sub (log (q i) - log (p i) + s) s
  have h2 := Finset.single_le_sum (f := fun j => |log (q j) - log (p j) + s|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  simp only at h2
  linarith

/-- `(A) → (C)`: a solution within distance `ρ` lies in the box `[e^{-ρ} P, e^{ρ} P]`. -/
theorem corners_of_proj (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ (∀ t, projDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y) :
    ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t => exp (-ρ) • P t) (fun t => exp ρ • P t))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  obtain ⟨Q, hQ, hdist, hws⟩ := h
  refine (BoxPerturbation.box_iff hd _ _ y (fun t i => mul_pos (exp_pos _) (hP t i))
    (fun t i => mul_le_mul_of_nonneg_right (exp_le_exp.2 (by linarith)) (hP t i).le) hy).1
    ⟨Q, fun t i => ?_, hws⟩
  obtain ⟨h1, h2⟩ := abs_le.1 ((abs_log_sub_le_projDist (Q t) (P t) i).trans (hdist t))
  have hp' := hP t i
  have hqp := div_pos (hQ t i) hp'
  have hlog := Real.log_div (hQ t i).ne' hp'.ne'
  constructor
  · rw [← le_div_iff₀ hp', ← Real.le_log_iff_exp_le hqp, hlog]; exact h1
  · rw [← div_le_iff₀ hp', ← Real.log_le_iff_le_exp hqp, hlog]; exact h2

/-- `(B) → (A)`: a rescaling `c • P t` with `c ∈ [e^{-ρ}, e^{ρ}]` is within distance `ρ`. -/
theorem proj_of_scale (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ)
    {ρ : ℝ} (h : ∃ c : Fin T → ℝ, (∀ t, exp (-ρ) ≤ c t ∧ c t ≤ exp ρ) ∧
        WeakSolvable (fun t => c t • P t) y) :
    ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ (∀ t, projDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y := by
  obtain ⟨c, hc, hws⟩ := h
  have hc0 : ∀ t, 0 < c t := fun t => (exp_pos _).trans_le (hc t).1
  refine ⟨fun t => c t • P t, fun t i => by simpa using mul_pos (hc0 t) (hP t i),
    fun t => (projDist_smul_le (hc0 t) (hP t)).trans (abs_le.2 ⟨?_, ?_⟩), hws⟩
  · exact (Real.le_log_iff_exp_le (hc0 t)).2 (hc t).1
  · exact (Real.log_le_iff_le_exp (hc0 t)).2 (hc t).2

/-- Some prices within distance `ρ` of `P` make `y` weakly solvable iff some rescalings
`c t • P t` with `e^{-ρ} ≤ c t ≤ e^{ρ}` do. -/
theorem proj_iff_scale (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ (∀ t, projDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y) ↔
      ∃ c : Fin T → ℝ, (∀ t, exp (-ρ) ≤ c t ∧ c t ≤ exp ρ) ∧
        WeakSolvable (fun t => c t • P t) y :=
  ⟨fun h => scale_of_corners hd P hP y hy hρ (corners_of_proj hd P hP y hy hρ h),
    proj_of_scale P hP y⟩

/-- Some prices within distance `ρ` of `P` make `y` weakly solvable iff the `2T` corners
`e^{-ρ} P t`, `e^{ρ} P t` carry a vector `w` of the cone of weakly reachable spectra with
`w (lower corner of t) ≥ y t ≥ w (upper corner of t)`. -/
theorem proj_iff_corners (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ (∀ t, projDist (Q t) (P t) ≤ ρ) ∧
        WeakSolvable Q y) ↔
      ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t => exp (-ρ) • P t) (fun t => exp ρ • P t))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) :=
  ⟨corners_of_proj hd P hP y hy hρ,
    fun h => proj_of_scale P hP y (scale_of_corners hd P hP y hy hρ h)⟩

end NeoTiling.PricePerturbation
