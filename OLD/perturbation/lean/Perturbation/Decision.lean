import NeoTiling.Closure

/-!
# `PERT-2`: the decision version of the minimal price perturbation at `d = 2`

Given prices `P : Fin T → Fin 2 → ℝ` with positive entries, outputs `y : Fin T → ℝ`
with nonnegative entries, and a threshold `θ ≥ 0`, decide whether there exists a
positive price set `Q` at which `y` is weakly solvable and whose total perturbation
`totalPert P Q = ∑ t, ∑ i, pert (P t i) (Q t i)` is at most `θ`.

Hardness of this decision problem (over rational data) is the open question we aim to
settle. This file sets up the formal statement so later reductions can target it.
-/

namespace Perturbation

open NeoTiling

variable {T : ℕ}

/-- Symmetric relative perturbation of one positive coordinate:
`π(p, q) = max(q/p, p/q) − 1`. Mirrors `OLD/Algorithms/Perturbation.lean`,
restated here to keep this subproject self-contained. -/
noncomputable def pert (p q : ℝ) : ℝ := max (q / p) (p / q) - 1

/-- Total perturbation: `∑ t, ∑ i, π(P t i, Q t i)` on `d = 2`. -/
noncomputable def totalPert (P Q : Fin T → Fin 2 → ℝ) : ℝ :=
  ∑ t, ∑ i, pert (P t i) (Q t i)

/-- `PERT-2` as a predicate: there exists a positive `Q` at which `y` is weakly
solvable and whose total perturbation is at most `θ`. -/
def Decide (P : Fin T → Fin 2 → ℝ) (y : Fin T → ℝ) (θ : ℝ) : Prop :=
  ∃ Q : Fin T → Fin 2 → ℝ, (∀ t, Q t ∈ orthant 2) ∧ WeakSolvable Q y ∧ totalPert P Q ≤ θ

/-- `π(p, q) ≥ 0`: both quotients are positive at positive data, and `max x x⁻¹ ≥ 1`. -/
theorem pert_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 ≤ pert p q := by
  unfold pert
  have hp' : 0 < q / p := div_pos hq hp
  have hq' : 0 < p / q := div_pos hp hq
  have : 1 ≤ max (q / p) (p / q) := by
    rcases le_total (q / p) 1 with h | h
    · -- 1 ≤ p / q since q / p ≤ 1 and both are positive
      have hqp : q ≤ p := (div_le_one hp).1 h
      have : 1 ≤ p / q := (one_le_div hq).2 hqp
      exact le_max_of_le_right this
    · exact le_max_of_le_left h
  linarith

/-- `π(p, p) = 0`. -/
theorem pert_self {p : ℝ} (hp : 0 < p) : pert p p = 0 := by
  simp [pert, div_self hp.ne']

/-- `totalPert P P = 0`: every row costs zero at `Q = P`. -/
theorem totalPert_self {P : Fin T → Fin 2 → ℝ} (hP : ∀ t, P t ∈ orthant 2) :
    totalPert P P = 0 := by
  simp [totalPert, pert_self (hP _ _)]

/-- `totalPert P Q ≥ 0` whenever both `P` and `Q` are positive. -/
theorem totalPert_nonneg {P Q : Fin T → Fin 2 → ℝ}
    (hP : ∀ t, P t ∈ orthant 2) (hQ : ∀ t, Q t ∈ orthant 2) :
    0 ≤ totalPert P Q :=
  Finset.sum_nonneg fun t _ =>
    Finset.sum_nonneg fun i _ => pert_nonneg (hP t i) (hQ t i)

/-- If `y` is already weakly solvable at the given positive `P` and `θ ≥ 0`, then
`Decide P y θ` holds (take `Q := P`, cost `0`). -/
theorem decide_of_weakSolvable {P : Fin T → Fin 2 → ℝ} {y : Fin T → ℝ} {θ : ℝ}
    (hP : ∀ t, P t ∈ orthant 2) (h : WeakSolvable P y) (hθ : 0 ≤ θ) :
    Decide P y θ :=
  ⟨P, hP, h, by rw [totalPert_self hP]; exact hθ⟩

end Perturbation
