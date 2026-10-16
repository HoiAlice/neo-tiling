import PricePerturbation.Search
import PricePerturbation.Weighted

/-!
# Least-radius search for equal weighted penalties

If the penalties satisfy `1 / κ t i + 1 / κ₀ t = c` for all `t, i`, the weighted ball of radius
`ρ` has the same corners as the unweighted ball of radius `c ρ`, so the unweighted least-radius
search also finds the least weighted radius.
-/

namespace NeoTiling.PricePerturbation

open NeoTiling Real NPHardness Costed

variable {d T : ℕ}

/-- **Equal penalties reduce to the unweighted metric.** If `1 / κ t i + 1 / κ₀ t = c` for all
`t, i`, then radius `ρ` is feasible in the weighted metric iff radius `c ρ` is feasible in the
unweighted one.

Proof. Both sides are corner conditions (`wfeasible_iff_corners`, `proj_iff_corners`), and the
corners coincide since `wscale κ κ₀ ρ t i = e^{c ρ}`. -/
theorem wfeasible_iff_feasible_mul (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {c ρ : ℝ} (hc : 0 < c)
    (hv : ∀ t i, 1 / κ t i + 1 / κ₀ t = c) (hρ : 0 ≤ ρ) :
    WFeasible κ κ₀ P y ρ ↔ Feasible P y (c * ρ) := by
  rw [wfeasible_iff_corners hd κ κ₀ hκ hκ₀ P hP y hy hρ, Feasible,
    proj_iff_corners hd P hP y hy (mul_nonneg hc.le hρ)]
  have hs : ∀ t i, wscale κ κ₀ ρ t i = exp (c * ρ) := fun t i => by
    rw [wscale, hv, mul_comm]
  have h1 : (fun t i => P t i / wscale κ κ₀ ρ t i) = fun t => exp (-(c * ρ)) • P t := by
    funext t i; simp [hs, Real.exp_neg, div_eq_inv_mul]
  have h2 : (fun t i => P t i * wscale κ κ₀ ρ t i) = fun t => exp (c * ρ) • P t := by
    funext t i; simp [hs, mul_comm]
  rw [h1, h2]

/-- **The least-radius search for equal penalties.** If `1 / κ t i + 1 / κ₀ t = c > 0` for all
`t, i`, the unweighted search `leastRadius O Pq` (with `O` the unweighted oracle at `z = e^{2ρ}`)
returns `z` with the feasible weighted radii exactly `[log z / (2c), ∞)`, or `none` if no weighted
radius is feasible, within the same number of oracle calls.

Proof. By `wfeasible_iff_feasible_mul` weighted radius `ρ` is unweighted radius `c ρ`, and
`ρ ↦ c ρ` is an order isomorphism of `[0, ∞)`; apply `leastRadius_spec`. -/
theorem leastWRadius_spec (hd : 2 ≤ d) (Pq : Fin T → Fin d → ℚ) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (hPP : ∀ t i, P t i = Pq t i) (y : Fin T → ℝ)
    (hy : ∀ t, 0 ≤ y t) (O : ℚ → Bool)
    (hO : ∀ z : ℚ, 1 ≤ z → (O z = true ↔ Feasible P y (Real.log z / 2)))
    (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t)
    {c : ℝ} (hc : 0 < c) (hv : ∀ t i, 1 / κ t i + 1 / κ₀ t = c) :
    ((∃ ρ, 0 ≤ ρ ∧ WFeasible κ κ₀ P y ρ) → ∃ z, (leastRadius O Pq).val = some z ∧
        ∀ ρ, 0 ≤ ρ → (WFeasible κ κ₀ P y ρ ↔ Real.log z / (2 * c) ≤ ρ)) ∧
      ((¬ ∃ ρ, 0 ≤ ρ ∧ WFeasible κ κ₀ P y ρ) → (leastRadius O Pq).val = none) ∧
      (leastRadius O Pq).cost ≤ (d + 1) * Nat.clog 2 (2 * T + d) + 2 := by
  obtain ⟨ha, hb, hcost⟩ := leastRadius_spec hd Pq P hP hPP y hy O hO
  have heq := fun ρ (hρ : 0 ≤ ρ) => wfeasible_iff_feasible_mul hd κ κ₀ hκ hκ₀ P hP y hy hc hv hρ
  refine ⟨fun ⟨ρ, hρ, hw⟩ => ?_, fun hn => hb fun ⟨ρ, hρ, hf⟩ => hn ⟨ρ / c, div_nonneg hρ hc.le,
    (heq _ (div_nonneg hρ hc.le)).2 (by rwa [mul_div_cancel₀ _ hc.ne'])⟩, hcost⟩
  obtain ⟨z, hz, hiff⟩ := ha ⟨c * ρ, mul_nonneg hc.le hρ, (heq ρ hρ).1 hw⟩
  refine ⟨z, hz, fun ρ hρ => ?_⟩
  rw [heq ρ hρ, hiff _ (mul_nonneg hc.le hρ), div_le_iff₀ (by norm_num : (0:ℝ) < 2),
    div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith
