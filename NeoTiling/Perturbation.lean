import NeoTiling.Solvability

/-!
# Minimal perturbation of prices

The symmetric relative perturbation `pert p q = max (|q/p - 1|, |p/q - 1|)` of one positive
coordinate and the total perturbation `totalPert P Q` between two price sets.

Main results:

* `pert_le_iff`: `pert p q ≤ D` iff `q` lies in the box `[p/(1+D), p(1+D)]`; in particular the
  prices stay positive without a lower bound on the perturbation.
* `totalPert_le_box`: a bound `D` on the total perturbation puts every coordinate in that box.
* `exists_neoSolvable_totalPert_le`: for `d ≥ 2` moving the prices to a surface `x₀ x₁ = κ`
  gives a solvable price set within total perturbation `hyperbolaBound hd P κ + η`.
* `exists_bound`: some `D ≥ 0` admits a solvable price set within total perturbation `D`, and all
  price sets within total perturbation `D` lie in the box.
* `exists_witness_le_of_hyperbola`: on a surface `x₀ x₁ = κ` with distinct `x₀` every price has
  a witness against all others of size at most the explicit `witnessBound hd P` (`Ξ_crit`).
-/

open Set Filter Topology

namespace NeoTiling

variable {d T : ℕ} {P Q : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

/-- Symmetric relative perturbation of one positive coordinate. -/
noncomputable def pert (p q : ℝ) : ℝ := max |q / p - 1| |p / q - 1|

/-- Total perturbation between two price sets. -/
noncomputable def totalPert {d T : ℕ} (P Q : Fin T → Fin d → ℝ) : ℝ :=
  ∑ t, ∑ i, pert (P t i) (Q t i)

/-- Cost of moving every price to the surface `x₀ x₁ = κ` by changing only coordinate `1`. -/
noncomputable def hyperbolaBound {d T : ℕ} (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (κ : ℝ) : ℝ :=
  ∑ t, (max (κ / (P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩))
             (P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩ / κ) - 1)

/-- For `a > 0`: `max (|a - 1|, |a⁻¹ - 1|) = max (a, a⁻¹) - 1`. -/
theorem max_abs_sub_one {a : ℝ} (ha : 0 < a) : max |a - 1| |a⁻¹ - 1| = max a a⁻¹ - 1 := by
  rcases le_total 1 a with h | h
  · have h1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
    have h2 : 1 - a⁻¹ ≤ a - 1 := by
      have : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
      nlinarith
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), max_eq_left (by linarith),
      max_eq_left (by linarith)]
  · have h1 : 1 ≤ a⁻¹ := one_le_inv₀ ha |>.2 h
    have h2 : 1 - a ≤ a⁻¹ - 1 := by
      have : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
      nlinarith
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith)]

/-- `pert p q = max (q/p, p/q) - 1`. -/
theorem pert_eq_max_div {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    pert p q = max (q / p) (p / q) - 1 := by
  have := max_abs_sub_one (div_pos hq hp)
  rwa [inv_div] at this

/-- `pert p q ≤ D` means exactly that `q` lies in the box `[p/(1+D), p(1+D)]`. -/
theorem pert_le_iff {p q D : ℝ} (hp : 0 < p) (hq : 0 < q) (hD : 0 ≤ D) :
    pert p q ≤ D ↔ p / (1 + D) ≤ q ∧ q ≤ p * (1 + D) := by
  rw [pert_eq_max_div hp hq, sub_le_iff_le_add, add_comm, max_le_iff, div_le_iff₀ hp,
    div_le_iff₀ hq, div_le_iff₀ (by linarith), mul_comm q, and_comm, mul_comm p]

theorem pert_nonneg (p q : ℝ) : 0 ≤ pert p q := (abs_nonneg _).trans (le_max_left _ _)

theorem pert_self {p : ℝ} (hp : 0 < p) : pert p p = 0 := by
  simp [pert, div_self hp.ne']

/-- A bound on the total perturbation bounds every coordinate. -/
theorem totalPert_le_box (hP : ∀ t, P t ∈ orthant d) (hQ : ∀ t, Q t ∈ orthant d) {D : ℝ}
    (h : totalPert P Q ≤ D) (t : Fin T) (i : Fin d) :
    P t i / (1 + D) ≤ Q t i ∧ Q t i ≤ P t i * (1 + D) := by
  have hle : pert (P t i) (Q t i) ≤ totalPert P Q :=
    (Finset.single_le_sum (f := fun j => pert (P t j) (Q t j))
      (fun j _ => pert_nonneg _ _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun s => ∑ j, pert (P s j) (Q s j))
      (fun s _ => Finset.sum_nonneg fun j _ => pert_nonneg _ _) (Finset.mem_univ t))
  exact (pert_le_iff (hP t i) (hQ t i) ((pert_nonneg _ _).trans (hle.trans h))).1
    (hle.trans h)

/-- The hyperbola witness: coordinate `0` of `p_t` is shifted to `x₀ = (p_t)₀ + θ t`, coordinate
`1` is set to `κ / x₀`, the others are kept. -/
noncomputable def hypPrices (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (κ θ : ℝ) :
    Fin T → Fin d → ℝ :=
  fun t i => if i = ⟨0, by omega⟩ then P t ⟨0, by omega⟩ + θ * ((t : ℕ) : ℝ)
    else if i = ⟨1, by omega⟩ then κ / (P t ⟨0, by omega⟩ + θ * ((t : ℕ) : ℝ)) else P t i

theorem hypPrices_mem (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) {κ θ : ℝ} (hκ : 0 < κ)
    (hθ : 0 ≤ θ) (t : Fin T) : hypPrices hd P κ θ t ∈ orthant d := by
  intro i
  have h0 : 0 < P t ⟨0, by omega⟩ + θ * ((t : ℕ) : ℝ) := by have := hP t ⟨0, by omega⟩; positivity
  unfold hypPrices; split_ifs
  · exact h0
  · exact div_pos hκ h0
  · exact hP t i

theorem hypPrices_mul (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) {κ θ : ℝ} (hθ : 0 ≤ θ)
    (t : Fin T) :
    hypPrices hd P κ θ t ⟨0, by omega⟩ * hypPrices hd P κ θ t ⟨1, by omega⟩ = κ := by
  have h0 : 0 < P t ⟨0, by omega⟩ + θ * ((t : ℕ) : ℝ) := by have := hP t ⟨0, by omega⟩; positivity
  simp only [hypPrices, if_true, Fin.ext_iff, zero_ne_one, one_ne_zero, if_false]
  field_simp

theorem hypPrices_injective (hd : 2 ≤ d) {κ θ : ℝ}
    (hθ : ∀ s t : Fin T, θ ≠ (P t ⟨0, by omega⟩ - P s ⟨0, by omega⟩) / (((s : ℕ) : ℝ) - (t : ℕ))) :
    Function.Injective fun t => hypPrices hd P κ θ t ⟨0, by omega⟩ := by
  intro s t hst
  by_contra hne
  simp only [hypPrices, if_true] at hst
  have hd' : ((s : ℕ) : ℝ) - (t : ℕ) ≠ 0 :=
    sub_ne_zero.2 (by exact_mod_cast Fin.val_injective.ne hne)
  exact hθ s t (by rw [eq_div_iff hd']; linarith)

theorem continuousAt_totalPert_hypPrices (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) {κ : ℝ}
    (hκ : 0 < κ) : ContinuousAt (fun θ => totalPert P (hypPrices hd P κ θ)) 0 := by
  have hpert : ∀ a : ℝ, ∀ f : ℝ → ℝ, ContinuousAt f 0 → f 0 ≠ 0 → a ≠ 0 →
      ContinuousAt (fun θ => pert a (f θ)) 0 := by
    intro a f hf h0 ha; unfold pert; fun_prop (disch := assumption)
  have hq : ∀ t i, ContinuousAt (fun θ => hypPrices hd P κ θ t i) 0 := by
    intro t i
    have h0 := (hP t ⟨0, by omega⟩).ne'
    by_cases h1 : i = ⟨0, by omega⟩
    · simp only [hypPrices, h1, if_true]; fun_prop
    · by_cases h2 : i = ⟨1, by omega⟩
      · simp only [hypPrices, h2, if_true]
        exact continuousAt_const.div (by fun_prop) (by simpa using h0)
      · simp only [hypPrices, h1, h2, if_false]; fun_prop
  exact tendsto_finset_sum _ fun t _ => tendsto_finset_sum _ fun i _ =>
    hpert _ _ (hq t i) (hypPrices_mem hd hP hκ le_rfl t i).ne' (hP t i).ne'

theorem totalPert_hypPrices_zero (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) {κ : ℝ}
    (hκ : 0 < κ) : totalPert P (hypPrices hd P κ 0) = hyperbolaBound hd P κ := by
  unfold totalPert hyperbolaBound
  refine Finset.sum_congr rfl fun t _ => ?_
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h10 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  have hp0 := hP t i0
  have hp1 := hP t i1
  rw [Finset.sum_eq_single i1]
  · simp only [hypPrices, zero_mul, add_zero]
    rw [if_neg h10, if_pos rfl, pert_eq_max_div hp1 (div_pos hκ hp0)]
    congr 2
    · rw [div_div]
    · field_simp
  · intro i _ hi
    have hq : hypPrices hd P κ 0 t i = P t i := by
      simp only [hypPrices, zero_mul, add_zero]; split_ifs with h <;> simp [h]
    rw [hq, pert_self (hP t i)]
  · simp

/-- The hyperbola witness: a solvable price set with total perturbation at most
`hyperbolaBound hd P κ + η`, for every `κ > 0`, `η > 0`.
Take `hypPrices hd P κ θ`: coordinate `0` shifted by `θ t`, coordinate `1` equal to `κ / x₀`.
Its cost is continuous in `θ` and equals `hyperbolaBound hd P κ` at `θ = 0`. For small generic
`θ > 0` the cost is below the bound plus `η` and the `x₀` are distinct, so
`neoSolvable_of_hyperbola` applies. -/
theorem exists_neoSolvable_totalPert_le (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d)
    (hy : ∀ t, 0 ≤ y t) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ NeoSolvable Q y ∧
      totalPert P Q ≤ hyperbolaBound hd P κ + η := by
  have hne : ∀ b : ℝ, ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ≠ b := fun b => by
    rcases le_or_gt b 0 with hb | hb
    · filter_upwards [self_mem_nhdsWithin] with θ hθ using (lt_of_le_of_lt hb hθ).ne'
    · filter_upwards [Ioo_mem_nhdsGT hb] with θ hθ using hθ.2.ne
  have h1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), totalPert P (hypPrices hd P κ θ) < hyperbolaBound hd P κ + η :=
    nhdsWithin_le_nhds <| (tendsto_order.1 (continuousAt_totalPert_hypPrices hd hP hκ).tendsto).2 _
      (by rw [totalPert_hypPrices_zero hd hP hκ]; linarith)
  have h2 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := (h1.and (h2.and
    (eventually_all.2 fun s => eventually_all.2 fun t => hne
      ((P t ⟨0, by omega⟩ - P s ⟨0, by omega⟩) / (((s : ℕ) : ℝ) - (t : ℕ)))))).exists
  have hQ := hypPrices_mem hd hP hκ hθ2.le
  exact ⟨_, hQ, neoSolvable_of_hyperbola hd hQ (hypPrices_mul hd hP hθ2.le)
    (hypPrices_injective hd hθ3) hy, hθ1.le⟩

/-- The bounds for the perturbation problem: some `D ≥ 0` admits a solvable price set within
total perturbation `D`, and every price set within total perturbation `D` lies in the box
`[p/(1+D), p(1+D)]` coordinatewise. -/
theorem exists_bound (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) (hy : ∀ t, 0 ≤ y t) :
    ∃ D : ℝ, 0 ≤ D ∧ (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ NeoSolvable Q y ∧
      totalPert P Q ≤ D) ∧
      ∀ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) → totalPert P Q ≤ D →
        ∀ t i, P t i / (1 + D) ≤ Q t i ∧ Q t i ≤ P t i * (1 + D) := by
  obtain ⟨Q, hQ, hsol, hle⟩ := exists_neoSolvable_totalPert_le hd hP hy one_pos one_pos
  refine ⟨_, ?_, ⟨Q, hQ, hsol, hle⟩, fun Q' hQ' h t i => totalPert_le_box hP hQ' h t i⟩
  exact le_trans (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun i _ =>
    pert_nonneg _ _) hle

/-- The witness bound `Ξ_crit` for prices on the surface `x₀ x₁ = κ`:
`max_t c_t · max((p_t)₀⁻¹, (p_t)₁⁻¹)` with `c_t = max_s (p_s)₀ (p_t)₀ / ((p_s)₀ - (p_t)₀)²`. -/
noncomputable def witnessBound (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) : ℝ :=
  ⨆ t, (⨆ s, P s ⟨0, by omega⟩ * P t ⟨0, by omega⟩ / (P s ⟨0, by omega⟩ - P t ⟨0, by omega⟩) ^ 2)
    * max (P t ⟨0, by omega⟩)⁻¹ (P t ⟨1, by omega⟩)⁻¹

/-- **Witnesses of bounded size.** For prices on the surface `x₀ x₁ = κ` with distinct `x₀`, each
`p_t` has a witness `ξ ∈ [0, witnessBound hd P]ᵈ` against all other prices: the witness of
`reachableSpectra_eq_univ_of_hyperbola`, `ξ = c_t (x₀⁻¹, x₁⁻¹, 0, …)`, has this size. -/
theorem exists_witness_le_of_hyperbola (hd : 2 ≤ d) (hQ : ∀ t, P t ∈ orthant d) {κ : ℝ}
    (hκ : ∀ t, P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩ = κ)
    (hinj : Function.Injective fun t => P t ⟨0, by omega⟩) (t : Fin T) :
    ∃ ξ : Fin d → ℝ, (∀ i, 0 ≤ ξ i ∧ ξ i ≤ witnessBound hd P) ∧
      ∀ s, s ≠ t → 1 ≤ ξ ⬝ᵥ (P s - P t) := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h10 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  set f : Fin T → Fin T → ℝ := fun t s => P s i0 * P t i0 / (P s i0 - P t i0) ^ 2
  set c := ⨆ s, f t s
  have hc : ∀ s, f t s ≤ c := fun s => le_ciSup (Set.finite_range (f t)).bddAbove s
  have hc0 : 0 ≤ c := le_trans (by have := hQ t i0; positivity) (hc t)
  refine ⟨fun i => c * (if i = i0 then (P t i0)⁻¹ else if i = i1 then (P t i1)⁻¹ else 0),
    fun i => ⟨?_, ?_⟩, fun s hs => ?_⟩
  · have := hQ t i0; have := hQ t i1
    show 0 ≤ c * _
    split_ifs <;> positivity
  · show c * _ ≤ _
    refine le_trans ?_ (le_ciSup (Set.finite_range fun t => (⨆ s, f t s)
      * max (P t i0)⁻¹ (P t i1)⁻¹).bddAbove t)
    have := hQ t i0; have := hQ t i1
    refine mul_le_mul_of_nonneg_left ?_ hc0
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
    · exact le_trans (by positivity) (le_max_left _ _)
  · have hst : P s i0 ≠ P t i0 := fun h => hs (hinj h)
    have ha := hQ s i0; have hb := hQ t i0; have hv := hQ t i1
    have hne : (P s i0 - P t i0) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hst)
    have hu : P s i1 = P t i0 * P t i1 / P s i0 := by
      rw [eq_div_iff ha.ne', mul_comm, hκ, hκ]
    rw [dotProduct, Finset.sum_eq_add i0 i1 h10.symm (fun j _ hj => by simp [hj.1, hj.2])
      (by simp) (by simp)]
    simp only [Pi.sub_apply, if_true, if_neg h10, hu]
    have key := hc s
    rw [div_le_iff₀ (by positivity)] at key
    have : c * (P t i0)⁻¹ * (P s i0 - P t i0)
        + c * (P t i1)⁻¹ * (P t i0 * P t i1 / P s i0 - P t i1)
        = c * (P s i0 - P t i0) ^ 2 / (P s i0 * P t i0) := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]; linarith

end NeoTiling
