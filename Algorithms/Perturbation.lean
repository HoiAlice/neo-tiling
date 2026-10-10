import NeoTiling.Closure

/-!
# Minimal perturbation of prices

The symmetric relative perturbation `pert p q = max (|q/p - 1|, |p/q - 1|)` of one positive
coordinate, the total perturbation `totalPert P Q` between two price sets, and the minimal
perturbation `minPert P y`: the infimum of `totalPert P Q` over positive `Q` at which `y` is
solvable.

Main results:

* `pert_le_iff`, `totalPert_le_box`: a bound `D` on the total perturbation puts every coordinate
  in the box `[p/(1+D), p(1+D)]`; in particular the prices stay positive.
* `weakReachableSpectra_eq_univ_of_hyperbola`: for `d ≥ 2` prices on a surface `x₀ x₁ = κ` have
  every set weakly reachable (no distinctness needed).
* `exists_weak_totalPert_eq`: moving the prices to `x₀ x₁ = κ` along coordinate `1` makes `y`
  weakly solvable at total perturbation exactly `hyperbolaBound hd P κ`.
* `exists_minPert`: **attained minimum**. `minPert P y` is the minimum of `totalPert P Q` over
  positive `Q` at which `y` is weakly solvable (compactness of the box plus the closure theorem).
-/

open Set Filter Topology

namespace NeoTiling

variable {d T : ℕ} {P Q : Fin T → Fin d → ℝ} {y : Fin T → ℝ}

/-! ### Perturbation -/

/-- Symmetric relative perturbation of one positive coordinate. -/
noncomputable def pert (p q : ℝ) : ℝ := max |q / p - 1| |p / q - 1|

/-- Total perturbation between two price sets. -/
noncomputable def totalPert {d T : ℕ} (P Q : Fin T → Fin d → ℝ) : ℝ :=
  ∑ t, ∑ i, pert (P t i) (Q t i)

/-- Cost of moving every price to the surface `x₀ x₁ = κ` by changing only coordinate `1`. -/
noncomputable def hyperbolaBound {d T : ℕ} (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (κ : ℝ) : ℝ :=
  ∑ t, (max (κ / (P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩))
             (P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩ / κ) - 1)

/-- The minimal perturbation `ρ(P, y)`: the infimum of `totalPert P Q` over positive `Q` at which
`y` is solvable. -/
noncomputable def minPert {d T : ℕ} (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) : ℝ :=
  sInf (totalPert P '' {Q | (∀ t, Q t ∈ orthant d) ∧ NeoSolvable Q y})

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

/-- The perturbation is nonnegative: it is a maximum of absolute values. -/
theorem pert_nonneg (p q : ℝ) : 0 ≤ pert p q := (abs_nonneg _).trans (le_max_left _ _)

/-- No change, no perturbation. -/
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

/-- Positive price sets form an open set. -/
theorem isOpen_setOf_orthant : IsOpen {Q : Fin T → Fin d → ℝ | ∀ t, Q t ∈ orthant d} := by
  simpa only [setOf_forall] using
    isOpen_iInter_of_finite fun t => isOpen_orthant.preimage (continuous_apply t)

/-- `totalPert P` is continuous at positive prices: each `pert (P t i) ·` is continuous away
from `0`. -/
theorem continuousOn_totalPert (hP : ∀ t, P t ∈ orthant d) :
    ContinuousOn (totalPert P) {Q | ∀ t, Q t ∈ orthant d} := by
  unfold totalPert pert
  refine continuousOn_finset_sum _ fun t _ => continuousOn_finset_sum _ fun i _ => ?_
  have hc : Continuous fun Q : Fin T → Fin d → ℝ => Q t i := by fun_prop
  refine ContinuousOn.sup' (f := fun Q : Fin T → Fin d → ℝ => |Q t i / P t i - 1|)
    (g := fun Q => |P t i / Q t i - 1|) (continuous_abs.comp_continuousOn ?_)
    (continuous_abs.comp_continuousOn ?_)
  · exact (hc.continuousOn.div continuousOn_const fun _ _ => (hP t i).ne').sub continuousOn_const
  · exact (continuousOn_const.div hc.continuousOn fun Q hQ => (hQ t i).ne').sub
      continuousOn_const

/-! ### Hyperbola -/

/-- **Hyperbola, weak form.** If all prices lie on `x₀ x₁ = κ`, every `S` is weakly reachable
with the witness `ξ = (x₀⁻¹, x₁⁻¹, 0, …)` at `p_t`: `⟨ξ, p_s - p_t⟩ = (a - b)² / (a b) ≥ 0` with
`a = (p_s)₀`, `b = (p_t)₀`. No injectivity needed. -/
theorem weakReachableSpectra_eq_univ_of_hyperbola (hd : 2 ≤ d) (hQ : ∀ t, P t ∈ orthant d)
    {κ : ℝ} (hκ : ∀ t, P t ⟨0, by omega⟩ * P t ⟨1, by omega⟩ = κ) :
    weakReachableSpectra P = Set.univ := by
  refine Set.eq_univ_of_forall fun S => show IsWeakReachable P S from fun t ht => ?_
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h10 : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨fun i => if i = i0 then (P t i0)⁻¹ else if i = i1 then (P t i1)⁻¹ else 0,
    fun i => ?_, fun h0 => ?_, fun s hs => ?_⟩
  · have := hQ t i0; have := hQ t i1
    simp only [Pi.zero_apply]; split_ifs <;> positivity
  · have := congrFun h0 i0
    simp only [if_true, Pi.zero_apply, inv_eq_zero] at this
    exact (hQ t i0).ne' this
  · have ha := hQ s i0; have hb := hQ t i0; have hv := hQ t i1
    have hu : P s i1 = P t i0 * P t i1 / P s i0 := by
      rw [eq_div_iff ha.ne', mul_comm, hκ, hκ]
    rw [dotProduct, Finset.sum_eq_add i0 i1 h10.symm (fun j _ hj => by simp [hj.1, hj.2])
      (by simp) (by simp)]
    simp only [Pi.sub_apply, if_true, if_neg h10, hu]
    have : (P t i0)⁻¹ * (P s i0 - P t i0) + (P t i1)⁻¹ * (P t i0 * P t i1 / P s i0 - P t i1)
        = (P s i0 - P t i0) ^ 2 / (P s i0 * P t i0) := by field_simp; ring
    rw [this]
    positivity

/-- **Upper bound.** Setting `q₁ = κ / p₀` and keeping the other coordinates puts the prices on
`x₀ x₁ = κ`, so `y` is weakly solvable there (`weakReachableSpectra_eq_univ_of_hyperbola`), and
`totalPert P Q = hyperbolaBound hd P κ`: only coordinate `1` moves, by `pert p₁ (κ/p₀)`. -/
theorem exists_weak_totalPert_eq (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) (hy : ∀ t, 0 ≤ y t)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧
      WeakSolvable Q y ∧ totalPert P Q = hyperbolaBound hd P κ := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set Q : Fin T → Fin d → ℝ := fun t i => if i = i1 then κ / P t i0 else P t i
  have hQ : ∀ t, Q t ∈ orthant d := fun t i => by
    have := hP t i0; have := hP t i
    show 0 < (if i = i1 then κ / P t i0 else P t i)
    split_ifs <;> positivity
  refine ⟨Q, hQ, (weakSolvable_iff hd (fun t i => (hQ t i).le) hy).2 ?_, ?_⟩
  · rw [weakReachableSpectra_eq_univ_of_hyperbola hd hQ (κ := κ) fun t => by
      have := (hP t i0).ne'
      show (if i0 = i1 then κ / P t i0 else P t i0) * (if i1 = i1 then κ / P t i0 else P t i1) = κ
      rw [if_neg h01, if_pos rfl]
      field_simp]
    have : y = ∑ t, y t • ((({t} : Finset (Fin T)) : Set (Fin T)).indicator 1) := by
      ext r; simp [Finset.sum_apply, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun t _ =>
      PointedCone.smul_mem _ (hy t) (PointedCone.subset_span ⟨{t}, trivial, rfl⟩)
  · unfold totalPert hyperbolaBound
    refine Finset.sum_congr rfl fun t _ => ?_
    have h0 := hP t i0
    have h1 := hP t i1
    rw [Finset.sum_eq_single i1
      (fun i _ hi => by simp only [Q, if_neg hi]; exact pert_self (hP t i))
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [Q, if_true]
    rw [pert_eq_max_div h1 (by positivity), div_div, div_div_eq_mul_div, mul_comm (P t i1)]

/-! ### Attained minimum -/

/-- Weak solvability at positive prices within total perturbation `c` is a compact condition:
the set lies in the compact box of `totalPert_le_box`, and inside the box it is the closure of
the solvable prices (the definition of `WeakSolvable`) cut by the closed condition
`totalPert P Q ≤ c`. -/
theorem isCompact_weak_totalPert_le (hP : ∀ t, P t ∈ orthant d) {c : ℝ} (hc : 0 ≤ c) :
    IsCompact {Q : Fin T → Fin d → ℝ | (∀ t, Q t ∈ orthant d) ∧
      WeakSolvable Q y ∧ totalPert P Q ≤ c} := by
  set B : Set (Fin T → Fin d → ℝ) := Set.pi univ fun t => Set.pi univ fun i =>
    Icc (P t i / (1 + c)) (P t i * (1 + c))
  have hBc : IsCompact B := isCompact_univ_pi fun t => isCompact_univ_pi fun i => isCompact_Icc
  have hBpos : ∀ Q ∈ B, ∀ t, Q t ∈ orthant d := fun Q hQ t i =>
    (div_pos (hP t i) (by linarith)).trans_le (hQ t (mem_univ _) i (mem_univ _)).1
  have hcl : IsClosed (B ∩ totalPert P ⁻¹' Iic c) :=
    ((continuousOn_totalPert hP).mono hBpos).preimage_isClosed_of_isClosed hBc.isClosed
      isClosed_Iic
  have heq : {Q : Fin T → Fin d → ℝ | (∀ t, Q t ∈ orthant d) ∧
      WeakSolvable Q y ∧ totalPert P Q ≤ c} =
      closure {Q | (∀ t, Q t ∈ orthant d) ∧ NeoSolvable Q y} ∩ (B ∩ totalPert P ⁻¹' Iic c) := by
    ext Q
    constructor
    · rintro ⟨hQ, hw, hc'⟩
      exact ⟨hw, fun t _ i _ => totalPert_le_box hP hQ hc' t i, hc'⟩
    · rintro ⟨hw, hQB, hc'⟩
      exact ⟨hBpos Q hQB, hw, hc'⟩
  rw [heq]
  exact hBc.of_isClosed_subset (isClosed_closure.inter hcl) fun Q hQ => hQ.2.1

/-- `minPert` is at most the perturbation of any weakly solvable positive `Q`: `Q` is a limit of
solvable positive prices, and `totalPert P` is continuous at `Q`. -/
theorem minPert_le (hP : ∀ t, P t ∈ orthant d) (hQ : ∀ t, Q t ∈ orthant d)
    (h : WeakSolvable Q y) : minPert P y ≤ totalPert P Q := by
  have hOpen := isOpen_setOf_orthant (d := d) (T := T)
  have hc : ContinuousAt (totalPert P) Q :=
    (continuousOn_totalPert hP).continuousAt (hOpen.mem_nhds hQ)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ Q' in 𝓝 Q, (∀ t, Q' t ∈ orthant d) ∧ totalPert P Q' < totalPert P Q + ε :=
    Filter.Eventually.and (hOpen.mem_nhds hQ) (hc.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨Q', ⟨-, hQ'lt⟩, hQ'o, hQ's⟩ := mem_closure_iff_nhds.1 h _ hev
  have hbdd : BddBelow (totalPert P '' {Q | (∀ t, Q t ∈ orthant d) ∧ NeoSolvable Q y}) :=
    ⟨0, by
      rintro _ ⟨Q'', -, rfl⟩
      exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun i _ => pert_nonneg _ _⟩
  exact (csInf_le hbdd ⟨Q', ⟨hQ'o, hQ's⟩, rfl⟩).trans hQ'lt.le

/-- **Attained minimum.** `ρ(P,y)` equals the minimum of `totalPert P Q` over positive `Q` at
which `y` is weakly solvable, and the minimum is attained.

Proof: with `c = hyperbolaBound hd P 1` the set of weakly solvable `Q` with `totalPert P Q ≤ c`
is nonempty (`exists_weak_totalPert_eq`) and compact (`isCompact_weak_totalPert_le`), so
`totalPert P` has a minimizer `Q̄` on it, which minimizes over all weakly solvable `Q`. Solvable
prices are weakly solvable, so `minPert P y ≥ totalPert P Q̄`; the reverse is `minPert_le`. -/
theorem exists_minPert (hd : 2 ≤ d) (hP : ∀ t, P t ∈ orthant d) (hy : ∀ t, 0 ≤ y t) :
    ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧
      WeakSolvable Q y ∧ totalPert P Q = minPert P y ∧
      ∀ Q' : Fin T → Fin d → ℝ, (∀ t, Q' t ∈ orthant d) →
        WeakSolvable Q' y → minPert P y ≤ totalPert P Q' := by
  obtain ⟨Q₀, hQ₀, hw₀, he₀⟩ := exists_weak_totalPert_eq hd hP hy (κ := 1) one_pos
  have hc : 0 ≤ hyperbolaBound hd P 1 :=
    he₀ ▸ Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun i _ => pert_nonneg _ _
  obtain ⟨Q, ⟨hQ, hw, -⟩, hmin⟩ := (isCompact_weak_totalPert_le hP hc).exists_isMinOn
    ⟨Q₀, hQ₀, hw₀, he₀.le⟩ ((continuousOn_totalPert hP).mono fun Q hQ => hQ.1)
  have hmin' : ∀ Q', (∀ t, Q' t ∈ orthant d) → WeakSolvable Q' y →
      totalPert P Q ≤ totalPert P Q' := fun Q' hQ' hw' => by
    by_cases h : totalPert P Q' ≤ hyperbolaBound hd P 1
    · exact isMinOn_iff.1 hmin _ ⟨hQ', hw', h⟩
    · exact (isMinOn_iff.1 hmin _ ⟨hQ₀, hw₀, he₀.le⟩).trans (he₀.le.trans (not_le.1 h).le)
  obtain ⟨Q', -, hQ'⟩ := mem_closure_iff_nhds.1 hw _ univ_mem
  refine ⟨Q, hQ, hw, le_antisymm ?_ (minPert_le hP hQ hw), fun Q' hQ' => minPert_le hP hQ'⟩
  refine le_csInf ⟨_, Q', hQ', rfl⟩ ?_
  rintro _ ⟨Q'', hQ'', rfl⟩
  exact hmin' Q'' hQ''.1 (subset_closure hQ'')

end NeoTiling
