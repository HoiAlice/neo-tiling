import PricePerturbation.Weighted

namespace NeoTiling.PricePerturbation

open NeoTiling Real Filter Topology

variable {d T : ℕ}

/-- Some prices make `y` weakly solvable while year `t` stays within weighted distance `r t`
(each year its own radius). -/
def RFeasible (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (r : Fin T → ℝ) : Prop :=
  ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ (∀ t, wdist (κ t) (κ₀ t) (Q t) (P t) ≤ r t) ∧
    WeakSolvable Q y

/-- **Per-year radii, corners.** For radii `r ≥ 0`: feasible iff the corners
`P t ∘ e^{∓ r_t (1/κ + 1/κ₀)}` carry a vector `w` of the cone of weakly reachable spectra with
`w (lower corner) ≥ y ≥ w (upper corner)`. -/
theorem rfeasible_iff_corners (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {r : Fin T → ℝ}
    (hr : ∀ t, 0 ≤ r t) :
    RFeasible κ κ₀ P y r ↔
      ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t i => P t i / wscale κ κ₀ (r t) t i)
            (fun t i => P t i * wscale κ κ₀ (r t) t i))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  constructor
  · rintro ⟨Q, hQ, hdist, hws⟩
    have hs1 : ∀ t i, 1 ≤ wscale κ κ₀ (r t) t i := fun t i =>
      one_le_exp (mul_nonneg (hr t) (by have := hκ t i; have := hκ₀ t; positivity))
    exact (BoxPerturbation.box_iff hd _ _ y (fun t i => div_pos (hP t i) (exp_pos _))
      (fun t i => (div_le_self (hP t i).le (hs1 t i)).trans
        (le_mul_of_one_le_right (hP t i).le (hs1 t i))) hy).1
      ⟨Q, fun t i => mem_wbox_of_wdist hκ hκ₀ (hQ t) (hP t) (hr t) t (hdist t) i, hws⟩
  · intro h
    obtain ⟨θ, hθ, hws⟩ := rpath_of_corners hd κ κ₀ P hP y hy hr h
    exact ⟨_, fun t i => mul_pos (hP t i) (exp_pos _),
      fun t => wdist_wpath_le hκ hκ₀ (hP t) t (hθ t), hws⟩

/-- **Per-year radii, path.** Feasible iff some `θ` with `|θ t| ≤ r t` makes `y` weakly solvable
at the path prices `P t ∘ e^{θ_t (1/κ + 1/κ₀)}`. -/
theorem rfeasible_iff_path (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {r : Fin T → ℝ}
    (hr : ∀ t, 0 ≤ r t) :
    RFeasible κ κ₀ P y r ↔
      ∃ θ : Fin T → ℝ, (∀ t, |θ t| ≤ r t) ∧
        WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y :=
  ⟨fun h => rpath_of_corners hd κ κ₀ P hP y hy hr
      ((rfeasible_iff_corners hd κ κ₀ hκ hκ₀ P hP y hy hr).1 h),
    fun ⟨_, hθ, hws⟩ => ⟨_, fun t i => mul_pos (hP t i) (exp_pos _),
      fun t => wdist_wpath_le hκ hκ₀ (hP t) t (hθ t), hws⟩⟩

/-- The feasible radius vectors are closed upwards. -/
theorem RFeasible.mono {κ : Fin T → Fin d → ℝ} {κ₀ : Fin T → ℝ} {P : Fin T → Fin d → ℝ}
    {y : Fin T → ℝ} {r r' : Fin T → ℝ} (h : RFeasible κ κ₀ P y r) (hrr : r ≤ r') :
    RFeasible κ κ₀ P y r' := by
  obtain ⟨Q, hQ, hd, hw⟩ := h
  exact ⟨Q, hQ, fun t => (hd t).trans (hrr t), hw⟩

/-- Feasible radii are nonnegative: the weighted distance is. -/
theorem RFeasible.nonneg {κ : Fin T → Fin d → ℝ} {κ₀ : Fin T → ℝ} (hκ₀ : ∀ t, 0 < κ₀ t)
    {P : Fin T → Fin d → ℝ} {y : Fin T → ℝ} {r : Fin T → ℝ} (h : RFeasible κ κ₀ P y r) (t : Fin T) :
    0 ≤ r t := by
  obtain ⟨Q, -, hd, -⟩ := h
  exact (le_ciInf fun s => le_max_of_le_left (mul_nonneg (hκ₀ t).le (abs_nonneg s))).trans (hd t)

/-- The feasible radius vectors form a closed set. -/
theorem isClosed_setOf_rfeasible (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) :
    IsClosed {r : Fin T → ℝ | RFeasible κ κ₀ P y r} := by
  refine isClosed_of_closure_subset fun r hr => ?_
  obtain ⟨rn, hrn, hlim⟩ := mem_closure_iff_seq_limit.1 hr
  have hcr : ∀ t, Tendsto (fun n => rn n t) atTop (𝓝 (r t)) := fun t =>
    (continuous_apply t).continuousAt.tendsto.comp hlim
  have hr0 : ∀ t, 0 ≤ r t := fun t =>
    ge_of_tendsto' (hcr t) fun n => RFeasible.nonneg hκ₀ (hrn n) t
  have hn : ∀ n, ∃ θ : Fin T → ℝ, (∀ t, |θ t| ≤ rn n t) ∧
      WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y := fun n =>
    (rfeasible_iff_path hd κ κ₀ hκ hκ₀ P hP y hy (RFeasible.nonneg hκ₀ (hrn n))).1 (hrn n)
  choose θ hθ hws using hn
  let K : Set (Fin T → ℝ) := Set.pi Set.univ (fun t => Set.Icc (-(r t + 1)) (r t + 1))
  have hev : ∀ᶠ n in atTop, θ n ∈ K := by
    have : ∀ᶠ n in atTop, ∀ t, rn n t < r t + 1 :=
      eventually_all.2 fun t => (hcr t).eventually (gt_mem_nhds (by linarith))
    filter_upwards [this] with n hn t _
    have := abs_le.1 ((hθ n t).trans (hn t).le)
    exact ⟨this.1, this.2⟩
  obtain ⟨θ0, -, φ, hφ, hθlim⟩ :=
    (isCompact_univ_pi fun _ => isCompact_Icc).tendsto_subseq' hev.frequently
  have hcl : IsClosed {θ : Fin T → ℝ |
      WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y} :=
    isClosed_closure.preimage (by fun_prop)
  refine (rfeasible_iff_path hd κ κ₀ hκ hκ₀ P hP y hy hr0).2 ⟨θ0, fun t => ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto'
      ((continuous_apply t).continuousAt.tendsto.comp hθlim).abs
      ((hcr t).comp hφ.tendsto_atTop) (fun n => hθ _ t)
  · exact hcl.mem_of_tendsto hθlim (Eventually.of_forall fun n => hws _)

/-- **Minimal radius vectors exist.** Below every feasible radius vector there is a feasible one
that is minimal (Pareto): no feasible vector is coordinatewise below it except itself. The
feasible set need not have a least element (the coordinatewise minimum of two feasible vectors
can be infeasible), so the lexicographic profile is one of these minimal vectors. -/
theorem exists_minimal_rfeasible (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {r : Fin T → ℝ}
    (hr : RFeasible κ κ₀ P y r) :
    ∃ r₀ ≤ r, RFeasible κ κ₀ P y r₀ ∧
      ∀ r', RFeasible κ κ₀ P y r' → r' ≤ r₀ → r' = r₀ := by
  set K := {r' : Fin T → ℝ | RFeasible κ κ₀ P y r'} ∩ {r' | r' ≤ r} with hK
  have hKc : IsCompact K :=
    (isCompact_Icc (a := (0 : Fin T → ℝ)) (b := r)).of_isClosed_subset
      ((isClosed_setOf_rfeasible hd κ κ₀ hκ hκ₀ P hP y hy).inter
        (isClosed_le continuous_id continuous_const))
      fun r' ⟨h1, h2⟩ => ⟨fun t => RFeasible.nonneg hκ₀ h1 t, h2⟩
  obtain ⟨r₀, ⟨hr₀, hr₀r⟩, hmin⟩ :=
    hKc.exists_isMinOn ⟨r, hr, show r ≤ r from le_rfl⟩ (f := fun r' => ∑ t, r' t) (by fun_prop)
  refine ⟨r₀, hr₀r, hr₀, fun r' hr' hle => funext fun t => ?_⟩
  refine le_antisymm (hle t) (not_lt.1 fun hlt => ?_)
  have h1 : ∑ t, r' t < ∑ t, r₀ t :=
    Finset.sum_lt_sum (fun t _ => hle t) ⟨t, Finset.mem_univ _, hlt⟩
  have h2 : ∑ t, r₀ t ≤ ∑ t, r' t := hmin ⟨hr', hle.trans hr₀r⟩
  linarith

end NeoTiling.PricePerturbation
