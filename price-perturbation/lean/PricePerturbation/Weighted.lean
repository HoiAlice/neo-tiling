import PricePerturbation.Shape

namespace NeoTiling.PricePerturbation

open NeoTiling Real Filter Topology

variable {d T : ℕ}

/-- Weighted distance between normalized prices: each of the `d + 1` prices of the tuple may
deviate in log by at most `ρ / κ`, with its own penalty `κ i` (the `d` normalized prices) and `κ₀`
(the normalizing price): `inf_s max (κ₀ |s|, max_i κ_i |log a_i - log b_i + s|)`. -/
noncomputable def wdist (κ : Fin d → ℝ) (κ₀ : ℝ) (a b : Fin d → ℝ) : ℝ :=
  ⨅ s : ℝ, max (κ₀ * |s|) (⨆ i, κ i * |log (a i) - log (b i) + s|)

/-- The scale of the corners of the bounding box of the weighted ball of radius `ρ` at `t`:
`e^{± ρ (1/κ_i + 1/κ₀)}` in coordinate `i`. -/
noncomputable def wscale (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (ρ : ℝ) (t : Fin T) (i : Fin d) :
    ℝ :=
  exp (ρ * (1 / κ t i + 1 / κ₀ t))

/-- Some prices within weighted distance `ρ` of `P` (at every `t`, with the penalties of year
`t`) make `y` weakly solvable. -/
def WFeasible (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (ρ : ℝ) : Prop :=
  ∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ (∀ t, wdist (κ t) (κ₀ t) (Q t) (P t) ≤ ρ) ∧
    WeakSolvable Q y

/-- **Shape of the weighted ball** (a zonotope in log coordinates): `wdist ≤ ρ` iff some common
shift `s` keeps the normalizing price within `ρ / κ₀` and every other price within `ρ / κ_i`. -/
theorem wdist_le_iff {κ : Fin d → ℝ} {κ₀ : ℝ} (hκ : ∀ i, 0 < κ i) (hκ₀ : 0 < κ₀)
    (a b : Fin d → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    wdist κ κ₀ a b ≤ ρ ↔
      ∃ s : ℝ, κ₀ * |s| ≤ ρ ∧ ∀ i, κ i * |log (a i) - log (b i) + s| ≤ ρ := by
  set g : Fin d → ℝ → ℝ := fun i s => κ i * |log (a i) - log (b i) + s| with hg
  set f : ℝ → ℝ := fun s => max (κ₀ * |s|) (⨆ i, g i s) with hf
  have hgc : ∀ i, Continuous (g i) := fun i => by rw [hg]; fun_prop
  have hfc : Continuous f := by
    rw [hf]
    refine Continuous.max (by fun_prop) ?_
    rcases isEmpty_or_nonempty (Fin d) with h | h
    · simp only [Real.iSup_of_isEmpty]; exact continuous_const
    · have : (fun s => ⨆ i, g i s) =
          fun s => Finset.univ.sup' Finset.univ_nonempty (fun i => g i s) := by
        funext s; rw [Finset.sup'_univ_eq_ciSup]
      rw [this]
      exact Continuous.finset_sup'_apply _ (fun i _ => hgc i)
  have hge : ∀ t, κ₀ * |t| ≤ f t := fun t => le_max_left _ _
  have hf0 : 0 ≤ f 0 := le_trans (by positivity) (hge 0)
  have hM : 0 ≤ f 0 / κ₀ := div_nonneg hf0 hκ₀.le
  have hbdd : BddBelow (Set.range f) := ⟨0, by
    rintro _ ⟨t, rfl⟩; exact le_trans (by positivity) (hge t)⟩
  constructor
  · intro h
    obtain ⟨s, -, hs⟩ := (isCompact_Icc (a := -(f 0 / κ₀)) (b := f 0 / κ₀)).exists_isMinOn
      ⟨0, by constructor <;> linarith⟩ hfc.continuousOn
    have hmin : f s ≤ ⨅ t, f t := by
      refine le_ciInf fun t => ?_
      by_cases ht : t ∈ Set.Icc (-(f 0 / κ₀)) (f 0 / κ₀)
      · exact hs ht
      · have h1 : f 0 / κ₀ < |t| := by
          by_contra hh
          exact ht (abs_le.mp (not_lt.mp hh))
        have h2 : f 0 < κ₀ * |t| := by
          rw [div_lt_iff₀ hκ₀] at h1; linarith
        have h0 : f s ≤ f 0 :=
          hs (show (0:ℝ) ∈ Set.Icc (-(f 0 / κ₀)) (f 0 / κ₀) from ⟨by linarith, hM⟩)
        linarith [hge t]
    have hfs : f s ≤ ρ := le_trans hmin h
    refine ⟨s, le_trans (hge s) hfs, fun i => ?_⟩
    exact le_trans (le_ciSup (f := fun i => g i s) (Finite.bddAbove_range _) i)
      (le_trans (le_max_right _ _) hfs)
  · rintro ⟨s, h1, h2⟩
    exact le_trans (ciInf_le hbdd s) (max_le h1 (Real.iSup_le h2 hρ))

/-- The weighted ball lies in the box of `wscale`: `wdist q p ≤ ρ` gives
`p i / wscale ≤ q i ≤ p i * wscale` (`|log q i - log p i| ≤ ρ / κ_i + ρ / κ₀`). -/
theorem mem_wbox_of_wdist {κ : Fin T → Fin d → ℝ} {κ₀ : Fin T → ℝ} (hκ : ∀ t i, 0 < κ t i)
    (hκ₀ : ∀ t, 0 < κ₀ t) {q p : Fin d → ℝ} (hq : q ∈ orthant d) (hp : p ∈ orthant d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (t : Fin T) (h : wdist (κ t) (κ₀ t) q p ≤ ρ) (i : Fin d) :
    p i / wscale κ κ₀ ρ t i ≤ q i ∧ q i ≤ p i * wscale κ κ₀ ρ t i := by
  obtain ⟨s, hs, hi⟩ := (wdist_le_iff (hκ t) (hκ₀ t) q p hρ).1 h
  have h0 := hκ₀ t
  have h1 := hκ t i
  have hs' : |s| ≤ ρ / κ₀ t := (le_div_iff₀ h0).2 (by linarith)
  have hi' : |log (q i) - log (p i) + s| ≤ ρ / κ t i := (le_div_iff₀ h1).2 (by linarith [hi i])
  have hc : |log (q i) - log (p i)| ≤ ρ * (1 / κ t i + 1 / κ₀ t) := by
    have : ρ * (1 / κ t i + 1 / κ₀ t) = ρ / κ t i + ρ / κ₀ t := by ring
    rw [this]
    obtain ⟨a1, a2⟩ := abs_le.1 hs'
    obtain ⟨b1, b2⟩ := abs_le.1 hi'
    exact abs_le.2 ⟨by linarith, by linarith⟩
  obtain ⟨c1, c2⟩ := abs_le.1 hc
  have hp' := hp i
  have hq' := hq i
  unfold wscale
  constructor
  · rw [div_le_iff₀ (exp_pos _), mul_comm, ← div_le_iff₀ hq',
      ← Real.log_le_iff_le_exp (div_pos hp' hq'), Real.log_div hp'.ne' hq'.ne']
    linarith
  · rw [mul_comm, ← div_le_iff₀ hp', ← Real.log_le_iff_le_exp (div_pos hq' hp'),
      Real.log_div hq'.ne' hp'.ne']
    exact c2

/-- A point of the log-linear path is within weighted distance `|θ|`: take the shift
`s = -θ / κ₀`. -/
theorem wdist_wpath_le {κ : Fin T → Fin d → ℝ} {κ₀ : Fin T → ℝ} (hκ : ∀ t i, 0 < κ t i)
    (hκ₀ : ∀ t, 0 < κ₀ t) {p : Fin d → ℝ} (hp : p ∈ orthant d) (t : Fin T) {θ ρ : ℝ}
    (hθ : |θ| ≤ ρ) :
    wdist (κ t) (κ₀ t) (fun i => p i * exp (θ * (1 / κ t i + 1 / κ₀ t))) p ≤ ρ := by
  have h0 := hκ₀ t
  refine (wdist_le_iff (hκ t) h0 _ _ ((abs_nonneg θ).trans hθ)).2 ⟨-θ / κ₀ t, ?_, fun i => ?_⟩
  · rw [abs_div, abs_neg, abs_of_pos h0, mul_div_cancel₀ _ h0.ne']; exact hθ
  · have h1 := hκ t i
    have : log (p i * exp (θ * (1 / κ t i + 1 / κ₀ t))) - log (p i) + -θ / κ₀ t =
        θ / κ t i := by
      rw [Real.log_mul (hp i).ne' (exp_pos _).ne', Real.log_exp]
      field_simp
      ring
    rw [this, abs_div, abs_of_pos h1, mul_div_cancel₀ _ h1.ne']; exact hθ

/-- `(C) → path` with per-year radii: the corner certificate at radii `r t` gives a point on each
log-linear path `θ ↦ P t ∘ e^{θ (1/κ + 1/κ₀)}`, `|θ t| ≤ r t` (`path_of_corners` with
`θ t = (2 s - 1) r t`). -/
theorem rpath_of_corners (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    {r : Fin T → ℝ} (hr : ∀ t, 0 ≤ r t)
    (h : ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t i => P t i / wscale κ κ₀ (r t) t i)
            (fun t i => P t i * wscale κ κ₀ (r t) t i))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) :
    ∃ θ : Fin T → ℝ, (∀ t, |θ t| ≤ r t) ∧
      WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y := by
  obtain ⟨s, hs, hws⟩ := path_of_corners hd (fun t i => P t i / wscale κ κ₀ (r t) t i)
    (fun t i => P t i * wscale κ κ₀ (r t) t i)
    (fun t s i => P t i * exp (((2 * s - 1) * r t) * (1 / κ t i + 1 / κ₀ t)))
    (fun t => by fun_prop)
    (fun t => by
      funext i
      simp only [wscale, div_eq_mul_inv, ← Real.exp_neg]
      congr 2; ring)
    (fun t => by funext i; simp only [wscale]; congr 2; ring)
    (fun t s _ i => (mul_pos (hP t i) (exp_pos _)).le) y hy h
  refine ⟨fun t => (2 * s t - 1) * r t, fun t => ?_, hws⟩
  obtain ⟨h0, h1⟩ := hs t
  have := hr t
  rw [abs_le]; constructor <;> nlinarith

/-- `(C) → path`: the corner certificate gives a point on each log-linear path
`θ ↦ P t ∘ e^{θ (1/κ + 1/κ₀)}`, `|θ| ≤ ρ` (`path_of_corners` with `θ = (2 s - 1) ρ`). -/
theorem wpath_of_corners (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t i => P t i / wscale κ κ₀ ρ t i)
            (fun t i => P t i * wscale κ κ₀ ρ t i))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) :
    ∃ θ : Fin T → ℝ, (∀ t, |θ t| ≤ ρ) ∧
      WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y :=
  rpath_of_corners hd κ κ₀ P hP y hy (r := fun _ => ρ) (fun _ => hρ) h

/-- **Reduction to the corners.** For positive penalties, some prices within weighted distance
`ρ` make `y` weakly solvable iff the `2T` corners `P t ∘ e^{∓ρ (1/κ + 1/κ₀)}` carry a vector `w`
of the cone of weakly reachable spectra with `w (lower corner) ≥ y ≥ w (upper corner)`. -/
theorem wfeasible_iff_corners (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    WFeasible κ κ₀ P y ρ ↔
      ∃ w ∈ indicatorCone (weakReachableSpectra
          (Fin.append (fun t i => P t i / wscale κ κ₀ ρ t i)
            (fun t i => P t i * wscale κ κ₀ ρ t i))),
        (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t) := by
  constructor
  · rintro ⟨Q, hQ, hdist, hws⟩
    have hs1 : ∀ t i, 1 ≤ wscale κ κ₀ ρ t i := fun t i =>
      one_le_exp (mul_nonneg hρ (by have := hκ t i; have := hκ₀ t; positivity))
    exact (BoxPerturbation.box_iff hd _ _ y (fun t i => div_pos (hP t i) (exp_pos _))
      (fun t i => (div_le_self (hP t i).le (hs1 t i)).trans
        (le_mul_of_one_le_right (hP t i).le (hs1 t i))) hy).1
      ⟨Q, fun t i => mem_wbox_of_wdist hκ hκ₀ (hQ t) (hP t) hρ t (hdist t) i, hws⟩
  · intro h
    obtain ⟨θ, hθ, hws⟩ := wpath_of_corners hd κ κ₀ P hP y hy hρ h
    exact ⟨_, fun t i => mul_pos (hP t i) (exp_pos _),
      fun t => wdist_wpath_le hκ hκ₀ (hP t) t (hθ t), hws⟩

/-- **One parameter per year suffices.** Some prices within weighted distance `ρ` make `y`
weakly solvable iff some prices on the log-linear paths
`θ ↦ P t ∘ e^{θ (1/κ + 1/κ₀)}`, `|θ| ≤ ρ`, do. -/
theorem wfeasible_iff_path (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    WFeasible κ κ₀ P y ρ ↔
      ∃ θ : Fin T → ℝ, (∀ t, |θ t| ≤ ρ) ∧
        WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y :=
  ⟨fun h => wpath_of_corners hd κ κ₀ P hP y hy hρ
      ((wfeasible_iff_corners hd κ κ₀ hκ hκ₀ P hP y hy hρ).1 h),
    fun ⟨_, hθ, hws⟩ => ⟨_, fun t i => mul_pos (hP t i) (exp_pos _),
      fun t => wdist_wpath_le hκ hκ₀ (hP t) t (hθ t), hws⟩⟩

/-- Weighted feasibility is monotone in the radius: the same prices work. -/
theorem WFeasible.mono {κ : Fin T → Fin d → ℝ} {κ₀ : Fin T → ℝ} {P : Fin T → Fin d → ℝ}
    {y : Fin T → ℝ} {ρ ρ' : ℝ} (h : WFeasible κ κ₀ P y ρ) (hρ : ρ ≤ ρ') :
    WFeasible κ κ₀ P y ρ' := by
  obtain ⟨Q, hQ, hd, hw⟩ := h
  exact ⟨Q, hQ, fun t => (hd t).trans hρ, hw⟩

/-- Weighted feasibility is closed from the right: path parameters `θ` for the radii
`ρ + 1/(n+1)` (`wfeasible_iff_path`) lie in a compact box; a limit point has `|θ t| ≤ ρ`, and
`WeakSolvable` (membership in a closure) passes to the limit. -/
theorem wfeasible_of_forall_gt (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ ρ', ρ < ρ' → WFeasible κ κ₀ P y ρ') : WFeasible κ κ₀ P y ρ := by
  have hn : ∀ n : ℕ, ∃ θ : Fin T → ℝ, (∀ t, |θ t| ≤ ρ + 1 / ((n:ℝ) + 1)) ∧
      WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y := fun n => by
    have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    exact (wfeasible_iff_path hd κ κ₀ hκ hκ₀ P hP y hy (by linarith)).1 (h _ (by linarith))
  choose θ hθ hws using hn
  let K : Set (Fin T → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-(ρ + 1)) (ρ + 1))
  have hθK : ∀ n, θ n ∈ K := by
    intro n t _
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have := abs_le.1 (hθ n t)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  obtain ⟨θ0, -, φ, hφ, hlim⟩ := (isCompact_univ_pi fun _ => isCompact_Icc).tendsto_subseq hθK
  have hε : Tendsto (fun n => 1 / (((φ n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hcoord : ∀ t, Tendsto (fun n => θ (φ n) t) atTop (𝓝 (θ0 t)) := fun t =>
    (continuous_apply t).continuousAt.tendsto.comp hlim
  have hb : Tendsto (fun n => ρ + 1 / (((φ n : ℕ) : ℝ) + 1)) atTop (𝓝 ρ) := by
    simpa using (tendsto_const_nhds (x := ρ)).add hε
  have hcl : IsClosed {θ : Fin T → ℝ |
      WeakSolvable (fun t i => P t i * exp (θ t * (1 / κ t i + 1 / κ₀ t))) y} :=
    isClosed_closure.preimage (by fun_prop)
  refine (wfeasible_iff_path hd κ κ₀ hκ hκ₀ P hP y hy hρ).2 ⟨θ0, fun t => ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto' (hcoord t).abs hb (fun n => hθ _ t)
  · exact hcl.mem_of_tendsto hlim (Eventually.of_forall fun n => hws _)

/-- The `2T` weighted corners at radius `ρ`: lower corners `P t / wscale`, then upper corners
`P t * wscale`. -/
noncomputable abbrev wcorners (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (P : Fin T → Fin d → ℝ)
    (ρ : ℝ) : Fin (T + T) → Fin d → ℝ :=
  Fin.append (fun t i => P t i / wscale κ κ₀ ρ t i) (fun t i => P t i * wscale κ κ₀ ρ t i)

/-- The `2T + d` homogenized vectors at radius `ρ`: lower and upper corners and the coordinate
directions. -/
noncomputable def wcornerVec (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (P : Fin T → Fin d → ℝ)
    (ρ : ℝ) : Fin T ⊕ Fin T ⊕ Fin d → Fin (d + 1) → ℝ :=
  Sum.elim (fun t => Fin.snoc (fun i => P t i / wscale κ κ₀ ρ t i) 1)
    (Sum.elim (fun t => Fin.snoc (fun i => P t i * wscale κ κ₀ ρ t i) 1)
      (fun i => Fin.snoc (Pi.single i 1) 0))

/-- The homogenized weighted corner `r` is `(wcorners r, 1)`. -/
theorem wcornerVec_cornerIdx (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (P : Fin T → Fin d → ℝ)
    (ρ : ℝ) (r : Fin (T + T)) :
    wcornerVec κ κ₀ P ρ (cornerIdx r) = Fin.snoc (wcorners κ κ₀ P ρ r) 1 := by
  induction r using Fin.addCases with
  | left t => simp [cornerIdx, wcornerVec, wcorners, Fin.append_left]
  | right t =>
    simp only [cornerIdx, wcorners, Fin.addCases_right, Fin.append_right]
    simp [wcornerVec]

/-- Each homogenized weighted corner vector is continuous in the radius. -/
theorem continuous_wcornerVec (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ) (P : Fin T → Fin d → ℝ)
    (j : Fin T ⊕ Fin T ⊕ Fin d) : Continuous fun ρ => wcornerVec κ κ₀ P ρ j := by
  rcases j with t | t | i
  · refine continuous_pi fun k => Fin.lastCases ?_ (fun i => ?_) k
    · simp [wcornerVec, Fin.snoc_last]; exact continuous_const
    · simp only [wcornerVec, wscale, Sum.elim_inl, Fin.snoc_castSucc]
      exact continuous_const.div (by fun_prop) fun _ => (exp_pos _).ne'
  · refine continuous_pi fun k => Fin.lastCases ?_ (fun i => ?_) k
    · simp [wcornerVec, Fin.snoc_last]; exact continuous_const
    · simp only [wcornerVec, wscale, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc]
      fun_prop
  · simp only [wcornerVec, Sum.elim_inr]; exact continuous_const

/-- If `ρs > 0` is feasible and no determinant vanishes at `ρs` without vanishing identically,
then some smaller radius is feasible: the corner certificate of `ρs` (`wfeasible_iff_corners`)
uses finitely many spectra, all still weakly reachable slightly below `ρs`
(`eventually_isWeakReachable_of`). -/
theorem exists_wfeasible_lt (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {ρs : ℝ} (hρs : 0 < ρs)
    (hfeas : WFeasible κ κ₀ P y ρs)
    (H : ∀ I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d,
      (Matrix.of fun j => wcornerVec κ κ₀ P ρs (I j)).det = 0 →
        ∀ ρ, (Matrix.of fun j => wcornerVec κ κ₀ P ρ (I j)).det = 0) :
    ∃ ρ, 0 ≤ ρ ∧ ρ < ρs ∧ WFeasible κ κ₀ P y ρ := by
  rcases isEmpty_or_nonempty (Fin T) with hT | ⟨⟨t₀⟩⟩
  · obtain ⟨Q, hQ, -, hW⟩ := hfeas
    exact ⟨0, le_rfl, hρs, Q, hQ, fun t => (IsEmpty.false t).elim, hW⟩
  obtain ⟨w, hw, h1, h2⟩ := (wfeasible_iff_corners hd κ κ₀ hκ hκ₀ P hP y hy hρs.le).1 hfeas
  have hev : ∀ᶠ ρ in 𝓝 ρs, ∀ S ∈ weakReachableSpectra (wcorners κ κ₀ P ρs),
      IsWeakReachable (wcorners κ κ₀ P ρ) S :=
    (Set.toFinite _).eventually_all.2 fun S hS =>
      eventually_isWeakReachable_of (wcornerVec κ κ₀ P) (wcorners κ κ₀ P)
        (continuous_wcornerVec κ κ₀ P) (wcornerVec_cornerIdx κ κ₀ P) (fun _ _ => rfl)
        (span_eq_top_of_snoc _ (fun i => ⟨Sum.inr (Sum.inr i), rfl⟩)
          (fun i => P t₀ i / wscale κ κ₀ ρs t₀ i) (Sum.inl t₀) rfl) H hS
  obtain ⟨ρ, hρ, hρI⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsLT (by linarith : ρs / 2 < ρs))).exists
  refine ⟨ρ, by linarith [hρI.1], hρI.2,
    (wfeasible_iff_corners hd κ κ₀ hκ hκ₀ P hP y hy (by linarith [hρI.1])).2 ⟨w, ?_, h1, h2⟩⟩
  exact Submodule.span_mono (Set.image_mono hρ) hw

/-- **The least weighted radius is a breakpoint.** If some radius is feasible, the feasible
radii form `[ρ*, ∞)`, and `ρ* = 0` or some `(d+1) × (d+1)` determinant of the homogenized corner
vectors vanishes at `ρ*` without vanishing identically in `ρ`.

Proof. As `least_radius_breakpoint`: feasibility is monotone (`WFeasible.mono`) and closed from
the right (`wfeasible_of_forall_gt`, via the log-linear paths of `wfeasible_iff_path`), so the
infimum is attained. If `ρ* > 0` and no determinant vanishes at `ρ*` unless identically, the corner
certificate of `wfeasible_iff_corners` survives slightly below `ρ*` (`exists_wfeasible_lt`). -/
theorem least_wradius_breakpoint (hd : 2 ≤ d) (κ : Fin T → Fin d → ℝ) (κ₀ : Fin T → ℝ)
    (hκ : ∀ t i, 0 < κ t i) (hκ₀ : ∀ t, 0 < κ₀ t) (P : Fin T → Fin d → ℝ)
    (hP : ∀ t, P t ∈ orthant d) (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t)
    (hfeas : ∃ ρ, 0 ≤ ρ ∧ WFeasible κ κ₀ P y ρ) :
    ∃ ρs, 0 ≤ ρs ∧ (∀ ρ, 0 ≤ ρ → (WFeasible κ κ₀ P y ρ ↔ ρs ≤ ρ)) ∧
      (ρs = 0 ∨ ∃ I : Fin (d + 1) → Fin T ⊕ Fin T ⊕ Fin d,
        (Matrix.of fun j => wcornerVec κ κ₀ P ρs (I j)).det = 0 ∧
          ∃ ρ, (Matrix.of fun j => wcornerVec κ κ₀ P ρ (I j)).det ≠ 0) := by
  obtain ⟨r0, hr0, hr0f⟩ := hfeas
  set A : Set ℝ := {ρ | 0 ≤ ρ ∧ WFeasible κ κ₀ P y ρ}
  have hne : A.Nonempty := ⟨r0, hr0, hr0f⟩
  have hbdd : BddBelow A := ⟨0, fun a ha => ha.1⟩
  have h0 : 0 ≤ sInf A := le_csInf hne fun a ha => ha.1
  have hF : WFeasible κ κ₀ P y (sInf A) := by
    refine wfeasible_of_forall_gt hd κ κ₀ hκ hκ₀ P hP y hy h0 fun ρ' hρ' => ?_
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt hne hρ'
    exact ha.2.mono hlt.le
  refine ⟨sInf A, h0, fun ρ hρ => ⟨fun h => csInf_le hbdd ⟨hρ, h⟩, fun h => hF.mono h⟩, ?_⟩
  rcases eq_or_lt_of_le h0 with h | h
  · exact Or.inl h.symm
  right
  by_contra hcon
  push_neg at hcon
  obtain ⟨ρ, hρ0, hρlt, hρf⟩ := exists_wfeasible_lt hd κ κ₀ hκ hκ₀ P hP y hy h hF hcon
  exact absurd (csInf_le hbdd ⟨hρ0, hρf⟩) (not_le.2 hρlt)

end NeoTiling.PricePerturbation
