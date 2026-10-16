import L1Perturbation.Algorithm

/-!
# Feasible half-widths form a closed set; the case `OPT = 0`

* `isClosed_setOf_isWeakReachable`: for a fixed `S`, the price tuples at which `S` is weakly
  reachable form a closed set (normalize the witness `ξ` into the compact standard simplex).
* `isClosed_setOf_boxFeasible`: the half-widths `z = (α, β)` passing the box query form a closed
  set. The bounds `y` of the box query do not depend on `z`; only the family of weakly reachable
  spectra does, and the cone condition is monotone in the family. So the set is a finite union,
  over the finite families `A` that pass the cone condition, of the closed sets where every
  `S ∈ A` is weakly reachable at the corners.
* `opt_pos_of_not_boxFeasible_zero`, `run_stops_of_not_boxFeasible_zero`: if the zero box fails
  the query and the cost is bounded away from `0` off every neighbourhood of `0`, then `OPT > 0`
  and `run_stops` applies. If the zero box passes the query, step 0 already stops
  (`init_stopped_of_boxFeasible_zero`). So the excluded case `OPT = 0` of `run_stops` is covered.
-/

namespace NeoTiling.L1Perturbation

open NeoTiling Real Polyblock

variable {d T N : ℕ}

/-- **Weak reachability is a closed condition.** For fixed `S`, the tuples `W` at which `S` is
weakly reachable form a closed set. For each `t ∈ S` the witness `ξ ≥ 0`, `ξ ≠ 0` can be scaled
into the compact standard simplex; the pairs `(ξ, W)` with `0 ≤ ⟨ξ, W s - W t⟩` for `s ∉ S` form a
closed set, and its projection to `W` along the compact factor is closed. -/
theorem isClosed_setOf_isWeakReachable (S : Finset (Fin N)) :
    IsClosed {W : Fin N → Fin d → ℝ | IsWeakReachable W S} := by
  haveI : CompactSpace (stdSimplex ℝ (Fin d)) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex _)
  have key : ∀ t, IsClosed {W : Fin N → Fin d → ℝ |
      ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∉ S, 0 ≤ ξ ⬝ᵥ (W s - W t)} := by
    intro t
    let C : Set (stdSimplex ℝ (Fin d) × (Fin N → Fin d → ℝ)) :=
      {p | ∀ s ∉ S, 0 ≤ (p.1 : Fin d → ℝ) ⬝ᵥ (p.2 s - p.2 t)}
    have hC : IsClosed C := by
      simp only [C, Set.setOf_forall]
      exact isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_le continuous_const
        ((continuous_subtype_val.comp continuous_fst).dotProduct
          (((continuous_apply s).comp continuous_snd).sub ((continuous_apply t).comp continuous_snd)))
    convert isClosedMap_snd_of_compactSpace _ hC using 1
    ext W
    constructor
    · rintro ⟨ξ, h0, hne, h⟩
      obtain ⟨c, hc, hcξ⟩ := exists_smul_mem_stdSimplex h0 hne
      refine ⟨(⟨c • ξ, hcξ⟩, W), fun s hs => ?_, rfl⟩
      show 0 ≤ (c • ξ) ⬝ᵥ (W s - W t)
      rw [smul_dotProduct]; exact mul_nonneg hc.le (h s hs)
    · rintro ⟨⟨⟨ξ, hξ⟩, W'⟩, h, rfl⟩
      refine ⟨ξ, hξ.1, ?_, h⟩
      rintro rfl
      simpa using hξ.2
  have : {W : Fin N → Fin d → ℝ | IsWeakReachable W S} = ⋂ t ∈ S, {W : Fin N → Fin d → ℝ |
      ∃ ξ : Fin d → ℝ, 0 ≤ ξ ∧ ξ ≠ 0 ∧ ∀ s ∉ S, 0 ≤ ξ ⬝ᵥ (W s - W t)} := by
    ext W; simp [IsWeakReachable]
  rw [this]
  exact isClosed_biInter fun t _ => key t

/-- The corners `P e^{-α}`, `P e^{β}` of the box with half-widths `z = (α, β)`. -/
noncomputable def corners (P : Fin T → Fin d → ℝ) (z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) :
    Fin (T + T) → Fin d → ℝ :=
  Fin.append (fun t i => P t i * exp (-alphaOf z t i)) (fun t i => P t i * exp (betaOf z t i))

/-- The box query through finite families: `z` passes iff some finite family `A` of sets, all
weakly reachable at the corners, already carries a vector `w` of its indicator cone with the
bounds `y`. (`→`: the whole family is finite. `←`: the indicator cone is monotone.) -/
theorem boxFeasible_iff_exists_finset (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) :
    BoxFeasible P y (alphaOf z) (betaOf z) ↔
      ∃ A : Finset (Finset (Fin (T + T))),
        (∃ w ∈ indicatorCone (A : Set (Finset (Fin (T + T)))),
          (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)) ∧
        ∀ S ∈ A, IsWeakReachable (corners P z) S := by
  classical
  constructor
  · rintro ⟨w, hw, hlo, hhi⟩
    refine ⟨Finset.univ.filter fun S => IsWeakReachable (corners P z) S, ⟨w, ?_, hlo, hhi⟩,
      fun S hS => (Finset.mem_filter.1 hS).2⟩
    convert hw using 2
    ext S
    simp [weakReachableSpectra, corners, alphaOf, betaOf]
  · rintro ⟨A, ⟨w, hw, hlo, hhi⟩, hA⟩
    refine ⟨w, Submodule.span_mono (Set.image_mono fun S hS => hA S hS) hw, hlo, hhi⟩

/-- The corners depend continuously on the half-widths. -/
theorem continuous_corners (P : Fin T → Fin d → ℝ) : Continuous (corners P) := by
  refine continuous_pi fun k => ?_
  refine Fin.addCases (fun t => ?_) (fun t => ?_) k
  · simp only [corners, Fin.append_left, alphaOf]
    exact continuous_pi fun i => continuous_const.mul
      (Real.continuous_exp.comp (continuous_apply _).neg)
  · simp only [corners, Fin.append_right, betaOf]
    exact continuous_pi fun i => continuous_const.mul
      (Real.continuous_exp.comp (continuous_apply _))

/-- **Feasible half-widths form a closed set.** The set of `z = (α, β)` passing the box query is
a finite union, over the finite families `A` carrying a good cone vector (a condition on `A` and
`y` only), of the finite intersections over `S ∈ A` of the preimages under the continuous
`corners P` of the closed sets `isClosed_setOf_isWeakReachable`. -/
theorem isClosed_setOf_boxFeasible (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ) :
    IsClosed {z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ |
      BoxFeasible P y (alphaOf z) (betaOf z)} := by
  have : {z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ | BoxFeasible P y (alphaOf z) (betaOf z)} =
      ⋃ A ∈ {A : Finset (Finset (Fin (T + T))) |
        ∃ w ∈ indicatorCone (A : Set (Finset (Fin (T + T)))),
          (∀ t, y t ≤ w (Fin.castAdd T t)) ∧ (∀ t, w (Fin.natAdd T t) ≤ y t)},
        ⋂ S ∈ A, corners P ⁻¹' {W | IsWeakReachable W S} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage,
      boxFeasible_iff_exists_finset, exists_prop]
  rw [this]
  exact (Set.toFinite _).isClosed_biUnion fun A _ => isClosed_biInter fun S _ =>
    (isClosed_setOf_isWeakReachable S).preimage (continuous_corners P)

/-- If the zero box fails the query, a whole neighbourhood `[0, r)^ι` of `0` fails it: every
point of `H ∩ box` has a coordinate at least `r`. -/
theorem exists_coord_ge_of_not_boxFeasible_zero (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (h0 : ¬ BoxFeasible P y 0 0) :
    ∃ r > 0, ∀ z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ, 0 ≤ z →
      BoxFeasible P y (alphaOf z) (betaOf z) → ∃ j, r ≤ z j := by
  have hO := (isClosed_setOf_boxFeasible P y).isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 (by exact h0)
  refine ⟨r, hr, fun z hz hzF => ?_⟩
  by_contra hlt
  push_neg at hlt
  refine hball ?_ hzF
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro j
  rw [Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_nonneg (hz j)]
  exact hlt j

/-- **`OPT > 0` when the zero box fails.** If the problem's `H` is, on the box, the set of
half-widths passing the box query, the zero box fails the query, and the cost is bounded away
from `0` on the points of the box with a coordinate at least `r` (for every `r > 0`), then
`OPT > 0`. -/
theorem opt_pos_of_not_boxFeasible_zero (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (Pr : Problem ((Fin T × Fin d) ⊕ (Fin T × Fin d)))
    (hH : ∀ z ∈ box Pr.M, z ∈ Pr.H ↔ BoxFeasible P y (alphaOf z) (betaOf z))
    (h0 : ¬ BoxFeasible P y 0 0)
    (hf0 : ∀ r > 0, ∃ η > 0, ∀ z ∈ box Pr.M, (∃ j, r ≤ z j) → η ≤ Pr.f z) :
    0 < Pr.opt := by
  obtain ⟨r, hr, hcoord⟩ := exists_coord_ge_of_not_boxFeasible_zero P y h0
  obtain ⟨η, hη, hfη⟩ := hf0 r hr
  refine hη.trans_le (Pr.le_opt fun z hz hb => hfη z hb ?_)
  exact hcoord z (fun j => (hb j).1) ((hH z hb).1 hz)

/-- **Termination when the zero box fails.** Under the hypotheses of
`opt_pos_of_not_boxFeasible_zero`, the run stops after the explicit number of steps of
`run_stops`. -/
theorem run_stops_of_not_boxFeasible_zero (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (Pr : Problem ((Fin T × Fin d) ⊕ (Fin T × Fin d)))
    (hH : ∀ z ∈ box Pr.M, z ∈ Pr.H ↔ BoxFeasible P y (alphaOf z) (betaOf z))
    (h0 : ¬ BoxFeasible P y 0 0)
    (hf0 : ∀ r > 0, ∃ η > 0, ∀ z ∈ box Pr.M, (∃ j, r ≤ z j) → η ≤ Pr.f z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n ≤ ⌈log (Pr.f Pr.top / (ε * Pr.opt)) / log (4 / 3)⌉₊ + 1 +
        (⌊Pr.M / (ε * Pr.opt / (2 * Pr.L))⌋₊ + 1) ^ Fintype.card ((Fin T × Fin d) ⊕ (Fin T × Fin d)),
      Stopped ε (Pr.run ε n) :=
  Pr.run_stops hε (opt_pos_of_not_boxFeasible_zero P y Pr hH h0 hf0)

/-- **Step 0 stops when the zero box passes.** Then `0 ∈ H`, the oracle answers YES at `0`, and
`init` has `UB = LB = f 0`. -/
theorem init_stopped_of_boxFeasible_zero (P : Fin T → Fin d → ℝ) (y : Fin T → ℝ)
    (Pr : Problem ((Fin T × Fin d) ⊕ (Fin T × Fin d)))
    (hH : ∀ z ∈ box Pr.M, z ∈ Pr.H ↔ BoxFeasible P y (alphaOf z) (betaOf z))
    (h0 : BoxFeasible P y 0 0) {ε : ℝ} (hε : 0 ≤ ε) : Stopped ε Pr.init := by
  have hb : (0 : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) ∈ box Pr.M :=
    fun _ => ⟨le_rfl, Pr.M_pos.le⟩
  have hO : Pr.O 0 = true := (Pr.O_spec 0 hb).2 ((hH 0 hb).2 h0)
  simp only [Stopped, Problem.init, hO, if_true, sub_self]
  exact mul_nonneg hε (Pr.f_nonneg 0)

end NeoTiling.L1Perturbation
