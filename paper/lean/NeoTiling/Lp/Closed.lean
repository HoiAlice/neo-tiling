import NeoTiling.Lp.Algorithm

/-!
# Feasible half-widths form a closed set; the case `OPT = 0`

* `isClosed_setOf_isWeakReachable`: for a fixed `S`, the price tuples at which `S` is weakly
  reachable form a closed set (normalize the witness `ξ` into the compact standard simplex).
* `isClosed_setOf_boxFeasible`: the half-widths `z = (α, β)` passing the box query form a closed
  set. The bounds `y` of the box query do not depend on `z`; only the family of weakly reachable
  spectra does, and the cone condition is monotone in the family. So the set is a finite union,
  over the finite families `A` that pass the cone condition, of the closed sets where every
  `S ∈ A` is weakly reachable at the corners.
* `opt_pos_of_not_boxFeasible_zero`, `run_stops_of_not_boxFeasible_zero`: on `D.problem S`, if
  the zero box fails the query, then `OPT > 0` (the box cost is at least `r min c` off the
  neighbourhood `[0, r)^ι` of `0`) and `run_stops` applies. If the zero box passes the query, step 0 already stops
  (`init_stopped_of_boxFeasible_zero`). So the excluded case `OPT = 0` of `run_stops` is covered.
-/

namespace NeoTiling.Lp

open Real

variable {d T N : ℕ}

/-- **Weak reachability is a closed condition.** For fixed `S`, the tuples `W` at which `S` is
weakly reachable form a closed set: `S` is weakly reachable at `W` iff every `W t`, `t ∈ S`, is
supported by `{W s | s ∉ S}`, a finite intersection of preimages of the closed set
`isClosed_setOf_supported_pair`. -/
theorem isClosed_setOf_isWeakReachable (S : Finset (Fin N)) :
    IsClosed {W : Fin N → Fin d → ℝ | IsWeakReachable W S} := by
  have : {W : Fin N → Fin d → ℝ | IsWeakReachable W S} =
      ⋂ t ∈ S, (fun W => (W, W t)) ⁻¹' {p | Perturbation.Supported p.1 S p.2} := by
    ext W; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]; rfl
  rw [this]
  exact isClosed_biInter fun t _ => (Perturbation.isClosed_setOf_supported_pair S).preimage
    (continuous_id.prodMk (continuous_apply t))

/-- The corners `P (1 - α)`, `P (1 + β)` of the box with half-widths `z = (α, β)`. -/
def corners (P : Fin T → Fin d → ℝ) (z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) :
    Fin (T + T) → Fin d → ℝ :=
  Fin.append (fun t i => P t i * (1 - alphaOf z t i)) (fun t i => P t i * (1 + betaOf z t i))

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
    exact continuous_pi fun i => continuous_const.mul (continuous_const.sub (continuous_apply _))
  · simp only [corners, Fin.append_right, betaOf]
    exact continuous_pi fun i => continuous_const.mul (continuous_const.add (continuous_apply _))

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

section BoxClosed

variable (D : BoxData T d)

/-- **`OPT > 0` when the zero box fails.** A neighbourhood `[0, r)^ι` of `0` fails the query
(`exists_coord_ge_of_not_boxFeasible_zero`), and a point of the box with a coordinate at least `r`
costs at least `r min c > 0` (`le_boxCost`). The optimum depends on the data only. -/
theorem opt_pos_of_not_boxFeasible_zero (h0 : ¬ BoxFeasible D.P D.y 0 0) : 0 < D.opt := by
  obtain ⟨r, hr, hcoord⟩ := exists_coord_ge_of_not_boxFeasible_zero D.P D.y h0
  have : Nonempty (Fin T × Fin d) := ⟨(⟨0, D.hT⟩, ⟨0, by have := D.hd; omega⟩)⟩
  obtain ⟨⟨t₀, i₀⟩, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun ti : Fin T × Fin d => D.c ti.1 ti.2) Finset.univ_nonempty
  have hne : (boxCost D.p D.c '' (boxH D.P D.y D.Mv ∩ box D.Mv)).Nonempty :=
    ⟨_, D.Mv, ⟨⟨fun j => ⟨(D.hM j).le, le_rfl⟩, D.top_mem⟩, fun j => ⟨(D.hM j).le, le_rfl⟩⟩, rfl⟩
  refine (mul_pos (D.hc t₀ i₀) hr).trans_le (le_csInf hne ?_)
  rintro _ ⟨z, ⟨hz, hb⟩, rfl⟩
  have hc0 : ∀ t i, 0 ≤ D.c t i := fun t i => (D.hc t i).le
  obtain ⟨j, hj⟩ := hcoord z (fun j => (hb j).1) hz.2
  rcases j with ⟨t, i⟩ | ⟨t, i⟩
  · exact (mul_le_mul_of_nonneg_right (hmin (t, i) (Finset.mem_univ _)) hr.le).trans
      (le_boxCost D.hp hc0 hr.le t i (hj.trans (le_max_left _ _)))
  · exact (mul_le_mul_of_nonneg_right (hmin (t, i) (Finset.mem_univ _)) hr.le).trans
      (le_boxCost D.hp hc0 hr.le t i (hj.trans (le_max_right _ _)))

variable (S : BoxOracle D)

/-- **Termination when the zero box fails.** The run stops after the explicit number of steps of
`run_stops`, for any bound `Mmax` on the sides of the box. -/
theorem run_stops_of_not_boxFeasible_zero (h0 : ¬ BoxFeasible D.P D.y 0 0) {ε : ℝ} (hε : 0 < ε)
    {Mmax : ℝ} (hMmax : ∀ j, D.Mv j ≤ Mmax) :
    ∃ n ≤ ⌈log (boxCost D.p D.c D.Mv / (ε * D.opt)) / log (4 / 3)⌉₊ + 1 +
        (⌊Mmax / (ε * D.opt / (2 * cNorm D.p D.c))⌋₊ + 1) ^
          Fintype.card ((Fin T × Fin d) ⊕ (Fin T × Fin d)),
      Stopped ε ((D.problem S).run ε n) :=
  (D.problem S).run_stops hε (opt_pos_of_not_boxFeasible_zero D h0) hMmax

/-- **Step 0 stops when the zero box passes.** Then the oracle answers YES at `0`, and `init` has
`UB = LB = f 0`. -/
theorem init_stopped_of_boxFeasible_zero (h0 : BoxFeasible D.P D.y 0 0) {ε : ℝ} (hε : 0 ≤ ε) :
    Stopped ε (D.problem S).init := by
  have hb : (0 : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) ∈ box D.Mv :=
    fun j => ⟨le_rfl, (D.hM j).le⟩
  have hO0 : S.O 0 = true := (S.hO 0 hb).2 h0
  simp only [Stopped, Problem.init, BoxData.problem, hO0, if_true, sub_self]
  exact mul_nonneg hε (Real.rpow_nonneg (lpPow_nonneg D.p (fun t i => (D.hc t i).le) _) _)

end BoxClosed

end NeoTiling.Lp
