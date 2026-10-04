import NeoTiling.PriceGeneralPosition

/-!
# Regular solvability

Notes, section "Разрешимость в общем положении": definition `def:regular-solvability` and theorem
`thm:regular-solvability`. Outputs `y` are *regularly solvable* at prices `P`
(`RegularlySolvable`) if a strictly positive neoclassical `h` with `(h, P)` in general position
realizes `y` at `P`.

Main results: for prices in general position (`PricesGeneralPosition`, `def:prices-gp`)
neoclassical and regular solvability coincide
(`PricesGeneralPosition.neoSolvable_iff_regularlySolvable`), and regular solvability is
neoclassical solvability at prices in general position (`regularlySolvable_iff`).
-/

namespace NeoTiling

/-- **Regular solvability** (notes, `def:regular-solvability`): some strictly positive
neoclassical `h` is in general position with the prices `P` and realizes `y` at `P`. -/
def RegularlySolvable {T : ℕ} (P : Fin T → ℝ × ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ h, IsPosNeoclassical h ∧ GeneralPosition h P ∧ Realizes h P y

/-- **Theorem `thm:regular-solvability`.** For prices in general position, `y` is neoclassically
solvable iff it is regularly solvable.

Proof: `(←)` is `neoSolvable_iff_exists_pos`. `(→)`: a strictly positive `h` realizes `y` at `P`
(`neoSolvable_iff_exists_pos`); take signature points `s` (`exists_signaturePoints`). A function
`g` with `(g, P)` in general position, closer to `h` at the finitely many points `p_t ∘ x`,
`x ∈ s`, than `h` is to `1` there (`PricesGeneralPosition.exists_generalPosition_near`), has the
same signature points (`SignaturePoints.of_abs_sub_lt`), hence realizes `y`
(`SignaturePoints.realizes`). -/
theorem PricesGeneralPosition.neoSolvable_iff_regularlySolvable {T : ℕ} {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) {y : Fin T → ℝ} :
    NeoSolvable P y ↔ RegularlySolvable P y := by
  refine ⟨fun hy => ?_, fun ⟨h, hh, _, hR⟩ =>
    (neoSolvable_iff_exists_pos hP.mem_orthant).mpr ⟨h, hh, hR⟩⟩
  obtain ⟨h, hh, hR⟩ := (neoSolvable_iff_exists_pos hP.mem_orthant).mp hy
  obtain ⟨s, m, H⟩ := exists_signaturePoints (hh.continuousOn.mono orthant_subset_quadrant)
    hP.mem_orthant (fun t => hh.toIsNeoclassical.volume_levelSet_eq_zero (hP.mem_orthant t)) hR
  classical
  -- the finitely many points `p_t ∘ x`, `x ∈ s`, all off the unit level of `h`
  set Z := (Finset.univ ×ˢ s).image fun q : Fin T × (ℝ × ℝ) => hadamard (P q.1) q.2
  have hZ : ∀ z ∈ Z, z ∈ orthant ∧ h z ≠ 1 := by
    simp only [Z, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
    rintro _ ⟨⟨t, x⟩, hx, rfl⟩
    exact ⟨hadamard_mem_orthant (hP.mem_orthant t) (H.1 x hx).1, (H.1 x hx).2 t⟩
  obtain ⟨g, hg, hgP, hgZ⟩ := hP.exists_generalPosition_near hh Z (fun z hz => (hZ z hz).1)
    (η := fun z => |h z - 1|) fun z hz => abs_pos.mpr (sub_ne_zero.mpr (hZ z hz).2)
  refine ⟨g, hg, hgP, (H.of_abs_sub_lt fun x hx t => hgZ _ ?_).realizes
    (hg.continuousOn.mono orthant_subset_quadrant) hP.mem_orthant⟩
  exact Finset.mem_image.mpr ⟨(t, x), Finset.mem_product.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

/-- Regular solvability is neoclassical solvability at prices in general position: regular
solvability forces general position of the prices (`GeneralPosition.pricesGeneralPosition`). -/
theorem regularlySolvable_iff {T : ℕ} {P : Fin T → ℝ × ℝ} {y : Fin T → ℝ} :
    RegularlySolvable P y ↔ PricesGeneralPosition P ∧ NeoSolvable P y := by
  refine ⟨fun hy => ?_, fun ⟨hP, hy⟩ => hP.neoSolvable_iff_regularlySolvable.mp hy⟩
  obtain ⟨h, hh, hG, -⟩ := id hy
  have hP := hG.pricesGeneralPosition hh
  exact ⟨hP, hP.neoSolvable_iff_regularlySolvable.mpr hy⟩

end NeoTiling
