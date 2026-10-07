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
neoclassical solvability at prices in general position (`regularlySolvable_iff`). Both reduce
to the cone lemma `IsNeoclassical.realizes_iff_mem_span` (`lem:signature-points`) via
`Realizes.mono_spectrum`; the approximation step is
`PricesGeneralPosition.exists_spectrum_subset` (`lem:gp-approx`).
-/

open Filter Topology

namespace NeoTiling

/-- **Regular solvability** (notes, `def:regular-solvability`): some strictly positive
neoclassical `h` is in general position with the prices `P` and realizes `y` at `P`. -/
def RegularlySolvable {T : ℕ} (P : Fin T → ℝ × ℝ) (y : Fin T → ℝ) : Prop :=
  ∃ h, IsPosNeoclassical h ∧ GeneralPosition h P ∧ Realizes h P y

/-- **Lemma `lem:gp-approx`.** For prices in general position and neoclassical `h`, some
strictly positive neoclassical `g` is in general position with `P` and has a larger spectrum.

Proof: pick in each `R_S`, `S ∈ Sp(h, P)`, a point `x_S` off the curves
(`exists_mem_specRegion_ne_one`); let `Z = {p_t ∘ x_S}` and `η = |h - 1| > 0` on `Z`. Take a
strictly positive `h'` with `|h' - h| < η / 2` on `Z` (`exists_isPosNeoclassical_near`) and `g`
in general position with `|g - h'| < η / 2` on `Z` (`exists_generalPosition_near`). The signs of
`g - 1` and `h - 1` agree strictly at `Z`, so `S ∈ Sp(g, P)` (`mem_spectrum_of_abs_sub_lt`). -/
theorem PricesGeneralPosition.exists_spectrum_subset {T : ℕ} {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) {h : ℝ × ℝ → ℝ} (hh : IsNeoclassical h) :
    ∃ g, IsPosNeoclassical g ∧ GeneralPosition g P ∧ spectrum h P ⊆ spectrum g P := by
  classical
  have hex (S) : ∃ x, S ∈ spectrum h P →
      x ∈ specRegion h P S ∧ ∀ t, h (hadamard (P t) x) ≠ 1 := by
    by_cases hS : S ∈ spectrum h P
    · obtain ⟨x, hx⟩ := exists_mem_specRegion_ne_one
        (fun t => hh.volume_levelSet_eq_zero (hP.mem_orthant t)) hS
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose x hx using hex
  -- the finitely many points `p_t ∘ x_S`, all off the unit level of `h`
  set Z : Finset (ℝ × ℝ) := (Finset.univ ×ˢ Finset.univ.filter (· ∈ spectrum h P)).image
    fun q : Fin T × Finset (Fin T) => hadamard (P q.1) (x q.2)
  have hZ : ∀ z ∈ Z, z ∈ orthant ∧ h z ≠ 1 := by
    simp only [Z, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_filter]
    rintro _ ⟨⟨t, S⟩, hS, rfl⟩
    exact ⟨hadamard_mem_orthant (hP.mem_orthant t) (hx S hS).1.1, (hx S hS).2 t⟩
  have hη : ∀ z ∈ Z, 0 < |h z - 1| / 2 := fun z hz =>
    half_pos (abs_pos.mpr (sub_ne_zero.mpr (hZ z hz).2))
  obtain ⟨h', hh', hh'Z⟩ := hh.exists_isPosNeoclassical_near Z hη
  obtain ⟨g, hg, hgP, hgZ⟩ :=
    hP.exists_generalPosition_near hh' Z (fun z hz => (hZ z hz).1) hη
  refine ⟨g, hg, hgP, fun S hS => mem_spectrum_of_abs_sub_lt
    (hg.continuousOn.mono orthant_subset_quadrant) hP.mem_orthant (hx S hS).1 fun t => ?_⟩
  have hz : hadamard (P t) (x S) ∈ Z := Finset.mem_image.mpr ⟨(t, S), by simp [hS], rfl⟩
  have h1 := abs_lt.mp (hh'Z _ hz)
  have h2 := abs_lt.mp (hgZ _ hz)
  rw [abs_lt]
  constructor <;> linarith

/-- **Theorem `thm:regular-solvability`.** For prices in general position, `y` is neoclassically
solvable iff it is regularly solvable.

Proof: by `lem:signature-points` both mean that `y` lies in a cone spanned by a spectrum, and
realization passes to a larger spectrum (`Realizes.mono_spectrum`). `(←)`: the spectrum of `h`
does not shrink near `P` (`IsNeoclassical.eventually_spectrum_subset`). `(→)`: take `h` and the
realization at `P` itself; `g` from `lem:gp-approx` (`exists_spectrum_subset`) is in general
position with `P` and has a larger spectrum. -/
theorem PricesGeneralPosition.neoSolvable_iff_regularlySolvable {T : ℕ} {P : Fin T → ℝ × ℝ}
    (hP : PricesGeneralPosition P) {y : Fin T → ℝ} :
    NeoSolvable P y ↔ RegularlySolvable P y := by
  refine ⟨fun ⟨h, hh, hev⟩ => ?_, fun ⟨g, hg, hgP, hR⟩ => ⟨g, hg.toIsNeoclassical, ?_⟩⟩
  · obtain ⟨g, hg, hgP, hS⟩ := hP.exists_spectrum_subset hh
    exact ⟨g, hg, hgP, hev.self_of_nhds.mono_spectrum hh hP.mem_orthant hg.toIsNeoclassical
      hP.mem_orthant hS⟩
  · filter_upwards [hg.toIsNeoclassical.eventually_spectrum_subset hP.mem_orthant,
      eventually_mem_orthant hP.mem_orthant] with Q hQ hQo
    exact hR.mono_spectrum hg.toIsNeoclassical hP.mem_orthant hg.toIsNeoclassical hQo hQ

/-- Regular solvability is neoclassical solvability at prices in general position: regular
solvability forces general position of the prices (`GeneralPosition.pricesGeneralPosition`). -/
theorem regularlySolvable_iff {T : ℕ} {P : Fin T → ℝ × ℝ} {y : Fin T → ℝ} :
    RegularlySolvable P y ↔ PricesGeneralPosition P ∧ NeoSolvable P y := by
  refine ⟨fun hy => ?_, fun ⟨hP, hy⟩ => hP.neoSolvable_iff_regularlySolvable.mp hy⟩
  obtain ⟨h, hh, hG, -⟩ := id hy
  have hP := hG.pricesGeneralPosition hh
  exact ⟨hP, hP.neoSolvable_iff_regularlySolvable.mpr hy⟩

end NeoTiling
