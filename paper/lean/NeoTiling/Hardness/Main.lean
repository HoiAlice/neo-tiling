import NeoTiling.Hardness.Coloring

/-!
# 3-colouring reduces to (weak) solvability in dimension 3

For a loopless graph `G` with `n` vertices and `m` edges, `G.prices` are `G.numPrices` rational
prices in `ℝ³₊₊` and `G.outputs` a rational output vector, built explicitly from `G`:
the gadget (`Gadget`) on the lattice drawing of `G □ K₃` (`Graph.drawing`) scaled into the box
`1/16`, with `s = G.sval`. Then

* `neoSolvable_iff_colorable`: `G.outputs` is neoclassically solvable at `G.prices` iff `G` is
  3-colourable;
* `weakSolvable_iff_colorable`: the same for weak solvability;
* `numPrices_le`: there are at most `100 (n + 1) (m + 1)` prices;
* `prices_rat`, `outputs_rat`: all numbers are rational.

Since 3-colourability is NP-complete, (weak) solvability at fixed prices in dimension `3` is
NP-hard under polynomial-time many-one (Karp) reductions.
-/

namespace NeoTiling.NPHardness

open Finset

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-- The scaling factor: all coordinates satisfy `|x| + |y| ≤ 24m + 8n + 8`. -/
noncomputable def scale (n m : ℕ) : ℝ := 1 / (16 * (24 * m + 8 * n + 8))

/-- The gadget of `G`. -/
noncomputable def gadget : Gadget G.Node G.Link := G.drawing.gadget (scale n m)

/-- The number of prices. -/
def numPrices : ℕ := Fintype.card (Option (G.Node ⊕ G.Link))

/-- Numbering of the prices. -/
noncomputable def index : Option (G.Node ⊕ G.Link) ≃ Fin G.numPrices := Fintype.equivFin _

/-- The prices. -/
noncomputable def prices (t : Fin G.numPrices) : Fin 3 → ℝ := G.gadget.price (G.index.symm t)

/-- The output vector. -/
noncomputable def outputs (t : Fin G.numPrices) : ℝ :=
  output (E := G.Link) G.sval (G.index.symm t)

/-! ### The gadget is valid -/

/-- **Bounding box.** All coordinates are nonnegative and `x + y ≤ 24m + 8n + 8`. -/
lemma pos_bound (w : G.Node) :
    0 ≤ (G.pos w).1 ∧ 0 ≤ (G.pos w).2 ∧ (G.pos w).1 + (G.pos w).2 ≤ 24 * m + 8 * n + 8 := by
  rcases w with ⟨v, i, j⟩ | ⟨k, i, j⟩
  · have := v.isLt; have := j.isLt
    fin_cases i <;> simp [pos, x0] <;> omega
  · have := k.isLt; have := j.isLt; have := (G.hi k).isLt; have := G.lo_lt_hi k
    simp only [colLen] at *
    fin_cases i <;> simp [pos, colX] <;> omega

/-- **The gadget is valid**: `scale n m ≤ 1/16`, and by the bounding box the drawing scaled by
`scale n m` lies in the box `1/16`. -/
theorem gadget_valid : G.gadget.Valid := by
  have hσ : 0 < scale n m := by unfold scale; positivity
  refine G.drawing.gadget_valid hσ ?_ fun w => ?_
  · unfold scale
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · obtain ⟨h1, h2, h3⟩ := G.pos_bound w
    have hxy : |((G.pos w).1 : ℝ)| + |((G.pos w).2 : ℝ)| ≤ 24 * m + 8 * n + 8 := by
      rw [abs_of_nonneg (by exact_mod_cast h1), abs_of_nonneg (by exact_mod_cast h2)]
      exact_mod_cast h3
    calc scale n m * (|((G.pos w).1 : ℝ)| + |((G.pos w).2 : ℝ)|)
        ≤ scale n m * (24 * m + 8 * n + 8) := mul_le_mul_of_nonneg_left hxy hσ.le
      _ = 1 / 16 := by unfold scale; field_simp

/-- The point `s` has coordinates `1/3` and `2/3`, in particular `≤ 1`. -/
lemma sval_le_one (p : G.Node) : G.sval p ≤ 1 := by
  rw [sval_eq]; split_ifs <;> norm_num

/-! ### Main theorems -/

/-- **Main theorem (strict).** The gadget theorem (`Gadget.neoSolvable_iff`) turns solvability
into `G.sval ∈ STAB`, and `inStab_iff_colorable` turns that into 3-colourability. -/
theorem neoSolvable_iff_colorable : NeoSolvable G.prices G.outputs ↔ G.Colorable :=
  (G.gadget.neoSolvable_iff G.gadget_valid G.index G.sval G.sval_le_one).trans
    G.inStab_iff_colorable

/-- **Main theorem (weak).** -/
theorem weakSolvable_iff_colorable : WeakSolvable G.prices G.outputs ↔ G.Colorable :=
  (G.gadget.weakSolvable_iff G.gadget_valid G.index G.sval G.sval_le_one).trans
    G.inStab_iff_colorable

/-- The instance has polynomial size. Each column has `colLen k ≤ 4n` nodes, so there are
`≤ 3n(12m + 1) + 12nm` nodes and `≤ 36nm + 12nm + 6m + 3n` links, plus the marker. -/
theorem numPrices_le : G.numPrices ≤ 100 * (n + 1) * (m + 1) := by
  have hcol : ∑ k, G.colLen k ≤ m * (4 * n) := by
    simpa using sum_le_sum fun k (_ : k ∈ univ) =>
      (by have := (G.hi k).isLt; unfold colLen; omega : G.colLen k ≤ 4 * n)
  have hcol' : ∑ k, (G.colLen k - 1) ≤ m * (4 * n) :=
    (sum_le_sum fun k _ => Nat.sub_le _ _).trans hcol
  simp only [numPrices, Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_sigma, Fintype.card_fin, Fintype.card_bool, ← mul_sum]
  nlinarith

/-! ### Rationality -/

/-- The rational reals, as a subfield of `ℝ`: all prices are built from integers and
`scale n m` by field operations. -/
noncomputable abbrev ratR : Subfield ℝ := (algebraMap ℚ ℝ).fieldRange

lemma mem_ratR {x : ℝ} : x ∈ ratR ↔ ∃ q : ℚ, x = q := by
  simp [RingHom.mem_fieldRange, eq_comm]

lemma int_mem (z : ℤ) : (z : ℝ) ∈ ratR := mem_ratR.2 ⟨z, by simp⟩

lemma scale_mem : scale n m ∈ ratR := mem_ratR.2 ⟨1 / (16 * (24 * m + 8 * n + 8)), by simp [scale]⟩

lemma lift_mem {a : Fin 2 → ℝ} (ha : ∀ j, a j ∈ ratR) (i : Fin 3) : lift a i ∈ ratR := by
  have := ha 0; have := ha 1
  fin_cases i <;> simp [lift, sqn, one3, -RingHom.mem_fieldRange] <;>
    apply_rules [add_mem, mul_mem, neg_mem, sub_mem, pow_mem, one_mem]

/-- The prices are rational. -/
theorem prices_rat (t : Fin G.numPrices) (i : Fin 3) : ∃ q : ℚ, G.prices t i = q := by
  have ha : ∀ w j, G.gadget.a w j ∈ ratR := fun w j => by
    fin_cases j <;> simp [gadget, Drawing.gadget, toR, -RingHom.mem_fieldRange] <;>
      exact mul_mem scale_mem (int_mem _)
  refine mem_ratR.1 ?_
  simp only [prices]
  rcases G.index.symm t with _ | w | k <;> simp only [Gadget.price]
  · simp only [one3, Pi.smul_apply, smul_eq_mul, mul_one]
    exact div_mem (one_mem _) (ofNat_mem _ 4)
  · exact lift_mem (ha w) i
  · simp only [Pi.add_apply, Pi.smul_apply, one3, smul_eq_mul, mul_one]
    refine add_mem (lift_mem (fun j => ?_) i) ?_
    · exact div_mem (add_mem (ha _ j) (ha _ j)) (ofNat_mem _ 2)
    · exact mul_mem (pow_mem scale_mem 2) (add_mem (div_mem (int_mem _) (ofNat_mem _ 4))
        (div_mem (one_mem _) (ofNat_mem _ 512)))

/-- The outputs are rational: `1`, `1 - 1/3` or `1 - 2/3`. -/
theorem outputs_rat (t : Fin G.numPrices) : ∃ q : ℚ, G.outputs t = q := by
  simp only [outputs]
  rcases G.index.symm t with _ | p | k
  · exact ⟨1, by simp [output]⟩
  · rcases (by rw [sval_eq]; split_ifs <;> simp : G.sval p = 1 / 3 ∨ G.sval p = 2 / 3)
      with h | h
    · exact ⟨2 / 3, by simp [output, h]; norm_num⟩
    · exact ⟨1 / 3, by simp [output, h]; norm_num⟩
  · exact ⟨1, by simp [output]⟩

end Graph

end NeoTiling.NPHardness
