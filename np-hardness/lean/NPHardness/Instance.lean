import NPHardness.Main

/-!
# The reduction as a computable rational instance

`Main.lean` builds the instance over `ℝ` and numbers it by the noncomputable `Fintype.equivFin`.
Here the same instance is written over `ℚ` with computable definitions:

* `priceQ`, `outputQ`: the prices and outputs over `ℚ`; `priceQ_cast`, `outputQ_cast`: their
  casts to `ℝ` are `Gadget.price` and `output`;
* `indexQ`: an explicit numbering of the prices, built from `finProdFinEquiv`,
  `finSumFinEquiv`, `finSigmaFinEquiv`, `finSuccEquiv`;
* `pricesQ`, `outputsQ`: the computable instance, and `weakSolvableQ_iff_colorable`,
  `neoSolvableQ_iff_colorable`.
-/

namespace NeoTiling.NPHardness

open Finset

/-- Squared norm over `ℚ`. -/
def sqnQ (a : Fin 2 → ℚ) : ℚ := a 0 ^ 2 + a 1 ^ 2

/-- `lift` over `ℚ`. -/
def liftQ (a : Fin 2 → ℚ) : Fin 3 → ℚ := ![a 0, a 1, -a 0 - a 1] + fun _ => 1 + sqnQ a

lemma liftQ_cast (a : Fin 2 → ℚ) (i : Fin 3) :
    ((liftQ a i : ℚ) : ℝ) = lift (fun j => (a j : ℝ)) i := by
  fin_cases i <;> simp [liftQ, lift, sqnQ, sqn, one3]

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-- `scale` over `ℚ`. -/
def scaleQ (n m : ℕ) : ℚ := 1 / (16 * (24 * m + 8 * n + 8))

lemma scaleQ_cast : ((scaleQ n m : ℚ) : ℝ) = scale n m := by simp [scaleQ, scale]

/-- `sval` over `ℚ`. -/
def svalQ : G.Node → ℚ
  | .inl (_, _, j) => if (j : ℕ) % 2 = 0 then 1 / 3 else 2 / 3
  | .inr ⟨_, _, j⟩ => if (j : ℕ) = 1 ∨ ((j : ℕ) % 2 = 0 ∧ (j : ℕ) ≠ 0) then 1 / 3 else 2 / 3

lemma svalQ_cast (w : G.Node) : ((G.svalQ w : ℚ) : ℝ) = G.sval w := by
  rcases w with ⟨_, _, j⟩ | ⟨_, _, j⟩ <;> simp only [svalQ, sval] <;> split_ifs <;> norm_num

/-- The reward points over `ℚ`. -/
def aQ (w : G.Node) : Fin 2 → ℚ := ![scaleQ n m * (G.pos w).1, scaleQ n m * (G.pos w).2]

/-- The heights over `ℚ`. -/
def etaQ (k : G.Link) : ℚ :=
  scaleQ n m ^ 2 * ((nrm (G.pos (G.linkV k) - G.pos (G.linkU k)) : ℚ) / 4 + 1 / 512)

/-- `Gadget.price` over `ℚ`. -/
def priceQ : Option (G.Node ⊕ G.Link) → Fin 3 → ℚ
  | none => fun _ => 1 / 4
  | some (.inl v) => liftQ (G.aQ v)
  | some (.inr k) =>
      liftQ (fun j => (G.aQ (G.linkU k) j + G.aQ (G.linkV k) j) / 2) + fun _ => G.etaQ k

/-- `output` over `ℚ`. -/
def outputQ : Option (G.Node ⊕ G.Link) → ℚ
  | none => 1
  | some (.inl v) => 1 - G.svalQ v
  | some (.inr _) => 1

lemma aQ_cast (w : G.Node) (j : Fin 2) : ((G.aQ w j : ℚ) : ℝ) = G.gadget.a w j := by
  fin_cases j <;> simp [aQ, gadget, Drawing.gadget, toR, drawing, scaleQ_cast]

lemma priceQ_cast (x : Option (G.Node ⊕ G.Link)) (i : Fin 3) :
    ((G.priceQ x i : ℚ) : ℝ) = G.gadget.price x i := by
  rcases x with _ | v | k
  · simp [priceQ, Gadget.price, one3]
  · simp only [priceQ, Gadget.price, liftQ_cast, aQ_cast]
  · simp only [priceQ, Gadget.price, Pi.add_apply, Rat.cast_add, liftQ_cast, Pi.smul_apply,
      smul_eq_mul, one3, mul_one]
    congr 2
    · funext j; simp [mid, aQ_cast, gadget, Drawing.gadget]
    · simp [etaQ, gadget, Drawing.gadget, drawing, scaleQ_cast]

lemma outputQ_cast (x : Option (G.Node ⊕ G.Link)) :
    ((G.outputQ x : ℚ) : ℝ) = output (E := G.Link) G.sval x := by
  rcases x with _ | v | k <;> simp [outputQ, output, svalQ_cast]

/-! ### An explicit numbering -/

/-- The number of row nodes. -/
def numRowNodes : ℕ := n * (3 * (12 * m + 1))

/-- The number of column nodes. -/
def numColNodes : ℕ := ∑ k, 3 * G.colLen k

/-- The number of nodes. -/
def numNodesQ : ℕ := numRowNodes (n := n) (m := m) + G.numColNodes

/-- The number of links. -/
def numLinksQ : ℕ :=
  n * (3 * (12 * m)) + ((∑ k, 3 * (G.colLen k - 1)) + (m * (3 * 2) + n * 3))

/-- The number of prices, an explicit expression. -/
def numPricesQ : ℕ := G.numNodesQ + G.numLinksQ + 1

/-- Numbering of `Fin a × Fin b × Fin c`. -/
def triple (a b c : ℕ) : Fin a × Fin b × Fin c ≃ Fin (a * (b * c)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

/-- Numbering of the nodes. -/
def nodeEquiv : G.Node ≃ Fin G.numNodesQ :=
  (Equiv.sumCongr (triple _ _ _)
    ((Equiv.sigmaCongrRight fun _ => finProdFinEquiv).trans finSigmaFinEquiv)).trans
    finSumFinEquiv

/-- Numbering of the links. -/
def linkEquiv : G.Link ≃ Fin G.numLinksQ :=
  (Equiv.sumCongr (triple _ _ _)
    (Equiv.sumCongr ((Equiv.sigmaCongrRight fun _ => finProdFinEquiv).trans finSigmaFinEquiv)
      (Equiv.sumCongr
        ((Equiv.prodCongr (Equiv.refl _)
          (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm)).trans (triple _ _ _))
        finProdFinEquiv |>.trans finSumFinEquiv) |>.trans finSumFinEquiv)).trans
    finSumFinEquiv

/-- The explicit numbering of the prices. -/
def indexQ : Option (G.Node ⊕ G.Link) ≃ Fin G.numPricesQ :=
  (Equiv.optionCongr ((Equiv.sumCongr G.nodeEquiv G.linkEquiv).trans finSumFinEquiv)).trans
    (finSuccEquiv _).symm

lemma numPricesQ_eq : G.numPricesQ = G.numPrices := by
  rw [numPrices, Fintype.card_congr G.indexQ, Fintype.card_fin]

lemma numPricesQ_le : G.numPricesQ ≤ 100 * (n + 1) * (m + 1) :=
  G.numPricesQ_eq ▸ G.numPrices_le

/-! ### The computable instance -/

/-- The prices, computable and rational. -/
def pricesQ (t : Fin G.numPricesQ) : Fin 3 → ℚ := G.priceQ (G.indexQ.symm t)

/-- The outputs, computable and rational. -/
def outputsQ (t : Fin G.numPricesQ) : ℚ := G.outputQ (G.indexQ.symm t)

lemma pricesQ_cast :
    (fun t i => ((G.pricesQ t i : ℚ) : ℝ)) = fun t => G.gadget.price (G.indexQ.symm t) := by
  funext t i; exact G.priceQ_cast _ i

lemma outputsQ_cast :
    (fun t => ((G.outputsQ t : ℚ) : ℝ)) = fun t => output (E := G.Link) G.sval (G.indexQ.symm t) := by
  funext t; exact G.outputQ_cast _

/-- **Main theorem (weak), rational form.** -/
theorem weakSolvableQ_iff_colorable :
    WeakSolvable (fun t i => ((G.pricesQ t i : ℚ) : ℝ)) (fun t => ((G.outputsQ t : ℚ) : ℝ)) ↔
      G.Colorable := by
  rw [pricesQ_cast, outputsQ_cast]
  exact (G.gadget.weakSolvable_iff G.gadget_valid G.indexQ G.sval G.sval_le_one).trans
    G.inStab_iff_colorable

/-- **Main theorem (strict), rational form.** -/
theorem neoSolvableQ_iff_colorable :
    NeoSolvable (fun t i => ((G.pricesQ t i : ℚ) : ℝ)) (fun t => ((G.outputsQ t : ℚ) : ℝ)) ↔
      G.Colorable := by
  rw [pricesQ_cast, outputsQ_cast]
  exact (G.gadget.neoSolvable_iff G.gadget_valid G.indexQ G.sval G.sval_le_one).trans
    G.inStab_iff_colorable

end Graph

end NeoTiling.NPHardness
