import NeoTiling.Hardness.Costed

/-!
# The reduction is polynomial: counted cost and Karp reductions

Status: everything is proved, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`
only. The cost is counted by the monad `Costed` (`Costed.lean`), not declared.

* `KarpReduction`, `QInstance`, `QInstance.size`: a Karp reduction in the unit-cost model and
  rational instances of solvability in dimension `3` with their bit size.
* `reduceM`: the reduction as a program: enumerate the indices `allX`, compute each price and
  output with `priceM`, `outputM`, collect them into an instance (`QInstance.ofList`).
* `val_instanceM`: the program outputs `instOf σ`, the instance of `Instance.lean` numbered by
  the list `allX`; `weakSolvable_instOf`, `neoSolvable_instOf`: for any bijective numbering it
  is solvable iff `G` is 3-colourable.
* `cost_instanceM_le`: at most `127` operations per price, `≤ 12700 (n + 1) (m + 1)`.
* `size_instOf_le`: the bit size of the instance is `≤ 2^40 (n + m + 1)^4`, by `Size.lean`.
* `karp_threeCol_weakSolvable`, `karp_threeCol_neoSolvable`: 3-colourability Karp-reduces to
  weak and to neoclassical solvability in dimension `3`, with `C = 2^40`, `k = 4`.
-/

namespace NeoTiling.Hardness

open Finset Costed

/-! ### Karp reductions -/

/-- A Karp reduction in the unit-cost model: a program `prog` in the cost monad, correct, with
counted cost and output size bounded by `C * (size + 1)^k`. The map and its cost are the value
and the cost of the program (`KarpReduction.f`, `KarpReduction.cost`), so the cost is not
declared. -/
structure KarpReduction {α β : Type*} (A : α → Prop) (B : β → Prop) (sizeA : α → ℕ)
    (sizeB : β → ℕ) where
  prog : α → Costed β
  C : ℕ
  k : ℕ
  correct : ∀ x, A x ↔ B (prog x).val
  cost_le : ∀ x, (prog x).cost ≤ C * (sizeA x + 1) ^ k
  size_le : ∀ x, sizeB (prog x).val ≤ C * (sizeA x + 1) ^ k

/-- The map of a Karp reduction: the value of its program. -/
def KarpReduction.f {α β : Type*} {A : α → Prop} {B : β → Prop} {sizeA : α → ℕ}
    {sizeB : β → ℕ} (R : KarpReduction A B sizeA sizeB) (x : α) : β := (R.prog x).val

/-- The cost of a Karp reduction: the counted cost of its program. -/
def KarpReduction.cost {α β : Type*} {A : α → Prop} {B : β → Prop} {sizeA : α → ℕ}
    {sizeB : β → ℕ} (R : KarpReduction A B sizeA sizeB) (x : α) : ℕ := (R.prog x).cost

/-- A rational instance of (weak) solvability in dimension `3`: `T` prices and outputs. -/
structure QInstance where
  T : ℕ
  P : Fin T → Fin 3 → ℚ
  y : Fin T → ℚ

/-- Weak solvability of a rational instance. -/
def QInstance.WeakSolvable (I : QInstance) : Prop :=
  NeoTiling.WeakSolvable (fun t i => ((I.P t i : ℚ) : ℝ)) (fun t => ((I.y t : ℚ) : ℝ))

/-- Neoclassical solvability of a rational instance. -/
def QInstance.NeoSolvable (I : QInstance) : Prop :=
  NeoTiling.NeoSolvable (fun t i => ((I.P t i : ℚ) : ℝ)) (fun t => ((I.y t : ℚ) : ℝ))

/-- The bit size of a rational instance. -/
def QInstance.size (I : QInstance) : ℕ :=
  I.T + ∑ t, ∑ i, (Nat.log 2 (I.P t i).num.natAbs + Nat.log 2 (I.P t i).den) +
    ∑ t, (Nat.log 2 (I.y t).num.natAbs + Nat.log 2 (I.y t).den)

/-- The instance with the prices and outputs of a list, in its order. -/
def QInstance.ofList (l : List ((Fin 3 → ℚ) × ℚ)) : QInstance :=
  ⟨l.length, fun t i => (l.get t).1 i, fun t => (l.get t).2⟩

/-- Graphs of any size. -/
def GraphIn : Type := Σ n m : ℕ, Graph n m

/-- The size of a graph: vertices plus edges. -/
def sizeG : GraphIn → ℕ
  | ⟨n, m, _⟩ => n + m

/-! ### The reduction as a program -/

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-- One price and its output. -/
def entryM (x : Option (G.Node ⊕ G.Link)) : Costed ((Fin 3 → ℚ) × ℚ) := do
  let p ← G.priceM x
  let o ← G.outputM x
  pure (p, o)

/-- The instance: enumerate the indices, compute every price and output. -/
def instanceM : Costed QInstance := do
  let xs ← G.enumM
  let l ← xs.mapM G.entryM
  pure (QInstance.ofList l)

/-- The instance of `Instance.lean` with the prices numbered by `σ`. -/
def instOf {T : ℕ} (σ : Fin T → Option (G.Node ⊕ G.Link)) : QInstance :=
  ⟨T, fun t => G.priceQ (σ t), fun t => G.outputQ (σ t)⟩

/-- The numbering by the list `allX`. -/
def sigmaX {T : ℕ} (hT : T = G.allX.length) (t : Fin T) : Option (G.Node ⊕ G.Link) :=
  G.allX[t.1]'(hT ▸ t.2)

lemma bijective_sigmaX {T : ℕ} (hT : T = G.allX.length) : Function.Bijective (G.sigmaX hT) := by
  subst hT
  refine ⟨fun s t h => Fin.ext ((G.nodup_allX.getElem_inj_iff).1 h), fun x => ?_⟩
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (G.mem_allX x)
  exact ⟨⟨i, hi⟩, h⟩

/-- **The program computes the instance**, numbered by `allX`. -/
theorem val_instanceM :
    G.instanceM.val = G.instOf (G.sigmaX (T := (G.allX.mapM G.entryM).val.length) (by simp)) := by
  simp only [instanceM, val_enumM, val_bind, val_pure, QInstance.ofList, instOf,
    QInstance.mk.injEq, heq_eq_eq, true_and]
  constructor <;> funext t <;> simp [sigmaX, entryM, val_priceM, val_outputM]

/-- **Correctness (weak)** for any bijective numbering. -/
theorem weakSolvable_instOf {T : ℕ} (σ : Fin T → Option (G.Node ⊕ G.Link))
    (hσ : Function.Bijective σ) : (G.instOf σ).WeakSolvable ↔ G.Colorable := by
  let e := (Equiv.ofBijective σ hσ).symm
  have hP : (fun t i => ((G.priceQ (σ t) i : ℚ) : ℝ)) = fun t => G.gadget.price (e.symm t) := by
    funext t i; exact G.priceQ_cast _ i
  have hy : (fun t => ((G.outputQ (σ t) : ℚ) : ℝ)) =
      fun t => output (E := G.Link) G.sval (e.symm t) := by
    funext t; exact G.outputQ_cast _
  simp only [QInstance.WeakSolvable, instOf, hP, hy]
  exact (G.gadget.weakSolvable_iff G.gadget_valid e G.sval G.sval_le_one).trans
    G.inStab_iff_colorable

/-- **Correctness (strict)** for any bijective numbering. -/
theorem neoSolvable_instOf {T : ℕ} (σ : Fin T → Option (G.Node ⊕ G.Link))
    (hσ : Function.Bijective σ) : (G.instOf σ).NeoSolvable ↔ G.Colorable := by
  let e := (Equiv.ofBijective σ hσ).symm
  have hP : (fun t i => ((G.priceQ (σ t) i : ℚ) : ℝ)) = fun t => G.gadget.price (e.symm t) := by
    funext t i; exact G.priceQ_cast _ i
  have hy : (fun t => ((G.outputQ (σ t) : ℚ) : ℝ)) =
      fun t => output (E := G.Link) G.sval (e.symm t) := by
    funext t; exact G.outputQ_cast _
  simp only [QInstance.NeoSolvable, instOf, hP, hy]
  exact (G.gadget.neoSolvable_iff G.gadget_valid e G.sval G.sval_le_one).trans
    G.inStab_iff_colorable

/-- **The cost is polynomial**: one operation per index for the enumeration, at most `120` per
price and `6` per output. -/
theorem cost_instanceM_le : G.instanceM.cost ≤ 12700 * (n + 1) * (m + 1) := by
  have h1 : ∀ c ∈ G.allX.map fun x => (G.entryM x).cost, c ≤ 126 := by
    simp only [List.mem_map]
    rintro _ ⟨x, -, rfl⟩
    have := G.cost_priceM_le x
    have := G.cost_outputM_le x
    simp only [entryM, cost_bind, cost_pure]; omega
  have h2 := List.sum_le_card_nsmul _ _ h1
  have h3 := G.numPrices_le
  simp only [List.length_map, smul_eq_mul, G.length_allX] at h2
  simp only [instanceM, cost_bind, G.cost_enumM, G.val_enumM, cost_mapM, cost_pure,
    G.length_allX]
  generalize (G.allX.map fun x => (G.entryM x).cost).sum = S at h2 ⊢
  generalize G.numPrices = N at h2 h3 ⊢
  nlinarith

/-- **Output size.** Every price entry has `den ≤ 2^17 B²`, `|num| ≤ 2^18 B²` with
`B = 24m + 8n + 8`, every output `den, |num| ≤ 3`, and there are `≤ 100 (n + 1) (m + 1)` prices;
`Nat.log 2 x ≤ x` crudely. -/
theorem size_instOf_le {T : ℕ} (σ : Fin T → Option (G.Node ⊕ G.Link))
    (hT : T ≤ 100 * (n + 1) * (m + 1)) : (G.instOf σ).size ≤ 2 ^ 40 * (n + m + 1) ^ 4 := by
  have hlog : ∀ x : ℕ, Nat.log 2 x ≤ x := fun x => Nat.log_le_self 2 x
  simp only [instOf, QInstance.size]
  have hp : ∀ t i, Nat.log 2 (G.priceQ (σ t) i).num.natAbs + Nat.log 2 (G.priceQ (σ t) i).den
      ≤ 2 ^ 19 * Graph.bnd n m ^ 2 := fun t i => by
    obtain ⟨N, h⟩ := G.priceQ_mul_int (σ t) i
    have := den_le_of_mul_eq_int denom_pos h
    have := natAbs_num_le_of_mul_eq_int denom_pos h (G.abs_priceQ_le _ i)
    have := hlog (G.priceQ (σ t) i).num.natAbs
    have := hlog (G.priceQ (σ t) i).den
    unfold denom at *
    omega
  have ho : ∀ t, Nat.log 2 (G.outputQ (σ t)).num.natAbs + Nat.log 2 (G.outputQ (σ t)).den ≤ 6 :=
    fun t => by
    have := hlog (G.outputQ (σ t)).num.natAbs
    have := hlog (G.outputQ (σ t)).den
    have : (G.outputQ (σ t)).den ≤ 3 ∧ (G.outputQ (σ t)).num.natAbs ≤ 3 := by
      rcases G.outputQ_cases (σ t) with h | h | h <;> rw [h] <;> decide +kernel
    omega
  have h1 : ∀ t, ∑ i : Fin 3, (Nat.log 2 (G.priceQ (σ t) i).num.natAbs +
      Nat.log 2 (G.priceQ (σ t) i).den) ≤ 3 * (2 ^ 19 * Graph.bnd n m ^ 2) := fun t => by
    have := sum_le_card_nsmul univ _ _ fun i _ => hp t i
    simpa using this
  have h2 := sum_le_card_nsmul univ _ _ fun t _ => h1 t
  have h3 := sum_le_card_nsmul univ _ _ fun t (_ : t ∈ univ) => ho t
  simp only [card_univ, Fintype.card_fin, smul_eq_mul] at h2 h3
  have hBle : Graph.bnd n m ≤ 24 * (n + m + 1) := by unfold Graph.bnd; omega
  have hB2 : Graph.bnd n m ^ 2 ≤ 576 * (n + m + 1) ^ 2 := by nlinarith
  clear hp ho h1
  generalize (∑ t : Fin T, ∑ i : Fin 3, (Nat.log 2 (G.priceQ (σ t) i).num.natAbs +
    Nat.log 2 (G.priceQ (σ t) i).den)) = S1 at *
  generalize (∑ t : Fin T, (Nat.log 2 (G.outputQ (σ t)).num.natAbs +
    Nat.log 2 (G.outputQ (σ t)).den)) = S2 at *
  generalize Graph.bnd n m ^ 2 = Q at *
  have hR : (n + m + 1) ^ 4 = (n + m + 1) ^ 2 * (n + m + 1) ^ 2 := by ring
  have hm' : (n + 1) * (m + 1) ≤ (n + m + 1) ^ 2 := by
    nlinarith [Nat.zero_le (n * m)]
  generalize (n + m + 1) ^ 2 = R at *
  generalize (n + m + 1) ^ 4 = W at *
  have h5 : T * Q ≤ 100 * R * (576 * R) :=
    Nat.mul_le_mul (by nlinarith) hB2
  nlinarith

end Graph

/-! ### The Karp reductions -/

/-- The reduction as a program on graphs of any size. -/
def reduceM : GraphIn → Costed QInstance
  | ⟨_, _, G⟩ => G.instanceM

/-- `(n + 1) (m + 1) ≤ (n + m + 1)^4`. -/
lemma mul_succ_le_pow (n m : ℕ) : (n + 1) * (m + 1) ≤ (n + m + 1) ^ 4 :=
  calc (n + 1) * (m + 1) ≤ (n + m + 1) * (n + m + 1) := Nat.mul_le_mul (by omega) (by omega)
    _ = (n + m + 1) ^ 2 := by ring
    _ ≤ (n + m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)

theorem cost_reduceM_le (g : GraphIn) : (reduceM g).cost ≤ 2 ^ 40 * (sizeG g + 1) ^ 4 := by
  obtain ⟨n, m, G⟩ := g
  calc G.instanceM.cost ≤ 12700 * ((n + 1) * (m + 1)) := by
        rw [← mul_assoc]; exact G.cost_instanceM_le
    _ ≤ 2 ^ 40 * (n + m + 1) ^ 4 := Nat.mul_le_mul (by norm_num) (mul_succ_le_pow n m)

theorem size_reduceM_le (g : GraphIn) : (reduceM g).val.size ≤ 2 ^ 40 * (sizeG g + 1) ^ 4 := by
  obtain ⟨n, m, G⟩ := g
  simp only [reduceM, sizeG, G.val_instanceM]
  refine G.size_instOf_le _ ?_
  rw [val_mapM, List.length_map, G.length_allX]; exact G.numPrices_le

/-- **3-colourability Karp-reduces to weak solvability in dimension `3`** in the unit-cost
model, with `C = 2^40`, `k = 4`. The program is `reduceM`. (A `def`, since a `KarpReduction`
is data.) -/
def karp_threeCol_weakSolvable :
    KarpReduction (fun g : GraphIn => g.2.2.Colorable) QInstance.WeakSolvable sizeG
      QInstance.size where
  prog := reduceM
  C := 2 ^ 40
  k := 4
  correct := fun ⟨_, _, G⟩ => by
    simp only [reduceM, G.val_instanceM]
    exact (G.weakSolvable_instOf _ (G.bijective_sigmaX _)).symm
  cost_le := cost_reduceM_le
  size_le := size_reduceM_le

/-- **3-colourability Karp-reduces to neoclassical solvability in dimension `3`**, by the same
program. -/
def karp_threeCol_neoSolvable :
    KarpReduction (fun g : GraphIn => g.2.2.Colorable) QInstance.NeoSolvable sizeG
      QInstance.size where
  prog := reduceM
  C := 2 ^ 40
  k := 4
  correct := fun ⟨_, _, G⟩ => by
    simp only [reduceM, G.val_instanceM]
    exact (G.neoSolvable_instOf _ (G.bijective_sigmaX _)).symm
  cost_le := cost_reduceM_le
  size_le := size_reduceM_le

end NeoTiling.Hardness
