import NeoTiling.Hardness.Size

/-!
# The reduction is polynomial: cost model and Karp reduction

Status: everything in `Instance.lean`, `Size.lean`, `Cost.lean` is proved, no `sorry`, axioms
`propext`, `Classical.choice`, `Quot.sound` only.

* `costPrice`, `costOutput`, `cost`: the number of arithmetic operations that compute the
  instance, in the unit-cost model below; `cost_le`: `cost ≤ 8400 (n + 1) (m + 1)`.
* `KarpReduction`, `QInstance`, `QInstance.size`: a Karp reduction in the unit-cost model and
  rational instances of weak solvability in dimension `3` with their bit size.
* `size_reduce_le`: the bit size of the instance is `≤ 2^40 (n + m + 1)^4`, by `Size.lean`.
* `karp_threeCol_weakSolvable`: 3-colourability Karp-reduces to weak solvability in
  dimension `3`.
-/

namespace NeoTiling.NPHardness

open Finset

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-! ### The cost model -/

/-- Unit-cost model: one arithmetic operation (+, -, *, /, comparison) on a rational number
counts 1; all numbers in the construction have bit length O(log(n+m)) (Size.lean), so this is
polynomially equivalent to bit cost.

The cost of one price, case by case.
* Marker: the constant `1/4`, one division.
* Reward `v`: `pos v` (`x0 i + 2j` with the test `i = 1`, `8v + 2i`: 6), `scaleQ` (6), `aQ`
  (2), `sqnQ` (3), `liftQ` (`1 + sqnQ`, `a₀ + c`, `a₁ + c`, `-a₀ - a₁ + c`: 6). Total `23`.
* Heavy point of the link `k`: its ends `linkU k`, `linkV k` and their positions (at most `14`
  each, `28`), `scaleQ` (6), two `aQ` (4), the midpoint (4), `sqnQ` (3), `liftQ` (6), `ηQ`
  (`nrm`: 5, `/4`, `1/512`, `+`, `scaleQ²`, `*`: 10), adding `ηQ` to three entries (3).
  Total `64`. -/
def costPrice : Option (G.Node ⊕ G.Link) → ℕ
  | none => 1
  | some (.inl _) => 23
  | some (.inr _) => 64

/-- The cost of one output: `1` at the marker and the heavy points (no operation); at a reward
`svalQ` (at most four comparisons, one division) and `1 - ·`: `7`. -/
def costOutput : Option (G.Node ⊕ G.Link) → ℕ
  | none => 0
  | some (.inl _) => 7
  | some (.inr _) => 0

/-- The cost of the whole instance; the last term pays for the enumeration `indexQ`. -/
def cost : ℕ := ∑ x : Option (G.Node ⊕ G.Link), (G.costPrice x + G.costOutput x) + G.numPricesQ

lemma cost_term_le (x : Option (G.Node ⊕ G.Link)) : G.costPrice x + G.costOutput x ≤ 83 := by
  rcases x with _ | v | k <;> simp [costPrice, costOutput]

/-- **The cost is polynomial**: at most `84` operations per price. -/
theorem cost_le : G.cost ≤ 8400 * (n + 1) * (m + 1) := by
  have h1 := sum_le_card_nsmul univ (fun x : Option (G.Node ⊕ G.Link) =>
    G.costPrice x + G.costOutput x) 83 fun x _ => G.cost_term_le x
  rw [card_univ, smul_eq_mul, ← numPrices, ← G.numPricesQ_eq] at h1
  have h2 := G.numPricesQ_le
  unfold cost
  generalize G.numPricesQ = N at h1 h2 ⊢
  generalize (∑ x : Option (G.Node ⊕ G.Link), (G.costPrice x + G.costOutput x)) = S at h1 ⊢
  nlinarith

end Graph

/-- `(n + 1) (m + 1) ≤ (n + m + 1)^4`. -/
lemma mul_succ_le_pow (n m : ℕ) : (n + 1) * (m + 1) ≤ (n + m + 1) ^ 4 :=
  calc (n + 1) * (m + 1) ≤ (n + m + 1) * (n + m + 1) := Nat.mul_le_mul (by omega) (by omega)
    _ = (n + m + 1) ^ 2 := by ring
    _ ≤ (n + m + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)

namespace Graph

variable {n m : ℕ} (G : Graph n m)

theorem cost_le_pow : G.cost ≤ 2 ^ 40 * (n + m + 1) ^ 4 :=
  calc G.cost ≤ 8400 * ((n + 1) * (m + 1)) := by rw [← mul_assoc]; exact G.cost_le
    _ ≤ 2 ^ 40 * (n + m + 1) ^ 4 := Nat.mul_le_mul (by norm_num) (mul_succ_le_pow n m)

end Graph

/-! ### Karp reductions -/

/-- A Karp reduction in the unit-cost model: a map `f` with an explicit cost, correct, with cost
and output size bounded by `C * (size + 1)^k`. -/
structure KarpReduction {α β : Type*} (A : α → Prop) (B : β → Prop) (sizeA : α → ℕ)
    (sizeB : β → ℕ) where
  f : α → β
  cost : α → ℕ
  C : ℕ
  k : ℕ
  correct : ∀ x, A x ↔ B (f x)
  cost_le : ∀ x, cost x ≤ C * (sizeA x + 1) ^ k
  size_le : ∀ x, sizeB (f x) ≤ C * (sizeA x + 1) ^ k

/-- A rational instance of (weak) solvability in dimension `3`: `T` prices and outputs. -/
structure QInstance where
  T : ℕ
  P : Fin T → Fin 3 → ℚ
  y : Fin T → ℚ

/-- Weak solvability of a rational instance. -/
def QInstance.WeakSolvable (I : QInstance) : Prop :=
  NeoTiling.WeakSolvable (fun t i => ((I.P t i : ℚ) : ℝ)) (fun t => ((I.y t : ℚ) : ℝ))

/-- The bit size of a rational instance. -/
def QInstance.size (I : QInstance) : ℕ :=
  I.T + ∑ t, ∑ i, (Nat.log 2 (I.P t i).num.natAbs + Nat.log 2 (I.P t i).den) +
    ∑ t, (Nat.log 2 (I.y t).num.natAbs + Nat.log 2 (I.y t).den)

/-- Graphs of any size. -/
def GraphIn : Type := Σ n m : ℕ, Graph n m

/-- The size of a graph: vertices plus edges. -/
def sizeG : GraphIn → ℕ
  | ⟨n, m, _⟩ => n + m

/-- The reduction: the computable rational instance of `Instance.lean`. -/
def reduce : GraphIn → QInstance
  | ⟨_, _, G⟩ => ⟨G.numPricesQ, G.pricesQ, G.outputsQ⟩

/-- The cost of the reduction. -/
def reduceCost : GraphIn → ℕ
  | ⟨_, _, G⟩ => G.cost

/-- **Output size.** Every price entry has `den ≤ 2^17 B²`, `|num| ≤ 2^18 B²` with
`B = 24m + 8n + 8`, every output `den, |num| ≤ 3`, and there are `≤ 100 (n + 1) (m + 1)` prices;
`Nat.log 2 x ≤ x` crudely. -/
theorem size_reduce_le {n m : ℕ} (G : Graph n m) :
    (reduce ⟨n, m, G⟩).size ≤ 2 ^ 40 * (n + m + 1) ^ 4 := by
  have hlog : ∀ x : ℕ, Nat.log 2 x ≤ x := fun x => Nat.log_le_self 2 x
  simp only [reduce, QInstance.size]
  have hp : ∀ t i, Nat.log 2 (G.pricesQ t i).num.natAbs + Nat.log 2 (G.pricesQ t i).den
      ≤ 2 ^ 19 * Graph.bnd n m ^ 2 := fun t i => by
    have := hlog (G.pricesQ t i).num.natAbs
    have := hlog (G.pricesQ t i).den
    have := G.pricesQ_den_le t i
    have := G.pricesQ_num_le t i
    omega
  have ho : ∀ t, Nat.log 2 (G.outputsQ t).num.natAbs + Nat.log 2 (G.outputsQ t).den ≤ 6 :=
    fun t => by
    have := hlog (G.outputsQ t).num.natAbs
    have := hlog (G.outputsQ t).den
    have := G.outputsQ_den_le t
    have := G.outputsQ_num_le t
    omega
  have h1 : ∀ t, ∑ i : Fin 3, (Nat.log 2 (G.pricesQ t i).num.natAbs +
      Nat.log 2 (G.pricesQ t i).den) ≤ 3 * (2 ^ 19 * Graph.bnd n m ^ 2) := fun t => by
    have := sum_le_card_nsmul univ _ _ fun i _ => hp t i
    simpa using this
  have h2 := sum_le_card_nsmul univ _ _ fun t _ => h1 t
  have h3 := sum_le_card_nsmul univ _ _ fun t (_ : t ∈ univ) => ho t
  simp only [card_univ, Fintype.card_fin, smul_eq_mul] at h2 h3
  have hT := G.numPricesQ_le
  have hBle : Graph.bnd n m ≤ 24 * (n + m + 1) := by unfold Graph.bnd; omega
  have hB2 : Graph.bnd n m ^ 2 ≤ 576 * (n + m + 1) ^ 2 := by nlinarith
  clear hp ho h1
  generalize (∑ t : Fin G.numPricesQ, ∑ i : Fin 3, (Nat.log 2 (G.pricesQ t i).num.natAbs +
    Nat.log 2 (G.pricesQ t i).den)) = S1 at *
  generalize (∑ t : Fin G.numPricesQ, (Nat.log 2 (G.outputsQ t).num.natAbs +
    Nat.log 2 (G.outputsQ t).den)) = S2 at *
  generalize G.numPricesQ = T at *
  generalize Graph.bnd n m ^ 2 = Q at *
  have hR : (n + m + 1) ^ 4 = (n + m + 1) ^ 2 * (n + m + 1) ^ 2 := by ring
  have hm' : (n + 1) * (m + 1) ≤ (n + m + 1) ^ 2 := by
    nlinarith [Nat.zero_le (n * m)]
  generalize (n + m + 1) ^ 2 = R at *
  generalize (n + m + 1) ^ 4 = W at *
  have h5 : T * Q ≤ 100 * R * (576 * R) :=
    Nat.mul_le_mul (by nlinarith) hB2
  nlinarith

/-- **3-colourability Karp-reduces to weak solvability in dimension `3`** in the unit-cost
model, with `C = 2^40`, `k = 4`. Correctness is `weakSolvableQ_iff_colorable`, the cost bound
`cost_le`, the size bound `size_reduce_le`. (A `def`, since a `KarpReduction` is data.) -/
def karp_threeCol_weakSolvable :
    KarpReduction (fun g : GraphIn => g.2.2.Colorable) QInstance.WeakSolvable sizeG
      QInstance.size where
  f := reduce
  cost := reduceCost
  C := 2 ^ 40
  k := 4
  correct := fun ⟨_, _, G⟩ => G.weakSolvableQ_iff_colorable.symm
  cost_le := fun ⟨_, _, G⟩ => G.cost_le_pow
  size_le := fun ⟨_, _, G⟩ => size_reduce_le G

/-- Neoclassical solvability of a rational instance. -/
def QInstance.NeoSolvable (I : QInstance) : Prop :=
  NeoTiling.NeoSolvable (fun t i => ((I.P t i : ℚ) : ℝ)) (fun t => ((I.y t : ℚ) : ℝ))

/-- The same reduction for neoclassical solvability (`neoSolvableQ_iff_colorable`). -/
def karp_threeCol_neoSolvable :
    KarpReduction (fun g : GraphIn => g.2.2.Colorable) QInstance.NeoSolvable sizeG
      QInstance.size where
  f := reduce
  cost := reduceCost
  C := 2 ^ 40
  k := 4
  correct := fun ⟨_, _, G⟩ => G.neoSolvableQ_iff_colorable.symm
  cost_le := fun ⟨_, _, G⟩ => G.cost_le_pow
  size_le := fun ⟨_, _, G⟩ => size_reduce_le G

end NeoTiling.NPHardness
