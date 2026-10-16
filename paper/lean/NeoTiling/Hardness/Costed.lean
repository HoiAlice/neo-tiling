import NeoTiling.Hardness.Size
import NeoTiling.Core.Costed

/-!
# Counted cost: a cost monad and the reduction as a program

* `Costed`: a value together with the number of operations spent on it; `pure` is free and
  `bind` adds the costs.
* Primitives `qadd`, …, `neq`: one arithmetic operation or comparison, one tick each.
* `priceM`, `outputM`: the programs that compute one price and one output, written with the
  primitives only; `val_priceM`, `val_outputM`: they compute `priceQ`, `outputQ`;
  `cost_priceM_le`, `cost_outputM_le`: at most `120` and `6` operations.
* `allX`: an explicit list of all `Option (G.Node ⊕ G.Link)`, without repetitions;
  `enumM`: its enumeration, one tick per element.
* `val_mapM`, `cost_mapM`: `List.mapM` in `Costed` maps the values and sums the costs.
-/

namespace NeoTiling.NPHardness


open Costed

/-! ### Primitives

Unit-cost model: one arithmetic operation or comparison on a number counts 1. All numbers in the
construction have bit length O(log(n+m)) (Size.lean), so this is polynomially equivalent to bit
cost. The programs below use numbers only through these primitives, so their cost is counted,
not declared.

Free: numerals, the coercions `Fin n → ℕ → ℤ → ℚ`, Boolean connectives on the results of
comparisons, and building tuples and vectors. -/


def qadd (a b : ℚ) : Costed ℚ := tick (a + b)
def qsub (a b : ℚ) : Costed ℚ := tick (a - b)
def qmul (a b : ℚ) : Costed ℚ := tick (a * b)
def qdiv (a b : ℚ) : Costed ℚ := tick (a / b)
def zadd (a b : ℤ) : Costed ℤ := tick (a + b)
def zsub (a b : ℤ) : Costed ℤ := tick (a - b)
def zmul (a b : ℤ) : Costed ℤ := tick (a * b)
def nadd (a b : ℕ) : Costed ℕ := tick (a + b)
def nsub (a b : ℕ) : Costed ℕ := tick (a - b)
def nmul (a b : ℕ) : Costed ℕ := tick (a * b)
def nmod (a b : ℕ) : Costed ℕ := tick (a % b)
def nlt (a b : ℕ) : Costed Bool := tick (decide (a < b))
def neq (a b : ℕ) : Costed Bool := tick (decide (a = b))

attribute [simp] qadd qsub qmul qdiv zadd zsub zmul nadd nsub nmul nmod nlt neq

/-! ### The programs -/

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-- `x0`: one comparison. -/
def x0M (i : Fin 3) : Costed ℤ := do
  let b ← neq i 1
  pure (if b then 3 else 1)

/-- `colX`: six operations. -/
def colXM (k : Fin m) (i : Fin 3) : Costed ℤ := do
  let a ← zmul 24 (k : ℕ)
  let b ← zmul 8 (i : ℕ)
  let c ← zadd a b
  let d ← zadd c 8
  let e ← neq i 1
  zadd d (if e then 2 else 0)

/-- `lo`: one comparison. -/
def loM (k : Fin m) : Costed (Fin n) := do
  let b ← nlt (G.ev k) (G.eu k)
  pure (if b then G.ev k else G.eu k)

/-- `pos`: at most `13` operations. -/
def posM : G.Node → Costed (ℤ × ℤ)
  | .inl (v, i, j) => do
      let x ← x0M i
      let a ← zmul 2 (j : ℕ)
      let px ← zadd x a
      let b ← zmul 8 (v : ℕ)
      let c ← zmul 2 (i : ℕ)
      let py ← zadd b c
      pure (px, py)
  | .inr ⟨k, i, j⟩ => do
      let px ← colXM k i
      let l ← G.loM k
      let b ← zmul 8 (l : ℕ)
      let c ← zmul 2 (i : ℕ)
      let d ← zadd b c
      let e ← zadd d 1
      let f ← zmul 2 (j : ℕ)
      let py ← zadd e f
      pure (px, py)

/-- `scaleQ n m`: six operations. -/
def scaleM (n m : ℕ) : Costed ℚ := do
  let a ← qmul 24 m
  let b ← qmul 8 n
  let c ← qadd a b
  let d ← qadd c 8
  let e ← qmul 16 d
  qdiv 1 e

/-- `aQ`, as a pair: at most `21` operations. -/
def aM (w : G.Node) : Costed (ℚ × ℚ) := do
  let p ← G.posM w
  let s ← scaleM n m
  let a0 ← qmul s p.1
  let a1 ← qmul s p.2
  pure (a0, a1)

/-- `sqnQ ![a0, a1]`: three operations. -/
def sqnM (a0 a1 : ℚ) : Costed ℚ := do
  let x ← qmul a0 a0
  let y ← qmul a1 a1
  qadd x y

/-- `liftQ ![a0, a1]`: eight operations. -/
def liftQM (a0 a1 : ℚ) : Costed (Fin 3 → ℚ) := do
  let s ← sqnM a0 a1
  let c ← qadd 1 s
  let x ← qadd a0 c
  let y ← qadd a1 c
  let u ← qadd a0 a1
  let z ← qsub c u
  pure ![x, y, z]

/-- The ends of the link `k`, charged `5` operations each: the index arithmetic in `linkU`,
`linkV` is at most `lo k`, `hi k` (one comparison each) and `colLen k - 1` (three more), or
`jA k i = 12k + 4i + 4` (four), or `j + 1`, or `t + 1` in `Fin 3` (two). -/
def endsM (k : G.Link) : Costed (G.Node × G.Node) := do
  let u ← tickN 5 (G.linkU k)
  let v ← tickN 5 (G.linkV k)
  pure (u, v)

/-- `etaQ`: at most `52` operations. -/
def etaM (k : G.Link) : Costed ℚ := do
  let e ← G.endsM k
  let pu ← G.posM e.1
  let pv ← G.posM e.2
  let d1 ← zsub pv.1 pu.1
  let d2 ← zsub pv.2 pu.2
  let a ← zmul d1 d1
  let b ← zmul d2 d2
  let N ← zadd a b
  let s ← scaleM n m
  let s2 ← qmul s s
  let q ← qdiv N 4
  let r ← qdiv 1 512
  let t ← qadd q r
  qmul s2 t

/-- `priceQ`: at most `120` operations. -/
def priceM : Option (G.Node ⊕ G.Link) → Costed (Fin 3 → ℚ)
  | none => do
      let q ← qdiv 1 4
      pure fun _ => q
  | some (.inl v) => do
      let a ← G.aM v
      liftQM a.1 a.2
  | some (.inr k) => do
      let e ← G.endsM k
      let au ← G.aM e.1
      let av ← G.aM e.2
      let s0 ← qadd au.1 av.1
      let m0 ← qdiv s0 2
      let s1 ← qadd au.2 av.2
      let m1 ← qdiv s1 2
      let L ← liftQM m0 m1
      let h ← G.etaM k
      let p0 ← qadd (L 0) h
      let p1 ← qadd (L 1) h
      let p2 ← qadd (L 2) h
      pure ![p0, p1, p2]

/-- `svalQ`: at most `5` operations. -/
def svalM : G.Node → Costed ℚ
  | .inl (_, _, j) => do
      let r ← nmod j 2
      let b ← neq r 0
      if b then qdiv 1 3 else qdiv 2 3
  | .inr ⟨_, _, j⟩ => do
      let b1 ← neq j 1
      let r ← nmod j 2
      let b2 ← neq r 0
      let b3 ← neq j 0
      if b1 || (b2 && !b3) then qdiv 1 3 else qdiv 2 3

/-- `outputQ`: at most `6` operations. -/
def outputM : Option (G.Node ⊕ G.Link) → Costed ℚ
  | none => pure 1
  | some (.inl v) => do
      let s ← G.svalM v
      qsub 1 s
  | some (.inr _) => pure 1

/-! ### Enumeration -/

/-- The elements of `α ⊕ β` from lists of `α` and of `β`. -/
def sumList {α β : Type u} (l₁ : List α) (l₂ : List β) : List (α ⊕ β) :=
  l₁.map .inl ++ l₂.map .inr

/-- All nodes: rows `(v, i, j)`, then columns `⟨k, i, j⟩`. -/
def allNodes : List G.Node :=
  sumList (List.finRange n ×ˢ (List.finRange 3 ×ˢ List.finRange (12 * m + 1)))
    ((List.finRange m).sigma fun k => List.finRange 3 ×ˢ List.finRange (G.colLen k))

/-- All links: row edges, column edges, attachments, triangle edges. -/
def allLinks : List G.Link :=
  sumList (List.finRange n ×ˢ (List.finRange 3 ×ˢ List.finRange (12 * m)))
    (sumList ((List.finRange m).sigma fun k => List.finRange 3 ×ˢ List.finRange (G.colLen k - 1))
      (sumList (List.finRange m ×ˢ (List.finRange 3 ×ˢ [false, true]))
        (List.finRange n ×ˢ List.finRange 3)))

/-- All indices of prices: the marker `none`, then the nodes and the links. -/
def allX : List (Option (G.Node ⊕ G.Link)) :=
  none :: (sumList G.allNodes G.allLinks).map some

/-- The enumeration, one operation per element. -/
def enumM : Costed (List (Option (G.Node ⊕ G.Link))) := ⟨G.allX, G.allX.length⟩

lemma nodup_sumList {α β : Type u} {l₁ : List α} {l₂ : List β} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) : (sumList l₁ l₂).Nodup := by
  simp only [sumList, List.nodup_append]
  exact ⟨h₁.map Sum.inl_injective, h₂.map Sum.inr_injective, by simp⟩

lemma nodup_allX : G.allX.Nodup := by
  have f := List.nodup_finRange
  have hB : [false, true].Nodup := by decide
  refine List.nodup_cons.2 ⟨by simp, List.Nodup.map (Option.some_injective _) ?_⟩
  refine nodup_sumList (nodup_sumList ((f _).product ((f _).product (f _)))
    ((f _).sigma fun _ => (f _).product (f _))) (nodup_sumList ((f _).product ((f _).product (f _)))
    (nodup_sumList ((f _).sigma fun _ => (f _).product (f _))
      (nodup_sumList ((f _).product ((f _).product hB)) ((f _).product (f _)))))

lemma mem_allX (x : Option (G.Node ⊕ G.Link)) : x ∈ G.allX := by
  have l {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} (h : a ∈ l₁) :
      Sum.inl a ∈ sumList l₁ l₂ := List.mem_append_left _ (List.mem_map_of_mem h)
  have r {α β : Type} {l₁ : List α} {l₂ : List β} {b : β} (h : b ∈ l₂) :
      Sum.inr b ∈ sumList l₁ l₂ := List.mem_append_right _ (List.mem_map_of_mem h)
  have f {k : ℕ} (a : Fin k) : a ∈ List.finRange k := List.mem_finRange a
  have p {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β} (ha : a ∈ l₁) (hb : b ∈ l₂) :
      (a, b) ∈ l₁ ×ˢ l₂ := List.mem_product.2 ⟨ha, hb⟩
  have s {k : Fin m} {β : Fin m → Type} {l₂ : ∀ k, List (β k)} {b : β k} (hb : b ∈ l₂ k) :
      (⟨k, b⟩ : Σ k, β k) ∈ (List.finRange m).sigma l₂ := List.mem_sigma.2 ⟨f _, hb⟩
  rcases x with _ | (⟨v, i, j⟩ | ⟨k, i, j⟩) | (⟨v, i, j⟩ | ⟨k, i, j⟩ | ⟨k, i, b⟩ | ⟨v, t⟩)
  · exact List.mem_cons_self
  all_goals refine List.mem_cons_of_mem _ (List.mem_map_of_mem ?_)
  · exact l (l (p (f _) (p (f _) (f _))))
  · exact l (r (s (p (f _) (f _))))
  · exact r (l (p (f _) (p (f _) (f _))))
  · exact r (r (l (s (p (f _) (f _)))))
  · exact r (r (r (l (p (f _) (p (f _) (by cases b <;> simp))))))
  · exact r (r (r (r (p (f _) (f _)))))

lemma length_allX : G.allX.length = G.numPrices := by
  classical
  rw [numPrices, ← Finset.card_univ, ← List.toFinset_card_of_nodup G.nodup_allX]
  congr 1; ext x; simp [G.mem_allX]

/-! ### The programs compute the instance -/

lemma val_posM (w : G.Node) : (G.posM w).val = G.pos w := by
  rcases w with ⟨v, i, j⟩ | ⟨k, i, j⟩
  · simp [posM, x0M, pos, x0, Fin.ext_iff]
  · have : (if G.ev k < G.eu k then G.ev k else G.eu k) = G.lo k := by
      simp only [lo]; split_ifs with h
      · exact (min_eq_right h.le).symm
      · exact (min_eq_left (not_lt.1 h)).symm
    simp [posM, colXM, loM, pos, colX, Fin.ext_iff, this]

lemma val_aM (w : G.Node) : (G.aM w).val = (G.aQ w 0, G.aQ w 1) := by
  simp [aM, val_posM, scaleM, aQ, scaleQ]

lemma val_liftQM (a0 a1 : ℚ) : (liftQM a0 a1).val = liftQ ![a0, a1] := by
  funext i; fin_cases i <;> simp [liftQM, sqnM, liftQ, sqnQ, sq]; ring

lemma liftQ_vec (a : Fin 2 → ℚ) : liftQ ![a 0, a 1] = liftQ a := by
  congr 1; funext j; fin_cases j <;> rfl

lemma val_etaM(k : G.Link) : (G.etaM k).val = G.etaQ k := by
  simp [etaM, endsM, val_posM, scaleM, etaQ, scaleQ, nrm, sq]

theorem val_priceM (x : Option (G.Node ⊕ G.Link)) : (G.priceM x).val = G.priceQ x := by
  rcases x with _ | v | k
  · rfl
  · simp only [priceM, val_bind, val_aM, val_liftQM, priceQ, liftQ_vec]
  · simp only [priceM, val_bind, val_aM, val_liftQM, val_etaM, endsM, priceQ]
    rw [← liftQ_vec (fun j => (G.aQ (G.linkU k) j + G.aQ (G.linkV k) j) / 2)]
    funext i; fin_cases i <;> rfl

theorem val_outputM (x : Option (G.Node ⊕ G.Link)) : (G.outputM x).val = G.outputQ x := by
  rcases x with _ | (⟨_, _, j⟩ | ⟨_, _, j⟩) | k
  · rfl
  all_goals simp only [outputM, svalM, outputQ, svalQ, val_bind, apply_ite Costed.val]
  all_goals simp

/-! ### Costs -/

lemma cost_posM_le (w : G.Node) : (G.posM w).cost ≤ 13 := by
  rcases w with ⟨v, i, j⟩ | ⟨k, i, j⟩ <;> simp [posM, x0M, colXM, loM]

lemma cost_aM_le (w : G.Node) : (G.aM w).cost ≤ 21 := by
  have := G.cost_posM_le w
  simp [aM, scaleM]; omega

theorem cost_priceM_le (x : Option (G.Node ⊕ G.Link)) : (G.priceM x).cost ≤ 120 := by
  rcases x with _ | v | k
  · simp [priceM]
  · have := G.cost_aM_le v
    simp [priceM, liftQM, sqnM]; omega
  · have := G.cost_aM_le (G.linkU k)
    have := G.cost_aM_le (G.linkV k)
    have := G.cost_posM_le (G.linkU k)
    have := G.cost_posM_le (G.linkV k)
    simp [priceM, liftQM, sqnM, etaM, endsM, scaleM]; omega

theorem cost_outputM_le (x : Option (G.Node ⊕ G.Link)) : (G.outputM x).cost ≤ 6 := by
  rcases x with _ | ⟨_, _, j⟩ | ⟨_, _, j⟩ | k <;> simp [outputM, svalM] <;> split <;> simp

end Graph

end NeoTiling.NPHardness
