import Mathlib

/-!
# A cost monad

`Costed α`: a value together with a count of operations; `pure` is free and `bind` adds the
counts. `tick` spends one unit, `tickN c` spends `c`. `val_mapM`, `cost_mapM`: `List.mapM` maps the
values and sums the costs. What a unit means is fixed by the user of the monad: one arithmetic
operation in `Hardness.Costed`, one oracle call in `Perturbation.Search`.
-/

namespace NeoTiling

universe u

/-- A value together with the number of operations spent to compute it. -/
@[ext]
structure Costed (α : Type u) where
  val : α
  cost : ℕ

namespace Costed

instance : Monad Costed where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

variable {α β : Type u}

@[simp] lemma val_pure (a : α) : (pure a : Costed α).val = a := rfl
@[simp] lemma cost_pure (a : α) : (pure a : Costed α).cost = 0 := rfl
@[simp] lemma val_bind (x : Costed α) (f : α → Costed β) : (x >>= f).val = (f x.val).val := rfl
@[simp] lemma cost_bind (x : Costed α) (f : α → Costed β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl
@[simp] lemma val_map (f : α → β) (x : Costed α) : (f <$> x).val = f x.val := rfl
@[simp] lemma cost_map (f : α → β) (x : Costed α) : (f <$> x).cost = x.cost := rfl

instance : LawfulMonad Costed := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => Costed.ext rfl (Nat.zero_add _))
  (bind_assoc := fun _ _ _ => Costed.ext rfl (Nat.add_assoc _ _ _))

/-- `List.mapM` maps the values. -/
@[simp] lemma val_mapM (f : α → Costed β) (l : List α) :
    (l.mapM f).val = l.map fun a => (f a).val := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- `List.mapM` sums the costs. -/
@[simp] lemma cost_mapM (f : α → Costed β) (l : List α) :
    (l.mapM f).cost = (l.map fun a => (f a).cost).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

end Costed

open Costed

/-- One operation. -/
def tick {α : Type u} (a : α) : Costed α := ⟨a, 1⟩

/-- `c` operations, used only for index plumbing (`linkU`, `linkV`, see `etaM`). -/
def tickN {α : Type u} (c : ℕ) (a : α) : Costed α := ⟨a, c⟩

attribute [simp] tick tickN

end NeoTiling
