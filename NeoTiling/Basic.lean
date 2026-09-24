import Mathlib

example (a b : ℕ) : a + b = b + a := Nat.add_comm a b
#check Nat.add_comm
