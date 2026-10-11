import Complexity

/-!
# Subdividing edges

`PathVert n c`: the graph with edges `{eu k, ev k}` in which edge `k` is replaced by a path
through `c k` new vertices. Along edge `k` the nodes are `pathNode c k 0 = eu k`, the new
vertices `pathNode c k j` for `1 ≤ j ≤ c k`, and `pathNode c k (c k + 1) = ev k`. The edge
`⟨k, j⟩ : PathEdge c` joins nodes `j` and `j + 1`.

Main result (Poljak 1974): subdividing every edge `k` by an even number `2 L k` of vertices
raises the independence number by `∑ₖ L k` (`exists_indep_subdivision_iff`).
-/

namespace NeoTiling.Complexity

open Finset

/-- `I` is independent for the edges `{eu k, ev k}`, on arbitrary vertex and edge types. -/
def IndepOn {V E : Type*} (eu ev : E → V) (I : Finset V) : Prop :=
  ∀ k, ¬ (eu k ∈ I ∧ ev k ∈ I)

/-- Vertices: the old ones and `c k` new ones on edge `k`. -/
abbrev PathVert (n : ℕ) {m : ℕ} (c : Fin m → ℕ) : Type := Fin n ⊕ (Σ k : Fin m, Fin (c k))

/-- Edges: `c k + 1` on the path of edge `k`. -/
abbrev PathEdge {m : ℕ} (c : Fin m → ℕ) : Type := Σ k : Fin m, Fin (c k + 1)

variable {n m : ℕ} (eu ev : Fin m → Fin n)

/-- Node `j` (`0 ≤ j ≤ c k + 1`) on the path of edge `k`. -/
def pathNode (c : Fin m → ℕ) (k : Fin m) (j : ℕ) : PathVert n c :=
  if h0 : j = 0 then .inl (eu k)
  else if h : j ≤ c k then .inr ⟨k, ⟨j - 1, by omega⟩⟩
  else .inl (ev k)

/-- First endpoint of an edge of the subdivision. -/
def pathU (c : Fin m → ℕ) (e : PathEdge c) : PathVert n c := pathNode eu ev c e.1 e.2

/-- Second endpoint of an edge of the subdivision. -/
def pathV (c : Fin m → ℕ) (e : PathEdge c) : PathVert n c := pathNode eu ev c e.1 (e.2 + 1)

/-- On a path, an independent set among `2L` consecutive nodes has at most `L` of them:
the nodes split into `L` pairs `{2i, 2i+1}` and each pair contains at most one. -/
theorem card_path_le (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : ∀ j, j + 1 < 2 * L → ¬ (p j ∧ p (j + 1))) :
    ((range (2 * L)).filter p).card ≤ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have h := ih fun j hj => hp j (by omega)
    have := hp (2 * L) (by omega)
    rw [show 2 * (L + 1) = 2 * L + 1 + 1 by ring, card_filter, sum_range_succ, sum_range_succ]
    rw [card_filter] at h
    split_ifs <;> simp_all; omega

/-- **Even subdivision (Poljak).** With `2 L k` new vertices on edge `k`,
`α(G'') = α(G) + ∑ₖ L k`.
(→) On the path of edge `k` take every second new vertex, starting next to an endpoint outside
`I`. (←) On each path at most `L k` new vertices are chosen, and at most `L k - 1` if both
endpoints are chosen. Drop one endpoint of every such edge. -/
theorem exists_indep_subdivision_iff (L : Fin m → ℕ) (k : ℕ) :
    (∃ I : Finset (Fin n), Indep eu ev I ∧ k ≤ I.card) ↔
      ∃ J : Finset (PathVert n fun e => 2 * L e),
        IndepOn (pathU eu ev fun e => 2 * L e) (pathV eu ev fun e => 2 * L e) J ∧
        k + ∑ e, L e ≤ J.card := by
  classical
  -- A set of vertices is its old part plus its new part on each path.
  have card_split (J : Finset (PathVert n fun e => 2 * L e)) : J.card =
      (univ.filter fun v => (.inl v : PathVert n _) ∈ J).card +
        ∑ e, (univ.filter fun i : Fin (2 * L e) => (.inr ⟨e, i⟩ : PathVert n _) ∈ J).card := by
    have : J.card = ∑ x, if x ∈ J then 1 else 0 := by rw [sum_boole]; simp
    rw [this, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [card_filter]
  -- Exactly `L` of the numbers `0, …, 2L - 1` have a given parity.
  have parity (e : Fin m) (r : ℕ) (hr : r < 2) :
      (univ.filter fun i : Fin (2 * L e) => (i : ℕ) % 2 = r).card = L e := by
    have := Nat.count_modEq_card (b := 2 * L e) (r := 2) (by norm_num) r
    rw [Nat.count_eq_card_filter_range] at this
    rw [card_filter, Fin.sum_univ_eq_sum_range (fun i => if i % 2 = r then 1 else 0), ← card_filter]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt hr, Nat.mul_mod_right] at this
    rw [this]; split_ifs <;> simp_all
  constructor
  · -- (→) every second new vertex, starting next to an endpoint outside `I`
    rintro ⟨I, hI, hk⟩
    let J : Finset (PathVert n fun e => 2 * L e) := univ.filter fun x =>
      match x with
      | .inl v => v ∈ I
      | .inr ⟨e, i⟩ => (i : ℕ) % 2 = if eu e ∈ I then 1 else 0
    have hJ : J.card = I.card + ∑ e, L e := by
      rw [card_split]
      congr 1
      · simp [J]
      · refine sum_congr rfl fun e _ => ?_
        simpa [J] using parity e _ (by split_ifs <;> omega)
    have hl : ∀ v, (.inl v : PathVert n _) ∈ J ↔ v ∈ I := by simp [J]
    have hr : ∀ e i, (.inr ⟨e, i⟩ : PathVert n _) ∈ J ↔
        (i : ℕ) % 2 = if eu e ∈ I then 1 else 0 := by simp [J]
    refine ⟨J, ?_, by omega⟩
    clear_value J; clear card_split parity hJ hk
    rintro ⟨e, j, hj⟩
    have := hI e
    simp only [pathU, pathV, pathNode]
    split_ifs <;> simp only [hl, hr] <;> (try split_ifs) <;> simp_all <;> omega
  · -- (←)
    rintro ⟨J, hJ, hk⟩
    -- edges with both ends in `J`, and the old part of `J`
    let B := univ.filter fun e =>
      (.inl (eu e) : PathVert n _) ∈ J ∧ (.inl (ev e) : PathVert n _) ∈ J
    let Jl := univ.filter fun v : Fin n => (.inl v : PathVert n _) ∈ J
    -- on each path: at most `L e` new vertices, at most `L e - 1` if both ends are in `J`
    have path (e) : (univ.filter fun i : Fin (2 * L e) => (.inr ⟨e, i⟩ : PathVert n _) ∈ J).card
        + (if e ∈ B then 1 else 0) ≤ L e := by
      obtain ⟨p, hpJ⟩ : ∃ p : ℕ → Prop, ∀ j, p j ↔ pathNode eu ev (fun e => 2 * L e) e j ∈ J :=
        ⟨_, fun _ => Iff.rfl⟩
      have hp : ∀ j, j ≤ 2 * L e → ¬ (p j ∧ p (j + 1)) := fun j hj => by
        simpa [hpJ] using hJ ⟨e, ⟨j, by show j < 2 * L e + 1; omega⟩⟩
      have hnew : (univ.filter fun i : Fin (2 * L e) => (.inr ⟨e, i⟩ : PathVert n _) ∈ J).card
          = ∑ j ∈ range (2 * L e), if p (j + 1) then 1 else 0 := by
        rw [card_filter, ← Fin.sum_univ_eq_sum_range (fun j => if p (j + 1) then 1 else 0)]
        refine sum_congr rfl fun i _ => ?_
        simp [hpJ, show pathNode eu ev (fun e => 2 * L e) e (i + 1) = .inr ⟨e, i⟩ by
          simp [pathNode]]
      -- new nodes `1, …, 2L`, and all nodes `0, …, 2L + 1`
      have h1 := card_path_le (fun j => p (j + 1)) (L e) fun j hj => hp (j + 1) (by omega)
      have h2 := card_path_le p (L e + 1) fun j hj => hp j (by omega)
      have hB : e ∈ B ↔ p 0 ∧ p (2 * L e + 1) := by simp [B, hpJ, pathNode]
      rw [card_filter] at h1 h2
      rw [show 2 * (L e + 1) = 2 * L e + 1 + 1 by ring, sum_range_succ, sum_range_succ'] at h2
      rw [hnew]
      -- the pairs `(0, 1), …, (2L, 2L + 1)`: the ends take two places if both are in `J`
      by_cases hb : p 0 ∧ p (2 * L e + 1)
      · rw [if_pos hb.1, if_pos hb.2] at h2
        rw [if_pos (hB.2 hb)]; omega
      · rw [if_neg (mt hB.1 hb)]; omega
    -- drop `eu e` for every edge `e ∈ B`
    refine ⟨Jl \ B.image eu, ?_, ?_⟩
    · rintro e ⟨h1, h2⟩
      simp only [mem_sdiff, mem_image, Jl, mem_filter, mem_univ, true_and] at h1 h2
      exact h1.2 ⟨e, by simpa [B] using ⟨h1.1, h2.1⟩, rfl⟩
    · have h1 := le_card_sdiff (B.image eu) Jl
      have h2 : (B.image eu).card ≤ B.card := card_image_le
      have h3 := sum_le_sum fun e (_ : e ∈ univ) => path e
      rw [sum_add_distrib, sum_boole] at h3
      have h4 : J.card = Jl.card + _ := card_split J
      simp only [Nat.cast_id, filter_mem_eq_inter, univ_inter] at h3
      omega

end NeoTiling.Complexity
