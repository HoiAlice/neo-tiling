import NeoTiling.Hardness.Disks

/-!
# The lattice drawing of `G □ K₃`

Input: a loopless graph `G` on `Fin n` with edges `{eu k, ev k}`, `k : Fin m`. Output: a graph
`H` drawn on `ℤ²` that encodes 3-colourings of `G`.

* **Rows.** For every vertex `v` and colour `i` a horizontal path, the row `(v, i)`, with nodes
  `(x₀ i + 2j, 8v + 2i)`, `j ≤ 12m`, where `x₀ 1 = 3` and `x₀ 0 = x₀ 2 = 1`. Its first nodes
  `(1, 8v)`, `(3, 8v + 2)`, `(1, 8v + 4)` are the corners of the triangle of `v`.
* **Columns.** For every edge `k` and colour `i` a vertical path, the column `(k, i)`, at
  `x = colX k i` (even) with nodes at the odd heights strictly between the rows `(lo k, i)` and
  `(hi k, i)`. Its ends are joined diagonally to the row nodes at `x = colX k i + 1`.

Rows run at even heights through odd `x`, columns at even `x` through odd heights, so every node
has `x + y` odd, and a row crosses a column at a point that is no node: the two edges through
the crossing point are perpendicular, of length `2`, with a common midpoint. No crossing needs a
special gadget.

Values `s`: `1/3` on the *copies*, `2/3` on the *anticopies*. Along a row the nodes alternate,
starting with a copy at the corner. Along the column `(k, i)` the nodes `0, 1` belong to the
lower end (anticopy, copy), the nodes `2, 3, …` to the upper end (copy, anticopy, …). Every edge
between a copy and an anticopy is tight (`1/3 + 2/3 = 1`). The only other edges are the triangles
and the junction edges `1 — 2` of the columns, which join a copy of `lo k` to a copy of `hi k`.

Main results: `pos_injective`, and `drawing`: the drawing has empty disks (`Drawing`).
-/

namespace NeoTiling.Hardness

open Finset

/-- A loopless graph on `Fin n` with edges `{eu k, ev k}`, `k : Fin m`. -/
structure Graph (n m : ℕ) where
  eu : Fin m → Fin n
  ev : Fin m → Fin n
  loopless : ∀ k, eu k ≠ ev k

namespace Graph

variable {n m : ℕ} (G : Graph n m)

/-- `G` has a proper 3-colouring. -/
def Colorable : Prop := ∃ c : Fin n → Fin 3, ∀ k, c (G.eu k) ≠ c (G.ev k)

/-- The lower end of edge `k`. -/
def lo (k : Fin m) : Fin n := min (G.eu k) (G.ev k)

/-- The upper end of edge `k`. -/
def hi (k : Fin m) : Fin n := max (G.eu k) (G.ev k)

/-- The number of nodes of a column of edge `k`. -/
def colLen (k : Fin m) : ℕ := 4 * ((G.hi k : ℕ) - G.lo k)

theorem lo_lt_hi (k : Fin m) : (G.lo k : ℕ) < G.hi k := by
  have : (G.eu k : ℕ) ≠ G.ev k := Fin.val_ne_of_ne (G.loopless k)
  simp only [lo, hi, Fin.coe_min, Fin.coe_max]
  omega

theorem colLen_pos (k : Fin m) : 0 < G.colLen k := by
  have := G.lo_lt_hi k; unfold colLen; omega

/-- Nodes of `H`: row nodes `(v, i, j)` and column nodes `⟨k, i, j⟩`. -/
abbrev Node : Type := (Fin n × Fin 3 × Fin (12 * m + 1)) ⊕ (Σ k : Fin m, Fin 3 × Fin (G.colLen k))

/-- Edges of `H`: row edges, column edges, attachments of the column ends (`false` lower,
`true` upper) and triangle edges (corner `t` to corner `t + 1`). -/
abbrev Link : Type :=
  (Fin n × Fin 3 × Fin (12 * m)) ⊕ (Σ k : Fin m, Fin 3 × Fin (G.colLen k - 1)) ⊕
    (Fin m × Fin 3 × Bool) ⊕ (Fin n × Fin 3)

/-- Row node `j` of the row `(v, i)`. -/
def row (v : Fin n) (i : Fin 3) (j : Fin (12 * m + 1)) : G.Node := .inl (v, i, j)

/-- Column node `j` of the column `(k, i)`. -/
def col (k : Fin m) (i : Fin 3) (j : Fin (G.colLen k)) : G.Node := .inr ⟨k, i, j⟩

/-- The row node where the column `(k, i)` is attached. -/
def jA (k : Fin m) (i : Fin 3) : Fin (12 * m + 1) :=
  ⟨12 * k + 4 * i + 4, by have := k.isLt; have := i.isLt; omega⟩

/-- First end of an edge of `H`. -/
def linkU : G.Link → G.Node
  | .inl (v, i, j) => G.row v i j.castSucc
  | .inr (.inl ⟨k, i, j⟩) => G.col k i ⟨j, by have := j.isLt; omega⟩
  | .inr (.inr (.inl (k, i, false))) => G.col k i ⟨0, G.colLen_pos k⟩
  | .inr (.inr (.inl (k, i, true))) => G.col k i ⟨G.colLen k - 1, by have := G.colLen_pos k; omega⟩
  | .inr (.inr (.inr (v, t))) => G.row v t 0

/-- Second end of an edge of `H`. -/
def linkV : G.Link → G.Node
  | .inl (v, i, j) => G.row v i j.succ
  | .inr (.inl ⟨k, i, j⟩) => G.col k i ⟨j + 1, by have := j.isLt; omega⟩
  | .inr (.inr (.inl (k, i, false))) => G.row (G.lo k) i (jA k i)
  | .inr (.inr (.inl (k, i, true))) => G.row (G.hi k) i (jA k i)
  | .inr (.inr (.inr (v, t))) => G.row v (t + 1) 0

/-- First `x` of a row: `3` for colour `1`, `1` otherwise. -/
def x0 (i : Fin 3) : ℤ := if i = 1 then 3 else 1

/-- The `x` of the column `(k, i)`. -/
def colX (k : Fin m) (i : Fin 3) : ℤ := 24 * (k : ℕ) + 8 * (i : ℕ) + 8 + if i = 1 then 2 else 0

/-- Positions of the nodes. -/
def pos : G.Node → ℤ × ℤ
  | .inl (v, i, j) => (x0 i + 2 * (j : ℕ), 8 * (v : ℕ) + 2 * (i : ℕ))
  | .inr ⟨k, i, j⟩ => (colX k i, 8 * (G.lo k : ℕ) + 2 * (i : ℕ) + 1 + 2 * (j : ℕ))

/-- The point `s`: `1/3` on copies, `2/3` on anticopies. -/
noncomputable def sval : G.Node → ℝ
  | .inl (_, _, j) => if (j : ℕ) % 2 = 0 then 1 / 3 else 2 / 3
  | .inr ⟨_, _, j⟩ => if (j : ℕ) = 1 ∨ ((j : ℕ) % 2 = 0 ∧ (j : ℕ) ≠ 0) then 1 / 3 else 2 / 3

/-! ### Positions -/

/-- **Parity.** Rows lie at odd `x ≥ 1` and even heights, and a row at a height `≡ 2 (mod 8)`
(colour `1`) starts at `x = 3`; columns lie at even `x ≥ 8` and odd heights. So every node has
`x + y` odd. -/
lemma pos_shape (w : G.Node) :
    ((G.pos w).1 % 2 = 1 ∧ (G.pos w).2 % 2 = 0 ∧ 1 ≤ (G.pos w).1 ∧
        ((G.pos w).2 % 8 = 2 → 3 ≤ (G.pos w).1)) ∨
      ((G.pos w).1 % 2 = 0 ∧ (G.pos w).2 % 2 = 1 ∧ 8 ≤ (G.pos w).1) := by
  rcases w with ⟨v, i, j⟩ | ⟨k, i, j⟩ <;> fin_cases i <;>
    simp [pos, x0, colX] <;> omega

/-- A row height `8v + 2i` determines the row `(v, i)`, since `2i ≤ 4 < 8`. -/
lemma row_height {v v' : Fin n} {i i' : Fin 3}
    (h : 8 * (v : ℤ) + 2 * (i : ℤ) = 8 * (v' : ℤ) + 2 * (i' : ℤ)) : v = v' ∧ i = i' := by
  have := v.isLt; have := v'.isLt; have := i.isLt; have := i'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- `colX k i` determines the column `(k, i)`: it is `24k + 8`, `24k + 18` or `24k + 24`. -/
lemma colX_inj {k k' : Fin m} {i i' : Fin 3} (h : colX k i = colX k' i') : k = k' ∧ i = i' := by
  have := k.isLt; have := k'.isLt
  fin_cases i <;> fin_cases i' <;> simp [colX] at h <;> simp <;> omega

/-- Distinct nodes have distinct positions. -/
theorem pos_injective : Function.Injective G.pos := by
  rintro (⟨v, i, j⟩ | ⟨k, i, j⟩) (⟨v', i', j'⟩ | ⟨k', i', j'⟩) h <;>
    simp only [pos, Prod.mk.injEq] at h
  · obtain ⟨hx, hy⟩ := h
    obtain ⟨rfl, rfl⟩ := row_height hy
    have : (j : ℕ) = j' := by omega
    simp [Fin.ext this]
  · have := i.isLt; have := i'.isLt; omega
  · have := i.isLt; have := i'.isLt; omega
  · obtain ⟨hx, hy⟩ := h
    obtain ⟨rfl, rfl⟩ := colX_inj hx
    have : (j : ℕ) = j' := by omega
    simp [Fin.ext this]

/-- Edges have length at most `4`. -/
theorem short (e : G.Link) : nrm (G.pos (G.linkV e) - G.pos (G.linkU e)) ≤ 16 := by
  rcases e with ⟨v, i, j⟩ | ⟨k, i, j⟩ | ⟨k, i, b⟩ | ⟨v, t⟩
  · simp [nrm, linkU, linkV, row, pos]; ring_nf; omega
  · simp [nrm, linkU, linkV, col, pos]; ring_nf; omega
  · have := G.lo_lt_hi k
    have h4 : (((G.colLen k - 1 : ℕ)) : ℤ) = 4 * ((G.hi k : ℕ) - (G.lo k : ℕ)) - 1 := by
      unfold colLen; omega
    cases b <;> fin_cases i <;> simp [nrm, linkU, linkV, col, row, pos, jA, colX, x0, h4] <;>
      ring_nf <;> omega
  · fin_cases t <;> simp [nrm, linkU, linkV, row, pos, x0]

/-! ### Disks -/

/-- Two row nodes at the same height and `2` apart are consecutive in one row: the ends of a
row edge. -/
lemma row_link_of_pos {w w' : G.Node} {X Y : ℤ} (hX : X % 2 = 1) (h : G.pos w = (X, Y))
    (h' : G.pos w' = (X + 2, Y)) : ∃ e, G.linkU e = w ∧ G.linkV e = w' := by
  have s := G.pos_shape w
  have s' := G.pos_shape w'
  rw [h] at s
  rw [h'] at s'
  rcases w with ⟨v, i, j⟩ | ⟨k, i, j⟩ <;> rcases w' with ⟨v', i', j'⟩ | ⟨k', i', j'⟩ <;>
    simp only [pos, Prod.mk.injEq] at h h' <;> try omega
  obtain ⟨rfl, rfl⟩ := row_height (v := v) (v' := v') (i := i) (i' := i') (by omega)
  have hj : (j' : ℕ) = j + 1 := by omega
  have hlt : (j : ℕ) < 12 * m := by have := j'.isLt; omega
  exact ⟨.inl (v, i, ⟨j, hlt⟩), rfl, by simp [linkV, row]; ext; simp [hj]⟩

/-- Two column nodes at the same `x` and `2` apart are consecutive in one column: the ends of a
column edge. -/
lemma col_link_of_pos {w w' : G.Node} {X Y : ℤ} (hY : Y % 2 = 1) (h : G.pos w = (X, Y))
    (h' : G.pos w' = (X, Y + 2)) : ∃ e, G.linkU e = w ∧ G.linkV e = w' := by
  have s := G.pos_shape w
  have s' := G.pos_shape w'
  rw [h] at s
  rw [h'] at s'
  rcases w with ⟨v, i, j⟩ | ⟨k, i, j⟩ <;> rcases w' with ⟨v', i', j'⟩ | ⟨k', i', j'⟩ <;>
    simp only [pos, Prod.mk.injEq] at h h' <;> try omega
  obtain ⟨rfl, rfl⟩ := colX_inj (h.1.trans h'.1.symm)
  have hj : (j' : ℕ) = j + 1 := by omega
  have hlt : (j : ℕ) < G.colLen k - 1 := by have := j'.isLt; omega
  exact ⟨.inr (.inl ⟨k, i, ⟨j, hlt⟩⟩), rfl, by simp [linkV, col]; ext; simp [hj]⟩

/-- The disk with diameter the edge `e` is good, with two marked points `P`, `Q`: no node lies
strictly inside it; on its circle nodes lie only at the ends and at `P`, `Q`; nodes at `P` and at
`Q` are equal or the ends of an edge. -/
def DiskOK (e : G.Link) (P Q : ℤ × ℤ) : Prop :=
  (∀ w, nrm (G.pos (G.linkV e) - G.pos (G.linkU e)) ≤
      nrm (2 • G.pos w - G.pos (G.linkU e) - G.pos (G.linkV e)) ∧
    (nrm (2 • G.pos w - G.pos (G.linkU e) - G.pos (G.linkV e)) =
        nrm (G.pos (G.linkV e) - G.pos (G.linkU e)) →
      G.pos w = G.pos (G.linkU e) ∨ G.pos w = G.pos (G.linkV e) ∨ G.pos w = P ∨ G.pos w = Q)) ∧
  ∀ w₁ w₂, G.pos w₁ = P → G.pos w₂ = Q → w₁ = w₂ ∨ ∃ e', G.linkU e' = w₁ ∧ G.linkV e' = w₂

/-- **Near a midpoint of even parity.** If `M` has `x + y` even and `p` has `x + y` odd, then `p`
is at squared distance `≥ 1` from `M`, and `= 1` only at the four neighbours of `M`. -/
private lemma near_even {M p : ℤ × ℤ} (hM : (M.1 + M.2) % 2 = 0) (hp : (p.1 + p.2) % 2 = 1) :
    1 ≤ nrm (p - M) ∧ (nrm (p - M) = 1 → p = M + (1, 0) ∨ p = M - (1, 0) ∨
      p = M + (0, 1) ∨ p = M - (0, 1)) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := M
  simp only [nrm, Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq] at *
  have hne : a - c ≠ 0 ∨ b - d ≠ 0 := by omega
  refine ⟨?_, fun h => ?_⟩
  · rcases hne with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg (a - c), sq_nonneg (b - d)]
  · have hx : -1 ≤ a - c ∧ a - c ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (b - d)]
    have hy : -1 ≤ b - d ∧ b - d ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (a - c)]
    rcases (by omega : a - c = -1 ∨ a - c = 0 ∨ a - c = 1) with e | e | e <;>
      rcases (by omega : b - d = -1 ∨ b - d = 0 ∨ b - d = 1) with f | f | f <;>
      simp [e, f] at h <;> omega

/-- Positions of nodes have `x + y` odd (from `pos_shape`). -/
private lemma pos_odd (w : G.Node) : ((G.pos w).1 + (G.pos w).2) % 2 = 1 := by
  rcases G.pos_shape w with h | h <;> omega

/-- **Axis edges.** An edge of length `2` with midpoint `M` of even `x + y` and direction
`d = (1, 0)` or `(0, 1)`: every node is at distance `≥ 1` from `M`, and at distance `1` only at the
ends `M ± d` and at the points `M ± d.swap`, which are marked. -/
private lemma disk_axis (e : G.Link) {M d : ℤ × ℤ} (hM : (M.1 + M.2) % 2 = 0)
    (hd : d = (1, 0) ∨ d = (0, 1)) (hU : G.pos (G.linkU e) = M - d) (hV : G.pos (G.linkV e) = M + d)
    (hlink : ∀ w₁ w₂, G.pos w₁ = M - d.swap → G.pos w₂ = M + d.swap →
      ∃ e', G.linkU e' = w₁ ∧ G.linkV e' = w₂) : G.DiskOK e (M - d.swap) (M + d.swap) := by
  have hmid : ∀ w, nrm (2 • G.pos w - G.pos (G.linkU e) - G.pos (G.linkV e)) =
      4 * nrm (G.pos w - M) := by
    intro w; rw [hU, hV]; obtain ⟨a, b⟩ := G.pos w; obtain ⟨c, c'⟩ := M
    rcases hd with rfl | rfl <;> simp [nrm] <;> ring
  have hlen : nrm (G.pos (G.linkV e) - G.pos (G.linkU e)) = 4 := by
    rw [hU, hV]; rcases hd with rfl | rfl <;> simp [nrm]
  refine ⟨fun w => ?_, fun w₁ w₂ h₁ h₂ => Or.inr (hlink w₁ w₂ h₁ h₂)⟩
  obtain ⟨h1, h2⟩ := near_even hM (G.pos_odd w)
  rw [hmid, hlen]
  refine ⟨by omega, fun h => ?_⟩
  rcases h2 (by omega) with h | h | h | h <;> rcases hd with rfl | rfl <;>
    simp [h, hU, hV]

/-- **Attachments.** The ends are `(X, Y ± 1)` and `(X + 1, Y)`, so `u_w` has odd coordinates
and every node is outside or at a corner of the square `{X, X + 1} × {Y, Y ± 1}`; the two
corners other than the ends have `x + y` even. -/
lemma disk_attach (k : Fin m) (i : Fin 3) (b : Bool) :
    G.DiskOK (.inr (.inr (.inl (k, i, b)))) (G.pos (G.linkU (.inr (.inr (.inl (k, i, b))))))
      (G.pos (G.linkU (.inr (.inr (.inl (k, i, b)))))) := by
  have hlt := G.lo_lt_hi k
  have hlen : (G.colLen k : ℤ) = 4 * ((G.hi k : ℕ) - (G.lo k : ℕ)) := by unfold colLen; omega
  have hi3 := i.isLt
  have hB : x0 i + 2 * ((jA k i : ℕ) : ℤ) = colX k i + 1 := by
    simp only [jA, x0, colX]; split_ifs <;> push_cast <;> omega
  have hX : colX k i % 2 = 0 := by unfold colX; split_ifs <;> omega
  -- the ends are `A = (X, Y + ε)` and `B = (X + 1, Y)`, `ε = ±1`
  obtain ⟨Y, ε, hε, hY, hA, hB'⟩ : ∃ Y ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Y % 2 = 0 ∧
      G.pos (G.linkU (.inr (.inr (.inl (k, i, b))))) = (colX k i, Y + ε) ∧
      G.pos (G.linkV (.inr (.inr (.inl (k, i, b))))) = (colX k i + 1, Y) := by
    cases b
    · exact ⟨8 * (G.lo k : ℕ) + 2 * (i : ℕ), 1, by simp, by omega,
        by simp [linkU, col, pos], by simp [linkV, row, pos, hB]⟩
    · exact ⟨8 * (G.hi k : ℕ) + 2 * (i : ℕ), -1, by simp, by omega,
        by simp [linkU, col, pos]; omega, by simp [linkV, row, pos, hB]⟩
  refine ⟨fun w => ?_, fun w₁ w₂ h₁ h₂ => Or.inl (G.pos_injective (h₁.trans h₂.symm))⟩
  have s := G.pos_shape w
  generalize G.pos w = p at s ⊢
  obtain ⟨x, y⟩ := p
  rw [hA, hB']
  clear hB hlen hlt hi3
  generalize colX k i = X at hX hA hB' ⊢
  have hxy : (x + y) % 2 = 1 := by simp at s; omega
  -- `u = 2(x, y) - A - B` has odd coordinates `(a, c)`, so `nrm u = a² + c² ≥ 2 = nrm (B - A)`,
  -- with equality only at the corners `A`, `B` of the unit square on `A`, `B`
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * x - 2 * X - 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * y - 2 * Y - ε := ⟨_, rfl⟩
  have h1 : 1 ≤ a ^ 2 := by have := sq_pos_of_ne_zero (show a ≠ 0 by omega); linarith
  have h2 : 1 ≤ c ^ 2 := by
    have := sq_pos_of_ne_zero (show c ≠ 0 by rcases hε with rfl | rfl <;> omega); linarith
  have e : (2 • x - X - (X + 1)) = a := by simp; omega
  have e' : (2 • y - (Y + ε) - Y) = c := by simp; omega
  simp only [nrm, Prod.smul_mk, Prod.mk_sub_mk, e, e']
  have e1 : X + 1 - X = 1 := by omega
  have e2 : Y - (Y + ε) = -ε := by omega
  rw [e1, e2]
  refine ⟨by rcases hε with rfl | rfl <;> nlinarith, fun h => ?_⟩
  have ha1 : -1 ≤ a ∧ a ≤ 1 := by rcases hε with rfl | rfl <;> constructor <;> nlinarith
  have hc1 : -1 ≤ c ∧ c ≤ 1 := by rcases hε with rfl | rfl <;> constructor <;> nlinarith
  simp only [Prod.mk.injEq]
  omega

/-- **Triangles.** Checked directly on the lattice points near the triangle of `v`: the only
node on a circle besides the ends is the second node of the row next to a corner. -/
lemma disk_tri (v : Fin n) (t : Fin 3) :
    ∃ P, G.DiskOK (.inr (.inr (.inr (v, t)))) P P := by
  -- The marked point `P` is the second node of the row next to a corner.
  refine ⟨(3, 8 * (v : ℤ) + (![0, 4, 2] : Fin 3 → ℤ) t), fun w => ?_,
    fun w₁ w₂ h₁ h₂ => Or.inl (G.pos_injective (h₁.trans h₂.symm))⟩
  fin_cases t
  all_goals
    have hs := G.pos_shape w
    generalize G.pos w = p at hs ⊢
    obtain ⟨x, y⟩ := p
    simp [linkU, linkV, row, pos, x0, nrm, Prod.ext_iff] at hs ⊢
    obtain ⟨d, rfl⟩ : ∃ d, y = 8 * (v : ℤ) + d := ⟨y - 8 * v, by ring⟩
    -- `nrm u_w` is `4 *` the squared distance from the centre of the edge. Inside the box
    -- `[-1, 4] × [-1, 5]` all points are enumerated, outside it the distance is too large.
    by_cases hb : -1 ≤ x ∧ x ≤ 4 ∧ -1 ≤ d ∧ d ≤ 5
    · obtain ⟨h1, h2, h3, h4⟩ := hb
      interval_cases x <;> interval_cases d <;> ring_nf <;> first | omega | simp
    · rcases (by omega : x < -1 ∨ 4 < x ∨ d < -1 ∨ 5 < d) with h | h | h | h <;>
        exact ⟨by nlinarith, fun h' => by nlinarith⟩

/-- Every edge has a good disk (`DiskOK`), by the kind of the edge. -/
lemma disk (e : G.Link) : ∃ P Q, G.DiskOK e P Q := by
  rcases e with ⟨v, i, j⟩ | ⟨k, i, j⟩ | ⟨k, i, b⟩ | ⟨v, t⟩
  · -- row edge: the marked points are column nodes at `M ± (0, 1)`
    have hx : x0 i % 2 = 1 := by unfold x0; split_ifs <;> omega
    refine ⟨_, _, G.disk_axis (.inl (v, i, j))
      (M := (x0 i + 2 * (j : ℕ) + 1, 8 * (v : ℕ) + 2 * (i : ℕ))) (d := (1, 0))
      (by simp only; omega) (.inl rfl) (by simp [linkU, row, pos])
      (by simp [linkV, row, pos]; ring) fun w₁ w₂ h₁ h₂ => ?_⟩
    refine G.col_link_of_pos (X := x0 i + 2 * (j : ℕ) + 1) (Y := 8 * (v : ℕ) + 2 * (i : ℕ) - 1)
      (by omega) (by rw [h₁]; simp) ?_
    rw [h₂]; ext <;> simp; ring
  · -- column edge: the marked points are row nodes at `M ± (1, 0)`
    have hx : colX k i % 2 = 0 := by unfold colX; split_ifs <;> omega
    refine ⟨_, _, G.disk_axis (.inr (.inl ⟨k, i, j⟩))
      (M := (colX k i, 8 * (G.lo k : ℕ) + 2 * (i : ℕ) + 2 + 2 * (j : ℕ)))
      (d := (0, 1)) (by simp only; omega) (.inr rfl) (by simp [linkU, col, pos]; ring)
      (by simp [linkV, col, pos]; ring) fun w₁ w₂ h₁ h₂ => ?_⟩
    refine G.row_link_of_pos (X := colX k i - 1)
      (Y := 8 * (G.lo k : ℕ) + 2 * (i : ℕ) + 2 + 2 * (j : ℕ)) (by omega) (by rw [h₁]; simp) ?_
    rw [h₂]; ext <;> simp; ring
  · exact ⟨_, _, G.disk_attach k i b⟩
  · obtain ⟨P, h⟩ := G.disk_tri v t
    exact ⟨P, P, h⟩

/-- No node lies strictly inside the disk with diameter an edge. Every node has `x + y` odd;
for a row or column edge the midpoint has `x + y` even, so every node is at distance `≥ 1` from
it; for an attachment every lattice point is outside; the triangles are checked directly. -/
theorem empty (e : G.Link) (w : G.Node) :
    nrm (G.pos (G.linkV e) - G.pos (G.linkU e)) ≤
      nrm (2 • G.pos w - G.pos (G.linkU e) - G.pos (G.linkV e)) := by
  obtain ⟨P, Q, h, -⟩ := G.disk e
  exact (h w).1

/-- On the circle with diameter an edge there is at most one more node, or the two ends of an
edge. Row edge: only column nodes `(x, y ± 1)` over the midpoint, and if both exist they are
consecutive in one column. Column edge: likewise with row nodes. Attachment: none, by parity.
Triangle edges: one row node next to a corner. -/
theorem circle (e : G.Link) :
    (onCircle G.pos G.linkU G.linkV e).card ≤ 1 ∨
      ∃ e', onCircle G.pos G.linkU G.linkV e = {G.linkU e', G.linkV e'} := by
  obtain ⟨P, Q, hD, hPQ⟩ := G.disk e
  -- every node on the circle sits at `P` or at `Q`
  have hS : ∀ w ∈ onCircle G.pos G.linkU G.linkV e, G.pos w = P ∨ G.pos w = Q := by
    intro w hw
    simp only [onCircle, mem_filter, mem_univ, true_and] at hw
    obtain ⟨hu, hv, hn⟩ := hw
    rcases (hD w).2 hn with h | h | h | h
    · exact absurd (G.pos_injective h) hu
    · exact absurd (G.pos_injective h) hv
    · exact .inl h
    · exact .inr h
  -- two nodes of the circle at `P` and at `Q` are all of it
  have key : ∀ a b, a ∈ onCircle G.pos G.linkU G.linkV e → b ∈ onCircle G.pos G.linkU G.linkV e →
      G.pos a = P → G.pos b = Q → onCircle G.pos G.linkU G.linkV e = {a, b} := by
    intro a b ha hb hPa hQb
    ext w
    simp only [mem_insert, mem_singleton]
    refine ⟨fun hw => ?_, by rintro (rfl | rfl) <;> assumption⟩
    rcases hS w hw with h | h
    · exact .inl (G.pos_injective (h.trans hPa.symm))
    · exact .inr (G.pos_injective (h.trans hQb.symm))
  by_cases hc : (onCircle G.pos G.linkU G.linkV e).card ≤ 1
  · exact .inl hc
  obtain ⟨w₁, h₁, w₂, h₂, hne⟩ := Finset.one_lt_card.mp (not_le.mp hc)
  refine .inr ?_
  rcases hS w₁ h₁, hS w₂ h₂ with ⟨hp | hp, hq | hq⟩
  · exact absurd (G.pos_injective (hp.trans hq.symm)) hne
  · obtain h | ⟨e', hu, hv⟩ := hPQ w₁ w₂ hp hq
    · exact absurd h hne
    · exact ⟨e', by rw [key w₁ w₂ h₁ h₂ hp hq, hu, hv]⟩
  · obtain h | ⟨e', hu, hv⟩ := hPQ w₂ w₁ hq hp
    · exact absurd h.symm hne
    · exact ⟨e', by rw [key w₂ w₁ h₂ h₁ hq hp, hu, hv]⟩
  · exact absurd (G.pos_injective (hp.trans hq.symm)) hne

/-- The lattice drawing of `H`. -/
def drawing : Drawing G.linkU G.linkV where
  pos := G.pos
  inj := G.pos_injective
  short := G.short
  empty := G.empty
  circle := G.circle

end Graph

end NeoTiling.Hardness
