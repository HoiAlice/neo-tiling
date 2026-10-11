import Complexity.Subdivision

/-!
# Grid drawings give Gabriel edges (Lemma 3.3)

Input: an orthogonal grid drawing of the graph (its existence in polynomial area for planar
graphs of maximum degree `3` is due to Valiant 1981 and Tamassia 1987, cited, not formalized).
Edge `k` is a lattice path through `c k` inner points. All points are distinct, consecutive
points are neighbours, and no edge is a loop.

Construction of `G''`. Double all coordinates. Put nodes at the doubled points and at the
midpoints of all steps except the first one of each path. Edge `k` then carries `2 c k` new
nodes, so `G'' = PathVert n (2 c)`. Each node is the sum of the ends of a step of length at
most `1` (`point_ends`): an integer point with at most one odd coordinate, which determines its
step (`unit_mid`). An edge of `G''` has length `1`, or length `2` (the first step of a path)
with a midpoint that is no node.

* `gabriel_local`: then `|2q - a - b|² ≥ |a - b|² + 4`, i.e. the edge `ab` is Gabriel with
  margin `1` with respect to `q`.
* `point_injective`, `gabriel`: the nodes are distinct, every edge of `G''` is Gabriel with
  margin `1`. Scaled by `D.scale` (`spoint_*`), the nodes lie in the box `|a₀| + |a₁| ≤ 1/8`
  and every edge is Gabriel with margin `D.gamma = D.scale² ∈ (0, 1/2]`.
-/

namespace NeoTiling.Complexity

/-- A lattice point as a point of the plane. -/
def toR (p : ℤ × ℤ) : Fin 2 → ℝ := ![(p.1 : ℝ), (p.2 : ℝ)]

/-- **Gabriel margin on the lattice.** Let `q ≠ a, b` be an integer point with at most one odd
coordinate. Let `ab` be a unit step, or a step `b = a + 2d` of length `2` from a point `a` with
even coordinates whose midpoint `a + d` is not `q`. Then `|2q - a - b|² ≥ |a - b|² + 4`.
Otherwise `|2q - a - b| ≤ 2`, which leaves finitely many positions of `q - a` to check. -/
theorem gabriel_local {a b q : ℤ × ℤ} (hq : ¬ (Odd q.1 ∧ Odd q.2)) (hqa : q ≠ a) (hqb : q ≠ b)
    (hab : |b.1 - a.1| + |b.2 - a.2| = 1 ∨
      ∃ d : ℤ × ℤ, |d.1| + |d.2| = 1 ∧ b = a + 2 • d ∧ Even a.1 ∧ Even a.2 ∧ q ≠ a + d) :
    (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 + 4 ≤
      (2 * q.1 - a.1 - b.1) ^ 2 + (2 * q.2 - a.2 - b.2) ^ 2 := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨q1, q2⟩ := q
  simp only [Prod.ext_iff, Int.odd_iff, Int.even_iff, ne_eq, not_and, Prod.exists, Prod.fst_add,
    Prod.snd_add, two_nsmul] at *
  -- `2q - a - b = (u, v)`, `b - a = (s, t)`
  generalize hu : 2 * q1 - a1 - b1 = u; generalize hv : 2 * q2 - a2 - b2 = v
  generalize hs : b1 - a1 = s at hab ⊢; generalize ht : b2 - a2 = t at hab ⊢; by_contra! h
  -- `(s, t)` is one of the vectors `±e₁, ±e₂` (unit step) or `±2e₁, ±2e₂` (length `2`)
  rcases hab with hab | ⟨d1, d2, hd, ⟨hb1, hb2⟩, ha1, ha2, hqd⟩
  on_goal 1 => rcases (show (s = 1 ∨ s = -1) ∧ t = 0 ∨ s = 0 ∧ (t = 1 ∨ t = -1) by
    rcases abs_cases s <;> rcases abs_cases t <;> omega) with ⟨rfl | rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  on_goal 5 => rcases (show (s = 2 ∨ s = -2) ∧ t = 0 ∨ s = 0 ∧ (t = 2 ∨ t = -2) by
    rcases abs_cases d1 <;> rcases abs_cases d2 <;> omega) with ⟨rfl | rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  -- then `u² + v² < 9`, so `|u|, |v| ≤ 2`, and we check all cases
  all_goals
    obtain ⟨_, _, _, _⟩ : -2 ≤ u ∧ u ≤ 2 ∧ -2 ≤ v ∧ v ≤ 2 := by and_intros <;> nlinarith
    interval_cases u <;> interval_cases v <;> norm_num at h <;> omega

/-- **A midpoint determines its step.** If `x, y` and `x', y'` are at distance at most `1` and
`x + y = x' + y'`, then `{x, y} = {x', y'}`. -/
theorem unit_mid {x y x' y' : ℤ × ℤ} (h : |y.1 - x.1| + |y.2 - x.2| ≤ 1)
    (h' : |y'.1 - x'.1| + |y'.2 - x'.2| ≤ 1) (hm : x + y = x' + y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y; obtain ⟨a', b'⟩ := x'; obtain ⟨c', d'⟩ := y'
  simp only [Prod.ext_iff, Prod.mk_add_mk] at *
  rcases abs_cases (c - a) with h1 | h1 <;> rcases abs_cases (d - b) with h2 | h2 <;>
    rcases abs_cases (c' - a') with h3 | h3 <;> rcases abs_cases (d' - b') with h4 | h4 <;> omega

variable {n m : ℕ}

/-- An orthogonal grid drawing: edge `k` is a lattice path through `c k` inner points, all
points are distinct, consecutive points are neighbours, and no edge is a loop. -/
structure GridDrawing (eu ev : Fin m → Fin n) where
  c : Fin m → ℕ
  pos : PathVert n c → ℤ × ℤ
  pos_inj : Function.Injective pos
  step : ∀ e : PathEdge c,
    |(pos (pathV eu ev c e)).1 - (pos (pathU eu ev c e)).1| +
      |(pos (pathV eu ev c e)).2 - (pos (pathU eu ev c e)).2| = 1
  loopless : ∀ k, eu k ≠ ev k

namespace GridDrawing

variable {eu ev : Fin m → Fin n} (D : GridDrawing eu ev)

/-- Vertices of `G''`: `2 c k` new vertices on edge `k`. -/
abbrev Vert : Type := PathVert n fun k => 2 * D.c k

/-- Edges of `G''`. -/
abbrev Edge : Type := PathEdge fun k => 2 * D.c k

/-- Node `j` of edge `k` of `G''`, doubled: the doubled point `(j + 1) / 2` for `j = 0` and
odd `j`, the midpoint of the step from point `j / 2` for even `j ≥ 2`. -/
def node (k : Fin m) (j : ℕ) : ℤ × ℤ :=
  if j = 0 ∨ j % 2 = 1 then 2 • D.pos (pathNode eu ev D.c k ((j + 1) / 2))
  else D.pos (pathNode eu ev D.c k (j / 2)) + D.pos (pathNode eu ev D.c k (j / 2 + 1))

/-- The nodes of `G''` in the plane. -/
def point : D.Vert → ℤ × ℤ
  | .inl v => 2 • D.pos (.inl v)
  | .inr ⟨k, i⟩ => D.node k (i + 1)

/-- **Nodes as sums.** For `j ≥ 1`, node `j` is the sum of drawing points `(j + 1) / 2` and
`j / 2 + 1` (equal for odd `j`, neighbours for even `j`). -/
theorem node_eq {k : Fin m} {j : ℕ} (hj : 0 < j) : D.node k j =
    D.pos (pathNode eu ev D.c k ((j + 1) / 2)) + D.pos (pathNode eu ev D.c k (j / 2 + 1)) := by
  unfold node; split_ifs with h
  · rw [two_smul, show j / 2 + 1 = (j + 1) / 2 by omega]
  · congr 3; omega

/-- **Nodes of `G''` are drawn at `D.node`.** -/
theorem point_pathNode {k : Fin m} {j : ℕ} (hj : j ≤ 2 * D.c k + 1) :
    D.point (pathNode eu ev (fun k => 2 * D.c k) k j) = D.node k j := by
  unfold pathNode; split_ifs with h0 h1
  · subst h0; simp [point, node, pathNode]
  · simp only [point]; congr 1; omega
  · have : (j + 1) / 2 = D.c k + 1 := by simp only at h1; omega
    simp [point, node, this, pathNode, show j % 2 = 1 by omega]

/-- The step of the drawing whose ends sum to a node of `G''` (a zero step for old vertices). -/
def ends : D.Vert → PathVert n D.c × PathVert n D.c
  | .inl v => (.inl v, .inl v)
  | .inr ⟨k, i⟩ =>
    (pathNode eu ev D.c k (((i : ℕ) + 1 + 1) / 2), pathNode eu ev D.c k (((i : ℕ) + 1) / 2 + 1))

/-- **Shape of a node:** the sum of the ends of a step of length at most `1`. -/
theorem point_ends (w : D.Vert) : D.point w = D.pos (D.ends w).1 + D.pos (D.ends w).2 ∧
    |(D.pos (D.ends w).2).1 - (D.pos (D.ends w).1).1| +
      |(D.pos (D.ends w).2).2 - (D.pos (D.ends w).1).2| ≤ 1 := by
  rcases w with v | ⟨k, i, hi : i < 2 * D.c k⟩
  · simp [point, ends, two_smul]
  refine ⟨D.node_eq (by omega), ?_⟩
  -- for odd `i` the step `(i + 1) / 2` of the drawing, for even `i` a zero step
  rcases (by omega : (i + 1 + 1) / 2 = (i + 1) / 2 ∨ (i + 1 + 1) / 2 = (i + 1) / 2 + 1) with h | h
  · simpa [ends, h, pathU, pathV] using (D.step ⟨k, ⟨(i + 1) / 2, by omega⟩⟩).le
  · simp [ends, h]

/-- The nodes are distinct: a node determines its step, and the step determines the node. -/
theorem point_injective : Function.Injective D.point := by
  intro w w' h; obtain ⟨h1, hs⟩ := D.point_ends w; obtain ⟨h2, hs'⟩ := D.point_ends w'
  have := unit_mid hs hs' (h1 ▸ h2 ▸ h)
  simp only [D.pos_inj.eq_iff] at this; clear h1 h2 hs hs' h
  -- the step determines the node (vertex equalities on edge `k` force `k = k'`, then omega)
  rcases w with v | ⟨k, i, hi : i < 2 * D.c k⟩ <;>
    rcases w' with v' | ⟨k', i', hi' : i' < 2 * D.c k'⟩ <;>
    rcases this with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp only [ends, pathNode] at h3 h4 <;>
    (try split_ifs at h3 h4) <;> simp_all <;>
    (try obtain ⟨rfl, h3⟩ := h3) <;> (try obtain ⟨rfl, h4⟩ := h4) <;> (try simp_all) <;> omega

/-- **Every edge of `G''` is Gabriel with margin `1`** (by `gabriel_local`). -/
theorem gabriel (e : D.Edge) (w : D.Vert) (hw1 : w ≠ pathU eu ev _ e)
    (hw2 : w ≠ pathV eu ev _ e) :
    sqn (toR (D.point (pathU eu ev _ e)) - toR (D.point (pathV eu ev _ e))) / 4 + 1 ≤
      sqn (toR (D.point w) -
        mid (toR (D.point (pathU eu ev _ e))) (toR (D.point (pathV eu ev _ e)))) := by
  -- `q = D.point w` is the sum `x + y` of the ends of a step of length at most `1`
  obtain ⟨k, j, hj : j < 2 * D.c k + 1⟩ := e; obtain ⟨hq, hs⟩ := D.point_ends w
  refine (fun h => ?_) (gabriel_local ?_ (D.point_injective.ne hw1) (D.point_injective.ne hw2) ?_)
  -- the claim is the integer estimate of `gabriel_local`, divided by `4`
  · have h := (Int.cast_le (R := ℝ)).2 h; push_cast at h
    simp [sqn, mid, toR]; linear_combination h / 4
  -- so `q` has at most one odd coordinate
  · simp only [hq, Prod.fst_add, Prod.snd_add, Int.odd_iff]
    generalize D.pos (D.ends w).1 = x at hs ⊢; generalize D.pos (D.ends w).2 = y at hs ⊢
    rcases abs_cases (y.1 - x.1) <;> rcases abs_cases (y.2 - x.2) <;> omega
  -- the edge joins nodes `j` and `j + 1` of edge `k`
  simp only [pathU, pathV, D.point_pathNode (show j ≤ 2 * D.c k + 1 by omega),
    D.point_pathNode (show j + 1 ≤ 2 * D.c k + 1 by omega)]
  rcases (Nat.eq_zero_or_pos j).symm with hj0 | rfl
  -- `j ≥ 1`: the nodes differ by the step `(j + 1) / 2` of the drawing
  · left; rw [D.node_eq hj0, D.node_eq (by omega), show (j + 1 + 1) / 2 = j / 2 + 1 by omega]
    convert D.step ⟨k, ⟨(j + 1) / 2, by omega⟩⟩ using 3 <;> simp [pathU, pathV] <;> ring
  -- `j = 0`: the doubled first step `x₀ x₁` of the drawn path, `d = x₁ - x₀`
  set x₀ := D.pos (.inl (eu k)) with hx₀
  set x₁ := D.pos (pathNode eu ev D.c k 1) with hx₁
  have h01 : |x₁.1 - x₀.1| + |x₁.2 - x₀.2| = 1 := by
    simpa [pathU, pathV, pathNode] using D.step ⟨k, 0⟩
  rw [show D.node k 0 = 2 • x₀ by simp [node, pathNode, x₀], show D.node k (0 + 1) = 2 • x₁ by
    simp [node, x₁]]
  refine Or.inr ⟨x₁ - x₀, by simpa using h01, by ext <;> simp <;> ring, by simp, by simp, ?_⟩
  -- the midpoint `x₀ + x₁` of the first step is no node, since it determines the step
  rw [hq, show 2 • x₀ + (x₁ - x₀) = x₀ + x₁ by ext <;> simp <;> ring]; intro h
  have := unit_mid hs h01.le h; simp only [hx₀, hx₁, D.pos_inj.eq_iff] at this
  have hl k : ev k ≠ eu k := (D.loopless k).symm
  rcases w with v | ⟨k', i, hi : i < 2 * D.c k'⟩ <;> rcases this with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    simp only [ends, pathNode] at h3 h4 <;> (try split_ifs at h3 h4) <;> simp_all <;>
    (try obtain ⟨rfl, h4⟩ := h4) <;> (try simp_all) <;> omega

/-- A bound on all coordinates of the nodes. -/
noncomputable def bound : ℝ := ∑ x : D.Vert, (|((D.point x).1 : ℝ)| + |((D.point x).2 : ℝ)|)

/-- The scaling factor into the box `|a₀| + |a₁| ≤ 1/8`. -/
noncomputable def scale : ℝ := 1 / (16 * (D.bound + 1))

/-- The Gabriel margin after scaling. -/
noncomputable def gamma : ℝ := D.scale ^ 2

/-- The scaled nodes. -/
noncomputable def spoint (x : D.Vert) : Fin 2 → ℝ := D.scale • toR (D.point x)

theorem bound_nonneg : 0 ≤ D.bound := Finset.sum_nonneg fun _ _ => by positivity

theorem spoint_box (x : D.Vert) : |D.spoint x 0| + |D.spoint x 1| ≤ 1 / 8 := by
  have hb := D.bound_nonneg
  have hx : _ ≤ D.bound := Finset.single_le_sum (fun y _ => by positivity) (Finset.mem_univ x)
  simp only [spoint, toR, scale, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, abs_mul,
    Matrix.cons_val_one, ← mul_add, abs_of_pos (by positivity : 0 < 1 / (16 * (D.bound + 1)))]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith

theorem gamma_pos : 0 < D.gamma := by have := D.bound_nonneg; unfold gamma scale; positivity

theorem gamma_le : D.gamma ≤ 1 / 2 := by
  have := D.bound_nonneg; unfold gamma scale; rw [div_pow, div_le_iff₀ (by positivity)]; nlinarith

theorem spoint_injective : Function.Injective D.spoint := fun x y h => D.point_injective <| by
  have hs : D.scale ≠ 0 := fun h0 => D.gamma_pos.ne' (by simp [gamma, h0])
  simpa [spoint, toR, hs, funext_iff, Fin.forall_fin_two, Prod.ext_iff] using h

theorem spoint_gabriel (e : D.Edge) (w : D.Vert) (hw1 : w ≠ pathU eu ev _ e)
    (hw2 : w ≠ pathV eu ev _ e) :
    sqn (D.spoint (pathU eu ev _ e) - D.spoint (pathV eu ev _ e)) / 4 + D.gamma ≤
      sqn (D.spoint w - mid (D.spoint (pathU eu ev _ e)) (D.spoint (pathV eu ev _ e))) := by
  have := mul_le_mul_of_nonneg_left (D.gabriel e w hw1 hw2) (sq_nonneg D.scale)
  simp [sqn, mid, spoint, gamma, toR] at this ⊢; linarith

/-- The two ends of an edge of `G''` are different vertices. -/
theorem pathU_ne_pathV (e : D.Edge) : pathU eu ev _ e ≠ pathV eu ev _ e := by
  obtain ⟨k, j, hj : j < 2 * D.c k + 1⟩ := e
  simp only [pathU, pathV, pathNode]; split_ifs <;> simp_all [D.loopless k]; omega

end GridDrawing

end NeoTiling.Complexity
