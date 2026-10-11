import PolyHardness.Chain

/-!
# Solvability in the plane is one linear program

Part of `poly-hardness/` (not part of the `NeoTiling` library).

Mode `b` as in `PolyHardness.Chain`: `IsReachableB false = IsWeakReachable`,
`IsReachableB true = IsReachable`. Prices `P : Fin T → Fin 2 → ℝ`, `X t = P t 0`, `Y t = P t 1`.

**The graph.** Nodes: a source, a sink, `start b` ("the chain begins at `b`") and `edge a b`
("the last edge of the chain is `a b`"). Arcs: `src → snk`, `src → start b`,
`start a → edge a b`, `edge a b → edge b c` (strictly convex turn), `start b → snk`,
`edge a b → snk`. Paths from `src` to `snk` other than `src → snk` are the strictly convex chains.
Every arc carries two sets of indices, `Out` (outside the region of the chain) and `Bnd` (on its
boundary): the arc into `start b` carries the left slab of `b`, the arc into `edge a b` the slab
of the edge, the arc into `snk` the right slab of the last vertex, `src → snk` carries `Out = univ`.

**Results.**
* `flow_decomposition`: a flow in a finite graph with a rank that grows along arcs is a
  nonnegative combination of source–sink paths.
* `isReachableB_iff_path`: `S` is (weakly) reachable iff for some path `Out(π) ⊆ S` and
  `S ⊆ Out(π) ∪ Bnd(π)` (weak) or `S = Out(π)` (strict).
* `mem_indicatorCone_iff_flow`: `y` lies in the cone of (weakly) reachable spectra iff the
  linear system `y = Σ_e f_e 1_{Out e} + g`, `0 ≤ g ≤ β Σ_e f_e 1_{Bnd e}`, `f` a flow, is
  solvable (`β = 1` weak, `β = 0` strict). The system has `O(T³)` nonzero variables.
-/

namespace NeoTiling.PolyHardness

open Finset
open scoped Classical

/-! ## Flows and paths in a finite graph -/

section Graph

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `w 0, …, w L` is a path from `a` to `b` along `arc`. -/
structure IsPath (arc : N → N → Prop) (a b : N) (w : ℕ → N) (L : ℕ) : Prop where
  start : w 0 = a
  stop : w L = b
  step : ∀ i < L, arc (w i) (w (i + 1))

/-- How many times the path `w 0, …, w L` uses the arc `u → v`. -/
noncomputable def pathVec (w : ℕ → N) (L : ℕ) (u v : N) : ℝ :=
  ((range L).filter fun i => w i = u ∧ w (i + 1) = v).card

/-- A flow from `src` to `snk`: nonnegative, supported on arcs, conserved at the other nodes. -/
structure IsFlow (arc : N → N → Prop) (src snk : N) (f : N → N → ℝ) : Prop where
  nonneg : ∀ u v, 0 ≤ f u v
  supp : ∀ u v, f u v ≠ 0 → arc u v
  cons : ∀ u, u ≠ src → u ≠ snk → ∑ v, f v u = ∑ v, f u v

/-- A path vector counts the arcs of the path: `Σ_{u,v} pathVec u v · F u v = Σ_{i<L} F (w i) (w (i+1))`. -/
theorem sum_pathVec_mul (w : ℕ → N) (L : ℕ) (F : N → N → ℝ) :
    ∑ u, ∑ v, pathVec w L u v * F u v = ∑ i ∈ range L, F (w i) (w (i + 1)) := by
  -- each arc count is a sum of indicators over `i < L`; swap sums and collapse over `u, v`
  simp only [pathVec, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ite_and, ite_mul, Finset.sum_ite_eq]

/-- A source–sink path is a flow: every inner node is entered as often as it is left, since the
path neither starts nor ends there. -/
theorem isFlow_pathVec {arc : N → N → Prop} {src snk : N} {w : ℕ → N} {L : ℕ}
    (hw : IsPath arc src snk w L) : IsFlow arc src snk (pathVec w L) := by
  refine ⟨fun u v => Nat.cast_nonneg _, fun u v h => ?_, fun u hs hk => ?_⟩
  · -- a used arc is a step of the path
    obtain ⟨i, hi, rfl, rfl⟩ : ∃ i ∈ range L, w i = u ∧ w (i + 1) = v := by
      simpa [pathVec, filter_eq_empty_iff] using h
    exact hw.step i (mem_range.1 hi)
  · -- inflow and outflow at `u` count the indices `i < L` with `w (i+1) = u`, resp. `w i = u`
    have hin := sum_pathVec_mul w L fun _ b => if b = u then 1 else 0
    have hout := sum_pathVec_mul w L fun a _ => if a = u then 1 else 0
    simp only [mul_ite, mul_one, mul_zero] at hin hout
    rw [Finset.sum_comm] at hout
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_boole] at hin hout
    -- the two counts differ only at `i = 0` and `i = L`, where `w i ≠ u`
    have h1 := Finset.sum_range_succ (fun i => if w i = u then (1:ℝ) else 0) L
    have h2 := Finset.sum_range_succ' (fun i => if w i = u then (1:ℝ) else 0) L
    simp [hw.stop, hw.start, hs.symm, hk.symm] at h1 h2
    rw [hin, hout]; exact_mod_cast h2.symm.trans h1

omit [Fintype N] in
/-- Along a path whose rank strictly grows, every arc is used at most once. -/
theorem pathVec_le_one {arc : N → N → Prop} (rank : N → ℕ) (hrank : ∀ u v, arc u v → rank u < rank v)
    {a b : N} {w : ℕ → N} {L : ℕ} (hw : IsPath arc a b w L) (u v : N) : pathVec w L u v ≤ 1 := by
  -- rank strictly increases along the path
  have hmono : ∀ i j, i < j → j ≤ L → rank (w i) < rank (w j) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun h => hrank _ _ (hw.step i h)
    | succ j hij ih =>
      exact fun h => (ih (by omega)).trans (hrank _ _ (hw.step j (by omega)))
  refine Nat.cast_le_one.mpr (Finset.card_le_one.mpr fun i hi j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hmono i j h (by omega); rw [hi.2.1, hj.2.1] at this; omega
  · have := hmono j i h (by omega); rw [hi.2.1, hj.2.1] at this; omega

/-- **Follow positive arcs.** In a flow, a positive arc `u → v` extends to a path from `u` to the
sink along positive arcs: at an inner node the outflow equals the inflow, which is positive. -/
theorem exists_pos_path {arc : N → N → Prop} {src snk : N} (rank : N → ℕ)
    (hrank : ∀ u v, arc u v → rank u < rank v) (hsrc : ∀ u, ¬ arc u src)
    {f : N → N → ℝ} (hf : IsFlow arc src snk f) {u v : N} (huv : 0 < f u v) :
    ∃ (w : ℕ → N) (L : ℕ), IsPath arc u snk w L ∧ ∀ i < L, 0 < f (w i) (w (i + 1)) := by
  -- induction on a bound for `max rank - rank u`, which drops along every arc
  induction' hn : univ.sup rank - rank u using Nat.strong_induction_on with n ih generalizing u v
  have huv' : arc u v := hf.supp u v huv.ne'
  by_cases hv : v = snk
  · -- the arc itself reaches the sink
    subst hv; refine ⟨fun i => if i = 0 then u else v, 1, ⟨rfl, by simp, ?_⟩, ?_⟩ <;>
      intro i hi <;> (obtain rfl : i = 0 := by omega) <;> simp [huv, huv']
  -- `v` is an inner node: its outflow equals its inflow `≥ f u v > 0`
  obtain ⟨t, -, hvt⟩ := exists_ne_zero_of_sum_ne_zero (hf.cons v (fun h => hsrc u (h ▸ huv')) hv ▸
    (huv.trans_le (single_le_sum (fun t _ => hf.nonneg t v) (mem_univ u))).ne')
  -- the rank grows, so the induction hypothesis applies at `v`
  have hrv : univ.sup rank - rank v < n := by
    have := hrank u v huv'; have := le_sup (f := rank) (mem_univ v); omega
  obtain ⟨w, L, hw, hpos⟩ := ih _ hrv ((hf.nonneg v t).lt_of_ne' hvt) rfl
  -- prepend `u`
  refine ⟨fun i => if i = 0 then u else w (i - 1), L + 1, ⟨rfl, by simpa using hw.stop, ?_⟩, ?_⟩ <;>
    intro i hi <;> rcases i with _ | i <;>
    simp (disch := omega) [hw.start, huv, huv', hw.step, hpos]

/-- **Flow decomposition.** In a finite graph with a rank that strictly grows along arcs, no arc
into the source and no arc out of the sink, every flow is a nonnegative combination of paths from
the source to the sink.

Proof: induction on the number of arcs with `f ≠ 0`. A positive arc of minimal rank starts at the
source; follow positive arcs to the sink (`exists_pos_path`) and subtract `m` times this path,
`m` the least value of `f` on it. The rest is a flow with fewer nonzero arcs. -/
theorem flow_decomposition {arc : N → N → Prop} {src snk : N} (rank : N → ℕ)
    (hrank : ∀ u v, arc u v → rank u < rank v) (hsrc : ∀ u, ¬ arc u src)
    (hsnk : ∀ v, ¬ arc snk v) {f : N → N → ℝ} (hf : IsFlow arc src snk f) :
    ∃ (n : ℕ) (m : Fin n → ℝ) (w : Fin n → ℕ → N) (L : Fin n → ℕ),
      (∀ i, 0 ≤ m i) ∧ (∀ i, IsPath arc src snk (w i) (L i)) ∧
      ∀ u v, f u v = ∑ i, m i * pathVec (w i) (L i) u v := by
  -- induction on the number of nonzero arcs
  induction' hk : (univ.filter fun e : N × N => f e.1 e.2 ≠ 0).card using Nat.strong_induction_on
    with k ih generalizing f
  rcases (univ.filter fun e : N × N => f e.1 e.2 ≠ 0).eq_empty_or_nonempty with h0 | h0
  · exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      by simpa [filter_eq_empty_iff] using h0⟩
  -- a nonzero arc `u → v` with `rank u` minimal
  obtain ⟨⟨u, v⟩, hmem, hmin⟩ := exists_min_image _ (fun e => rank e.1) h0
  have huv : 0 < f u v := (hf.nonneg u v).lt_of_ne' (by simpa using hmem)
  -- it starts at the source: otherwise a positive arc enters `u`, and its tail has smaller rank
  have hu : u = src := by
    by_contra hu
    have husnk : u ≠ snk := fun h => hsnk v (h ▸ hf.supp u v huv.ne')
    -- the inflow at `u` equals its outflow `≥ f u v > 0`, so some arc `t → u` is nonzero
    obtain ⟨t, -, htu⟩ := exists_ne_zero_of_sum_ne_zero (hf.cons u hu husnk ▸
      (huv.trans_le (single_le_sum (fun t _ => hf.nonneg u t) (mem_univ v))).ne')
    have := hmin (t, u) (by simpa using htu)
    have := hrank t u (hf.supp t u htu)
    simp only at *; omega
  subst u
  -- follow positive arcs to the sink; the path is nonempty since `src ≠ snk`
  obtain ⟨w, L, hw, hpos⟩ := exists_pos_path rank hrank hsrc hf huv
  have hL : 0 < L := Nat.pos_of_ne_zero fun h => hsnk v (by
    subst h; rw [← hw.stop, hw.start]; exact hf.supp _ v huv.ne')
  -- `m`: the least value of `f` on the path, attained at the arc `i₀`
  obtain ⟨i₀, hi₀, hmin'⟩ := exists_min_image (range L) (fun i => f (w i) (w (i + 1)))
    ⟨0, mem_range.2 hL⟩
  set m := f (w i₀) (w (i₀ + 1))
  have hm : 0 < m := hpos i₀ (mem_range.1 hi₀)
  have hused : ∀ a b, pathVec w L a b ≠ 0 → m ≤ f a b := by
    intro a b h
    obtain ⟨i, hi, rfl, rfl⟩ : ∃ i ∈ range L, w i = a ∧ w (i + 1) = b := by
      simpa [pathVec, filter_eq_empty_iff] using h
    exact hmin' i hi
  have hz : ∀ a b, f a b = 0 → pathVec w L a b = 0 := fun a b h => by
    by_contra hc; linarith [hused a b hc]
  -- subtract `m` times the path
  set f' := fun a b => f a b - m * pathVec w L a b
  have hp := isFlow_pathVec hw
  have hf' : IsFlow arc src snk f' := by
    refine ⟨fun a b => ?_, fun a b h => ?_, fun a ha hb => ?_⟩
    · by_cases h : pathVec w L a b = 0
      · simpa [f', h] using hf.nonneg a b
      · nlinarith [pathVec_le_one rank hrank hw a b, hused a b h, hp.nonneg a b]
    · by_cases hc : pathVec w L a b = 0
      · exact hf.supp a b (by simpa [f', hc] using h)
      · exact hp.supp a b hc
    · simp only [f', sum_sub_distrib, ← mul_sum, hf.cons a ha hb, hp.cons a ha hb]
  -- `f'` has fewer nonzero arcs: none outside those of `f`, and not the arc `i₀`
  have h1 : pathVec w L (w i₀) (w (i₀ + 1)) = 1 :=
    le_antisymm (pathVec_le_one rank hrank hw _ _)
      (Nat.one_le_cast.2 (card_pos.2 ⟨i₀, by simp [hi₀]⟩))
  have hcard : (univ.filter fun e : N × N => f' e.1 e.2 ≠ 0).card <
      (univ.filter fun e : N × N => f e.1 e.2 ≠ 0).card := by
    refine card_lt_card ⟨fun e he => ?_, fun hs => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at he ⊢
      exact fun h => he (by simp [f', h, hz _ _ h])
    · have := hs (show (w i₀, w (i₀ + 1)) ∈ univ.filter fun e : N × N => f e.1 e.2 ≠ 0 by
        simpa using hm.ne')
      simp [f', h1, m] at this
  obtain ⟨n, ms, ws, Ls, hms, hws, hsum⟩ := ih _ (hk ▸ hcard) hf' rfl
  refine ⟨n + 1, Fin.cons m ms, Fin.cons w ws, Fin.cons L Ls, Fin.cases hm.le hms,
    Fin.cases hw hws, fun a b => ?_⟩
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← hsum, f']
  ring

end Graph

/-! ## The graph of strictly convex chains -/

/-- Nodes of the chain graph. -/
inductive Node (T : ℕ) where
  | src
  | snk
  | start (b : Fin T)
  | edge (a b : Fin T)
  deriving DecidableEq, Fintype

variable {T : ℕ} (P : Fin T → Fin 2 → ℝ)

/-- `a → b` may be an edge of a chain: `X` increases and `Y` decreases. -/
def Down (a b : Fin T) : Prop := P a 0 < P b 0 ∧ P b 1 < P a 1

/-- Arcs of the chain graph. -/
def Arc : Node T → Node T → Prop
  | .src, .snk => True
  | .src, .start _ => True
  | .start a, .edge a' b => a' = a ∧ Down P a b
  | .edge a b, .edge b' c => b' = b ∧ Down P b c ∧ 0 < cross P a b c
  | .start _, .snk => True
  | .edge _ _, .snk => True
  | _, _ => False

/-- Left slab of `b`, outside the region: left of `b`, or straight below it. -/
noncomputable def leftOut (b : Fin T) : Finset (Fin T) :=
  univ.filter fun q => q ≠ b ∧ (P q 0 < P b 0 ∨ (P q 0 = P b 0 ∧ P q 1 < P b 1))

/-- Left slab of `b`, on the boundary: the vertical ray above `b`. -/
noncomputable def leftBnd (b : Fin T) : Finset (Fin T) :=
  univ.filter fun q => q ≠ b ∧ P q 0 = P b 0 ∧ P b 1 ≤ P q 1

/-- Slab `X a < X q ≤ X b` of the edge `a b`, strictly below the line `a b`. -/
noncomputable def edgeOut (a b : Fin T) : Finset (Fin T) :=
  univ.filter fun q => q ≠ b ∧ P a 0 < P q 0 ∧ P q 0 ≤ P b 0 ∧ cross P a b q < 0

/-- Slab of the edge `a b`, on the line `a b`. -/
noncomputable def edgeBnd (a b : Fin T) : Finset (Fin T) :=
  univ.filter fun q => q ≠ b ∧ P a 0 < P q 0 ∧ P q 0 ≤ P b 0 ∧ cross P a b q = 0

/-- Right slab of `b`, outside the region: right of `b` and lower. -/
noncomputable def rightOut (b : Fin T) : Finset (Fin T) :=
  univ.filter fun q => P b 0 < P q 0 ∧ P q 1 < P b 1

/-- Right slab of `b`, on the boundary: the horizontal ray right of `b`. -/
noncomputable def rightBnd (b : Fin T) : Finset (Fin T) :=
  univ.filter fun q => P b 0 < P q 0 ∧ P q 1 = P b 1

/-- The set `Out` carried by the arc `u → v`. -/
noncomputable def Out : Node T → Node T → Finset (Fin T)
  | .src, .snk => univ
  | _, .start b => leftOut P b
  | .start a, .edge _ b => edgeOut P a b
  | .edge _ a, .edge _ b => edgeOut P a b
  | .start b, .snk => rightOut P b
  | .edge _ b, .snk => rightOut P b
  | _, _ => ∅

/-- The set `Bnd` carried by the arc `u → v`. -/
noncomputable def Bnd : Node T → Node T → Finset (Fin T)
  | _, .start b => leftBnd P b
  | .start a, .edge _ b => edgeBnd P a b
  | .edge _ a, .edge _ b => edgeBnd P a b
  | .start b, .snk => rightBnd P b
  | .edge _ b, .snk => rightBnd P b
  | _, _ => ∅

/-- Union of the sets `Out` along a path. -/
noncomputable def pathOut (w : ℕ → Node T) (L : ℕ) : Finset (Fin T) :=
  (range L).biUnion fun i => Out P (w i) (w (i + 1))

/-- Union of the sets `Bnd` along a path. -/
noncomputable def pathBnd (w : ℕ → Node T) (L : ℕ) : Finset (Fin T) :=
  (range L).biUnion fun i => Bnd P (w i) (w (i + 1))

/-- `1_S` as a vector. -/
noncomputable def ind (S : Finset (Fin T)) : Fin T → ℝ := (S : Set (Fin T)).indicator 1

/-- Boundary points are free in the weak mode (`β = 1`) and excluded in the strict mode
(`β = 0`). -/
def beta (b : Bool) : ℝ := if b then 0 else 1

/-! ## Paths are chains -/

/-- The path of the chain `v 0, …, v k`: `src, start v₀, edge v₀ v₁, …, edge v_{k-1} v_k, snk`. -/
def chainPath (v : ℕ → Fin T) (k : ℕ) : ℕ → Node T
  | 0 => .src
  | 1 => .start (v 0)
  | j + 2 => if j < k then .edge (v j) (v (j + 1)) else .snk

/-- The arcs of the chain path carry the left slab of `v 0`, the slabs of the edges and the right
slab of `v k`. -/
theorem chainPath_sets (v : ℕ → Fin T) (k : ℕ) :
    (Out P (chainPath v k 0) (chainPath v k 1) = leftOut P (v 0) ∧
      Bnd P (chainPath v k 0) (chainPath v k 1) = leftBnd P (v 0)) ∧
    (∀ j < k, Out P (chainPath v k (j + 1)) (chainPath v k (j + 2)) = edgeOut P (v j) (v (j + 1)) ∧
      Bnd P (chainPath v k (j + 1)) (chainPath v k (j + 2)) = edgeBnd P (v j) (v (j + 1))) ∧
    (Out P (chainPath v k (k + 1)) (chainPath v k (k + 2)) = rightOut P (v k) ∧
      Bnd P (chainPath v k (k + 1)) (chainPath v k (k + 2)) = rightBnd P (v k)) := by
  refine ⟨by simp [chainPath, Out, Bnd], fun j hj => ?_, ?_⟩
  · rcases j with _ | j
    · simp [chainPath, Out, Bnd, hj]
    · simp [chainPath, Out, Bnd, hj, Nat.lt_of_succ_lt hj]
  · rcases k with _ | k <;> simp [chainPath, Out, Bnd]

/-- The last vertex of a node (`d` for `src`, `snk`). -/
def Node.last (d : Fin T) : Node T → Fin T
  | .start b => b
  | .edge _ b => b
  | _ => d

/-- **Paths are chains.** A source–sink path is either `src → snk` or the path of a strictly
convex chain. -/
theorem path_cases {w : ℕ → Node T} {L : ℕ} (hw : IsPath (Arc P) .src .snk w L) :
    (L = 1 ∧ w 1 = .snk) ∨ ∃ (v : ℕ → Fin T) (k : ℕ), IsChain P v k ∧ L = k + 2 ∧
      ∀ i ≤ k + 2, w i = chainPath v k i := by
  -- the node `w (j + 2)` is an edge starting at the last vertex of `w (j + 1)`
  have step : ∀ d j, j + 2 < L →
      ∃ c, w (j + 2) = .edge ((w (j + 1)).last d) c ∧ Down P ((w (j + 1)).last d) c := by
    intro d j hL
    have h0 := hw.step j (by omega)
    have h1 := hw.step (j + 1) (by omega)
    have h2 := hw.step (j + 2) hL
    cases hx : w j <;> cases hy : w (j + 1) <;> cases hz : w (j + 2) <;>
      simp_all [Arc, Node.last]
  have hL0 : L ≠ 0 := by rintro rfl; simpa using hw.start.symm.trans hw.stop
  -- the first arc goes to `snk` or to `start b`
  obtain h1' | ⟨b, h1'⟩ : w 1 = .snk ∨ ∃ b, w 1 = .start b := by
    have := hw.step 0 (by omega)
    cases hx : w 1 <;> simp_all [Arc, hw.start]
  · refine .inl ⟨?_, h1'⟩
    by_contra hne -- the path would continue from `snk`
    cases hx : w 2 <;> simpa [h1', hx, Arc] using hw.step 1 (by omega)
  · right
    have hL1 : L ≠ 1 := by rintro rfl; simpa [h1'] using hw.stop
    -- the chain is `v j = last (w (j+1))`
    let v : ℕ → Fin T := fun j => (w (j + 1)).last b
    have hedge : ∀ j, j + 2 < L →
        w (j + 2) = .edge (v j) (v (j + 1)) ∧ Down P (v j) (v (j + 1)) := by
      intro j hj
      obtain ⟨c, hc, hd⟩ := step b j hj
      simpa [v, hc, Node.last] using hd
    refine ⟨v, L - 2, ⟨fun j hj => (hedge j (by omega)).2.1,
      fun j hj => (hedge j (by omega)).2.2, ?_⟩, by omega, ?_⟩
    · -- convexity from the arcs `edge → edge`
      intro j hj
      have h := hw.step (j + 2) (by omega)
      rw [(hedge j (by omega)).1, (hedge (j + 1) (by omega)).1] at h
      simpa [Arc] using h.2.2
    · intro i hi
      rcases i with _ | _ | j
      · simpa [chainPath] using hw.start
      · simp [chainPath, v, h1', Node.last]
      · by_cases hj : j < L - 2
        · simp [chainPath, hj, (hedge j (by omega)).1]
        · have : j + 2 = L := by omega
          simp [chainPath, hj, this, hw.stop]

/-- The chain path of a strictly convex chain is a source–sink path. -/
theorem isPath_chainPath {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) :
    IsPath (Arc P) .src .snk (chainPath v k) (k + 2) := by
  refine ⟨rfl, by simp [chainPath], fun i hi => ?_⟩
  rcases i with _ | _ | j
  · simp [chainPath, Arc]
  · rcases k with _ | k
    · simp [chainPath, Arc]
    · simp [chainPath, Arc, Down, hc.xlt 0 (by omega), hc.ylt 0 (by omega)]
  · by_cases h : j + 1 < k
    · simp [chainPath, Arc, Down, h, show j < k by omega, hc.xlt (j + 1) h, hc.ylt (j + 1) h,
        hc.convex j h]
    · simp [chainPath, Arc, h, show j < k by omega]

/-! ## Locality: every point lies in exactly one slab -/

/-- `q` lies in the slab of the arc `i` of the chain path: `X q ≤ X (v i)` unless `i = k + 1`,
and `X (v (i - 1)) < X q` unless `i = 0`. -/
def InSlab (v : ℕ → Fin T) (k i : ℕ) (q : Fin T) : Prop :=
  (i ≤ k → P q 0 ≤ P (v i) 0) ∧ (0 < i → P (v (i - 1)) 0 < P q 0)

/-- `X` strictly increases along a chain. -/
theorem chain_x_lt {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) {j i : ℕ} (hji : j < i)
    (hik : i ≤ k) : P (v j) 0 < P (v i) 0 := by
  induction i, hji using Nat.le_induction with
  | base => exact hc.xlt j (by omega)
  | succ i _ ih => exact (ih (by omega)).trans (hc.xlt i (by omega))

/-- The slabs `X ≤ X v₀`, `X v_j < X ≤ X v_{j+1}`, `X > X v_k` partition the plane. -/
theorem existsUnique_slab {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) (q : Fin T) :
    (∃ i ≤ k + 1, InSlab P v k i q) ∧
      ∀ i ≤ k + 1, ∀ j ≤ k + 1, InSlab P v k i q → InSlab P v k j q → i = j := by
  refine ⟨?_, fun i hi j hj hsi hsj => ?_⟩
  · -- the first `i` with `X q ≤ X (v i)`, or `k + 1` if there is none
    have hex : ∃ i, i = k + 1 ∨ P q 0 ≤ P (v i) 0 := ⟨k + 1, Or.inl rfl⟩
    exact ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl),
      fun h => (Nat.find_spec hex).resolve_left (by omega),
      fun h => not_le.1 fun h' => Nat.find_min hex (Nat.sub_lt h one_pos) (Or.inr h')⟩
  · by_contra hne
    -- WLOG `i < j`; then `X q ≤ X (v i) ≤ X (v (j - 1)) < X q`
    wlog h : i < j generalizing i j
    · exact this j hj i hi hsj hsi (Ne.symm hne) (by omega)
    have h1 := hsi.1 (by omega)
    have h2 := hsj.2 (by omega)
    rcases (show i ≤ j - 1 by omega).lt_or_eq with h' | rfl
    · linarith [chain_x_lt P hc h' (by omega)]
    · linarith

/-- The sets of an arc lie in its slab. -/
theorem inSlab_of_mem {v : ℕ → Fin T} {k i : ℕ} (hi : i ≤ k + 1) {q : Fin T}
    (hq : q ∈ Out P (chainPath v k i) (chainPath v k (i + 1)) ∪
      Bnd P (chainPath v k i) (chainPath v k (i + 1))) : InSlab P v k i q := by
  obtain ⟨⟨hO0, hB0⟩, hE, ⟨hOk, hBk⟩⟩ := chainPath_sets P v k
  obtain rfl | ⟨j, rfl⟩ : i = 0 ∨ ∃ j, i = j + 1 := by cases i <;> simp
  · -- left slab of `v 0`
    rw [hO0, hB0] at hq
    simp only [leftOut, leftBnd, mem_union, mem_filter, mem_univ, true_and] at hq
    refine ⟨fun _ => ?_, fun h => absurd h (lt_irrefl 0)⟩
    rcases hq with ⟨_, h | h⟩ | ⟨_, h, _⟩
    exacts [h.le, h.1.le, h.le]
  rcases (show j ≤ k by omega).lt_or_eq with hj | rfl
  · -- slab of the edge `v j → v (j + 1)`
    rw [show j + 1 + 1 = j + 2 from rfl, (hE j hj).1, (hE j hj).2] at hq
    simp only [edgeOut, edgeBnd, mem_union, mem_filter, mem_univ, true_and] at hq
    refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> rcases hq with h | h
    exacts [h.2.2.1, h.2.2.1, h.2.1, h.2.1]
  · -- right slab of `v k`
    rw [show j + 1 + 1 = j + 2 from rfl, hOk, hBk] at hq
    simp only [rightOut, rightBnd, mem_union, mem_filter, mem_univ, true_and] at hq
    refine ⟨fun h => by omega, fun _ => ?_⟩
    rcases hq with h | h <;> simpa using h.1

/-- **Locality.** Inside its slab, a point is in `Out` of the arc iff it is outside `C(V)`, and in
`Bnd` iff it is a boundary point of `C(V)` other than a vertex (`inHull_iff_of_left`,
`inHull_iff_of_piece`, `inHull_iff_of_right`). -/
theorem mem_iff_of_inSlab {v : ℕ → Fin T} {k i : ℕ} (hc : IsChain P v k) (hi : i ≤ k + 1)
    {q : Fin T} (hq : InSlab P v k i q) :
    (q ∈ Out P (chainPath v k i) (chainPath v k (i + 1)) ↔ ¬ InHull P v k q) ∧
      (q ∈ Bnd P (chainPath v k i) (chainPath v k (i + 1)) ↔
        (∀ l ≤ k, q ≠ v l) ∧ InHull P v k q ∧ ¬ InInt P v k q) := by
  obtain ⟨⟨hO0, hB0⟩, hE, ⟨hOk, hBk⟩⟩ := chainPath_sets P v k
  -- a vertex `v l` lies in the slab `l`, so the only vertex in the slab `i` is `v i`
  have hv : ∀ l ≤ k, q = v l → l = i := fun l hl h =>
    (existsUnique_slab P hc q).2 l (by omega) i hi (h ▸ ⟨fun _ => le_rfl, fun h0 => by
      simpa [Nat.sub_add_cancel h0] using hc.xlt (l - 1) (by omega)⟩) hq
  obtain rfl | ⟨j, rfl⟩ : i = 0 ∨ ∃ j, i = j + 1 := by cases i <;> simp
  · -- left slab: `InHull` is the vertical ray above `v 0`, no other vertex is here
    have hx : P q 0 ≤ P (v 0) 0 := hq.1 (by omega)
    obtain ⟨hH, hI⟩ := inHull_iff_of_left hc hx
    rw [hO0, hB0]
    simp only [leftOut, leftBnd, mem_filter, mem_univ, true_and, hH, hI, not_false_eq_true,
      and_true]
    refine ⟨?_, ⟨fun ⟨h0, h⟩ => ⟨fun l hl h' => h0 (hv l hl h' ▸ h'), h⟩,
      fun ⟨h0, h⟩ => ⟨h0 0 (by omega), h⟩⟩⟩
    by_cases h0 : q = v 0 <;> rcases hx.lt_or_eq with h | h <;> simp [h0, h, ne_of_lt]
  rcases (show j ≤ k by omega).lt_or_eq with hj | rfl
  · -- edge slab: the sign of `cross`; the only vertex here is `v (j + 1)`, on the line
    have hx1 : P (v j) 0 < P q 0 := by simpa using hq.2 (by omega)
    have hx2 : P q 0 ≤ P (v (j + 1)) 0 := hq.1 (by omega)
    have hc0 : cross P (v j) (v (j + 1)) (v (j + 1)) = 0 := by unfold cross; ring
    obtain ⟨hH, hI⟩ := inHull_iff_of_piece hc hj hx1 hx2
    rw [show j + 1 + 1 = j + 2 from rfl, (hE j hj).1, (hE j hj).2]
    simp only [edgeOut, edgeBnd, mem_filter, mem_univ, true_and, hH, hI, hx1, hx2, not_le,
      not_lt]
    refine ⟨?_, ⟨fun ⟨h0, h⟩ => ⟨fun l hl h' => h0 (hv l hl h' ▸ h'), h.ge, h.le⟩,
      fun ⟨h0, h1, h2⟩ => ⟨h0 (j + 1) (by omega), le_antisymm h2 h1⟩⟩⟩
    by_cases h0 : q = v (j + 1) <;> simp [h0, hc0]
  · -- right slab: `InHull` is `Y q ≥ Y (v k)`, no vertex is here
    have hx : P (v j) 0 < P q 0 := by simpa using hq.2 (by omega)
    obtain ⟨hH, hI⟩ := inHull_iff_of_right hc hx
    rw [show j + 1 + 1 = j + 2 from rfl, hOk, hBk]
    simp only [rightOut, rightBnd, mem_filter, mem_univ, true_and, hH, hI, hx, not_le, not_lt]
    exact ⟨fun h => ⟨fun l hl h' => by have := hv l hl h'; omega, h.ge, h.le⟩,
      fun ⟨_, h1, h2⟩ => le_antisymm h2 h1⟩

/-- The sets `Out(π)`, `Bnd(π)` of a chain path: the outside of `C(V)` and its boundary without
the vertices. -/
theorem chainPath_out_bnd {v : ℕ → Fin T} {k : ℕ} (hc : IsChain P v k) :
    pathOut P (chainPath v k) (k + 2) = univ.filter (fun q => ¬ InHull P v k q) ∧
      pathBnd P (chainPath v k) (k + 2) =
        univ.filter (fun q => (∀ l ≤ k, q ≠ v l) ∧ InHull P v k q ∧ ¬ InInt P v k q) := by
  -- `q` is in the sets of some arc iff it is in the sets of the arc of its own slab
  constructor <;> ext q <;>
    simp only [pathOut, pathBnd, mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
  · constructor
    · rintro ⟨i, hi, h⟩
      exact ((mem_iff_of_inSlab P hc (by omega)
        (inSlab_of_mem P (by omega) (mem_union_left _ h))).1).1 h
    · intro h
      obtain ⟨i, hi, hs⟩ := (existsUnique_slab P hc q).1
      exact ⟨i, by omega, ((mem_iff_of_inSlab P hc hi hs).1).2 h⟩
  · constructor
    · rintro ⟨i, hi, h⟩
      exact ((mem_iff_of_inSlab P hc (by omega)
        (inSlab_of_mem P (by omega) (mem_union_right _ h))).2).1 h
    · intro h
      obtain ⟨i, hi, hs⟩ := (existsUnique_slab P hc q).1
      exact ⟨i, by omega, ((mem_iff_of_inSlab P hc hi hs).2).2 h⟩

/-- A path agreeing with `chainPath v k` on `[0, k + 2]` has the same `Out` and `Bnd`. -/
theorem path_congr {w : ℕ → Node T} {v : ℕ → Fin T} {k : ℕ}
    (hwv : ∀ i ≤ k + 2, w i = chainPath v k i) :
    pathOut P w (k + 2) = pathOut P (chainPath v k) (k + 2) ∧
      pathBnd P w (k + 2) = pathBnd P (chainPath v k) (k + 2) := by
  constructor <;> exact biUnion_congr rfl fun i hi => by
    rw [hwv i (by simp at hi; omega), hwv (i + 1) (by simp at hi; omega)]

/-- **(Weakly) reachable sets are the paths.** `S` is (weakly) reachable iff some source–sink
path has `Out(π) ⊆ S ⊆ Out(π) ∪ β Bnd(π)`: all points outside the region of the chain are in
`S`, all points of its interior are not, boundary points are free in the weak mode and outside
`S` in the strict mode. -/
theorem isReachableB_iff_path (b : Bool) (S : Finset (Fin T)) :
    IsReachableB b P S ↔ ∃ (w : ℕ → Node T) (L : ℕ), IsPath (Arc P) .src .snk w L ∧
      pathOut P w L ⊆ S ∧ S ⊆ pathOut P w L ∪ (if b then ∅ else pathBnd P w L) := by
  rw [isReachableB_iff_chain]
  constructor
  · rintro (rfl | ⟨v, k, hc, hv, hout, hforb⟩)
    · -- `S = univ`: the path `src → snk`
      exact ⟨fun i => if i = 0 then .src else .snk, 1, ⟨by simp, by simp, fun i hi => by
        obtain rfl : i = 0 := by omega
        simp [Arc]⟩, by simp [pathOut, Out], by simp [pathOut, Out]⟩
    · -- a chain: the path `chainPath v k`; a point of `S` in the hull is a boundary point
      obtain ⟨ho, hb⟩ := chainPath_out_bnd P hc
      refine ⟨chainPath v k, k + 2, isPath_chainPath P hc, ?_, fun q hq => ?_⟩
      · simpa [ho, subset_iff] using hout
      · have hf := hforb q
        have hqv : ∀ l ≤ k, q ≠ v l := fun l hl h => hv l hl (h ▸ hq)
        rw [ho, hb]
        cases b <;> simp_all [Forbidden, em']
  · rintro ⟨w, L, hw, h1, h2⟩
    rcases path_cases P hw with ⟨rfl, hs⟩ | ⟨v, k, hc, rfl, hwv⟩
    · -- `src → snk`: `Out = univ`
      exact .inl (eq_univ_of_forall fun q => h1 (by simp [pathOut, hw.start, hs, Out]))
    · -- a chain: vertices and forbidden points are in the hull, not outside nor boundary points
      simp only [(path_congr P hwv).1, (path_congr P hwv).2, (chainPath_out_bnd P hc).1,
        (chainPath_out_bnd P hc).2] at h1 h2
      have hint : ∀ q, InInt P v k q → InHull P v k q := fun q h =>
        ⟨h.1.le, h.2.1.le, fun j hj => (h.2.2 j hj).le⟩
      refine .inr ⟨v, k, hc, fun i hi hS => ?_, fun q hq => h1 (by simpa using hq),
        fun q hq hS => ?_⟩
      · have := h2 hS; cases b <;> simp [inHull_vertex hc hi] at this
        exact this.1 i hi rfl
      · have := h2 hS; cases b <;> simp_all [Forbidden]

/-- **Disjoint slabs.** Along a path the sets `Out` and `Bnd` of different arcs are pairwise
disjoint, and `Out e ∩ Bnd e' = ∅` for all arcs `e, e'` of the path. So
`1_{Out(π)} = Σ_e 1_{Out e}` and `1_{Bnd(π)} = Σ_e 1_{Bnd e}`. -/
theorem path_ind_eq {w : ℕ → Node T} {L : ℕ} (hw : IsPath (Arc P) .src .snk w L) :
    ind (pathOut P w L) = (fun q => ∑ u, ∑ v, pathVec w L u v * ind (Out P u v) q) ∧
      ind (pathBnd P w L) = (fun q => ∑ u, ∑ v, pathVec w L u v * ind (Bnd P u v) q) ∧
      Disjoint (pathOut P w L) (pathBnd P w L) := by
  -- the sets `Out ∪ Bnd` of different arcs are disjoint, and `Out(π) ∩ Bnd(π) = ∅`
  have key : (∀ i ∈ range L, ∀ j ∈ range L, i ≠ j →
      Disjoint (Out P (w i) (w (i + 1)) ∪ Bnd P (w i) (w (i + 1)))
        (Out P (w j) (w (j + 1)) ∪ Bnd P (w j) (w (j + 1)))) ∧
      Disjoint (pathOut P w L) (pathBnd P w L) := by
    rcases path_cases P hw with ⟨rfl, h1⟩ | ⟨v, k, hc, rfl, hwv⟩
    · exact ⟨fun i hi j hj hij => by simp at hi hj; omega,
        by simp [pathOut, pathBnd, Out, Bnd, hw.start, h1]⟩
    refine ⟨fun i hi j hj hij => disjoint_left.2 fun q hqi hqj => hij ?_, ?_⟩
    · -- the sets of the arc `i` lie in the slab `i`, and a point lies in a single slab
      simp only [mem_range] at hi hj
      rw [hwv i (by omega), hwv (i + 1) (by omega)] at hqi
      rw [hwv j (by omega), hwv (j + 1) (by omega)] at hqj
      exact (existsUnique_slab P hc q).2 i (by omega) j (by omega)
        (inSlab_of_mem P (by omega) hqi) (inSlab_of_mem P (by omega) hqj)
    · rw [(path_congr P hwv).1, (path_congr P hwv).2, (chainPath_out_bnd P hc).1,
        (chainPath_out_bnd P hc).2]
      exact disjoint_left.2 fun q h h' => by simp at h h'; exact h h'.2.1
  -- the indicator of a union along the path of subsets of `Out ∪ Bnd` is the sum over its arcs
  have hsum : ∀ F : Node T → Node T → Finset (Fin T), (∀ u v, F u v ⊆ Out P u v ∪ Bnd P u v) →
      ind ((range L).biUnion fun i => F (w i) (w (i + 1))) =
        fun q => ∑ u, ∑ v, pathVec w L u v * ind (F u v) q := fun F hF => by
    ext q
    rw [sum_pathVec_mul w L fun u v => ind (F u v) q]
    simpa [ind] using indicator_biUnion_apply (range L)
      (fun i => (F (w i) (w (i + 1)) : Set (Fin T))) (f := 1)
      (fun i hi j hj hij => disjoint_coe.2 ((key.1 i hi j hj hij).mono (hF _ _) (hF _ _))) q
  exact ⟨hsum _ fun _ _ => subset_union_left, hsum _ fun _ _ => subset_union_right, key.2⟩

/-- **The cube is the hull of its vertices.** If `O ∩ B = ∅` and `0 ≤ z ≤ 1_B`, then `1_O + z` is a
nonnegative combination of the indicators `1_{O ∪ B'}`, `B' ⊆ B`. Induction on `B`: for
`B = insert q B₀`, `1_O + z = (1 - z_q)(1_O + z|B₀) + z_q (1_{O ∪ {q}} + z|B₀)`. -/
theorem cube_mem_span (O B : Finset (Fin T)) (hOB : Disjoint O B) (z : Fin T → ℝ)
    (hz0 : ∀ q, 0 ≤ z q) (hz1 : ∀ q, z q ≤ ind B q) :
    (fun q => ind O q + z q) ∈
      PointedCone.span ℝ ((fun B' => ind (O ∪ B')) '' {B' | B' ⊆ B}) := by
  induction B using Finset.induction_on generalizing O z with
  | empty =>
    obtain rfl : z = 0 := funext fun q => le_antisymm (by simpa [ind] using hz1 q) (hz0 q)
    exact PointedCone.subset_span ⟨∅, by simp, by ext; simp⟩
  | insert q B₀ hq ih =>
    obtain ⟨hqO, hOB₀⟩ := Finset.disjoint_insert_right.1 hOB
    -- zero out the `q`-coordinate of `z`
    set z₀ := Function.update z q 0 with hz₀
    have h0 : ∀ r, 0 ≤ z₀ r := fun r => by by_cases h : r = q <;> simp [hz₀, h, hz0]
    have h1 : ∀ r, z₀ r ≤ ind B₀ r := fun r => by
      by_cases h : r = q
      · simp [hz₀, h, ind, Set.indicator_nonneg]
      · simpa [hz₀, h, ind, Set.indicator] using hz1 r
    have hc1 : z q ≤ 1 := by simpa [ind] using hz1 q
    -- `1_O + z = (1 - z_q) (1_O + z₀) + z_q (1_{O ∪ {q}} + z₀)`
    have key : (fun r => ind O r + z r) =
        (⟨1 - z q, by linarith⟩ : NNReal) • (fun r => ind O r + z₀ r) +
        (⟨z q, hz0 q⟩ : NNReal) • (fun r => ind (insert q O) r + z₀ r) := by
      funext r
      by_cases h : r = q
      · subst h; simp [hz₀, ind, hqO]
      · simp [hz₀, ind, Set.indicator, h]; ring
    rw [key]
    -- both endpoints of the edge lie in the span of the big generator set
    refine Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.span_mono ?_ (ih O hOB₀ z₀ h0 h1)))
      (Submodule.smul_mem _ _ (Submodule.span_mono ?_
        (ih (insert q O) (Finset.disjoint_insert_left.2 ⟨hq, hOB₀⟩) z₀ h0 h1)))
    · exact Set.image_mono fun B' h => h.trans (Finset.subset_insert _ _)
    · rintro _ ⟨B', hB', rfl⟩
      exact ⟨insert q B', Finset.insert_subset_insert _ hB',
        by simp [Finset.insert_union, Finset.union_insert]⟩

/-- **The chain graph is acyclic.** `src`, `start`, `edge a b` (by the number of points left of
`b`), `snk` is a rank that grows along every arc. -/
theorem exists_rank : ∃ rank : Node T → ℕ, ∀ u v, Arc P u v → rank u < rank v := by
  let c : Fin T → ℕ := fun b => (univ.filter fun q => P q 0 < P b 0).card
  have hc : ∀ b, c b ≤ T := fun b => (card_filter_le _ _).trans (by simp)
  -- along `edge a b → edge b d` the point `b` joins the points left of the last vertex
  have hlt : ∀ b d, P b 0 < P d 0 → c b < c d := fun b d h => card_lt_card
    ⟨fun q hq => by simp only [mem_filter, mem_univ, true_and] at hq ⊢; linarith,
      fun hs => by simpa using hs (show b ∈ univ.filter fun q => P q 0 < P d 0 by simpa using h)⟩
  refine ⟨fun | .src => 0 | .start _ => 1 | .edge _ b => c b + 2 | .snk => T + 3, ?_⟩
  rintro (_ | _ | _ | ⟨_, a⟩) (_ | _ | _ | ⟨_, b⟩) h <;> simp only [Arc, Down] at h ⊢ <;>
    first | omega | (have := hc a; omega) | (have := hlt a b h.2.1.1; omega)

/-- **Solvability in the plane as a flow LP.** `y` lies in the cone of (weakly) reachable spectra
iff there are a flow `f` from `src` to `snk` and a vector `g` with
`y = Σ_e f_e 1_{Out e} + g` and `0 ≤ g ≤ β Σ_e f_e 1_{Bnd e}`. -/
theorem mem_indicatorCone_iff_flow (b : Bool) (y : Fin T → ℝ) :
    y ∈ indicatorCone {S | IsReachableB b P S} ↔
      ∃ (f : Node T → Node T → ℝ) (g : Fin T → ℝ), IsFlow (Arc P) .src .snk f ∧
        (∀ q, 0 ≤ g q) ∧
        (∀ q, g q ≤ beta b * ∑ u, ∑ v, f u v * ind (Bnd P u v) q) ∧
        ∀ q, y q = ∑ u, ∑ v, f u v * ind (Out P u v) q + g q := by
  -- indicators: `0 ≤ 1_S` and `1_{β B} = β 1_B`
  have hind0 : ∀ (S : Finset (Fin T)) q, 0 ≤ ind S q := fun S q => Set.indicator_nonneg (by simp) q
  have hbetaInd : ∀ (B : Finset (Fin T)) q, ind (if b then ∅ else B) q = beta b * ind B q := by
    cases b <;> simp [beta, ind]
  -- weights of paths pass to arc sums: `Σ_e (Σ_i m_i π_i)_e F_e = Σ_i m_i Σ_e (π_i)_e F_e`
  have hswap : ∀ {ι : Type} [Fintype ι] (m : ι → ℝ) (π : ι → Node T → Node T → ℝ)
      (F : Node T → Node T → ℝ),
      ∑ u, ∑ v, (∑ i, m i * π i u v) * F u v = ∑ i, m i * ∑ u, ∑ v, π i u v * F u v := by
    intro ι _ m π F; simp only [sum_mul, mul_sum, mul_assoc, sum_comm (γ := ι)]
  constructor
  · -- (⇒) take a path `π_S` for every set of the combination, sum them up
    intro hy
    obtain ⟨m, hm0, hmA, -, rfl⟩ := exists_coef_of_mem_indicatorCone hy
    -- `m_S 1_S = m_S (1_{Out(π_S)} + 1_{S \ Out(π_S)})` and `S \ Out(π_S) ⊆ β Bnd(π_S)`
    have hpath : ∀ S : Finset (Fin T), ∃ (w : ℕ → Node T) (L : ℕ), IsPath (Arc P) .src .snk w L ∧
        ∀ q, m S * ind S q = m S * (ind (pathOut P w L) q + ind (S \ pathOut P w L) q) ∧
          m S * ind (S \ pathOut P w L) q ≤ m S * ind (if b then ∅ else pathBnd P w L) q := by
      intro S
      by_cases h : m S = 0  -- then any path will do, e.g. the one of `univ`
      · obtain ⟨w, L, hw, -⟩ := (isReachableB_iff_path P b univ).1
          ((isReachableB_iff_chain (P := P) b univ).2 (.inl rfl))
        exact ⟨w, L, hw, by simp [h]⟩
      obtain ⟨w, L, hw, h1, h2⟩ := (isReachableB_iff_path P b S).1 (hmA S h)
      refine ⟨w, L, hw, fun q => ⟨?_, mul_le_mul_of_nonneg_left ?_ (hm0 S)⟩⟩
      · by_cases hq : q ∈ pathOut P w L <;> simp [ind, Set.indicator_apply, hq, @h1 q]
      · exact Set.indicator_le_indicator_of_subset (coe_subset.2 (sdiff_le_iff.2 h2 : S \ _ ≤ _))
          (by simp) q
    choose w L hw hS using hpath
    -- a nonnegative combination of path flows is a flow
    have hflow : IsFlow (Arc P) .src .snk fun u v => ∑ S, m S * pathVec (w S) (L S) u v := by
      refine ⟨fun u v => sum_nonneg fun S _ => mul_nonneg (hm0 S) (Nat.cast_nonneg _),
        fun u v h => ?_, fun u hs hk => ?_⟩
      · obtain ⟨S, -, hS⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (isFlow_pathVec (hw S)).supp u v (right_ne_zero_of_mul hS)
      · simp only [sum_comm (γ := Node T), ← mul_sum, (isFlow_pathVec (hw _)).cons u hs hk]
    refine ⟨_, fun q => ∑ S, m S * ind (S \ pathOut P (w S) (L S)) q, hflow,
      fun q => sum_nonneg fun S _ => mul_nonneg (hm0 S) (hind0 _ q), fun q => ?_, fun q => ?_⟩ <;>
      simp only [hswap, ← fun S => congrFun (path_ind_eq P (hw S)).1,
        ← fun S => congrFun (path_ind_eq P (hw S)).2.1, mul_sum, ← sum_add_distrib, sum_apply]
    · exact sum_le_sum fun S _ => (hS S q).2.trans_eq (by rw [hbetaInd, mul_left_comm])
    · exact sum_congr rfl fun S _ => (hS S q).1.trans (mul_add ..)
  · -- (⇐) decompose the flow into paths `π_i`; each contributes `1_{Out(π_i)} + z_i`
    rintro ⟨f, g, hf, hg0, hgB, hy⟩
    obtain ⟨n, m, w, L, hm0, hw, hfm⟩ := flow_decomposition _ (exists_rank P).choose_spec
      (fun u => by cases u <;> simp [Arc]) (fun v => by cases v <;> simp [Arc]) hf
    obtain rfl : f = fun u v => ∑ i, m i * pathVec (w i) (L i) u v := funext₂ hfm
    simp only [hswap, ← fun i => congrFun (path_ind_eq P (hw i)).1,
      ← fun i => congrFun (path_ind_eq P (hw i)).2.1] at hgB hy
    -- proportional split of `g` over the boundaries: `H = Σ_i m_i 1_{Bnd(π_i)}`,
    -- `z_i = 1_{Bnd(π_i)} · g / H`, with `0 ≤ g / H ≤ β`
    set H : Fin T → ℝ := fun q => ∑ i, m i * ind (pathBnd P (w i) (L i)) q
    set z : Fin n → Fin T → ℝ := fun i q => ind (pathBnd P (w i) (L i)) q * (g q / H q)
    have hH0 : ∀ q, 0 ≤ H q := fun q => sum_nonneg fun i _ => mul_nonneg (hm0 i) (hind0 _ q)
    have hratio : ∀ q, g q / H q ≤ beta b := fun q =>
      div_le_of_le_mul₀ (hH0 q) (by cases b <;> simp [beta]) (mul_comm (H q) _ ▸ hgB q)
    have hz : ∀ q, ∑ i, m i * z i q = g q := fun q => by
      simp only [z, ← mul_assoc, ← sum_mul]; rw [mul_comm]
      exact div_mul_cancel_of_imp fun h => le_antisymm (by simpa [H, h] using hgB q) (hg0 q)
    rw [show y = ∑ i, m i • fun q => ind (pathOut P (w i) (L i)) q + z i q from
      funext fun q => by simp [hy q, ← hz q, mul_add, sum_add_distrib]]
    refine Submodule.sum_mem _ fun i _ => PointedCone.smul_mem _ (hm0 i) ?_
    -- `1_{Out(π_i)} + z_i` is in the cube spanned by reachable `Out(π_i) ∪ B'`, `B' ⊆ β Bnd(π_i)`
    refine Submodule.span_mono ?_ (cube_mem_span _ (if b then ∅ else pathBnd P (w i) (L i))
      (by cases b <;> simp [(path_ind_eq P (hw i)).2.2]) (z i)
      (fun q => mul_nonneg (hind0 _ q) (div_nonneg (hg0 q) (hH0 q))) (fun q =>
        (mul_le_mul_of_nonneg_left (hratio q) (hind0 _ q)).trans_eq (by rw [hbetaInd, mul_comm])))
    exact fun _ ⟨B', hB', e⟩ => ⟨_, (isReachableB_iff_path P b _).2
      ⟨w i, L i, hw i, subset_union_left, union_subset_union_right hB'⟩, e⟩

end NeoTiling.PolyHardness
