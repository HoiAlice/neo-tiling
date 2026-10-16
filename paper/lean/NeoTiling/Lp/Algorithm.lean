import NeoTiling.Lp.Reduction

/-!
# The polyblock algorithm: correctness and termination

An abstract monotonic-optimization algorithm minimizing a monotone cost `f` over an up-closed set
`H` inside the product box `∏ j, [0, Mv j]`, given a membership oracle `O` and a master-problem
oracle. The oracles are hypotheses (fields of `Problem`), not programs.

One step (`step`), while the relative gap is above `ε`: the master returns a point `v` satisfying
all polyblock cuts and a lower bound `lb`; the oracle is queried at `w = min (v + τ 1, Mv)`
(coordinatewise), `τ = (UB - LB) / (2 L)`. YES improves `UB`, NO adds `w` as a polyblock cut.

* `run_correct` (A): `LB ≤ OPT ≤ UB`, the best point lies in `H ∩ box` and costs `UB`, at every
  step.
* `run_stops` (B): if `0 < OPT` and `0 < ε`, the run stops after an explicit number of steps.
* `boxRun_correct` (C): for the box query (`H` = relative half-widths passing `BoxFeasible`,
  cost a monotone function of `lpPow p c (max α β)`), `UB` is the cost of prices `Q` at which `y`
  is weakly solvable, and `LB` is a lower bound for the relative cost of all such `Q` whose
  half-widths lie in the box. The fields `upClosed` and `reduce` are discharged by
  `boxFeasible_upClosed` and `box_reduce`.

The polyblock cuts are strict (`ẑ j < z j`): this is what makes NO-points separated even where
the query point is clipped to `Mv`. The master spec is required only on a cut region containing a
one-signed point, its lower bound only over the one-signed points (for the box: one sign per
year, `α t = 0` or `β t = 0`, as the sign rows of the implemented master), and the relative gap
only when `lb < UB`, so an exact master satisfies it. Cover
cuts of the real
algorithm are not modelled: they are extra constraints valid on `H ∩ box`, and the proofs would go
through unchanged if the master respected them too.
-/

namespace NeoTiling.L1Perturbation.Polyblock

open Real

variable {ι : Type*} [Fintype ι]

/-- The product box `∏ j, [0, Mv j]`. -/
def box (Mv : ι → ℝ) : Set (ι → ℝ) := {z | ∀ j, 0 ≤ z j ∧ z j ≤ Mv j}

/-- `z` satisfies the polyblock cuts `cs`: it exceeds every cut point in some coordinate. -/
def Sat (cs : List (ι → ℝ)) (z : ι → ℝ) : Prop := ∀ c ∈ cs, ∃ j, c j < z j

/-- The abstract problem: an up-closed set `H` in the box `∏ j, [0, Mv j]` containing the top
corner `Mv`, a
monotone cost `f` with Lipschitz constant `L` along the diagonal, a membership oracle `O`, a
class `OneSigned` of points that represents `H ∩ box` (`reduce`: every point of `H ∩ box` is
dominated in cost by a one-signed one), and a master oracle: on cut points `cs` (with a one-signed
point in the cut region) and the current `UB` it returns a point `v` of the cut region and a lower
bound `lb` for `f` on the one-signed points of the cut region, with relative gap
`f v - lb ≤ (UB - lb) / 4` when `lb < UB`. -/
structure Problem (ι : Type*) [Fintype ι] where
  Mv : ι → ℝ
  H : Set (ι → ℝ)
  f : (ι → ℝ) → ℝ
  L : ℝ
  O : (ι → ℝ) → Bool
  master : List (ι → ℝ) → ℝ → (ι → ℝ) × ℝ
  OneSigned : (ι → ℝ) → Prop
  M_pos : ∀ j, 0 < Mv j
  upClosed : ∀ z w, z ∈ H → z ≤ w → w ∈ box Mv → w ∈ H
  top_mem : Mv ∈ H
  f_nonneg : ∀ z, 0 ≤ f z
  f_mono : Monotone f
  L_pos : 0 < L
  f_shift : ∀ v (a : ℝ), 0 ≤ a → f (v + fun _ => a) ≤ f v + a * L
  O_spec : ∀ z ∈ box Mv, (O z = true ↔ z ∈ H)
  reduce : ∀ z ∈ H ∩ box Mv, ∃ z' ∈ H ∩ box Mv, OneSigned z' ∧ f z' ≤ f z
  master_box : ∀ cs UB, (∃ z ∈ box Mv, Sat cs z ∧ OneSigned z) → (master cs UB).1 ∈ box Mv
  master_sat : ∀ cs UB, (∃ z ∈ box Mv, Sat cs z ∧ OneSigned z) → Sat cs (master cs UB).1
  master_lb : ∀ cs UB, (∃ z ∈ box Mv, Sat cs z ∧ OneSigned z) →
    ∀ z ∈ box Mv, Sat cs z → OneSigned z → (master cs UB).2 ≤ f z
  master_gap : ∀ cs UB, (∃ z ∈ box Mv, Sat cs z ∧ OneSigned z) → (master cs UB).2 < UB →
    f (master cs UB).1 ≤ (master cs UB).2 + (UB - (master cs UB).2) / 4

/-- The state of the run: polyblock cut points, bounds, best point found. -/
structure State (ι : Type*) where
  cuts : List (ι → ℝ)
  UB : ℝ
  LB : ℝ
  best : ι → ℝ

/-- The run has stopped: relative gap at most `ε`. -/
abbrev Stopped (ε : ℝ) (s : State ι) : Prop := s.UB - s.LB ≤ ε * s.UB

namespace Problem

variable (P : Problem ι)

/-- The top corner of the box. -/
def top : ι → ℝ := P.Mv

/-- The optimal value `inf f` over `H ∩ box`. -/
noncomputable def opt : ℝ := sInf (P.f '' (P.H ∩ box P.Mv))

/-- The master point at state `s`. -/
noncomputable def masterPt (s : State ι) : ι → ℝ := (P.master s.cuts s.UB).1

/-- The step length `τ = (UB - LB) / (2 L)`. -/
noncomputable def tau (s : State ι) : ℝ := (s.UB - s.LB) / (2 * P.L)

/-- The query point `min (v + τ 1, Mv)`, coordinatewise. -/
noncomputable def query (s : State ι) : ι → ℝ := fun j => min (P.masterPt s j + P.tau s) (P.Mv j)

/-- Step 0: query `0`. YES: `0` is optimal, gap `0`. NO: `0` is the first cut. -/
noncomputable def init : State ι :=
  if P.O 0 then ⟨[], P.f 0, P.f 0, 0⟩ else ⟨[0], P.f P.top, 0, P.top⟩

/-- One step of the algorithm. -/
noncomputable def step (ε : ℝ) (s : State ι) : State ι :=
  if Stopped ε s then s else
    let lb := (P.master s.cuts s.UB).2
    let w := P.query s
    if P.O w then ⟨s.cuts, min s.UB (P.f w), max s.LB lb, if P.f w < s.UB then w else s.best⟩
    else ⟨w :: s.cuts, s.UB, max s.LB lb, s.best⟩

/-- The state after `n` steps. -/
noncomputable def run (ε : ℝ) (n : ℕ) : State ι := (P.step ε)^[n] P.init

/-- The invariants of the run. -/
structure Inv (s : State ι) : Prop where
  lb_le : s.LB ≤ P.opt
  best_mem : s.best ∈ P.H
  best_box : s.best ∈ box P.Mv
  ub_eq : P.f s.best = s.UB
  cuts : ∀ c ∈ s.cuts, c ∉ P.H ∧ c ∈ box P.Mv

/-! ### (A) Invariants -/

theorem top_box : P.top ∈ box P.Mv := fun j => ⟨(P.M_pos j).le, le_rfl⟩

theorem opt_le {z : ι → ℝ} (hz : z ∈ P.H) (hb : z ∈ box P.Mv) : P.opt ≤ P.f z :=
  csInf_le ⟨0, by rintro _ ⟨x, -, rfl⟩; exact P.f_nonneg x⟩ ⟨z, ⟨hz, hb⟩, rfl⟩

theorem le_opt {a : ℝ} (h : ∀ z ∈ P.H, z ∈ box P.Mv→ a ≤ P.f z) : a ≤ P.opt :=
  le_csInf ⟨_, P.top, ⟨P.top_mem, P.top_box⟩, rfl⟩ (by rintro _ ⟨x, ⟨hx, hb⟩, rfl⟩; exact h x hx hb)

/-- Points of `H ∩ box` satisfy every cut whose point lies in `box \ H`. -/
theorem sat_of_cuts {cs : List (ι → ℝ)} (hcs : ∀ c ∈ cs, c ∉ P.H ∧ c ∈ box P.Mv)
    {z : ι → ℝ} (hz : z ∈ P.H) : Sat cs z := by
  intro c hc
  by_contra h
  push_neg at h
  exact (hcs c hc).1 (P.upClosed z c hz h (hcs c hc).2)

/-- With cuts in `box \ H` the master spec applies: a one-signed representative of the top corner
(`reduce`) satisfies the cuts. -/
theorem exists_reg {cs : List (ι → ℝ)} (hcs : ∀ c ∈ cs, c ∉ P.H ∧ c ∈ box P.Mv) :
    ∃ z ∈ box P.Mv, Sat cs z ∧ P.OneSigned z := by
  obtain ⟨z, ⟨hz, hb⟩, hos, -⟩ := P.reduce P.top ⟨P.top_mem, P.top_box⟩
  exact ⟨z, hb, P.sat_of_cuts hcs hz, hos⟩

/-- With cuts in `box \ H` the master lower bound is at most `OPT`: for `z ∈ H ∩ box` its
one-signed representative `z'` satisfies the cuts, so `lb ≤ f z' ≤ f z`. -/
theorem master_lb_le_opt {cs : List (ι → ℝ)} (hcs : ∀ c ∈ cs, c ∉ P.H ∧ c ∈ box P.Mv) (UB : ℝ) :
    (P.master cs UB).2 ≤ P.opt := P.le_opt fun z hz hb => by
  obtain ⟨z', ⟨hz', hb'⟩, hos, hle⟩ := P.reduce z ⟨hz, hb⟩
  exact (P.master_lb _ _ (P.exists_reg hcs) z' hb' (P.sat_of_cuts hcs hz') hos).trans hle

theorem inv_init : P.Inv P.init := by
  have h0 : (0 : ι → ℝ) ∈ box P.Mv := fun j => ⟨le_rfl, (P.M_pos j).le⟩
  unfold init
  split_ifs with h
  · have hH := (P.O_spec 0 h0).1 h
    exact ⟨P.le_opt fun _ _ hb => P.f_mono fun j => (hb j).1, hH, h0, rfl, by simp⟩
  · have hH : (0 : ι → ℝ) ∉ P.H := fun hH => h ((P.O_spec 0 h0).2 hH)
    exact ⟨P.le_opt fun z _ _ => P.f_nonneg z, P.top_mem, P.top_box, rfl, by simp [hH, h0]⟩

theorem inv_step (ε : ℝ) {s : State ι} (hs : P.Inv s) : P.Inv (P.step ε s) := by
  unfold step
  dsimp only
  split_ifs with hst hO hlt
  · exact hs
  all_goals
    have hreg := P.exists_reg hs.cuts
    have hlb : (P.master s.cuts s.UB).2 ≤ P.opt := P.master_lb_le_opt hs.cuts s.UB
    have hopt : P.opt ≤ s.UB := hs.ub_eq ▸ P.opt_le hs.best_mem hs.best_box
    have htau : 0 ≤ P.tau s := div_nonneg (by linarith [hs.lb_le]) (by linarith [P.L_pos])
    have hv : P.masterPt s ∈ box P.Mv:= P.master_box _ s.UB hreg
    have hw : P.query s ∈ box P.Mv:= fun j =>
      ⟨le_min (by linarith [(hv j).1]) (P.M_pos j).le, min_le_right _ _⟩
  · exact ⟨max_le hs.lb_le hlb, (P.O_spec _ hw).1 hO, hw, (min_eq_right hlt.le).symm, hs.cuts⟩
  · exact ⟨max_le hs.lb_le hlb, hs.best_mem, hs.best_box,
      by rw [min_eq_left (not_lt.1 hlt)]; exact hs.ub_eq, hs.cuts⟩
  · have hH : P.query s ∉ P.H := fun hH => hO ((P.O_spec _ hw).2 hH)
    refine ⟨max_le hs.lb_le hlb, hs.best_mem, hs.best_box, hs.ub_eq, ?_⟩
    simpa [hH, hw] using hs.cuts

theorem inv_run (ε : ℝ) (n : ℕ) : P.Inv (P.run ε n) := by
  induction n with
  | zero => exact P.inv_init
  | succ n ih =>
    rw [run, Function.iterate_succ_apply']
    exact P.inv_step ε ih

/-- **(A) Correctness.** After any number of steps `LB ≤ OPT ≤ UB`, and `UB` is the cost of the
best point found, which lies in `H ∩ box`. -/
theorem run_correct (ε : ℝ) (n : ℕ) :
    (P.run ε n).LB ≤ P.opt ∧ P.opt ≤ (P.run ε n).UB ∧ (P.run ε n).best ∈ P.H ∩ box P.Mv∧
      P.f (P.run ε n).best = (P.run ε n).UB := by
  have h := P.inv_run ε n
  exact ⟨h.lb_le, h.ub_eq ▸ P.opt_le h.best_mem h.best_box, ⟨h.best_mem, h.best_box⟩, h.ub_eq⟩

/-! ### (B) Termination -/

theorem opt_le_ub {s : State ι} (hs : P.Inv s) : P.opt ≤ s.UB :=
  hs.ub_eq ▸ P.opt_le hs.best_mem hs.best_box

/-- The gap never grows. -/
theorem gap_step_le (ε : ℝ) (s : State ι) :
    (P.step ε s).UB - (P.step ε s).LB ≤ s.UB - s.LB := by
  have h1 := min_le_left s.UB (P.f (P.query s))
  have h2 := le_max_left s.LB (P.master s.cuts s.UB).2
  simp only [step]
  split_ifs <;> (try simp only) <;> linarith

/-- A YES step shrinks the gap by `3/4`: `f w ≤ f v + τ L ≤ LB + 3/4 (UB - LB)`. -/
theorem gap_step_yes (ε : ℝ) {s : State ι} (hs : P.Inv s) (hns : ¬ Stopped ε s)
    (hyes : P.O (P.query s) = true) :
    (P.step ε s).UB - (P.step ε s).LB ≤ 3 / 4 * (s.UB - s.LB) := by
  have hne := P.exists_reg hs.cuts
  have hopt := P.opt_le_ub hs
  have hLB := hs.lb_le
  have hτ : 0 ≤ P.tau s := by
    unfold tau
    apply div_nonneg _ (by have := P.L_pos; positivity)
    linarith
  have hwle : P.query s ≤ P.masterPt s + fun _ => P.tau s := fun j => min_le_left _ _
  have hfw : P.f (P.query s) ≤ P.f (P.masterPt s) + P.tau s * P.L :=
    (P.f_mono hwle).trans (P.f_shift _ _ hτ)
  have hτL : P.tau s * P.L = (s.UB - s.LB) / 2 := by
    unfold tau; have := P.L_pos; field_simp
  have hmin : min s.UB (P.f (P.query s)) ≤ P.f (P.query s) := min_le_right _ _
  have hmax1 := le_max_left s.LB (P.master s.cuts s.UB).2
  have hmax2 := le_max_right s.LB (P.master s.cuts s.UB).2
  simp only [step, if_neg hns, hyes, if_true]
  try simp only
  by_cases hlb : (P.master s.cuts s.UB).2 < s.UB
  · have hg := P.master_gap s.cuts s.UB hne hlb
    change P.f (P.masterPt s) ≤ _ at hg
    rcases le_total s.LB (P.master s.cuts s.UB).2 with h | h
    · rw [max_eq_right h]
      have : s.UB - s.LB ≥ 0 := by linarith
      linarith
    · rw [max_eq_left h]
      have : s.UB - s.LB ≥ 0 := by linarith
      linarith
  · have h := not_lt.mp hlb
    have : s.UB - s.LB ≥ 0 := by linarith
    have := min_le_left s.UB (P.f (P.query s))
    linarith

/-- While not stopped, `τ ≥ τ₀ = ε OPT / (2 L)`. -/
theorem tau_ge {ε : ℝ} (hε : 0 ≤ ε) {s : State ι} (hs : P.Inv s) (hns : ¬ Stopped ε s) :
    ε * P.opt / (2 * P.L) ≤ P.tau s := by
  unfold tau
  have := P.L_pos
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := P.opt_le_ub hs
  have := not_le.mp hns
  nlinarith

/-- Cuts are never removed. -/
theorem cuts_step_subset (ε : ℝ) (s : State ι) : s.cuts ⊆ (P.step ε s).cuts := by
  unfold step
  by_cases h : Stopped ε s
  · rw [if_pos h]; exact List.Subset.refl _
  · rw [if_neg h]
    dsimp only
    split_ifs <;> first | exact List.Subset.refl _ | exact List.subset_cons_self _ _

theorem cuts_run_subset (ε : ℝ) {m n : ℕ} (h : m ≤ n) : (P.run ε m).cuts ⊆ (P.run ε n).cuts := by
  induction n, h using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ n _ ih =>
    have : P.run ε (n + 1) = P.step ε (P.run ε n) := by
      unfold run; exact Function.iterate_succ_apply' _ _ _
    rw [this]
    exact ih.trans (P.cuts_step_subset ε _)

/-- **Separation.** If step `m` was a NO and step `n > m` is not stopped, the master point of
step `n` exceeds that of step `m` by `τ₀` in some coordinate: it satisfies the cut `w_m`, and a
coordinate where `w_m` is clipped to `Mv` cannot be exceeded. -/
theorem master_separated {ε : ℝ} (hε : 0 ≤ ε) {m n : ℕ} (hmn : m < n)
    (hm : ¬ Stopped ε (P.run ε m)) (hno : P.O (P.query (P.run ε m)) = false) :
    ∃ j, P.masterPt (P.run ε m) j + ε * P.opt / (2 * P.L) ≤ P.masterPt (P.run ε n) j := by
  have hstep : P.run ε (m + 1) = P.step ε (P.run ε m) := by
    unfold run; exact Function.iterate_succ_apply' _ _ _
  have hmem : P.query (P.run ε m) ∈ (P.run ε (m + 1)).cuts := by
    rw [hstep]; unfold step
    rw [if_neg hm]
    simp only [hno]
    simp
  have hmem' := P.cuts_run_subset ε (Nat.succ_le_of_lt hmn) hmem
  have hex := P.exists_reg (P.inv_run ε n).cuts
  have hsat := P.master_sat _ (P.run ε n).UB hex
  have hbox := P.master_box _ (P.run ε n).UB hex
  obtain ⟨j, hj⟩ := hsat _ hmem'
  refine ⟨j, ?_⟩
  have hb : P.masterPt (P.run ε n) j ≤ P.Mv j := (hbox j).2
  have hq : P.query (P.run ε m) j =
      min (P.masterPt (P.run ε m) j + P.tau (P.run ε m)) (P.Mv j) := rfl
  rw [hq] at hj
  have h1 : P.masterPt (P.run ε m) j + P.tau (P.run ε m) < P.masterPt (P.run ε n) j := by
    rcases min_lt_iff.mp hj with h | h
    · exact h
    · exact absurd hb (not_le.mpr h)
  have := P.tau_ge hε (P.inv_run ε m) hm
  linarith

/-- At most `(⌊Mmax / τ₀⌋ + 1)^|ι|` NO steps before stopping, `Mmax ≥ Mv j` for all `j`. -/
theorem card_no_le {ε : ℝ} (hε : 0 < ε) (hopt : 0 < P.opt) {Mmax : ℝ}
    (hMmax : ∀ j, P.Mv j ≤ Mmax) (N : ℕ) (hN : ∀ n < N, ¬ Stopped ε (P.run ε n)) :
    ((Finset.range N).filter (fun n => P.O (P.query (P.run ε n)) = false)).card ≤
      (⌊Mmax / (ε * P.opt / (2 * P.L))⌋₊ + 1) ^ Fintype.card ι := by
  classical
  set S := (Finset.range N).filter (fun n => P.O (P.query (P.run ε n)) = false) with hS
  let e := S.orderEmbOfFin rfl
  let σ := Fintype.equivFin ι
  have hτ : 0 < ε * P.opt / (2 * P.L) := by
    have := P.L_pos
    positivity
  have heS : ∀ k, e k ∈ S := fun k => S.orderEmbOfFin_mem rfl k
  have := separated_bound (M := Mmax) hτ
    (fun k j => P.masterPt (P.run ε (e k)) (σ.symm j))
    (by
      intro k j
      have h := P.master_box _ (P.run ε (e k)).UB (P.exists_reg (P.inv_run ε (e k)).cuts)
        (σ.symm j)
      exact ⟨h.1, h.2.trans (hMmax _)⟩)
    (by
      intro k l hkl
      have hlt : e k < e l := e.strictMono hkl
      have hk := Finset.mem_filter.mp (heS k)
      have hk1 := Finset.mem_range.mp hk.1
      have hk' : e k < N := hk1
      have hk := hk.2
      obtain ⟨j, hj⟩ := P.master_separated hε.le hlt (hN _ hk') hk
      exact ⟨σ j, by simpa using hj⟩)
  simpa using this

/-- The gap after `N` steps is at most `(3/4)^(number of YES steps)` times the initial gap. -/
theorem gap_run_le (ε : ℝ) (N : ℕ) :
    (P.run ε N).UB - (P.run ε N).LB ≤
      (3 / 4 : ℝ) ^ ((Finset.range N).filter (fun n => ¬ Stopped ε (P.run ε n) ∧
        P.O (P.query (P.run ε n)) = true)).card * (P.init.UB - P.init.LB) := by
  induction N with
  | zero => simp [run]
  | succ N ih =>
    have hrun : P.run ε (N+1) = P.step ε (P.run ε N) := by
      simp only [run]; rw [Function.iterate_succ_apply']
    have hinv := P.inv_run ε N
    rw [Finset.range_add_one, Finset.filter_insert, hrun]
    by_cases hc : ¬ Stopped ε (P.run ε N) ∧ P.O (P.query (P.run ε N)) = true
    · rw [if_pos hc, Finset.card_insert_of_notMem (by simp), pow_succ]
      have := P.gap_step_yes ε hinv hc.1 hc.2
      have h34 : (0:ℝ) ≤ 3/4 := by norm_num
      nlinarith [mul_le_mul_of_nonneg_left ih h34]
    · rw [if_neg hc]
      exact (P.gap_step_le ε _).trans ih

/-- Fewer than `log (UB₀ / (ε OPT)) / log (4/3)` YES steps before stopping. -/
theorem card_yes_lt {ε : ℝ} (hε : 0 < ε) (hopt : 0 < P.opt) (h0 : P.O 0 = false) (N : ℕ)
    (hN : ∀ n ≤ N, ¬ Stopped ε (P.run ε n)) :
    (((Finset.range N).filter (fun n => P.O (P.query (P.run ε n)) = true)).card : ℝ) <
      log (P.f P.top / (ε * P.opt)) / log (4 / 3) := by
  set Y := ((Finset.range N).filter (fun n => P.O (P.query (P.run ε n)) = true)).card with hY
  have hfilt : (Finset.range N).filter (fun n => P.O (P.query (P.run ε n)) = true) =
      (Finset.range N).filter (fun n => ¬ Stopped ε (P.run ε n) ∧
        P.O (P.query (P.run ε n)) = true) := by
    apply Finset.filter_congr
    intro n hn
    have := hN n (Finset.mem_range.mp hn).le
    simp [this]
  have hg := P.gap_run_le ε N
  rw [← hfilt] at hg
  have hinit : P.init.UB - P.init.LB = P.f P.top := by
    simp [init, h0]
  rw [hinit] at hg
  have hns := hN N le_rfl
  have hc := P.run_correct ε N
  unfold Stopped at hns
  push_neg at hns
  have h1 : ε * P.opt < (3/4:ℝ)^Y * P.f P.top := by
    have : ε * P.opt ≤ ε * (P.run ε N).UB := mul_le_mul_of_nonneg_left hc.2.1 hε.le
    linarith
  have hpow : (0:ℝ) < (3/4)^Y := by positivity
  have hεo : 0 < ε * P.opt := mul_pos hε hopt
  have hf : 0 < P.f P.top := by
    by_contra h
    have : P.f P.top = 0 := le_antisymm (not_lt.mp h) (P.f_nonneg _)
    rw [this] at h1; simp at h1; linarith
  have h2 : (4/3:ℝ)^Y < P.f P.top / (ε * P.opt) := by
    rw [lt_div_iff₀ hεo]
    have : (4/3:ℝ)^Y * (3/4)^Y = 1 := by rw [← mul_pow]; norm_num
    nlinarith [pow_pos (show (0:ℝ) < 4/3 by norm_num) Y]
  have h3 := Real.log_lt_log (by positivity) h2
  rw [Real.log_pow] at h3
  have hl : 0 < Real.log (4/3) := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ hl]
  exact h3

/-- **(B) Termination.** If `0 < OPT` and `0 < ε`, the run stops (`UB - LB ≤ ε UB`) within
`⌈log (UB₀ / (ε OPT)) / log (4/3)⌉ + 1 + (⌊Mmax / τ₀⌋ + 1)^|ι|` steps, `τ₀ = ε OPT / (2 L)`,
`UB₀ = f (top)`, for any bound `Mmax ≥ Mv j` on the box (e.g. its largest side).

Proof. While not stopped, `UB - LB > ε UB ≥ ε OPT`, so `τ ≥ τ₀` (`tau_ge`). A YES step shrinks
the gap by `3/4` (`gap_step_yes`), and the gap never grows (`gap_step_le`), so there are fewer
than `log (UB₀ / (ε OPT)) / log (4/3)` YES steps (`card_yes_lt`). The master points of NO steps
are `τ₀`-separated in `[0, Mmax]^ι` (`master_separated`), so by `separated_bound` there are at
most `(⌊Mmax / τ₀⌋ + 1)^|ι|` of them (`card_no_le`).

The case `OPT = 0` is excluded on purpose: with the relative stop test and `LB = 0` the test
`UB ≤ ε UB` can fail forever. Step 0 (`init`) handles `OPT = 0` when `0 ∈ H`. -/
theorem run_stops {ε : ℝ} (hε : 0 < ε) (hopt : 0 < P.opt) {Mmax : ℝ}
    (hMmax : ∀ j, P.Mv j ≤ Mmax) :
    ∃ n ≤ ⌈log (P.f P.top / (ε * P.opt)) / log (4 / 3)⌉₊ + 1 +
        (⌊Mmax / (ε * P.opt / (2 * P.L))⌋₊ + 1) ^ Fintype.card ι,
      Stopped ε (P.run ε n) := by
  by_cases h0 : P.O 0 = true
  · refine ⟨0, Nat.zero_le _, ?_⟩
    simp only [Stopped, run, Function.iterate_zero, id, init, h0, if_true, sub_self]
    exact mul_nonneg hε.le (P.f_nonneg 0)
  have h0' : P.O 0 = false := by simpa using h0
  by_contra hcon
  push_neg at hcon
  have hY := Nat.lt_ceil.2 (P.card_yes_lt hε hopt h0' _ fun n hn => not_le.2 (hcon n hn))
  have hNo := P.card_no_le hε hopt hMmax _ fun n hn => not_le.2 (hcon n hn.le)
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range
    (⌈log (P.f P.top / (ε * P.opt)) / log (4 / 3)⌉₊ + 1 +
        (⌊Mmax / (ε * P.opt / (2 * P.L))⌋₊ + 1) ^ Fintype.card ι))
    (fun n => P.O (P.query (P.run ε n)) = true)
  simp only [Bool.not_eq_true, Finset.card_range] at hsplit
  omega

end Problem

/-! ### (C) Instantiation: the box query -/

section Box

variable {d T : ℕ}

/-- The down half-widths `α` of a point `z = (α, β)`. -/
def alphaOf (z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) : Fin T → Fin d → ℝ :=
  fun t i => z (Sum.inl (t, i))

/-- The up half-widths `β` of a point `z = (α, β)`. -/
def betaOf (z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) : Fin T → Fin d → ℝ :=
  fun t i => z (Sum.inr (t, i))

/-- One-signed half-widths, one sign per year: in every year either no price is moved down
(`α t = 0`) or no price is moved up (`β t = 0`). This is the class cut out by the sign rows of the
implemented master. -/
def BoxOneSigned (z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) : Prop :=
  ∀ t, (∀ i, z (Sum.inl (t, i)) = 0) ∨ (∀ i, z (Sum.inr (t, i)) = 0)

/-- The half-widths passing the box query form an up-closed set in the box `∏ j, [0, Mv j]` when
the `α`-sides are at most `1` (`BoxFeasible.mono`): this discharges `Problem.upClosed` for
`H = {z | BoxFeasible P y (alphaOf z) (betaOf z)}`. -/
theorem boxFeasible_upClosed (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {Mv : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ}
    (hM : ∀ t i, Mv (Sum.inl (t, i)) ≤ 1)
    {z w : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ} (hz : z ∈ box Mv) (hw : w ∈ box Mv)
    (h : BoxFeasible P y (alphaOf z) (betaOf z)) (hzw : z ≤ w) :
    BoxFeasible P y (alphaOf w) (betaOf w) :=
  h.mono hd hP hy (fun _ _ => (hz _).1) (fun _ _ => (hz _).1) (fun _ _ => hzw _) (fun _ _ => hzw _)
    (fun t i => (hw _).2.trans (hM t i))

/-- **One-signed representatives.** For the box instance (`α`-sides `Mv (inl _) < 1`, cost
`f z = g (lpPow p c (max α β))`, `g` monotone) every `z ∈ H ∩ box` is dominated by a one-signed
`z' ∈ H ∩ box`: this discharges `Problem.reduce` with `OneSigned = BoxOneSigned`.

Proof. `exists_oneSigned_of_boxFeasible` gives prices `Q`, moving every year in one direction,
in the box: `-α ≤ ε ≤ β`, `ε = relDev P Q`, hence `|ε| ≤ max α β`. Take `z' = (ε⁻, ε⁺)`: it is
one-signed by years (a year moved down has `ε⁺ = 0`, a year moved up has `ε⁻ = 0`), passes the
query since its box contains `Q` (`boxFeasible_of_weakSolvable`), lies in the box
(`ε⁻ ≤ α ≤ Mv`, `ε⁺ ≤ β ≤ Mv`) and has `max ε⁻ ε⁺ = |ε| ≤ max α β`. -/
theorem box_reduce (hd : 2 ≤ d) {P : Fin T → Fin d → ℝ} (hP : ∀ t, P t ∈ orthant d)
    {y : Fin T → ℝ} (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 0 ≤ p) {c : Fin T → Fin d → ℝ}
    (hc : ∀ t i, 0 ≤ c t i) {g : ℝ → ℝ} (hg : Monotone g)
    {Mv : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ} (hM : ∀ t i, Mv (Sum.inl (t, i)) < 1)
    {H : Set ((Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ)}
    {f : ((Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ) → ℝ}
    (hH : ∀ z ∈ box Mv, z ∈ H ↔ BoxFeasible P y (alphaOf z) (betaOf z))
    (hf : ∀ z, f z = g (lpPow p c (maxHW (alphaOf z) (betaOf z)))) :
    ∀ z ∈ H ∩ box Mv, ∃ z' ∈ H ∩ box Mv, BoxOneSigned z' ∧ f z' ≤ f z := by
  rintro z ⟨hzH, hzb⟩
  obtain ⟨Q, hQ, hws, hos, hle, hin⟩ := exists_oneSigned_of_boxFeasible hd hP hy
    (fun t i => (hzb _).1) (fun t i => (hzb _).1) (fun t i => (hzb _).2.trans_lt (hM t i))
    ((hH z hzb).1 hzH)
  have hin' : ∀ t i, -z (Sum.inl (t, i)) ≤ relDev (P t) (Q t) i ∧
      relDev (P t) (Q t) i ≤ z (Sum.inr (t, i)) := hin
  let z' : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ :=
    Sum.elim (fun ti => max (-relDev (P ti.1) (Q ti.1) ti.2) 0)
      (fun ti => max (relDev (P ti.1) (Q ti.1) ti.2) 0)
  have hz'b : z' ∈ box Mv := by
    rintro (⟨t, i⟩ | ⟨t, i⟩)
    · exact ⟨le_max_right _ _,
        (max_le (by linarith [(hin' t i).1]) (hzb (Sum.inl (t, i))).1).trans (hzb _).2⟩
    · exact ⟨le_max_right _ _, (max_le (hin' t i).2 (hzb (Sum.inr (t, i))).1).trans (hzb _).2⟩
  refine ⟨z', ⟨(hH z' hz'b).2 (boxFeasible_of_weakSolvable hd hP hy hQ hws), hz'b⟩,
    fun t => ?_, ?_⟩
  · rcases hos t with h | h
    · refine Or.inr fun i => ?_
      show max (relDev (P t) (Q t) i) 0 = 0
      exact max_eq_right (sub_nonpos.2 ((div_le_one (hP t i)).2 (h i)))
    · refine Or.inl fun i => ?_
      show max (-relDev (P t) (Q t) i) 0 = 0
      exact max_eq_right (neg_nonpos.2 (sub_nonneg.2 ((one_le_div (hP t i)).2 (h i))))
  · rw [hf, hf]
    refine hg (lpPow_mono hp hc fun t i => ?_)
    simp only [maxHW, alphaOf, betaOf, z', Sum.elim_inl, Sum.elim_inr]
    rw [abs_of_nonneg ((le_max_right _ _).trans (le_max_left _ _)),
      abs_of_nonneg ((hzb _).1.trans (le_max_left _ _))]
    exact (max_negPart_posPart_le _).trans (hle t i)

/-- **(C) The algorithm for the least relative `l_p` price perturbation.** Let the problem's box
`∏ j, [0, Mv j]` have `α`-sides `Mv (inl (t, i)) < 1` (the `β`-sides are arbitrary), its `H` be,
on the box, the set of half-widths `z = (α, β)` passing the box query, and its cost be
`f z = g (lpPow p c (max α β))` with `g` monotone (`g = (·)^(1/p)` gives the weighted `l_p`
norm). Then after any number of steps the upper bound `UB` is attained by prices `Q` at which `y`
is weakly solvable, and `LB` is at most the cost `g (lpPow p c (relDev P Q))` of every such `Q`
whose half-widths `ε⁻, ε⁺` (`ε = relDev P Q`) lie in the box.

Remark (how the box is chosen). For `g = (·)^(1/p)` the cost of `Q` is at least
`c t i |ε t i|`, so choosing `Mv (inr (t, i)) ≥ UB₀ / c t i` (and the `α`-sides likewise, as far
as `< 1` allows) puts every `Q` of cost at most `UB₀` into the box; then `LB ≤ OPT_p`. This is
how the implementation chooses `z^max`. The remark is not formalized.

Proof. `run_correct`. `UB`: `exists_weakSolvable_iff_boxFeasible` (`←`) at the best point (in the
box, so `α < 1`) gives `Q`. `LB`: `z = (ε⁻, ε⁺)` lies in the box by assumption, passes the query
(`boxFeasible_of_weakSolvable`) and costs at most the cost of `Q` (`max ε⁻ ε⁺ ≤ |ε|`), so
`LB ≤ OPT ≤ f z`. -/
theorem boxRun_correct (hd : 2 ≤ d) (P : Fin T → Fin d → ℝ) (hP : ∀ t, P t ∈ orthant d)
    (y : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) {p : ℝ} (hp : 1 ≤ p) (c : Fin T → Fin d → ℝ)
    (hc : ∀ t i, 0 ≤ c t i) {g : ℝ → ℝ} (hg : Monotone g)
    (Pr : Problem ((Fin T × Fin d) ⊕ (Fin T × Fin d)))
    (hM1 : ∀ t i, Pr.Mv (Sum.inl (t, i)) < 1)
    (hH : ∀ z ∈ box Pr.Mv, z ∈ Pr.H ↔ BoxFeasible P y (alphaOf z) (betaOf z))
    (hf : ∀ z, Pr.f z = g (lpPow p c (maxHW (alphaOf z) (betaOf z)))) (ε : ℝ) (n : ℕ) :
    (∃ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) ∧ WeakSolvable Q y ∧
        g (lpPow p c (fun t => relDev (P t) (Q t))) ≤ (Pr.run ε n).UB) ∧
      ∀ Q : Fin T → Fin d → ℝ, (∀ t, Q t ∈ orthant d) → WeakSolvable Q y →
        (∀ t i, max (-relDev (P t) (Q t) i) 0 ≤ Pr.Mv (Sum.inl (t, i)) ∧
          max (relDev (P t) (Q t) i) 0 ≤ Pr.Mv (Sum.inr (t, i))) →
        (Pr.run ε n).LB ≤ g (lpPow p c (fun t => relDev (P t) (Q t))) := by
  obtain ⟨hLB, -, ⟨hbH, hbb⟩, hUB⟩ := Pr.run_correct ε n
  set b := (Pr.run ε n).best
  refine ⟨?_, fun Q hQ hws hQb => ?_⟩
  · obtain ⟨Q, hQ, hws, hle⟩ :=
      (exists_weakSolvable_iff_boxFeasible hd P hP y hy hp c hc _).2
        ⟨alphaOf b, betaOf b, fun _ _ => (hbb _).1, fun _ _ => (hbb _).1,
          fun t i => (hbb _).2.trans_lt (hM1 t i), (hH b hbb).1 hbH, le_rfl⟩
    exact ⟨Q, hQ, hws, (hg hle).trans (hf b ▸ hUB).le⟩
  · let z : (Fin T × Fin d) ⊕ (Fin T × Fin d) → ℝ :=
      Sum.elim (fun ti => max (-relDev (P ti.1) (Q ti.1) ti.2) 0)
        (fun ti => max (relDev (P ti.1) (Q ti.1) ti.2) 0)
    have hzb : z ∈ box Pr.Mv := by
      rintro (⟨t, i⟩ | ⟨t, i⟩)
      exacts [⟨le_max_right _ _, (hQb t i).1⟩, ⟨le_max_right _ _, (hQb t i).2⟩]
    have hzH : z ∈ Pr.H := (hH z hzb).2 (boxFeasible_of_weakSolvable hd hP hy hQ hws)
    refine hLB.trans ((Pr.opt_le hzH hzb).trans ?_)
    rw [hf]
    refine hg (lpPow_mono (by linarith) hc fun t i => ?_)
    simp only [maxHW, alphaOf, betaOf, z, Sum.elim_inl, Sum.elim_inr]
    rw [abs_of_nonneg ((le_max_right _ _).trans (le_max_left _ _))]
    exact max_negPart_posPart_le _

end Box

end NeoTiling.L1Perturbation.Polyblock
