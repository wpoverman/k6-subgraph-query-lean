import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Count
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Adaptive pair queries on a pre-sampled random board

This file isolates the part of the online Ramsey argument which is genuinely
about adaptivity.  The type `Q` is the type of legal queries (in the intended
application, unordered pairs of vertices), and a `Board Q` fixes the answer to
every possible query before the strategy starts.

Histories are stored newest first.  This convention makes both `run` and
`replay` structural recursions.  A deterministic strategy is allowed to depend
on its complete history.  No probability theory is needed for the basic
coupling facts: changing an as-yet unqueried board coordinate cannot change the
past, and prescribing a fresh list of answers produces a well-defined cylinder
event in board space.

The cylinder-law section deliberately abstracts the probability measure.
`adaptive_path_mass` proves the standard principle that a deterministic
adaptive strategy which never repeats a query sees fresh independent bits.
The final finite-product section discharges that cylinder law by an explicit
sum over boards, computes the push-forward law of the entire adaptive answer
vector, and derives its exact binomial positive-answer count.
-/

namespace OnlineRamsey

open scoped ENNReal

universe u

section Deterministic

variable {Q : Type u}

/-- A board fixes the response to every possible query in advance. -/
abbrev Board (Q : Type u) := Q → Bool

/-- A transcript is newest first. -/
abbrev Transcript (Q : Type u) := List (Q × Bool)

/-- The queries occurring in a transcript, newest first. -/
def queries (h : Transcript Q) : List Q := h.map Prod.fst

/-- The answers occurring in a transcript, newest first. -/
def answers (h : Transcript Q) : List Bool := h.map Prod.snd

/-- A deterministic strategy chooses its next query from the transcript. -/
abbrev Strategy (Q : Type u) := Transcript Q → Q

/-- Run a strategy for exactly `n` queries against a pre-sampled board. -/
def run (strategy : Strategy Q) (board : Board Q) : Nat → Transcript Q
  | 0 => []
  | n + 1 =>
      let h := run strategy board n
      let q := strategy h
      (q, board q) :: h

@[simp] theorem run_zero (strategy : Strategy Q) (board : Board Q) :
    run strategy board 0 = [] := rfl

@[simp] theorem run_succ (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    run strategy board (n + 1) =
      (strategy (run strategy board n),
        board (strategy (run strategy board n))) :: run strategy board n := rfl

@[simp] theorem length_run (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    (run strategy board n).length = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [run, ih]

@[simp] theorem length_queries (h : Transcript Q) :
    (queries h).length = h.length := by
  simp [queries]

@[simp] theorem length_answers (h : Transcript Q) :
    (answers h).length = h.length := by
  simp [answers]

@[simp] theorem length_queries_run (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    (queries (run strategy board n)).length = n := by
  simp

@[simp] theorem length_answers_run (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    (answers (run strategy board n)).length = n := by
  simp

/-- The board is consistent with every answer recorded by `run`. -/
def Consistent (board : Board Q) (h : Transcript Q) : Prop :=
  ∀ entry ∈ h, board entry.1 = entry.2

theorem consistent_run (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    Consistent board (run strategy board n) := by
  induction n with
  | zero => simp [Consistent]
  | succ n ih =>
      intro entry hentry
      simp only [run_succ, List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · rfl
      · exact ih entry hentry

/-- Replay a prescribed answer list.  Like transcripts, answers are newest first. -/
def replay (strategy : Strategy Q) : List Bool → Transcript Q
  | [] => []
  | bit :: bits =>
      let h := replay strategy bits
      (strategy h, bit) :: h

@[simp] theorem replay_nil (strategy : Strategy Q) : replay strategy [] = [] := rfl

@[simp] theorem replay_cons (strategy : Strategy Q) (bit : Bool) (bits : List Bool) :
    replay strategy (bit :: bits) =
      (strategy (replay strategy bits), bit) :: replay strategy bits := rfl

@[simp] theorem length_replay (strategy : Strategy Q) (bits : List Bool) :
    (replay strategy bits).length = bits.length := by
  induction bits with
  | nil => simp
  | cons bit bits ih => simp [replay, ih]

@[simp] theorem answers_replay (strategy : Strategy Q) (bits : List Bool) :
    answers (replay strategy bits) = bits := by
  induction bits with
  | nil => simp [answers]
  | cons bit bits ih =>
      change bit :: answers (replay strategy bits) = bit :: bits
      rw [ih]

/-- Replaying the answers actually seen reconstructs the complete transcript. -/
theorem replay_answers_run (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    replay strategy (answers (run strategy board n)) = run strategy board n := by
  induction n with
  | zero => simp [answers]
  | succ n ih =>
      change replay strategy
          (board (strategy (run strategy board n)) :: answers (run strategy board n)) =
        (strategy (run strategy board n), board (strategy (run strategy board n))) ::
          run strategy board n
      rw [replay_cons, ih]

/-- A board which is consistent with a prescribed path makes the strategy follow it. -/
theorem run_eq_replay_of_consistent (strategy : Strategy Q) (board : Board Q)
    (bits : List Bool) (hconsistent : Consistent board (replay strategy bits)) :
    run strategy board bits.length = replay strategy bits := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      have htail : Consistent board (replay strategy bits) := by
        intro entry hentry
        exact hconsistent entry (by simp [replay, hentry])
      have hhead : board (strategy (replay strategy bits)) = bit :=
        hconsistent (strategy (replay strategy bits), bit) (by simp [replay])
      simp [replay, ih htail, hhead]

/-- Following a prescribed path is exactly the corresponding cylinder event. -/
theorem run_eq_replay_iff_consistent (strategy : Strategy Q) (board : Board Q)
    (bits : List Bool) :
    run strategy board bits.length = replay strategy bits ↔
      Consistent board (replay strategy bits) := by
  constructor
  · intro h
    rw [← h]
    exact consistent_run strategy board bits.length
  · exact run_eq_replay_of_consistent strategy board bits

/-- The next query has not occurred in the current transcript. -/
def FreshAt (strategy : Strategy Q) (h : Transcript Q) : Prop :=
  strategy h ∉ queries h

/-- All queries on a prescribed response path are distinct. -/
def FreshPath (strategy : Strategy Q) (bits : List Bool) : Prop :=
  (queries (replay strategy bits)).Nodup

theorem freshPath_cons (strategy : Strategy Q) (bit : Bool) (bits : List Bool) :
    FreshPath strategy (bit :: bits) ↔
      FreshAt strategy (replay strategy bits) ∧ FreshPath strategy bits := by
  simp [FreshPath, FreshAt, replay, queries]

/-- A pathwise freshness hypothesis gives distinct queries in an actual run. -/
theorem queries_run_nodup (strategy : Strategy Q) (board : Board Q) (n : Nat)
    (hfresh : ∀ k, k < n → FreshAt strategy (run strategy board k)) :
    (queries (run strategy board n)).Nodup := by
  induction n with
  | zero => simp [queries]
  | succ n ih =>
      simp only [run_succ, queries, List.map_cons, List.nodup_cons]
      constructor
      · exact hfresh n (Nat.lt_succ_self n)
      · exact ih fun k hk => hfresh k (Nat.lt.step hk)

/-- Updating an unqueried board coordinate cannot alter the past transcript. -/
theorem run_update_of_not_queried [DecidableEq Q]
    (strategy : Strategy Q) (board : Board Q) (q : Q) (bit : Bool) (n : Nat)
    (hq : q ∉ queries (run strategy board n)) :
    run strategy (Function.update board q bit) n = run strategy board n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hqTail : q ∉ queries (run strategy board n) := by
        intro hmem
        apply hq
        change q ∈ strategy (run strategy board n) :: queries (run strategy board n)
        exact List.mem_cons_of_mem _ hmem
      have hqNext : q ≠ strategy (run strategy board n) := by
        intro heq
        apply hq
        change q ∈ strategy (run strategy board n) :: queries (run strategy board n)
        exact List.mem_cons.mpr (Or.inl heq)
      have hnextQ : strategy (run strategy board n) ≠ q := hqNext.symm
      have hpast := ih hqTail
      simp only [run_succ, hpast]
      rw [hpast, Function.update_of_ne hnextQ]

/--
At a fresh next query we may reveal either bit by updating only that coordinate;
the previous transcript is unchanged and the new answer is the chosen bit.
-/
theorem run_succ_update_at_next [DecidableEq Q]
    (strategy : Strategy Q) (board : Board Q) (bit : Bool) (n : Nat)
    (hfresh : FreshAt strategy (run strategy board n)) :
    run strategy
        (Function.update board (strategy (run strategy board n)) bit) (n + 1) =
      (strategy (run strategy board n), bit) :: run strategy board n := by
  have hpast := run_update_of_not_queried strategy board
    (strategy (run strategy board n)) bit n hfresh
  rw [run_succ, hpast]
  simp

/-- Install a finite transcript on top of an arbitrary background board. -/
def realize [DecidableEq Q] (base : Board Q) : Transcript Q → Board Q
  | [] => base
  | entry :: h => Function.update (realize base h) entry.1 entry.2

/-- Distinct-query transcripts can be installed without contradictory updates. -/
theorem consistent_realize [DecidableEq Q] (base : Board Q) (h : Transcript Q)
    (hnodup : (queries h).Nodup) : Consistent (realize base h) h := by
  induction h with
  | nil => simp [Consistent]
  | cons head tail ih =>
      simp only [queries, List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, htail⟩
      intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp [realize]
      · have hne : entry.1 ≠ head.1 := by
          intro heq
          apply hhead
          have : entry.1 ∈ queries tail := by
            exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
          rw [← heq]
          exact this
        simpa [realize, Function.update_of_ne hne] using ih htail entry hentry

/-- Every fresh answer path is realized by at least one pre-sampled board. -/
theorem exists_board_for_fresh_path [DecidableEq Q]
    (strategy : Strategy Q) (bits : List Bool) (hfresh : FreshPath strategy bits) :
    ∃ board : Board Q,
      run strategy board bits.length = replay strategy bits := by
  let board := realize (fun _ => false) (replay strategy bits)
  refine ⟨board, run_eq_replay_of_consistent strategy board bits ?_⟩
  exact consistent_realize (fun _ => false) (replay strategy bits) hfresh

end Deterministic

section CylinderLaw

variable {Q : Type u}

/-- The cylinder event that a board agrees with a finite transcript. -/
def cylinder (h : Transcript Q) : Set (Board Q) :=
  {board | Consistent board h}

/-- The event that the adaptive strategy follows the prescribed answer path. -/
def pathEvent (strategy : Strategy Q) (bits : List Bool) : Set (Board Q) :=
  {board | run strategy board bits.length = replay strategy bits}

theorem pathEvent_eq_cylinder (strategy : Strategy Q) (bits : List Bool) :
    pathEvent strategy bits = cylinder (replay strategy bits) := by
  ext board
  exact run_eq_replay_iff_consistent strategy board bits

/-- Product of one-bit weights along a transcript. -/
def transcriptWeight {R : Type*} [CommMonoid R] (weight : Bool → R)
    (h : Transcript Q) : R :=
  (answers h).map weight |>.prod

@[simp] theorem transcriptWeight_replay {R : Type*} [CommMonoid R]
    (weight : Bool → R) (strategy : Strategy Q) (bits : List Bool) :
    transcriptWeight weight (replay strategy bits) = (bits.map weight).prod := by
  simp [transcriptWeight]

/--
The finite-cylinder characterization of a pre-sampled independent board.

`mass` can be an actual measure evaluated on sets, or the finite weighted sum
over all boards.  This formulation keeps the adaptive lemma independent of the
particular construction of the product Bernoulli measure.
-/
def BernoulliCylinderLaw {R : Type*} [CommMonoid R]
    (mass : Set (Board Q) → R) (weight : Bool → R) : Prop :=
  ∀ h : Transcript Q, (queries h).Nodup →
    mass (cylinder h) = transcriptWeight weight h

/--
Fresh independent coordinates remain independent under deterministic adaptive
selection: every fresh adaptive path has the product of its one-bit masses.
-/
theorem adaptive_path_mass {R : Type*} [CommMonoid R]
    (mass : Set (Board Q) → R) (weight : Bool → R)
    (hlaw : BernoulliCylinderLaw mass weight)
    (strategy : Strategy Q) (bits : List Bool) (hfresh : FreshPath strategy bits) :
    mass (pathEvent strategy bits) = (bits.map weight).prod := by
  rw [pathEvent_eq_cylinder]
  exact (hlaw (replay strategy bits) hfresh).trans
    (transcriptWeight_replay weight strategy bits)

/-- One more fresh query multiplies the path mass by the selected bit's mass. -/
theorem adaptive_fresh_step_mass {R : Type*} [CommMonoid R]
    (mass : Set (Board Q) → R) (weight : Bool → R)
    (hlaw : BernoulliCylinderLaw mass weight)
    (strategy : Strategy Q) (bit : Bool) (bits : List Bool)
    (hfresh : FreshPath strategy (bit :: bits)) :
    mass (pathEvent strategy (bit :: bits)) =
      weight bit * mass (pathEvent strategy bits) := by
  have htail : FreshPath strategy bits :=
    ((freshPath_cons strategy bit bits).mp hfresh).2
  rw [adaptive_path_mass mass weight hlaw strategy (bit :: bits) hfresh]
  rw [adaptive_path_mass mass weight hlaw strategy bits htail]
  simp

end CylinderLaw

section FiniteProductBoard

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Bernoulli(`p`) coordinate weights, in `ENNReal`. -/
def bernoulliWeight (p : ℝ≥0∞) : Bool → ℝ≥0∞
  | false => 1 - p
  | true => p

theorem sum_bernoulliWeight (p : ℝ≥0∞) (hp : p ≤ 1) :
    (∑ bit : Bool, bernoulliWeight p bit) = 1 := by
  simpa [bernoulliWeight, add_comm] using (tsub_add_cancel_of_le hp)

/-- Point mass of a board under coordinate weights `weight`. -/
noncomputable def boardWeight (weight : Bool → ℝ≥0∞) (board : Board Q) : ℝ≥0∞ :=
  ∏ q : Q, weight (board q)

/-- Product coordinate weights sum to one when the one-bit weights do. -/
theorem sum_boardWeight (weight : Bool → ℝ≥0∞)
    (hnormalized : (∑ bit : Bool, weight bit) = 1) :
    (∑ board : Board Q, boardWeight weight board) = 1 := by
  rw [show (∑ board : Board Q, boardWeight weight board) =
      ∏ _q : Q, ∑ bit : Bool, weight bit by
        simpa [boardWeight] using
          (Fintype.prod_sum (fun (_q : Q) (bit : Bool) => weight bit)).symm]
  rw [hnormalized]
  simp

/-- The explicit finite product probability mass function on boards. -/
noncomputable def independentBoardPMF (weight : Bool → ℝ≥0∞)
    (hnormalized : (∑ bit : Bool, weight bit) = 1) : PMF (Board Q) :=
  PMF.ofFintype (boardWeight weight) (sum_boardWeight weight hnormalized)

@[simp] theorem independentBoardPMF_apply (weight : Bool → ℝ≥0∞)
    (hnormalized : (∑ bit : Bool, weight bit) = 1) (board : Board Q) :
    independentBoardPMF weight hnormalized board = boardWeight weight board := by
  exact PMF.ofFintype_apply (sum_boardWeight weight hnormalized) board

/-- Probability of an event, written as the explicit finite sum of point masses. -/
noncomputable def finiteBoardMass (weight : Bool → ℝ≥0∞)
    (event : Set (Board Q)) : ℝ≥0∞ := by
  classical
  exact ∑ board : Board Q, if board ∈ event then boardWeight weight board else 0

/-- A cylinder described by a finite domain and a total value function. -/
def assignmentCylinder (domain : Finset Q) (value : Board Q) : Set (Board Q) :=
  {board | ∀ q ∈ domain, board q = value q}

private theorem indicator_boardWeight_eq_constrained_product
    (weight : Bool → ℝ≥0∞) (domain : Finset Q) (value board : Board Q) :
    (if board ∈ assignmentCylinder domain value then boardWeight weight board else 0) =
      ∏ q : Q,
        if q ∈ domain then
          if board q = value q then weight (board q) else 0
        else weight (board q) := by
  classical
  by_cases hagree : ∀ q ∈ domain, board q = value q
  · have hmem : board ∈ assignmentCylinder domain value := hagree
    rw [if_pos hmem]
    unfold boardWeight
    apply Finset.prod_congr rfl
    intro q _hq
    by_cases hqdomain : q ∈ domain
    · simp [hqdomain, hagree q hqdomain]
    · simp [hqdomain]
  · have hnotmem : board ∉ assignmentCylinder domain value := hagree
    rw [if_neg hnotmem]
    have hexists : ∃ q, q ∈ domain ∧ board q ≠ value q := by
      by_contra hnone
      apply hagree
      intro q hqdomain
      by_contra hqne
      exact hnone ⟨q, hqdomain, hqne⟩
    obtain ⟨q, hqdomain, hqne⟩ := hexists
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [hqdomain, hqne]

/-- The explicit product law of a cylinder given as a partial assignment. -/
theorem finiteBoardMass_assignmentCylinder
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (domain : Finset Q) (value : Board Q) :
    finiteBoardMass weight (assignmentCylinder domain value) =
      ∏ q ∈ domain, weight (value q) := by
  classical
  unfold finiteBoardMass
  calc
    (∑ board : Board Q,
        if board ∈ assignmentCylinder domain value then boardWeight weight board else 0) =
        ∑ board : Board Q, ∏ q : Q,
          if q ∈ domain then
            if board q = value q then weight (board q) else 0
          else weight (board q) := by
            apply Finset.sum_congr rfl
            intro board _hboard
            exact indicator_boardWeight_eq_constrained_product weight domain value board
    _ = ∏ q : Q, ∑ bit : Bool,
          if q ∈ domain then
            if bit = value q then weight bit else 0
          else weight bit := by
            simpa using
              (Fintype.prod_sum (fun q : Q => fun bit : Bool =>
                if q ∈ domain then
                  if bit = value q then weight bit else 0
                else weight bit)).symm
    _ = ∏ q : Q, if q ∈ domain then weight (value q) else 1 := by
          apply Finset.prod_congr rfl
          intro q _hq
          by_cases hqdomain : q ∈ domain
          · cases hvalue : value q <;> simp [hqdomain]
          · simp only [hqdomain, if_false, hnormalized]
    _ = ∏ q ∈ domain, weight (value q) := by
          symm
          calc
            (∏ q ∈ domain, weight (value q)) =
                ∏ q ∈ domain, if q ∈ domain then weight (value q) else 1 := by
                  apply Finset.prod_congr rfl
                  intro q hq
                  simp [hq]
            _ = ∏ q ∈ (Finset.univ : Finset Q),
                  if q ∈ domain then weight (value q) else 1 := by
                  apply Finset.prod_subset (Finset.subset_univ domain)
                  intro q _hquniv hqnot
                  simp [hqnot]
            _ = ∏ q : Q, if q ∈ domain then weight (value q) else 1 := by
                  rfl

/-- The finite set of coordinates mentioned by a transcript. -/
def queryFinset (h : Transcript Q) : Finset Q := (queries h).toFinset

/-- A total assignment extending a distinct-query transcript. -/
def transcriptAssignment (h : Transcript Q) : Board Q :=
  realize (fun _ => false) h

theorem cylinder_eq_assignmentCylinder (h : Transcript Q)
    (hnodup : (queries h).Nodup) :
    cylinder h = assignmentCylinder (queryFinset h) (transcriptAssignment h) := by
  ext board
  constructor
  · intro hboard q hq
    have hqList : q ∈ queries h := by
      simpa [queryFinset] using hq
    obtain ⟨entry, hentry, hentryq⟩ := List.mem_map.mp hqList
    have hinstalled : Consistent (transcriptAssignment h) h := by
      exact consistent_realize (fun _ => false) h hnodup
    have hboardEntry := hboard entry hentry
    have hinstalledEntry := hinstalled entry hentry
    simpa [hentryq] using hboardEntry.trans hinstalledEntry.symm
  · intro hboard entry hentry
    have hq : entry.1 ∈ queryFinset h := by
      have hqList : entry.1 ∈ queries h :=
        List.mem_map.mpr ⟨entry, hentry, rfl⟩
      simpa [queryFinset] using hqList
    have hinstalled : Consistent (transcriptAssignment h) h := by
      exact consistent_realize (fun _ => false) h hnodup
    exact (hboard entry.1 hq).trans (hinstalled entry hentry)

theorem assignment_product_eq_transcriptWeight
    (weight : Bool → ℝ≥0∞) (h : Transcript Q) (hnodup : (queries h).Nodup) :
    (∏ q ∈ queryFinset h, weight (transcriptAssignment h q)) =
      transcriptWeight weight h := by
  induction h with
  | nil => simp [queryFinset, queries, transcriptAssignment, transcriptWeight, answers]
  | cons head tail ih =>
      simp only [queries, List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, htail⟩
      have hheadFinset : head.1 ∉ queryFinset tail := by
        intro hmem
        apply hhead
        change head.1 ∈ (queries tail).toFinset at hmem
        exact List.mem_toFinset.mp hmem
      rw [show queryFinset (head :: tail) = insert head.1 (queryFinset tail) by
        simp [queryFinset, queries]]
      rw [Finset.prod_insert hheadFinset]
      have htailProduct :
          (∏ q ∈ queryFinset tail, weight (transcriptAssignment (head :: tail) q)) =
            ∏ q ∈ queryFinset tail, weight (transcriptAssignment tail q) := by
        apply Finset.prod_congr rfl
        intro q hq
        have hqne : q ≠ head.1 := by
          intro heq
          apply hheadFinset
          simpa [heq] using hq
        simp [transcriptAssignment, realize, Function.update_of_ne hqne]
      rw [htailProduct, ih htail]
      simp [transcriptAssignment, realize, transcriptWeight, answers]

/-- The explicit finite board mass satisfies the cylinder law exactly. -/
theorem finiteBoardMass_cylinder
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (h : Transcript Q) (hnodup : (queries h).Nodup) :
    finiteBoardMass weight (cylinder h) = transcriptWeight weight h := by
  rw [cylinder_eq_assignmentCylinder h hnodup]
  rw [finiteBoardMass_assignmentCylinder weight hnormalized]
  exact assignment_product_eq_transcriptWeight weight h hnodup

/-- The explicit finite product board supplies the law used by the adaptive theorem. -/
theorem finiteBoardMass_bernoulliCylinderLaw
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1) :
    BernoulliCylinderLaw (Q := Q) (finiteBoardMass (Q := Q) weight) weight := by
  intro h hnodup
  exact finiteBoardMass_cylinder weight hnormalized h hnodup

/-- Fully instantiated adaptive fresh-bit theorem for the finite product board. -/
theorem finiteProduct_adaptive_path_mass
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (strategy : Strategy Q) (bits : List Bool) (hfresh : FreshPath strategy bits) :
    finiteBoardMass weight (pathEvent strategy bits) = (bits.map weight).prod := by
  exact adaptive_path_mass (finiteBoardMass weight) weight
    (finiteBoardMass_bernoulliCylinderLaw weight hnormalized) strategy bits hfresh

/-- Bernoulli-specialized form of the adaptive path theorem. -/
theorem bernoulli_adaptive_path_mass
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q) (bits : List Bool)
    (hfresh : FreshPath strategy bits) :
    finiteBoardMass (bernoulliWeight p) (pathEvent strategy bits) =
      (bits.map (bernoulliWeight p)).prod := by
  exact finiteProduct_adaptive_path_mass (bernoulliWeight p)
    (sum_bernoulliWeight p hp) strategy bits hfresh

/-! ### The complete law of the adaptive answer sequence -/

/-- The answers seen in an `n`-step run, packaged as a length-`n` vector. -/
def answerVector (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    List.Vector Bool n :=
  ⟨answers (run strategy board n), length_answers_run strategy board n⟩

@[simp] theorem answerVector_toList (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    (answerVector strategy board n).toList = answers (run strategy board n) := rfl

/-- The path event associated to a length-indexed answer vector. -/
def vectorPathEvent (strategy : Strategy Q) {n : Nat} (bits : List.Vector Bool n) :
    Set (Board Q) :=
  pathEvent strategy bits.toList

/--
The adaptive path cylinders are precisely the fibers of the answer-vector map.
In particular, the length-`n` path events partition the whole board space.
-/
theorem mem_vectorPathEvent_iff (strategy : Strategy Q) (board : Board Q)
    {n : Nat} (bits : List.Vector Bool n) :
    board ∈ vectorPathEvent strategy bits ↔ answerVector strategy board n = bits := by
  constructor
  · intro hpath
    apply Subtype.ext
    change answers (run strategy board n) = bits.toList
    have hrun : run strategy board n = replay strategy bits.toList := by
      simpa [vectorPathEvent, pathEvent] using hpath
    rw [hrun, answers_replay]
  · intro hanswers
    have hlist : answers (run strategy board n) = bits.toList := by
      exact congrArg Subtype.val hanswers
    have hrun := (replay_answers_run strategy board n).symm
    rw [hlist] at hrun
    simpa [vectorPathEvent, pathEvent] using hrun

/--
Exact push-forward of the finite product board law through an arbitrary fresh
deterministic strategy.  This is stronger than independence of any one path:
it computes the mass of every event depending on the entire answer vector.
-/
theorem finiteProduct_answerVector_event_mass
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (strategy : Strategy Q) (n : Nat) (P : List.Vector Bool n → Prop)
    [DecidablePred P]
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    finiteBoardMass weight {board | P (answerVector strategy board n)} =
      ∑ bits : List.Vector Bool n,
        if P bits then (bits.toList.map weight).prod else 0 := by
  classical
  unfold finiteBoardMass
  calc
    _ = ∑ board : Board Q, ∑ bits : List.Vector Bool n,
          if P bits ∧ board ∈ vectorPathEvent strategy bits then
            boardWeight weight board else 0 := by
              apply Finset.sum_congr rfl
              intro board _hboard
              rw [Fintype.sum_eq_single (answerVector strategy board n)]
              · simp [mem_vectorPathEvent_iff]
              · intro bits hne
                have hnotmem : board ∉ vectorPathEvent strategy bits := by
                  intro hmem
                  apply hne
                  exact (mem_vectorPathEvent_iff strategy board bits).mp hmem |>.symm
                simp [hnotmem]
    _ = ∑ bits : List.Vector Bool n, ∑ board : Board Q,
          if P bits ∧ board ∈ vectorPathEvent strategy bits then
            boardWeight weight board else 0 := by
              exact Finset.sum_comm
    _ = ∑ bits : List.Vector Bool n,
          if P bits then (bits.toList.map weight).prod else 0 := by
            apply Finset.sum_congr rfl
            intro bits _hbits
            by_cases hP : P bits
            · rw [if_pos hP]
              simp only [hP, true_and]
              have hpath := finiteProduct_adaptive_path_mass weight hnormalized
                strategy bits.toList (hfresh bits)
              change (∑ board : Board Q,
                  if board ∈ vectorPathEvent strategy bits then
                    boardWeight weight board else 0) = _
              exact hpath
            · simp [hP]

/-- Number of positive answers in the first `n` adaptive queries. -/
def trueAnswerCount (strategy : Strategy Q) (board : Board Q) (n : Nat) : Nat :=
  (answers (run strategy board n)).count true

@[simp] theorem trueAnswerCount_eq_answerVector_count
    (strategy : Strategy Q) (board : Board Q) (n : Nat) :
    trueAnswerCount strategy board n = (answerVector strategy board n).toList.count true := rfl

/-- The set of positions carrying `true` in a Boolean vector. -/
def trueSupport {n : Nat} (bits : List.Vector Bool n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ bits.get i = true

@[simp] theorem mem_trueSupport {n : Nat} (bits : List.Vector Bool n) (i : Fin n) :
    i ∈ trueSupport bits ↔ bits.get i = true := by
  simp [trueSupport]

theorem card_trueSupport {n : Nat} (bits : List.Vector Bool n) :
    (trueSupport bits).card = bits.toList.count true := by
  simpa [trueSupport] using
    (Fin.card_filter_univ_eq_vector_get_eq_count true bits)

/-- Boolean vectors are equivalent to their sets of positive positions. -/
def trueSupportEquiv (n : Nat) : List.Vector Bool n ≃ Finset (Fin n) where
  toFun := trueSupport
  invFun support := List.Vector.ofFn fun i ↦ decide (i ∈ support)
  left_inv bits := by
    apply List.Vector.ext
    intro i
    simp [trueSupport]
  right_inv support := by
    ext i
    simp [trueSupport]

/-- Restriction of `trueSupportEquiv` to vectors with exactly `k` positive entries. -/
def trueCountEquiv (n k : Nat) :
    {bits : List.Vector Bool n // bits.toList.count true = k} ≃
      {support : Finset (Fin n) // support.card = k} :=
  (trueSupportEquiv n).subtypeEquiv fun bits ↦ by
    change bits.toList.count true = k ↔ (trueSupport bits).card = k
    rw [card_trueSupport]

/-- There are `n.choose k` Boolean vectors of length `n` with exactly `k` true entries. -/
theorem card_trueCountVectors (n k : Nat) :
    Fintype.card {bits : List.Vector Bool n // bits.toList.count true = k} =
      Nat.choose n k := by
  rw [Fintype.card_congr (trueCountEquiv n k)]
  simpa using (Fintype.card_finset_len (α := Fin n) k)

/-- Product of Bernoulli weights, grouped by the two possible bit values. -/
theorem prod_bernoulliWeight_eq_count (p : ℝ≥0∞) (bits : List Bool) :
    (bits.map (bernoulliWeight p)).prod =
      p ^ bits.count true * (1 - p) ^ bits.count false := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      cases bit <;>
        simp [bernoulliWeight, ih, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/--
Exact binomial distribution of the number of positive answers to a fresh
deterministic adaptive strategy.  Adaptivity does not change the law.
-/
theorem bernoulli_trueAnswerCount_mass
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q) (n k : Nat)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight p)
        {board | trueAnswerCount strategy board n = k} =
      (Nat.choose n k : ℝ≥0∞) * p ^ k * (1 - p) ^ (n - k) := by
  classical
  rw [show {board | trueAnswerCount strategy board n = k} =
      {board | (answerVector strategy board n).toList.count true = k} by rfl]
  rw [finiteProduct_answerVector_event_mass (bernoulliWeight p)
    (sum_bernoulliWeight p hp) strategy n
    (fun bits ↦ bits.toList.count true = k) hfresh]
  have hterm : ∀ bits : List.Vector Bool n,
      bits.toList.count true = k →
        (bits.toList.map (bernoulliWeight p)).prod =
          p ^ k * (1 - p) ^ (n - k) := by
    intro bits hcount
    rw [prod_bernoulliWeight_eq_count, hcount]
    have hcomplement : bits.toList.count false = n - k := by
      symm
      apply Nat.sub_eq_of_eq_add'
      have hsum := List.count_true_add_count_false bits.toList
      rw [hcount, List.Vector.toList_length] at hsum
      exact hsum.symm
    rw [hcomplement]
  calc
    (∑ bits : List.Vector Bool n,
        if bits.toList.count true = k then
          (bits.toList.map (bernoulliWeight p)).prod else 0) =
        ∑ bits : List.Vector Bool n,
          if bits.toList.count true = k then
            p ^ k * (1 - p) ^ (n - k) else 0 := by
              apply Finset.sum_congr rfl
              intro bits _hbits
              by_cases hcount : bits.toList.count true = k
              · simp [hcount, hterm bits hcount]
              · simp [hcount]
    _ = (Nat.choose n k : ℝ≥0∞) *
          (p ^ k * (1 - p) ^ (n - k)) := by
            let selected := (Finset.univ : Finset (List.Vector Bool n)).filter
              fun bits ↦ bits.toList.count true = k
            have hselected : selected.card = Nat.choose n k := by
              calc
                selected.card = Fintype.card
                    {bits : List.Vector Bool n // bits.toList.count true = k} := by
                      symm
                      apply Fintype.card_of_subtype selected
                      intro bits
                      simp [selected]
                _ = Nat.choose n k := card_trueCountVectors n k
            rw [show (∑ bits : List.Vector Bool n,
                if bits.toList.count true = k then
                  p ^ k * (1 - p) ^ (n - k) else 0) =
                ∑ _bits ∈ selected, p ^ k * (1 - p) ^ (n - k) by
                  simpa only [selected] using
                    (Finset.sum_filter
                      (s := (Finset.univ : Finset (List.Vector Bool n)))
                      (fun bits ↦ bits.toList.count true = k)
                      (fun _bits ↦ p ^ k * (1 - p) ^ (n - k))).symm]
            rw [Finset.sum_const, hselected, nsmul_eq_mul]
    _ = (Nat.choose n k : ℝ≥0∞) * p ^ k * (1 - p) ^ (n - k) := by
          exact (mul_assoc _ _ _).symm

end FiniteProductBoard

end OnlineRamsey
