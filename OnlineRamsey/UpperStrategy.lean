import OnlineRamsey.Amplification
import OnlineRamsey.BaselineStrategy
import OnlineRamsey.QueryComplexity
import Mathlib.Data.Sym.Card
import Mathlib.Data.List.GetD
import Lean.Elab.Tactic.Omega

/-!
# A concrete strategy interface for the branch-and-fill upper bound

This module closes two deterministic gaps between the finite probability
calculation in `Amplification.lean` and the query-game definition.

First, `legalizeStrategy` turns any proposed query rule into an admissible
strategy.  Whenever the proposed query is a fresh nonloop it is retained;
otherwise the rule chooses a fresh nonloop from the finite board.  There are
always enough such coordinates before an `N`-query run ends.

Second, the branch-and-fill certificate is connected to the actual
`TranscriptSucceeds` predicate.  In particular, a successful `K4OneTrial`
board, embedded as a fresh filled set whose vertices are common neighbours of
a positive centre--root edge, gives a genuine copy of `K6` in the positive
transcript graph.

The remaining probabilistic step is global: construct the reservoir and the
common-neighbour sets with sufficiently high probability, and identify the
joint law of all unrevealed fill coordinates with the product mass in
`Amplification.lean`.
-/

namespace OnlineRamsey
namespace UpperStrategy

open scoped ENNReal
open QueryComplexity K4Moments K4OneTrial Amplification

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Making an arbitrary proposed rule admissible -/

/-- The finite set of genuine nonloop coordinates on the canonical board. -/
def legalQueries (N : ℕ) : Finset (Query N) :=
  Finset.univ.filter fun q ↦ ¬q.IsDiag

theorem card_legalQueries (N : ℕ) :
    (legalQueries N).card = Nat.choose (2 * N) 2 := by
  calc
    (legalQueries N).card = Fintype.card {q : Query N // ¬q.IsDiag} := by
      symm
      apply Fintype.card_of_subtype (legalQueries N)
      intro q
      simp [legalQueries]
    _ = Nat.choose (2 * N) 2 := by
      simpa using (Sym2.card_subtype_not_diag (α := Vertex N))

/-- Before time `N`, fewer coordinates have been queried than the number of
available nonloop coordinates.  Thus a legal fresh coordinate exists even on
an arbitrary (possibly unreachable) history of the relevant length. -/
theorem exists_fresh_nonloop_query {N : ℕ} (h : Transcript (Query N))
    (hlen : h.length < N) :
    ∃ q : Query N, ¬q.IsDiag ∧ q ∉ queries h := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlen
  have hbudget : N ≤ Nat.choose (2 * N) 2 := by
    rw [Nat.choose_two_right]
    have htwo : 2 ≤ 2 * N := by omega
    calc
      N ≤ N * (2 * N - 1) := Nat.le_mul_of_pos_right N (by omega)
      _ = 2 * N * (2 * N - 1) / 2 := by
        rw [show 2 * N * (2 * N - 1) = 2 * (N * (2 * N - 1)) by ring]
        exact (Nat.mul_div_cancel_left _ (by omega)).symm
  have hcardList : (queries h).toFinset.card < N :=
    (List.toFinset_card_le (queries h)).trans_lt (by simpa using hlen)
  have hnsub : ¬ legalQueries N ⊆ (queries h).toFinset := by
    intro hsub
    have hcardSub := Finset.card_le_card hsub
    rw [card_legalQueries] at hcardSub
    omega
  rw [Finset.not_subset] at hnsub
  obtain ⟨q, hqlegal, hqfresh⟩ := hnsub
  refine ⟨q, ?_, ?_⟩
  · simpa [legalQueries] using hqlegal
  · simpa using hqfresh

/-- A choice of a fresh nonloop query.  Outside the relevant depth it returns
an arbitrary diagonal coordinate; this branch is never used by admissibility. -/
def fallbackQuery {N : ℕ} (hN : 0 < N) (h : Transcript (Query N)) : Query N :=
  if hlen : h.length < N then
    Classical.choose (exists_fresh_nonloop_query h hlen)
  else
    s((⟨0, by omega⟩ : Vertex N), (⟨0, by omega⟩ : Vertex N))

theorem fallbackQuery_nonloop {N : ℕ} (hN : 0 < N)
    (h : Transcript (Query N)) (hlen : h.length < N) :
    ¬(fallbackQuery hN h).IsDiag := by
  rw [fallbackQuery, dif_pos hlen]
  exact (Classical.choose_spec (exists_fresh_nonloop_query h hlen)).1

theorem fallbackQuery_fresh {N : ℕ} (hN : 0 < N)
    (h : Transcript (Query N)) (hlen : h.length < N) :
    fallbackQuery hN h ∉ queries h := by
  rw [fallbackQuery, dif_pos hlen]
  exact (Classical.choose_spec (exists_fresh_nonloop_query h hlen)).2

/-- Retain a proposed query when it is legal and fresh, and use a certified
fallback coordinate otherwise. -/
def legalizeStrategy {N : ℕ} (hN : 0 < N) (proposed : K6Strategy N) :
    K6Strategy N := fun h ↦
  if hgood : ¬(proposed h).IsDiag ∧ proposed h ∉ queries h then
    proposed h
  else
    fallbackQuery hN h

theorem legalizeStrategy_eq_of_legal_fresh {N : ℕ} (hN : 0 < N)
    (proposed : K6Strategy N) (h : Transcript (Query N))
    (hgood : ¬(proposed h).IsDiag ∧ proposed h ∉ queries h) :
    legalizeStrategy hN proposed h = proposed h := by
  simp [legalizeStrategy, hgood]

theorem legalizeStrategy_nonloop {N : ℕ} (hN : 0 < N)
    (proposed : K6Strategy N) (h : Transcript (Query N))
    (hlen : h.length < N) :
    ¬(legalizeStrategy hN proposed h).IsDiag := by
  by_cases hgood : ¬(proposed h).IsDiag ∧ proposed h ∉ queries h
  · simpa [legalizeStrategy, hgood] using hgood.1
  · simpa [legalizeStrategy, hgood] using fallbackQuery_nonloop hN h hlen

theorem legalizeStrategy_freshAt {N : ℕ} (hN : 0 < N)
    (proposed : K6Strategy N) (h : Transcript (Query N))
    (hlen : h.length < N) :
    FreshAt (legalizeStrategy hN proposed) h := by
  by_cases hgood : ¬(proposed h).IsDiag ∧ proposed h ∉ queries h
  · simpa [FreshAt, legalizeStrategy, hgood] using hgood.2
  · simpa [FreshAt, legalizeStrategy, hgood] using fallbackQuery_fresh hN h hlen

theorem legalizeStrategy_freshPath_of_length_le {N : ℕ} (hN : 0 < N)
    (proposed : K6Strategy N) (bits : List Bool) (hbits : bits.length ≤ N) :
    FreshPath (legalizeStrategy hN proposed) bits := by
  induction bits with
  | nil => simp [FreshPath, queries]
  | cons bit bits ih =>
      simp only [List.length_cons] at hbits
      have htail : bits.length < N := by omega
      rw [freshPath_cons]
      constructor
      · apply legalizeStrategy_freshAt hN proposed
        simpa using htail
      · exact ih (Nat.le_of_lt htail)

/-- Every proposed rule has an admissible completion, and the completion only
changes choices that were already illegal or repeated. -/
theorem legalizeStrategy_admissible {N : ℕ} (hN : 0 < N)
    (proposed : K6Strategy N) :
    Admissible (legalizeStrategy hN proposed) := by
  constructor
  · intro bits
    exact legalizeStrategy_freshPath_of_length_le hN proposed bits.toList
      (by simp)
  · intro h hlen
    exact legalizeStrategy_nonloop hN proposed h hlen

/-- Pathwise condition under which a proposed rule never invokes the
fallback.  The recursion follows the newest-first convention of `replay`. -/
def ProposedPathLegal {N : ℕ} (proposed : K6Strategy N) : List Bool → Prop
  | [] => True
  | _bit :: bits =>
      (¬(proposed (replay proposed bits)).IsDiag ∧
        proposed (replay proposed bits) ∉ queries (replay proposed bits)) ∧
      ProposedPathLegal proposed bits

/-- A completed proposed path is legal whenever its replay contains distinct
nonloop coordinates.  This convenient converse packages the recursive
condition expected by `legalizeStrategy`. -/
theorem proposedPathLegal_of_replay_nodup_nonloop {N : ℕ}
    (proposed : K6Strategy N) (bits : List Bool)
    (hnodup : (queries (replay proposed bits)).Nodup)
    (hnonloop : ∀ q ∈ queries (replay proposed bits), ¬q.IsDiag) :
    ProposedPathLegal proposed bits := by
  induction bits with
  | nil => simp [ProposedPathLegal]
  | cons bit bits ih =>
      simp only [replay_cons, queries, List.map_cons,
        List.nodup_cons] at hnodup
      rw [ProposedPathLegal]
      refine ⟨⟨?_, hnodup.1⟩, ih hnodup.2 ?_⟩
      · exact hnonloop _ (by simp [replay, queries])
      · intro q hq
        apply hnonloop q
        simp only [replay_cons, queries, List.map_cons, List.mem_cons]
        exact Or.inr hq

theorem replay_legalizeStrategy_eq_of_proposedPathLegal {N : ℕ}
    (hN : 0 < N) (proposed : K6Strategy N) (bits : List Bool)
    (hlegal : ProposedPathLegal proposed bits) :
    replay (legalizeStrategy hN proposed) bits = replay proposed bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rcases hlegal with ⟨hhead, htail⟩
      rw [replay_cons, replay_cons, ih htail]
      rw [legalizeStrategy_eq_of_legal_fresh hN proposed _ hhead]

/-- On a path on which the proposed branch-and-fill program is legal, every
success certificate for that program is also a certificate for its globally
admissible completion. -/
theorem answerVectorSucceeds_legalizeStrategy_of_proposed {N : ℕ}
    (hN : 0 < N) (proposed : K6Strategy N) (bits : List.Vector Bool N)
    (hlegal : ProposedPathLegal proposed bits.toList)
    (hsuccess : answerVectorSucceeds proposed bits) :
    answerVectorSucceeds (legalizeStrategy hN proposed) bits := by
  unfold answerVectorSucceeds at hsuccess ⊢
  rw [replay_legalizeStrategy_eq_of_proposedPathLegal hN proposed bits.toList hlegal]
  exact hsuccess

/-- Exact finite compiler from a partially specified branch-and-fill program
to `Achievable`.  The premise is an explicit Bernoulli sum over precisely the
answer paths on which the proposed program is legal and produces a `K6`; no
probabilistic or strategy-semantic assertion is hidden in the statement. -/
theorem achievable_of_proposed_goodPath_mass
    {N : ℕ} (hN : 0 < N) (p : ℝ≥0∞) (hp : p ≤ 1)
    (proposed : K6Strategy N)
    (hmass : threshold ≤
      ∑ bits : List.Vector Bool N,
        if ProposedPathLegal proposed bits.toList ∧
            answerVectorSucceeds proposed bits then
          (bits.toList.map (bernoulliWeight p)).prod else 0) :
    Achievable p N := by
  let strategy := legalizeStrategy hN proposed
  have hadmissible : Admissible strategy := legalizeStrategy_admissible hN proposed
  refine ⟨hp, strategy, hadmissible, ?_⟩
  rw [successProbability_eq_answer_sum p hp N strategy hadmissible.1]
  exact hmass.trans (Finset.sum_le_sum fun bits _ ↦ by
    by_cases hgood : ProposedPathLegal proposed bits.toList ∧
        answerVectorSucceeds proposed bits
    · have hs : answerVectorSucceeds strategy bits :=
        answerVectorSucceeds_legalizeStrategy_of_proposed hN proposed bits
          hgood.1 hgood.2
      simp [hgood, hs]
    · simp [hgood])

/-! ## A transcript-level branch-and-fill certificate -/

/-- Six vertices spanning positive queried edges give query-game success. -/
theorem transcriptSucceeds_of_sixSet {N : ℕ} (h : Transcript (Query N))
    (S : Finset (Vertex N)) (hcard : S.card = 6)
    (hcomplete : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (s(u, v), true) ∈ h) :
    TranscriptSucceeds h := by
  let e : Fin 6 ≃ ↑S := Fintype.equivOfCardEq (by simpa [hcard])
  let hom : K6 →g positiveGraph h :=
    { toFun := fun i ↦ (e i : Vertex N)
      map_rel' := by
        intro i j hij
        have hij' : i ≠ j := by
          simpa [K6, SimpleGraph.completeGraph_eq_top] using hij
        have heij : (e i : Vertex N) ≠ e j := fun heq ↦
          hij' (e.injective (Subtype.ext heq))
        exact ⟨heij, hcomplete (e i) (e i).property (e j) (e j).property heij⟩ }
  exact ⟨⟨hom, fun _ _ hij ↦ e.injective (Subtype.ext hij)⟩⟩

/-- The deterministic certificate produced by one successful branch-and-fill
trial: `A` consists of four filled vertices, all adjacent to a centre and a
branch root. -/
structure BranchFillWitness {N : ℕ} (h : Transcript (Query N)) where
  center : Vertex N
  root : Vertex N
  leaves : Finset (Vertex N)
  leaves_card : leaves.card = 4
  center_ne_root : center ≠ root
  center_not_mem : center ∉ leaves
  root_not_mem : root ∉ leaves
  center_root : (s(center, root), true) ∈ h
  center_leaf : ∀ v ∈ leaves, (s(center, v), true) ∈ h
  root_leaf : ∀ v ∈ leaves, (s(root, v), true) ∈ h
  leaf_leaf : ∀ u ∈ leaves, ∀ v ∈ leaves, u ≠ v → (s(u, v), true) ∈ h

/-- A branch-and-fill certificate really is a `K6` copy in the positive
transcript graph. -/
theorem BranchFillWitness.transcriptSucceeds {N : ℕ}
    {h : Transcript (Query N)} (w : BranchFillWitness h) :
    TranscriptSucceeds h := by
  let S := insert w.center (insert w.root w.leaves)
  apply transcriptSucceeds_of_sixSet h S
  · simp [S, w.center_ne_root, w.center_not_mem, w.root_not_mem,
      w.leaves_card]
  · intro u hu v hv huv
    simp only [S, Finset.mem_insert] at hu hv
    rcases hu with rfl | rfl | hu <;> rcases hv with rfl | rfl | hv
    · exact False.elim (huv rfl)
    · exact w.center_root
    · exact w.center_leaf v hv
    · simpa only [Sym2.eq_swap] using w.center_root
    · exact False.elim (huv rfl)
    · exact w.root_leaf v hv
    · simpa only [Sym2.eq_swap] using w.center_leaf u hu
    · simpa only [Sym2.eq_swap] using w.root_leaf u hu
    · exact w.leaf_leaf u hu v hv huv

/-! ## Connecting the one-trial board to the certificate -/

/-- Positive `trialK4Count` is equivalent to an explicit successful
four-subset.  This exposes the witness hidden inside the moment argument. -/
theorem k4TrialSucceeds_iff_exists_fourSet (a : ℕ)
    (board : Board (Sym2 (TrialVertex a))) :
    k4TrialSucceeds a board ↔
      ∃ A ∈ (Finset.univ : Finset (TrialVertex a)).powersetCard 4,
        board ∈ AllTrue (cliqueEdges A) := by
  unfold k4TrialSucceeds trialK4Count
  rw [ENNReal.toReal_pos_iff]
  constructor
  · rintro ⟨hpos, _htop⟩
    rw [k4Count, Finset.sum_pos_iff] at hpos
    obtain ⟨A, hA, hApos⟩ := hpos
    refine ⟨A, hA, ?_⟩
    unfold allTrueIndicator at hApos
    split at hApos
    · assumption
    · simp at hApos
  · rintro ⟨A, hA, htrue⟩
    constructor
    · rw [k4Count, Finset.sum_pos_iff]
      refine ⟨A, hA, ?_⟩
      simp [allTrueIndicator, htrue]
    · exact lt_top_iff_ne_top.mpr
        (k4Count_ne_top (Finset.univ : Finset (TrialVertex a)) cliqueEdges board)

/-- A successful trial board embedded into a genuinely queried filled set
produces the exact branch-and-fill witness needed for a `K6`. -/
theorem transcriptSucceeds_of_embedded_k4Trial
    {N a : ℕ} (h : Transcript (Query N))
    (board : Board (Sym2 (TrialVertex a)))
    (embed : TrialVertex a ↪ Vertex N)
    (center root : Vertex N)
    (hcenterRoot : center ≠ root)
    (hcenterRange : ∀ x, center ≠ embed x)
    (hrootRange : ∀ x, root ≠ embed x)
    (hcr : (s(center, root), true) ∈ h)
    (hc : ∀ x, (s(center, embed x), true) ∈ h)
    (hr : ∀ x, (s(root, embed x), true) ∈ h)
    (hfill : ∀ x y, x ≠ y →
      (s(embed x, embed y), board s(x, y)) ∈ h)
    (hsuccess : k4TrialSucceeds a board) :
    TranscriptSucceeds h := by
  rw [k4TrialSucceeds_iff_exists_fourSet] at hsuccess
  obtain ⟨A, hApow, hAtrue⟩ := hsuccess
  have hAsub : A ⊆ (Finset.univ : Finset (TrialVertex a)) :=
    (Finset.mem_powersetCard.mp hApow).1
  have hAcard : A.card = 4 := (Finset.mem_powersetCard.mp hApow).2
  let leaves : Finset (Vertex N) := A.map embed
  have hleavesCard : leaves.card = 4 := by simp [leaves, hAcard]
  have hcnot : center ∉ leaves := by
    intro hmem
    simp only [leaves, Finset.mem_map] at hmem
    obtain ⟨x, _hx, heq⟩ := hmem
    exact hcenterRange x heq.symm
  have hrnot : root ∉ leaves := by
    intro hmem
    simp only [leaves, Finset.mem_map] at hmem
    obtain ⟨x, _hx, heq⟩ := hmem
    exact hrootRange x heq.symm
  let witness : BranchFillWitness h :=
    { center := center
      root := root
      leaves := leaves
      leaves_card := hleavesCard
      center_ne_root := hcenterRoot
      center_not_mem := hcnot
      root_not_mem := hrnot
      center_root := hcr
      center_leaf := by
        intro v hv
        simp only [leaves, Finset.mem_map] at hv
        obtain ⟨x, _hx, rfl⟩ := hv
        exact hc x
      root_leaf := by
        intro v hv
        simp only [leaves, Finset.mem_map] at hv
        obtain ⟨x, _hx, rfl⟩ := hv
        exact hr x
      leaf_leaf := by
        intro u hu v hv huv
        simp only [leaves, Finset.mem_map] at hu hv
        obtain ⟨x, hxA, rfl⟩ := hu
        obtain ⟨y, hyA, rfl⟩ := hv
        have hxy : x ≠ y := fun hxy ↦ huv (congrArg embed hxy)
        have hedge : s(x, y) ∈ cliqueEdges A := by
          exact (mem_cliqueEdges).2 ⟨hxA, hyA, hxy⟩
        have htrue : board s(x, y) = true := hAtrue _ hedge
        simpa [htrue] using hfill x y hxy }
  exact witness.transcriptSucceeds

/-! ## Removing the unused diagonal coordinates from the trial boards

The moment calculation samples a board on all of `Sym2`, including diagonal
coordinates, whereas an admissible query strategy may reveal only nonloops.
The following finite marginalization result proves that those unused
coordinates integrate out exactly. -/

section Marginalization

universe u

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Split a finite board into its restrictions to a predicate and its
complement. -/
def splitBoardEquiv (P : Q → Prop) [DecidablePred P] :
    Board Q ≃ Board {q : Q // P q} × Board {q : Q // ¬P q} where
  toFun board := (fun q ↦ board q, fun q ↦ board q)
  invFun boards q := if hq : P q then boards.1 ⟨q, hq⟩ else boards.2 ⟨q, hq⟩
  left_inv board := by
    funext q
    by_cases hq : P q <;> simp [hq]
  right_inv boards := by
    apply Prod.ext <;> funext q
    · simp [q.property]
    · simp [q.property]

/-- Product point masses factor under the board split. -/
theorem boardWeight_split (weight : Bool → ℝ≥0∞) (P : Q → Prop)
    [DecidablePred P] (board : Board Q) :
    boardWeight weight board =
      boardWeight weight (splitBoardEquiv P board).1 *
        boardWeight weight (splitBoardEquiv P board).2 := by
  classical
  unfold boardWeight
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ P
    (fun q ↦ weight (board q))]
  congr 1
  · rw [Finset.prod_subtype (p := P) (Finset.univ.filter P) (by simp)]
    rfl
  · rw [Finset.prod_subtype (p := fun q ↦ ¬P q)
      (Finset.univ.filter fun q ↦ ¬P q) (by simp)]
    rfl

/-- Exact product-measure marginalization on a finite coordinate subtype. -/
theorem finiteBoardMass_restrict (weight : Bool → ℝ≥0∞)
    (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (P : Q → Prop) [DecidablePred P]
    (event : Set (Board {q : Q // P q})) :
    finiteBoardMass weight
        {board : Board Q | (splitBoardEquiv P board).1 ∈ event} =
      finiteBoardMass weight event := by
  classical
  unfold finiteBoardMass
  change (∑ board : Board Q,
      if (splitBoardEquiv P board).1 ∈ event then boardWeight weight board else 0) = _
  rw [Fintype.sum_equiv (splitBoardEquiv P)
    (fun board : Board Q ↦
      if (splitBoardEquiv P board).1 ∈ event then boardWeight weight board else 0)
    (fun boards : Board {q : Q // P q} × Board {q : Q // ¬P q} ↦
      if boards.1 ∈ event then
        boardWeight weight boards.1 * boardWeight weight boards.2 else 0)
    (by
      intro board
      by_cases hevent : (splitBoardEquiv P board).1 ∈ event
      · simp [hevent, boardWeight_split weight P board]
      · simp [hevent])]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro kept _hkept
  by_cases hevent : kept ∈ event
  · simp only [hevent, if_true, ← Finset.mul_sum]
    rw [sum_boardWeight weight hnormalized]
    simp
  · simp [hevent]

end Marginalization

/-- Genuine (nonloop) coordinates of a one-trial filled graph. -/
abbrev OffDiagTrialQuery (a : ℕ) :=
  {q : Sym2 (TrialVertex a) // ¬q.IsDiag}

/-- Extend an off-diagonal trial board by assigning an arbitrary value to
diagonals.  Clique success is insensitive to this choice. -/
def extendOffDiagTrialBoard (a : ℕ) (board : Board (OffDiagTrialQuery a)) :
    Board (Sym2 (TrialVertex a)) := fun q ↦
  if hq : ¬q.IsDiag then board ⟨q, hq⟩ else false

/-- Success predicate on exactly the coordinates a legal fill queries. -/
def offDiagTrialSucceeds (a : ℕ) (board : Board (OffDiagTrialQuery a)) : Prop :=
  k4TrialSucceeds a (extendOffDiagTrialBoard a board)

/-- Restricting a full trial board and extending it back does not alter any
off-diagonal coordinate. -/
theorem extend_restrict_offDiag (a : ℕ)
    (board : Board (Sym2 (TrialVertex a)))
    (q : Sym2 (TrialVertex a)) (hq : ¬q.IsDiag) :
    extendOffDiagTrialBoard a
        (splitBoardEquiv (fun q : Sym2 (TrialVertex a) ↦ ¬q.IsDiag) board).1 q =
      board q := by
  simp [extendOffDiagTrialBoard, hq, splitBoardEquiv]

/-- `K4` success depends only on off-diagonal coordinates. -/
theorem k4TrialSucceeds_extend_restrict_iff (a : ℕ)
    (board : Board (Sym2 (TrialVertex a))) :
    k4TrialSucceeds a
        (extendOffDiagTrialBoard a
          (splitBoardEquiv (fun q : Sym2 (TrialVertex a) ↦ ¬q.IsDiag) board).1) ↔
      k4TrialSucceeds a board := by
  rw [k4TrialSucceeds_iff_exists_fourSet,
    k4TrialSucceeds_iff_exists_fourSet]
  constructor <;> rintro ⟨A, hA, hall⟩ <;> refine ⟨A, hA, ?_⟩
  · intro q hq
    induction q using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := (mem_cliqueEdges.mp hq).2.2
      have hnonloop : ¬s(x, y).IsDiag := by simpa using hxy
      have ht := hall s(x, y) hq
      rw [extend_restrict_offDiag a board s(x, y) hnonloop] at ht
      exact ht
  · intro q hq
    induction q using Sym2.ind with
    | _ x y =>
      have hxy : x ≠ y := (mem_cliqueEdges.mp hq).2.2
      have hnonloop : ¬s(x, y).IsDiag := by simpa using hxy
      rw [extend_restrict_offDiag a board s(x, y) hnonloop]
      exact hall s(x, y) hq

/-- The one-trial success mass is unchanged when diagonal coordinates are
removed. -/
theorem offDiagTrialSuccessMass_eq (a : ℕ) (ha : 2 ≤ a) :
    finiteBoardMass (bernoulliWeight (densityENN a))
        {board : Board (OffDiagTrialQuery a) | offDiagTrialSucceeds a board} =
      finiteBoardMass (bernoulliWeight (densityENN a))
        {board | k4TrialSucceeds a board} := by
  let P : Sym2 (TrialVertex a) → Prop := fun q ↦ ¬q.IsDiag
  rw [← finiteBoardMass_restrict (bernoulliWeight (densityENN a))
    (sum_bernoulliWeight (densityENN a) (densityENN_le_one a ha)) P
    {board : Board (OffDiagTrialQuery a) | offDiagTrialSucceeds a board}]
  apply congrArg (finiteBoardMass (bernoulliWeight (densityENN a)))
  ext board
  exact k4TrialSucceeds_extend_restrict_iff a board

/-- Repeated failure mass using only the legal, off-diagonal fill boards. -/
noncomputable def repeatedOffDiagK4FailureMass (a t : ℕ) : ℝ≥0∞ :=
  finiteOutcomeProductMass
    (fun board : Board (OffDiagTrialQuery a) ↦
      boardWeight (bernoulliWeight (densityENN a)) board) t
    (allTrialsFailEvent (offDiagTrialSucceeds a) t)

/-- Removing the unused diagonal coordinates preserves the complete
independent amplification calculation exactly. -/
theorem repeatedOffDiagK4FailureMass_eq (a t : ℕ) (ha : 2 ≤ a) :
    repeatedOffDiagK4FailureMass a t = repeatedK4FailureMass a t := by
  unfold repeatedOffDiagK4FailureMass repeatedK4FailureMass
  rw [finiteOutcomeProductMass_allTrialsFail_eq_one_sub_pow
    (fun board : Board (OffDiagTrialQuery a) ↦
      boardWeight (bernoulliWeight (densityENN a)) board)
    (offDiagTrialSucceeds a) t
    (sum_boardWeight _
      (sum_bernoulliWeight (densityENN a) (densityENN_le_one a ha)))]
  rw [finiteOutcomeProductMass_allTrialsFail_eq_one_sub_pow
    (k4TrialBoardWeight a) (k4TrialSucceeds a) t
    (sum_k4TrialBoardWeight a ha)]
  congr 2
  rw [oneTrialSuccessMass_k4_eq]
  change finiteBoardMass (bernoulliWeight (densityENN a))
      {board : Board (OffDiagTrialQuery a) | offDiagTrialSucceeds a board} =
    finiteBoardMass (bernoulliWeight (densityENN a))
      {board : Board (Sym2 (TrialVertex a)) | k4TrialSucceeds a board}
  exact offDiagTrialSuccessMass_eq a ha

/-- Thus the concrete amplification theorem is already a theorem about the
nonloop coordinates that an admissible fill strategy can actually query. -/
theorem repeatedOffDiagK4FailureMass_toReal_le_half (a : ℕ) (ha : 2 ≤ a) :
    (repeatedOffDiagK4FailureMass a
      (K6Upper.momentAmplification * a ^ 2)).toReal ≤ (1 : ℝ) / 2 := by
  rw [repeatedOffDiagK4FailureMass_eq a _ ha]
  exact repeatedK4FailureMass_toReal_le_half a ha

/-! ## Sequential fill answers are exactly the amplified product space -/

/-- Number of legal fill-edge answers in `t` consecutive complete trial
blocks. -/
def fillAnswerCount (a t : ℕ) : ℕ :=
  t * Fintype.card (OffDiagTrialQuery a)

/-- Pack a chronological vector of consecutive fill answers into one legal
off-diagonal board per trial.  The coordinate order is canonical but
mathematically immaterial. -/
noncomputable def packFillAnswers (a t : ℕ)
    (bits : List.Vector Bool (fillAnswerCount a t)) :
    Fin t → Board (OffDiagTrialQuery a) := fun i q ↦
  bits.get (finProdFinEquiv
    (i, Fintype.equivFin (OffDiagTrialQuery a) q))

/-- Inverse operation to `packFillAnswers`. -/
noncomputable def unpackFillAnswers (a t : ℕ)
    (boards : Fin t → Board (OffDiagTrialQuery a)) :
    List.Vector Bool (fillAnswerCount a t) := List.Vector.ofFn fun j ↦
  let iq := finProdFinEquiv.symm j
  boards iq.1 ((Fintype.equivFin (OffDiagTrialQuery a)).symm iq.2)

theorem unpack_pack_fillAnswers (a t : ℕ)
    (bits : List.Vector Bool (fillAnswerCount a t)) :
    unpackFillAnswers a t (packFillAnswers a t bits) = bits := by
  apply List.Vector.ext
  intro j
  simp only [unpackFillAnswers, List.Vector.get_ofFn, packFillAnswers,
    fillAnswerCount]
  rw [Equiv.apply_symm_apply (Fintype.equivFin (OffDiagTrialQuery a))]
  exact congrArg bits.get (Equiv.apply_symm_apply finProdFinEquiv j)

theorem pack_unpack_fillAnswers (a t : ℕ)
    (boards : Fin t → Board (OffDiagTrialQuery a)) :
    packFillAnswers a t (unpackFillAnswers a t boards) = boards := by
  funext i q
  simp only [packFillAnswers, unpackFillAnswers, List.Vector.get_ofFn,
    fillAnswerCount]
  rw [Equiv.symm_apply_apply]
  simp

/-- Canonical equivalence between a sequential answer block and the product
of all legal trial boards. -/
noncomputable def fillAnswerEquiv (a t : ℕ) :
    List.Vector Bool (fillAnswerCount a t) ≃
      (Fin t → Board (OffDiagTrialQuery a)) where
  toFun := packFillAnswers a t
  invFun := unpackFillAnswers a t
  left_inv := unpack_pack_fillAnswers a t
  right_inv := pack_unpack_fillAnswers a t

@[simp] theorem fillAnswerEquiv_apply (a t : ℕ)
    (bits : List.Vector Bool (fillAnswerCount a t))
    (i : Fin t) (q : OffDiagTrialQuery a) :
    fillAnswerEquiv a t bits i q =
      bits.get (finProdFinEquiv
        (i, Fintype.equivFin (OffDiagTrialQuery a) q)) := rfl

/-- The Bernoulli path weight of a sequential fill block factors as the
product point mass of its packed trial boards. -/
theorem fillAnswerEquiv_weight (p : ℝ≥0∞) (a t : ℕ)
    (bits : List.Vector Bool (fillAnswerCount a t)) :
    (bits.toList.map (bernoulliWeight p)).prod =
      outcomeVectorWeight
        (fun board : Board (OffDiagTrialQuery a) ↦
          boardWeight (bernoulliWeight p) board)
        (fillAnswerEquiv a t bits) := by
  let e := Fintype.equivFin (OffDiagTrialQuery a)
  have hlist : bits.toList = List.ofFn bits.get := by
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  simp only [outcomeVectorWeight, boardWeight, fillAnswerEquiv,
    packFillAnswers]
  rw [hlist, List.map_ofFn, List.prod_ofFn]
  change (∏ j : Fin (t * Fintype.card (OffDiagTrialQuery a)),
      bernoulliWeight p (bits.get j)) = _
  rw [Fintype.prod_equiv finProdFinEquiv.symm
    (fun j : Fin (t * Fintype.card (OffDiagTrialQuery a)) ↦
      bernoulliWeight p (bits.get j))
    (fun iq : Fin t × Fin (Fintype.card (OffDiagTrialQuery a)) ↦
      bernoulliWeight p (bits.get (finProdFinEquiv iq))) (by
        intro j
        exact congrArg (fun z ↦ bernoulliWeight p (bits.get z))
          (Equiv.apply_symm_apply finProdFinEquiv j).symm)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [Fintype.prod_equiv e.symm
    (fun k : Fin (Fintype.card (OffDiagTrialQuery a)) ↦
      bernoulliWeight p (bits.get (finProdFinEquiv (i, k))))
    (fun q : OffDiagTrialQuery a ↦
      bernoulliWeight p
        (bits.get (finProdFinEquiv (i, e q)))) (by simp)]
  apply Finset.prod_congr rfl
  intro q _hq
  rfl

/-- Exact finite answer-path/product-mass bridge for consecutive fresh fill
blocks.  After packing, the event that every trial fails has exactly the
`repeatedOffDiagK4FailureMass` used by amplification. -/
theorem sequentialFill_allFailure_weight_eq (a t : ℕ) :
    (∑ bits : List.Vector Bool (fillAnswerCount a t),
      if fillAnswerEquiv a t bits ∈
          allTrialsFailEvent (offDiagTrialSucceeds a) t then
        (bits.toList.map (bernoulliWeight (densityENN a))).prod else 0) =
      repeatedOffDiagK4FailureMass a t := by
  unfold repeatedOffDiagK4FailureMass finiteOutcomeProductMass
  apply Fintype.sum_equiv (fillAnswerEquiv a t)
  intro bits
  by_cases hfail : fillAnswerEquiv a t bits ∈
      allTrialsFailEvent (offDiagTrialSucceeds a) t
  · simp [hfail, fillAnswerEquiv_weight]
  · simp [hfail]

/-- Board event obtained by interpreting the complete answer vector of a
fresh sequential fill program as `t` off-diagonal trial boards. -/
def sequentialFillFailureEvent {Q : Type*}
    (strategy : Strategy Q) (a t : ℕ) : Set (Board Q) :=
  {board | fillAnswerEquiv a t
      (answerVector strategy board (fillAnswerCount a t)) ∈
        allTrialsFailEvent (offDiagTrialSucceeds a) t}

/-- Exact adaptive product-law bridge.  For *any* strategy whose coordinates
are fresh on all paths of the fill horizon, the extracted consecutive fill
boards have precisely the independent product failure mass used in
`Amplification.lean`.  The strategy may choose the actual host coordinates
adaptively; freshness is the only probabilistic requirement. -/
theorem finiteBoardMass_sequentialFillFailureEvent_eq
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (strategy : Strategy Q) (a t : ℕ) (ha : 2 ≤ a)
    (hfresh : ∀ bits : List.Vector Bool (fillAnswerCount a t),
      FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight (densityENN a))
        (sequentialFillFailureEvent strategy a t) =
      repeatedOffDiagK4FailureMass a t := by
  unfold sequentialFillFailureEvent
  rw [finiteProduct_answerVector_event_mass
    (bernoulliWeight (densityENN a))
    (sum_bernoulliWeight (densityENN a) (by
      exact densityENN_le_one a ha))
    strategy (fillAnswerCount a t)
    (fun bits ↦ fillAnswerEquiv a t bits ∈
      allTrialsFailEvent (offDiagTrialSucceeds a) t) hfresh]
  exact sequentialFill_allFailure_weight_eq a t

/-- The exact bridge immediately imports the amplified one-half failure
bound for a fresh consecutive fill phase of the concrete length. -/
theorem finiteBoardMass_sequentialFillFailureEvent_toReal_le_half
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (strategy : Strategy Q) (a : ℕ) (ha : 2 ≤ a)
    (hfresh : ∀ bits : List.Vector Bool
        (fillAnswerCount a (K6Upper.momentAmplification * a ^ 2)),
      FreshPath strategy bits.toList) :
    (finiteBoardMass (bernoulliWeight (densityENN a))
      (sequentialFillFailureEvent strategy a
        (K6Upper.momentAmplification * a ^ 2))).toReal ≤ (1 : ℝ) / 2 := by
  rw [finiteBoardMass_sequentialFillFailureEvent_eq strategy a
    (K6Upper.momentAmplification * a ^ 2) ha hfresh]
  exact repeatedOffDiagK4FailureMass_toReal_le_half a ha

/-! ## A finite empty-block tail for reservoir scans -/

/-- A scan is arranged as `groups` blocks of `blockSize` fresh coordinates.
A block is empty when all of its answers are negative. -/
def EmptyBlock {groups blockSize : ℕ}
    (board : Board (Fin groups × Fin blockSize)) (i : Fin groups) : Prop :=
  ∀ j, board (i, j) = false

/-- Number of empty blocks in a grouped scan. -/
def emptyBlockCount {groups blockSize : ℕ}
    (board : Board (Fin groups × Fin blockSize)) : ℕ :=
  ((Finset.univ : Finset (Fin groups)).filter fun i ↦ EmptyBlock board i).card

/-- Event that at least `R` blocks in a grouped scan are empty. -/
def emptyBlockUpperTailEvent (groups blockSize R : ℕ) :
    Set (Board (Fin groups × Fin blockSize)) :=
  {board | R ≤ emptyBlockCount board}

/-- Exact mass of one specified empty block. -/
theorem finiteBoardMass_emptyBlock (p : ℝ≥0∞) (hp : p ≤ 1)
    (groups blockSize : ℕ) (i : Fin groups) :
    finiteBoardMass (bernoulliWeight p)
        {board : Board (Fin groups × Fin blockSize) | EmptyBlock board i} =
      (1 - p) ^ blockSize := by
  let S : Finset (Fin groups × Fin blockSize) :=
    {i} ×ˢ (Finset.univ : Finset (Fin blockSize))
  have hset : {board : Board (Fin groups × Fin blockSize) |
      EmptyBlock board i} = assignmentCylinder S (fun _ ↦ false) := by
    ext board
    constructor
    · intro hempty q hq
      rcases q with ⟨q₁, q₂⟩
      rcases Finset.mem_product.mp hq with ⟨hq₁, _hq₂⟩
      have hfirst : q₁ = i := by simpa using hq₁
      subst q₁
      exact hempty q₂
    · intro hcyl j
      exact hcyl (i, j) (by simp [S])
  rw [hset, finiteBoardMass_assignmentCylinder (bernoulliWeight p)
    (sum_bernoulliWeight p hp)]
  have hcard : S.card = blockSize := by simp [S]
  rw [show (∏ q ∈ S, bernoulliWeight p false) =
      (1 - p) ^ blockSize by simp [bernoulliWeight, hcard]]

/-- First-moment/Markov tail for empty scan blocks.  It needs no independence
between the block indicators beyond the exact mass of each block cylinder:

`R * P(at least R empty blocks) ≤ groups * (1-p)^blockSize`.

This is the robust finite substitute for the reservoir and common-neighbour
Chernoff steps in the branch-and-fill argument. -/
theorem emptyBlockUpperTail_mul_le
    (p : ℝ≥0∞) (hp : p ≤ 1) (groups blockSize R : ℕ) :
    (R : ℝ≥0∞) *
        finiteBoardMass (bernoulliWeight p)
          (emptyBlockUpperTailEvent groups blockSize R) ≤
      (groups : ℝ≥0∞) * (1 - p) ^ blockSize := by
  classical
  unfold finiteBoardMass emptyBlockUpperTailEvent
  simp only [Set.mem_setOf_eq]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ board : Board (Fin groups × Fin blockSize),
          boardWeight (bernoulliWeight p) board *
            (emptyBlockCount board : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro board _hboard
      by_cases htail : R ≤ emptyBlockCount board
      · rw [if_pos htail]
        have hcast : (R : ℝ≥0∞) ≤ (emptyBlockCount board : ℝ≥0∞) := by
          exact_mod_cast htail
        simpa [mul_comm] using
          mul_le_mul_right' hcast (boardWeight (bernoulliWeight p) board)
      · simp [htail]
    _ = ∑ i : Fin groups,
          finiteBoardMass (bernoulliWeight p)
            {board : Board (Fin groups × Fin blockSize) | EmptyBlock board i} := by
      have hcount (board : Board (Fin groups × Fin blockSize)) :
          (emptyBlockCount board : ℝ≥0∞) =
            ∑ i : Fin groups, if EmptyBlock board i then 1 else 0 := by
        unfold emptyBlockCount
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        simp
      calc
        _ = ∑ board : Board (Fin groups × Fin blockSize),
            ∑ i : Fin groups,
              if EmptyBlock board i then
                boardWeight (bernoulliWeight p) board else 0 := by
          apply Finset.sum_congr rfl
          intro board _hboard
          rw [hcount board, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hempty : EmptyBlock board i <;> simp [hempty]
        _ = ∑ i : Fin groups,
            ∑ board : Board (Fin groups × Fin blockSize),
              if EmptyBlock board i then
                boardWeight (bernoulliWeight p) board else 0 :=
          Finset.sum_comm
        _ = _ := by rfl
    _ = ∑ _i : Fin groups, (1 - p) ^ blockSize := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact finiteBoardMass_emptyBlock p hp groups blockSize i
    _ = (groups : ℝ≥0∞) * (1 - p) ^ blockSize := by simp

/-! ## Pathwise coupling of legal fill boards to the host transcript -/

/-- One off-diagonal trial board, embedded into the host transcript together
with its already-discovered centre and root, is enough for success whenever
the trial board contains a four-clique. -/
theorem transcriptSucceeds_of_embedded_offDiagTrial
    {N a : ℕ} (h : Transcript (Query N))
    (board : Board (OffDiagTrialQuery a))
    (embed : TrialVertex a ↪ Vertex N)
    (center root : Vertex N)
    (hcenterRoot : center ≠ root)
    (hcenterRange : ∀ x, center ≠ embed x)
    (hrootRange : ∀ x, root ≠ embed x)
    (hcr : (s(center, root), true) ∈ h)
    (hc : ∀ x, (s(center, embed x), true) ∈ h)
    (hr : ∀ x, (s(root, embed x), true) ∈ h)
    (hfill : ∀ q : OffDiagTrialQuery a,
      (Sym2.map embed q, board q) ∈ h)
    (hsuccess : offDiagTrialSucceeds a board) :
    TranscriptSucceeds h := by
  apply transcriptSucceeds_of_embedded_k4Trial h
    (extendOffDiagTrialBoard a board) embed center root hcenterRoot
    hcenterRange hrootRange hcr hc hr
  · intro x y hxy
    let q : OffDiagTrialQuery a :=
      ⟨s(x, y), by simpa [Sym2.mk_isDiag_iff] using hxy⟩
    have hq := hfill q
    simpa [q, Sym2.map_pair_eq, extendOffDiagTrialBoard, hxy,
      Sym2.mk_isDiag_iff] using hq
  · exact hsuccess

/-- Complete pathwise data furnished by the reservoir/branch/fill phase for
a family of disjoint legal fill boards.  This structure contains no
probability assumption: every field is a statement about one concrete
transcript and its extracted boards. -/
structure EmbeddedTrialFamily {N a t : ℕ} (h : Transcript (Query N))
    (boards : Fin t → Board (OffDiagTrialQuery a)) where
  embed : Fin t → TrialVertex a ↪ Vertex N
  center : Fin t → Vertex N
  root : Fin t → Vertex N
  center_ne_root : ∀ i, center i ≠ root i
  center_ne_fill : ∀ i x, center i ≠ embed i x
  root_ne_fill : ∀ i x, root i ≠ embed i x
  center_root_positive : ∀ i, (s(center i, root i), true) ∈ h
  center_fill_positive : ∀ i x, (s(center i, embed i x), true) ∈ h
  root_fill_positive : ∀ i x, (s(root i, embed i x), true) ∈ h
  fill_answers : ∀ i (q : OffDiagTrialQuery a),
    (Sym2.map (embed i) (q : Sym2 (TrialVertex a)), boards i q) ∈ h

/-- The deterministic implication needed by amplification: if any extracted
legal fill board succeeds, then the actual positive transcript contains a
`K6`. -/
theorem EmbeddedTrialFamily.transcriptSucceeds_of_exists
    {N a t : ℕ} {h : Transcript (Query N)}
    {boards : Fin t → Board (OffDiagTrialQuery a)}
    (family : EmbeddedTrialFamily h boards)
    (hsuccess : ∃ i, offDiagTrialSucceeds a (boards i)) :
    TranscriptSucceeds h := by
  obtain ⟨i, hi⟩ := hsuccess
  exact transcriptSucceeds_of_embedded_offDiagTrial h (boards i)
    (family.embed i) (family.center i) (family.root i)
    (family.center_ne_root i) (family.center_ne_fill i)
    (family.root_ne_fill i) (family.center_root_positive i)
    (family.center_fill_positive i) (family.root_fill_positive i)
    (family.fill_answers i) hi

/-- Contrapositive form matching `allTrialsFailEvent`: failure of the host
strategy forces every coupled fill board to fail. -/
theorem EmbeddedTrialFamily.allTrialsFail_of_not_transcriptSucceeds
    {N a t : ℕ} {h : Transcript (Query N)}
    {boards : Fin t → Board (OffDiagTrialQuery a)}
    (family : EmbeddedTrialFamily h boards)
    (hfailure : ¬TranscriptSucceeds h) :
    boards ∈ allTrialsFailEvent (offDiagTrialSucceeds a) t := by
  intro i hi
  exact hfailure (family.transcriptSucceeds_of_exists ⟨i, hi⟩)

/-! ## Deterministic slack geometry and query budget

The probabilistic reservoir construction is most convenient with genuine
slack.  We split every scan into blocks of `64 * a³` coordinates and use
`2 * a⁴` blocks in a branch scan.  Thus a branch attempt scans
`128 * a⁷` candidates.  We schedule twice as many branch attempts as the
number of fills ultimately needed by the moment amplification.

The reservoir below contains the complete branch scan plus enough additional
vertices to discard one root and a set of `a⁴` leaves after every attempted
branch.  The elementary capacity theorem makes the disjointness bookkeeping
explicit; it is not a probabilistic hypothesis.
-/

/-- Number of amplified fill trials ultimately required. -/
def slackTrialCount (a : ℕ) : ℕ :=
  K6Upper.momentAmplification * a ^ 2

/-- Number of branch attempts made, allowing a factor-two failure slack. -/
def slackAttemptCount (a : ℕ) : ℕ :=
  2 * slackTrialCount a

/-- Size of one selected common-neighbour set. -/
def slackFillSize (a : ℕ) : ℕ := a ^ 4

/-- Number of fresh coordinates in one positivity-search block. -/
def slackBlockSize (a : ℕ) : ℕ := 64 * a ^ 3

/-- Number of blocks in one branch scan. -/
def slackBranchGroups (a : ℕ) : ℕ := 2 * a ^ 4

/-- Total number of candidate queries in one branch scan. -/
def slackBranchScan (a : ℕ) : ℕ :=
  slackBranchGroups a * slackBlockSize a

theorem slackBranchScan_eq (a : ℕ) :
    slackBranchScan a = 128 * a ^ 7 := by
  unfold slackBranchScan slackBranchGroups slackBlockSize
  ring

/-- Star-positive vertices reserved before branch scans begin.  Besides a
whole branch scan, this reserves one root and one fill set for every attempted
branch. -/
def slackReservoirSize (a : ℕ) : ℕ :=
  slackBranchScan a + slackAttemptCount a * (slackFillSize a + 1)

/-- Initial centre-star queries: twice as many blocks as required reservoir
vertices, each of size `64 * a³`. -/
def slackStarQueries (a : ℕ) : ℕ :=
  (2 * slackReservoirSize a) * slackBlockSize a

/-- Full deterministic query budget for the slack construction. -/
def slackQueryBudget (a : ℕ) : ℕ :=
  slackStarQueries a +
    slackAttemptCount a * slackBranchScan a +
    slackTrialCount a * K6Upper.fillCost (slackFillSize a)

/-- Length of the final complete-fill phase. -/
def slackFillQueryCount (a : ℕ) : ℕ :=
  slackTrialCount a * K6Upper.fillCost (slackFillSize a)

/-- Number of queries before the complete-fill phase begins. -/
def slackFillStart (a : ℕ) : ℕ :=
  slackStarQueries a + slackAttemptCount a * slackBranchScan a

theorem slackQueryBudget_eq_fillStart_add (a : ℕ) :
    slackQueryBudget a = slackFillStart a + slackFillQueryCount a := by
  rfl

/-- Explicit absolute coefficient in the slack query bound. -/
def slackUpperConstant : ℕ :=
  16896 + 257 * K6Upper.momentAmplification

/-- At the cubic density scale, a `64 a³` block is empty with probability
at most `2⁻⁶⁴`.  The proof uses only the elementary exponential
inequality already used by the amplification layer. -/
theorem one_sub_densityENN_pow_slackBlockSize_le
    (a : ℕ) (ha : 2 ≤ a) :
    (1 - densityENN a) ^ slackBlockSize a ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 64 := by
  have ha0 : 0 < a := by omega
  have hdensityMul : K4MomentBounds.density a *
      ((slackBlockSize a : ℕ) : ℝ) = 64 := by
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
    unfold K4MomentBounds.density slackBlockSize
    norm_num
    field_simp [ne_of_gt haR]
  have hexp := Amplification.one_sub_pow_le_exp_neg_mul
    (K4OneTrial.density_le_one a ha) (slackBlockSize a)
  apply (ENNReal.toReal_le_toReal
    (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top (by simp))).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le]
  · rw [ENNReal.toReal_one, K4OneTrial.densityENN_toReal]
    calc
      (1 - K4MomentBounds.density a) ^ slackBlockSize a ≤
          Real.exp (-K4MomentBounds.density a *
            ((slackBlockSize a : ℕ) : ℝ)) := hexp
      _ = Real.exp (-1) ^ 64 := by
        rw [neg_mul, hdensityMul]
        convert Real.exp_nat_mul (-1) 64 using 1 <;> norm_num
      _ ≤ ((2 : ℝ)⁻¹) ^ 64 := by
        have hhalf : Real.exp (-1) ≤ (2 : ℝ)⁻¹ := by
          simpa only [one_div] using Amplification.exp_neg_one_le_half
        exact pow_le_pow_left₀ (Real.exp_pos (-1)).le hhalf 64
      _ = (((2 : ℝ≥0∞)⁻¹) ^ 64).toReal := by norm_num
  · exact K4OneTrial.densityENN_le_one a ha
  · simp

/-- The same block bound is robust throughout the density bucket
`a⁻³ ≤ p ≤ 1`. -/
theorem one_sub_pow_slackBlockSize_le
    (a : ℕ) (ha : 2 ≤ a) (p : ℝ≥0∞)
    (hdensity : densityENN a ≤ p) :
    (1 - p) ^ slackBlockSize a ≤ ((2 : ℝ≥0∞)⁻¹) ^ 64 := by
  calc
    (1 - p) ^ slackBlockSize a ≤
        (1 - densityENN a) ^ slackBlockSize a := by
      gcongr
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ 64 :=
      one_sub_densityENN_pow_slackBlockSize_le a ha

/-- Uniform tail for a grouped fresh scan: among `2R` blocks of size
`64a³`, the probability that at least `R` blocks are empty is at most
`2⁻⁶³`.  This is the quantitative concentration input used by both the
initial reservoir and every branch scan. -/
theorem emptyBlockHalfTail_le
    (a R : ℕ) (ha : 2 ≤ a) (hR : 0 < R)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    finiteBoardMass (bernoulliWeight p)
        (emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  have hmarkov := emptyBlockUpperTail_mul_le p hp
    (2 * R) (slackBlockSize a) R
  have hpow := one_sub_pow_slackBlockSize_le a ha p hdensity
  have hmul : (R : ℝ≥0∞) *
      finiteBoardMass (bernoulliWeight p)
        (emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R) ≤
      (2 * R : ℕ) * (((2 : ℝ≥0∞)⁻¹) ^ 64) := by
    exact hmarkov.trans (mul_le_mul_left' hpow (2 * R : ℕ))
  have hRzero : (R : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hRtop : (R : ℝ≥0∞) ≠ ∞ := by simp
  rw [← ENNReal.mul_le_mul_left hRzero hRtop]
  calc
    (R : ℝ≥0∞) *
        finiteBoardMass (bernoulliWeight p)
          (emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R) ≤
        (2 * R : ℕ) * (((2 : ℝ≥0∞)⁻¹) ^ 64) := hmul
    _ = (R : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ 63) := by
      push_cast
      calc
        (2 : ℝ≥0∞) * R * ((2 : ℝ≥0∞)⁻¹) ^ 64 =
            R * ((2 : ℝ≥0∞)⁻¹) ^ 63 *
              ((2 : ℝ≥0∞)⁻¹ * 2) := by
          rw [show (64 : ℕ) = 63 + 1 by omega, pow_succ]
          ac_rfl
        _ = R * ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
          have hcancel : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := by
            rw [mul_comm, ENNReal.mul_inv_cancel] <;> norm_num
          rw [hcancel, mul_one]

/-! ### Adaptive grouped scans

The preceding estimate is stated on a rectangular finite board.  The next
bridge shows that any fresh adaptive scan of the same length has exactly that
law after its answers are packed in chronological row-major order. -/

def groupedScanAnswerCount (groups blockSize : ℕ) : ℕ :=
  groups * blockSize

noncomputable def packGroupedScanAnswers (groups blockSize : ℕ)
    (bits : List.Vector Bool (groupedScanAnswerCount groups blockSize)) :
    Board (Fin groups × Fin blockSize) := fun ij ↦
  bits.get (finProdFinEquiv ij)

noncomputable def unpackGroupedScanAnswers (groups blockSize : ℕ)
    (board : Board (Fin groups × Fin blockSize)) :
    List.Vector Bool (groupedScanAnswerCount groups blockSize) :=
  List.Vector.ofFn fun k ↦ board (finProdFinEquiv.symm k)

theorem unpack_pack_groupedScanAnswers (groups blockSize : ℕ)
    (bits : List.Vector Bool (groupedScanAnswerCount groups blockSize)) :
    unpackGroupedScanAnswers groups blockSize
        (packGroupedScanAnswers groups blockSize bits) = bits := by
  apply List.Vector.ext
  intro k
  simp only [unpackGroupedScanAnswers, List.Vector.get_ofFn,
    packGroupedScanAnswers]
  exact congrArg bits.get (Equiv.apply_symm_apply finProdFinEquiv k)

theorem pack_unpack_groupedScanAnswers (groups blockSize : ℕ)
    (board : Board (Fin groups × Fin blockSize)) :
    packGroupedScanAnswers groups blockSize
        (unpackGroupedScanAnswers groups blockSize board) = board := by
  funext ij
  simp only [packGroupedScanAnswers, unpackGroupedScanAnswers,
    List.Vector.get_ofFn]
  rw [Equiv.symm_apply_apply]

noncomputable def groupedScanAnswerEquiv (groups blockSize : ℕ) :
    List.Vector Bool (groupedScanAnswerCount groups blockSize) ≃
      Board (Fin groups × Fin blockSize) where
  toFun := packGroupedScanAnswers groups blockSize
  invFun := unpackGroupedScanAnswers groups blockSize
  left_inv := unpack_pack_groupedScanAnswers groups blockSize
  right_inv := pack_unpack_groupedScanAnswers groups blockSize

theorem groupedScanAnswerEquiv_weight
    (p : ℝ≥0∞) (groups blockSize : ℕ)
    (bits : List.Vector Bool (groupedScanAnswerCount groups blockSize)) :
    (bits.toList.map (bernoulliWeight p)).prod =
      boardWeight (bernoulliWeight p)
        (groupedScanAnswerEquiv groups blockSize bits) := by
  have hlist : bits.toList = List.ofFn bits.get := by
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  simp only [boardWeight, groupedScanAnswerEquiv, packGroupedScanAnswers]
  rw [hlist, List.map_ofFn, List.prod_ofFn]
  change (∏ k : Fin (groups * blockSize),
      bernoulliWeight p (bits.get k)) = _
  rw [Fintype.prod_equiv finProdFinEquiv.symm
    (fun k : Fin (groups * blockSize) ↦ bernoulliWeight p (bits.get k))
    (fun ij : Fin groups × Fin blockSize ↦
      bernoulliWeight p (bits.get (finProdFinEquiv ij))) (by
        intro k
        exact congrArg (fun z ↦ bernoulliWeight p (bits.get z))
          (Equiv.apply_symm_apply finProdFinEquiv k).symm)]
  rfl

theorem groupedScanEmptyBlockTail_weight_eq
    (p : ℝ≥0∞) (groups blockSize R : ℕ) :
    (∑ bits : List.Vector Bool (groupedScanAnswerCount groups blockSize),
      if groupedScanAnswerEquiv groups blockSize bits ∈
          emptyBlockUpperTailEvent groups blockSize R then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      finiteBoardMass (bernoulliWeight p)
        (emptyBlockUpperTailEvent groups blockSize R) := by
  unfold finiteBoardMass
  apply Fintype.sum_equiv (groupedScanAnswerEquiv groups blockSize)
  intro bits
  by_cases hbad : groupedScanAnswerEquiv groups blockSize bits ∈
      emptyBlockUpperTailEvent groups blockSize R
  · simp [hbad, groupedScanAnswerEquiv_weight]
  · simp [hbad]

/-- A fresh continuation path appended to a fixed legal prefix has the
expected product mass.  Disjointness from the prefix is explicit, so this is
the exact finite conditional-independence statement needed for sequential
reservoir attempts. -/
theorem finiteBoardMass_cylinder_replay_append
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit, weight bit) = 1)
    (base : Transcript Q) (hbase : (queries base).Nodup)
    (continuation : Strategy Q) (bits : List Bool)
    (hfresh : FreshPath continuation bits)
    (hdisjoint : List.Disjoint (queries (replay continuation bits))
      (queries base)) :
    finiteBoardMass weight
        (cylinder (replay continuation bits ++ base)) =
      (bits.map weight).prod * transcriptWeight weight base := by
  rw [finiteBoardMass_cylinder weight hnormalized]
  · calc
      transcriptWeight weight (replay continuation bits ++ base) =
          transcriptWeight weight (replay continuation bits) *
            transcriptWeight weight base := by
        simp [transcriptWeight, answers, List.map_append, List.prod_append]
      _ = (bits.map weight).prod * transcriptWeight weight base := by
        rw [transcriptWeight_replay]
  · simpa [queries, List.map_append, FreshPath] using
      hfresh.append hbase hdisjoint

/-- Finite conditional product law, summed over an arbitrary continuation
answer event. -/
theorem continuationPathEventMass_eq
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit, weight bit) = 1)
    (base : Transcript Q) (hbase : (queries base).Nodup)
    (continuation : Strategy Q) (n : ℕ)
    (P : List.Vector Bool n → Prop) [DecidablePred P]
    (hfresh : ∀ bits : List.Vector Bool n,
      FreshPath continuation bits.toList)
    (hdisjoint : ∀ bits : List.Vector Bool n,
      List.Disjoint (queries (replay continuation bits.toList))
        (queries base)) :
    (∑ bits : List.Vector Bool n,
      if P bits then
        finiteBoardMass weight
          (cylinder (replay continuation bits.toList ++ base)) else 0) =
      (∑ bits : List.Vector Bool n,
        if P bits then (bits.toList.map weight).prod else 0) *
        transcriptWeight weight base := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro bits _hbits
  by_cases hP : P bits
  · simp only [hP, if_true]
    exact finiteBoardMass_cylinder_replay_append weight hnormalized base hbase
      continuation bits.toList (hfresh bits) (hdisjoint bits)
  · simp [hP]

/-- Quantitative conditional scan tail.  The left side is a sum of genuine
full-board cylinder masses extending a fixed transcript, not a heuristic
conditional probability. -/
theorem continuationGroupedScanHalfTail_le
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (base : Transcript Q) (hbase : (queries base).Nodup)
    (continuation : Strategy Q) (a R : ℕ)
    (ha : 2 ≤ a) (hR : 0 < R)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p)
    (hfresh : ∀ bits : List.Vector Bool
        (groupedScanAnswerCount (2 * R) (slackBlockSize a)),
      FreshPath continuation bits.toList)
    (hdisjoint : ∀ bits : List.Vector Bool
        (groupedScanAnswerCount (2 * R) (slackBlockSize a)),
      List.Disjoint (queries (replay continuation bits.toList))
        (queries base)) :
    (∑ bits : List.Vector Bool
        (groupedScanAnswerCount (2 * R) (slackBlockSize a)),
      if groupedScanAnswerEquiv (2 * R) (slackBlockSize a) bits ∈
          emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R then
        finiteBoardMass (bernoulliWeight p)
          (cylinder (replay continuation bits.toList ++ base)) else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 *
        transcriptWeight (bernoulliWeight p) base := by
  rw [continuationPathEventMass_eq (bernoulliWeight p)
    (sum_bernoulliWeight p hp) base hbase continuation
    (groupedScanAnswerCount (2 * R) (slackBlockSize a))
    (fun bits ↦ groupedScanAnswerEquiv (2 * R) (slackBlockSize a) bits ∈
      emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R)
    hfresh hdisjoint]
  rw [groupedScanEmptyBlockTail_weight_eq]
  exact mul_le_mul_right'
    (emptyBlockHalfTail_le a R ha hR p hp hdensity) _

/-- Bad grouped-scan event extracted from the complete answer vector of an
arbitrary adaptive strategy. -/
def adaptiveEmptyBlockHalfTailEvent {Q : Type*}
    (strategy : Strategy Q) (a R : ℕ) : Set (Board Q) :=
  {board | groupedScanAnswerEquiv (2 * R) (slackBlockSize a)
      (answerVector strategy board
        (groupedScanAnswerCount (2 * R) (slackBlockSize a))) ∈
      emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R}

/-- Exact law of a fresh adaptive grouped scan. -/
theorem finiteBoardMass_adaptiveEmptyBlockHalfTailEvent_eq
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (strategy : Strategy Q) (a R : ℕ)
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (hfresh : ∀ bits : List.Vector Bool
        (groupedScanAnswerCount (2 * R) (slackBlockSize a)),
      FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight p)
        (adaptiveEmptyBlockHalfTailEvent strategy a R) =
      finiteBoardMass (bernoulliWeight p)
        (emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R) := by
  unfold adaptiveEmptyBlockHalfTailEvent
  rw [finiteProduct_answerVector_event_mass
    (bernoulliWeight p) (sum_bernoulliWeight p hp) strategy
    (groupedScanAnswerCount (2 * R) (slackBlockSize a))
    (fun bits ↦ groupedScanAnswerEquiv (2 * R) (slackBlockSize a) bits ∈
      emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R) hfresh]
  unfold finiteBoardMass
  apply Fintype.sum_equiv
    (groupedScanAnswerEquiv (2 * R) (slackBlockSize a))
  intro bits
  by_cases hbad : groupedScanAnswerEquiv (2 * R) (slackBlockSize a) bits ∈
      emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R
  · simp [hbad, groupedScanAnswerEquiv_weight]
  · simp [hbad]

/-- Direct reusable concentration theorem for any fresh adaptive scan. -/
theorem finiteBoardMass_adaptiveEmptyBlockHalfTailEvent_le
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (strategy : Strategy Q) (a R : ℕ)
    (ha : 2 ≤ a) (hR : 0 < R)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p)
    (hfresh : ∀ bits : List.Vector Bool
        (groupedScanAnswerCount (2 * R) (slackBlockSize a)),
      FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight p)
        (adaptiveEmptyBlockHalfTailEvent strategy a R) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  rw [finiteBoardMass_adaptiveEmptyBlockHalfTailEvent_eq
    strategy a R p hp hfresh]
  exact emptyBlockHalfTail_le a R ha hR p hp hdensity

/-- After `j` attempts, even if every attempt consumes a distinct root and a
complete fill set, a full branch scan remains in the reservoir. -/
theorem slackReservoir_capacity (a j : ℕ)
    (hj : j ≤ slackAttemptCount a) :
    slackBranchScan a + j * (slackFillSize a + 1) ≤
      slackReservoirSize a := by
  unfold slackReservoirSize
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right (slackFillSize a + 1) hj) _

/-- Equivalent subtraction form of the capacity statement, useful for a
policy that physically removes roots and selected leaves from its pool. -/
theorem slackBranchScan_le_remaining (a j : ℕ)
    (hj : j ≤ slackAttemptCount a) :
    slackBranchScan a ≤
      slackReservoirSize a - j * (slackFillSize a + 1) := by
  exact Nat.le_sub_of_add_le (slackReservoir_capacity a j hj)

/-- At the large integer scales used for asymptotics, the slack reservoir is
still only a constant multiple of `a⁷`. -/
theorem slackReservoirSize_le (a : ℕ) (ha : 1 ≤ a)
    (hlarge : K6Upper.momentAmplification ≤ a) :
    slackReservoirSize a ≤ 132 * a ^ 7 := by
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hp3p7 : a ^ 3 ≤ a ^ 7 := Nat.pow_le_pow_right ha0 (by omega)
  have hamp6 : K6Upper.momentAmplification * a ^ 6 ≤ a ^ 7 := by
    calc
      K6Upper.momentAmplification * a ^ 6 ≤ a * a ^ 6 :=
        Nat.mul_le_mul_right (a ^ 6) hlarge
      _ = a ^ 7 := by ring
  have hamp2 : K6Upper.momentAmplification * a ^ 2 ≤ a ^ 7 := by
    calc
      K6Upper.momentAmplification * a ^ 2 ≤ a * a ^ 2 :=
        Nat.mul_le_mul_right (a ^ 2) hlarge
      _ = a ^ 3 := by ring
      _ ≤ a ^ 7 := hp3p7
  rw [slackReservoirSize, slackBranchScan_eq]
  unfold slackAttemptCount slackTrialCount slackFillSize
  calc
    128 * a ^ 7 + 2 * (K6Upper.momentAmplification * a ^ 2) *
          (a ^ 4 + 1)
        = 128 * a ^ 7 +
            2 * (K6Upper.momentAmplification * a ^ 6) +
            2 * (K6Upper.momentAmplification * a ^ 2) := by ring
    _ ≤ 128 * a ^ 7 + 2 * a ^ 7 + 2 * a ^ 7 := by
      gcongr
    _ = 132 * a ^ 7 := by ring

/-- The complete slack construction has an explicit `O(a¹⁰)` budget.
The only large-scale side condition is `momentAmplification ≤ a`; finitely
many smaller `a` can be absorbed separately by the final asymptotic constant.
-/
theorem slackQueryBudget_le (a : ℕ) (ha : 1 ≤ a)
    (hlarge : K6Upper.momentAmplification ≤ a) :
    slackQueryBudget a ≤ slackUpperConstant * a ^ 10 := by
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hpow9 : a ^ 9 ≤ a ^ 10 :=
    Nat.pow_le_pow_right ha0 (by omega)
  have hstar : slackStarQueries a ≤ 16896 * a ^ 10 := by
    unfold slackStarQueries slackBlockSize
    calc
      2 * slackReservoirSize a * (64 * a ^ 3)
          ≤ 2 * (132 * a ^ 7) * (64 * a ^ 3) := by
            gcongr
            exact slackReservoirSize_le a ha hlarge
      _ = 16896 * a ^ 10 := by ring
  have hbranch : slackAttemptCount a * slackBranchScan a ≤
      (256 * K6Upper.momentAmplification) * a ^ 10 := by
    rw [slackBranchScan_eq]
    unfold slackAttemptCount slackTrialCount
    calc
      2 * (K6Upper.momentAmplification * a ^ 2) * (128 * a ^ 7) =
          (256 * K6Upper.momentAmplification) * a ^ 9 := by ring
      _ ≤ (256 * K6Upper.momentAmplification) * a ^ 10 :=
        Nat.mul_le_mul_left _ hpow9
  have hfill : slackTrialCount a * K6Upper.fillCost (slackFillSize a) ≤
      K6Upper.momentAmplification * a ^ 10 := by
    calc
      slackTrialCount a * K6Upper.fillCost (slackFillSize a)
          ≤ slackTrialCount a * (slackFillSize a) ^ 2 :=
            Nat.mul_le_mul_left _ (K6Upper.fillCost_le_sq _)
      _ = K6Upper.momentAmplification * a ^ 10 := by
        unfold slackTrialCount slackFillSize
        ring
  unfold slackQueryBudget slackUpperConstant
  calc
    slackStarQueries a + slackAttemptCount a * slackBranchScan a +
          slackTrialCount a * K6Upper.fillCost (slackFillSize a)
        ≤ 16896 * a ^ 10 +
            (256 * K6Upper.momentAmplification) * a ^ 10 +
            K6Upper.momentAmplification * a ^ 10 :=
          Nat.add_le_add (Nat.add_le_add hstar hbranch) hfill
    _ = (16896 + 257 * K6Upper.momentAmplification) * a ^ 10 := by ring

/-! ### Freshness of the scheduled star, branch, and fill coordinates -/

/-- Labels for every query in the three phases. -/
abbrev SlackQueryCoord (a : ℕ) :=
  Fin (slackStarQueries a) ⊕
    ((Fin (slackAttemptCount a) × Fin (slackBranchScan a)) ⊕
      (Fin (slackTrialCount a) × OffDiagTrialQuery a))

theorem card_offDiagTrialQuery (a : ℕ) :
    Fintype.card (OffDiagTrialQuery a) =
      K6Upper.fillCost (slackFillSize a) := by
  rw [Sym2.card_subtype_not_diag]
  simp [K6Upper.fillCost, slackFillSize, TrialVertex]

/-- Canonical row-major decoding of final-fill query positions. -/
noncomputable def slackFillCoordEquiv (a : ℕ) :
    Fin (slackFillQueryCount a) ≃
      Fin (slackTrialCount a) × OffDiagTrialQuery a :=
  (finCongr (by
      unfold slackFillQueryCount
      rw [card_offDiagTrialQuery])).trans
    (finProdFinEquiv.symm.trans
      (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _).symm))

theorem card_slackQueryCoord (a : ℕ) :
    Fintype.card (SlackQueryCoord a) = slackQueryBudget a := by
  simp only [SlackQueryCoord, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_prod]
  rw [card_offDiagTrialQuery]
  simp [slackQueryBudget, Nat.add_assoc]

/-- Pathwise geometric data for a successful slack allocation.  Branch
candidate sets may be reused by different roots.  Fill sets are globally
disjoint, and neither branch nor fill vertices are roots; these are exactly
the conditions needed to prevent collisions between unordered queries. -/
structure SlackQueryGeometry (a : ℕ) (V : Type*) where
  center : V
  starVertex : Fin (slackStarQueries a) → V
  starVertex_injective : Function.Injective starVertex
  root : Fin (slackAttemptCount a) → V
  root_injective : Function.Injective root
  branchVertex : Fin (slackAttemptCount a) → Fin (slackBranchScan a) → V
  branchVertex_injective : ∀ i, Function.Injective (branchVertex i)
  fillVertex : Fin (slackTrialCount a) → TrialVertex a → V
  fillVertex_pair_injective : Function.Injective
    (fun ix : Fin (slackTrialCount a) × TrialVertex a ↦
      fillVertex ix.1 ix.2)
  center_ne_star : ∀ i, center ≠ starVertex i
  center_ne_root : ∀ i, center ≠ root i
  center_ne_branch : ∀ i k, center ≠ branchVertex i k
  center_ne_fill : ∀ i x, center ≠ fillVertex i x
  branch_ne_root : ∀ i k j, branchVertex i k ≠ root j
  fill_ne_root : ∀ i x j, fillVertex i x ≠ root j

/-- The host-board query attached to a phase coordinate. -/
def SlackQueryGeometry.query {a : ℕ} {V : Type*}
    (g : SlackQueryGeometry a V) : SlackQueryCoord a → Sym2 V
  | Sum.inl i => s(g.center, g.starVertex i)
  | Sum.inr (Sum.inl ik) => s(g.root ik.1, g.branchVertex ik.1 ik.2)
  | Sum.inr (Sum.inr iq) => Sym2.map (g.fillVertex iq.1) iq.2

private theorem sym2_map_const {X I : Type*} (q : Sym2 X) (i : I) :
    Sym2.map (fun _ ↦ i) q = s(i, i) := by
  induction q using Sym2.inductionOn with
  | _ x y => rfl

/-- Attaching a common trial label to both endpoints makes a family of
unordered pairs injective in the trial label and in the pair. -/
private theorem taggedSym2_source_injective {I X : Type*} :
    Function.Injective
      (fun iq : I × Sym2 X ↦ Sym2.map (fun x ↦ (iq.1, x)) iq.2) := by
  intro iq jr htag
  have hi := congrArg (Sym2.map Prod.fst) htag
  have hq := congrArg (Sym2.map Prod.snd) htag
  have hi' : iq.1 = jr.1 := by
    simpa [Sym2.map_map, Function.comp_def, sym2_map_const,
      Sym2.eq_iff] using hi
  have hq' : iq.2 = jr.2 := by
    simpa [Sym2.map_map, Function.comp_def] using hq
  exact Prod.ext hi' hq'

/-- A tagged family remains injective after embedding all tagged vertices. -/
private theorem taggedSym2_injective
    {I X V : Type*} (f : I → X → V)
    (hf : Function.Injective (fun ix : I × X ↦ f ix.1 ix.2)) :
    Function.Injective
      (fun iq : I × Sym2 X ↦ Sym2.map (f iq.1) iq.2) := by
  let emb : I × X ↪ V :=
    ⟨fun ix ↦ f ix.1 ix.2, hf⟩
  intro iq jr heq
  apply taggedSym2_source_injective
  apply emb.sym2Map.injective
  simpa [emb, Function.Embedding.sym2Map_apply, Sym2.map_map,
    Function.comp_def] using heq

/-- Within each phase, and between all three phases, scheduled unordered
coordinates are distinct.  In particular, reusing the same candidate vertex
for different branch roots is harmless. -/
theorem SlackQueryGeometry.query_injective {a : ℕ} {V : Type*}
    (g : SlackQueryGeometry a V) : Function.Injective g.query := by
  have hstar (i j : Fin (slackStarQueries a))
      (h : g.query (Sum.inl i) = g.query (Sum.inl j)) : i = j := by
    simp only [SlackQueryGeometry.query, Sym2.eq_iff] at h
    rcases h with hsame | hswap
    · exact g.starVertex_injective hsame.2
    · exact False.elim (g.center_ne_star j hswap.1)
  have hbranch (ik jk : Fin (slackAttemptCount a) ×
      Fin (slackBranchScan a))
      (h : g.query (Sum.inr (Sum.inl ik)) =
        g.query (Sum.inr (Sum.inl jk))) : ik = jk := by
    simp only [SlackQueryGeometry.query, Sym2.eq_iff] at h
    rcases h with hsame | hswap
    · have hi : ik.1 = jk.1 := g.root_injective hsame.1
      have hk : ik.2 = jk.2 := by
        apply g.branchVertex_injective ik.1
        simpa [hi] using hsame.2
      exact Prod.ext hi hk
    · exact False.elim
        (g.branch_ne_root jk.1 jk.2 ik.1 hswap.1.symm)
  have hfill (iq jq : Fin (slackTrialCount a) × OffDiagTrialQuery a)
      (h : g.query (Sum.inr (Sum.inr iq)) =
        g.query (Sum.inr (Sum.inr jq))) : iq = jq := by
    have htag : (iq.1, (iq.2 : Sym2 (TrialVertex a))) =
        (jq.1, (jq.2 : Sym2 (TrialVertex a))) := by
      apply taggedSym2_injective g.fillVertex g.fillVertex_pair_injective
      simpa [SlackQueryGeometry.query] using h
    have hi : iq.1 = jq.1 := congrArg
      (fun z : Fin (slackTrialCount a) × Sym2 (TrialVertex a) ↦ z.1) htag
    have hq : iq.2 = jq.2 := Subtype.ext (congrArg
      (fun z : Fin (slackTrialCount a) × Sym2 (TrialVertex a) ↦ z.2) htag)
    exact Prod.ext hi hq
  have hstarBranch (i : Fin (slackStarQueries a))
      (jk : Fin (slackAttemptCount a) × Fin (slackBranchScan a)) :
      g.query (Sum.inl i) ≠ g.query (Sum.inr (Sum.inl jk)) := by
    intro h
    simp only [SlackQueryGeometry.query, Sym2.eq_iff] at h
    rcases h with hsame | hswap
    · exact g.center_ne_root jk.1 hsame.1
    · exact g.center_ne_branch jk.1 jk.2 hswap.1
  have hstarFill (i : Fin (slackStarQueries a))
      (jq : Fin (slackTrialCount a) × OffDiagTrialQuery a) :
      g.query (Sum.inl i) ≠ g.query (Sum.inr (Sum.inr jq)) := by
    intro h
    rcases jq with ⟨j, ⟨q, hq⟩⟩
    induction q using Sym2.inductionOn with
    | _ x y =>
      simp only [SlackQueryGeometry.query, Sym2.map_pair_eq,
        Sym2.eq_iff] at h
      rcases h with hsame | hswap
      · exact g.center_ne_fill j x hsame.1
      · exact g.center_ne_fill j y hswap.1
  have hbranchFill
      (ik : Fin (slackAttemptCount a) × Fin (slackBranchScan a))
      (jq : Fin (slackTrialCount a) × OffDiagTrialQuery a) :
      g.query (Sum.inr (Sum.inl ik)) ≠
        g.query (Sum.inr (Sum.inr jq)) := by
    intro h
    rcases jq with ⟨j, ⟨q, hq⟩⟩
    induction q using Sym2.inductionOn with
    | _ x y =>
      simp only [SlackQueryGeometry.query, Sym2.map_pair_eq,
        Sym2.eq_iff] at h
      rcases h with hsame | hswap
      · exact g.fill_ne_root j x ik.1 hsame.1.symm
      · exact g.fill_ne_root j y ik.1 hswap.1.symm
  intro q r hqr
  rcases q with i | q
  · rcases r with j | r
    · exact congrArg Sum.inl (hstar i j hqr)
    · rcases r with jk | jq
      · exact False.elim (hstarBranch i jk hqr)
      · exact False.elim (hstarFill i jq hqr)
  · rcases q with ik | iq
    · rcases r with j | r
      · exact False.elim (hstarBranch j ik hqr.symm)
      · rcases r with jk | jq
        · exact congrArg Sum.inr
            (congrArg Sum.inl (hbranch ik jk hqr))
        · exact False.elim (hbranchFill ik jq hqr)
    · rcases r with j | r
      · exact False.elim (hstarFill j iq hqr.symm)
      · rcases r with jk | jq
        · exact False.elim (hbranchFill jk iq hqr.symm)
        · exact congrArg Sum.inr (congrArg Sum.inr (hfill iq jq hqr))

/-- Every scheduled coordinate is a genuine nonloop. -/
theorem SlackQueryGeometry.query_nonloop {a : ℕ} {V : Type*}
    (g : SlackQueryGeometry a V) (q : SlackQueryCoord a) :
    ¬(g.query q).IsDiag := by
  rcases q with i | q
  · simpa [SlackQueryGeometry.query, Sym2.mk_isDiag_iff] using
      g.center_ne_star i
  · rcases q with ik | iq
    · simpa [SlackQueryGeometry.query, Sym2.mk_isDiag_iff] using
        (g.branch_ne_root ik.1 ik.2 ik.1).symm
    · rw [SlackQueryGeometry.query, Sym2.isDiag_map]
      · exact iq.2.property
      · intro x y hxy
        have hpair := g.fillVertex_pair_injective
          (a₁ := (iq.1, x)) (a₂ := (iq.1, y)) hxy
        exact congrArg Prod.snd hpair

/-- Canonical enumeration of every coordinate in a slack geometry. -/
noncomputable def slackCoordEquiv (a : ℕ) :
    Fin (slackQueryBudget a) ≃ SlackQueryCoord a :=
  Fintype.equivOfCardEq (by simpa using (card_slackQueryCoord a).symm)

/-- The resulting fixed schedule along a path whose adaptive choices have
produced `g`. -/
noncomputable def SlackQueryGeometry.schedule {a : ℕ} {V : Type*}
    (g : SlackQueryGeometry a V) : Fin (slackQueryBudget a) → Sym2 V :=
  fun i ↦ g.query (slackCoordEquiv a i)

theorem SlackQueryGeometry.schedule_injective {a : ℕ} {V : Type*}
    (g : SlackQueryGeometry a V) : Function.Injective g.schedule :=
  g.query_injective.comp (slackCoordEquiv a).injective

theorem SlackQueryGeometry.schedule_nonloop {a : ℕ} {V : Type*}
    (g : SlackQueryGeometry a V) (i : Fin (slackQueryBudget a)) :
    ¬(g.schedule i).IsDiag :=
  g.query_nonloop (slackCoordEquiv a i)

/-- If a proposed adaptive program's completed replay is exactly a slack
geometry schedule, then the legalizer never changes any query on that path.
This is the direct bridge from the pathwise reservoir allocator to
`ProposedPathLegal`. -/
theorem proposedPathLegal_of_slackGeometry
    (a : ℕ) (proposed : K6Strategy (slackQueryBudget a))
    (bits : List Bool)
    (g : SlackQueryGeometry a (Vertex (slackQueryBudget a)))
    (hqueries : queries (replay proposed bits) = List.ofFn g.schedule) :
    ProposedPathLegal proposed bits := by
  apply proposedPathLegal_of_replay_nodup_nonloop proposed bits
  · rw [hqueries]
    exact List.nodup_ofFn.mpr g.schedule_injective
  · intro q hq
    rw [hqueries] at hq
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' g.schedule q).mp hq
    exact g.schedule_nonloop i

/-! ### The actual history-dependent slack program

The following definitions give a total proposed strategy, not merely an
existence interface.  Bad histories are handled by harmless default values;
`legalizeStrategy` subsequently replaces any illegal default query.  On the
intended paths the program performs these operations:

1. query a fixed centre against `slackStarQueries a` distinct vertices;
2. take the first `slackReservoirSize a` positive star vertices, reserving the
   first `slackAttemptCount a` of them as roots;
3. for each root, scan the first `slackBranchScan a` vertices not consumed by
   earlier successful fills, and retain the first `a⁴` positive answers;
4. completely query the first `slackTrialCount a` retained fill sets.

All selections use the canonical order on the finite star indices, so the
rule is deterministic and depends only on the supplied transcript.
-/

theorem slackStarQueries_pos (a : ℕ) (ha : 1 ≤ a) :
    0 < slackStarQueries a := by
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  unfold slackStarQueries slackReservoirSize slackBranchScan
    slackBranchGroups slackBlockSize
  positivity

theorem slackQueryBudget_pos (a : ℕ) (ha : 1 ≤ a) :
    0 < slackQueryBudget a := by
  have hs := slackStarQueries_pos a ha
  unfold slackQueryBudget
  omega

theorem slackStarVertex_capacity (a : ℕ) (ha : 1 ≤ a) :
    slackStarQueries a + 1 ≤ 2 * slackQueryBudget a := by
  have hs := slackStarQueries_pos a ha
  have hle : slackStarQueries a ≤ slackQueryBudget a := by
    unfold slackQueryBudget
    omega
  have hbudget := slackQueryBudget_pos a ha
  omega

/-- The distinguished centre on the canonical game board. -/
def slackCenter (a : ℕ) (ha : 1 ≤ a) : Vertex (slackQueryBudget a) :=
  ⟨0, by have := slackQueryBudget_pos a ha; omega⟩

/-- Fixed distinct vertices used by the initial centre-star phase. -/
def slackStarVertex (a : ℕ) (ha : 1 ≤ a)
    (i : Fin (slackStarQueries a)) : Vertex (slackQueryBudget a) :=
  ⟨i.1 + 1, by
    have hi := i.2
    have hcap := slackStarVertex_capacity a ha
    omega⟩

theorem slackStarVertex_injective (a : ℕ) (ha : 1 ≤ a) :
    Function.Injective (slackStarVertex a ha) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_right_cancel (congrArg Fin.val hij)

theorem slackCenter_ne_starVertex (a : ℕ) (ha : 1 ≤ a)
    (i : Fin (slackStarQueries a)) :
    slackCenter a ha ≠ slackStarVertex a ha i := by
  intro h
  have hv := congrArg Fin.val h
  simp [slackCenter, slackStarVertex] at hv

/-- Canonically ordered indices whose centre-star query has received a
positive answer in the current transcript. -/
def positiveStarIndices (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    List (Fin (slackStarQueries a)) :=
  ((Finset.univ : Finset (Fin (slackStarQueries a))).filter fun i ↦
    (s(slackCenter a ha, slackStarVertex a ha i), true) ∈ h).toList

/-- The first positive star vertices, truncated at the reservoir target. -/
def selectedReservoir (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    List (Vertex (slackQueryBudget a)) :=
  ((positiveStarIndices a ha h).map (slackStarVertex a ha)).take
    (slackReservoirSize a)

/-- Reserved root number `i`; on a bad path the centre is returned as a
default and will be repaired by `legalizeStrategy`. -/
def selectedRoot (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) (i : ℕ) :
    Vertex (slackQueryBudget a) :=
  (selectedReservoir a ha h).getD i (slackCenter a ha)

/-- Candidate pool after reserving all potential roots and deleting the
leaves already consumed by successful earlier attempts. -/
def availableBranchPool (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (used : List (Vertex (slackQueryBudget a))) :
    List (Vertex (slackQueryBudget a)) :=
  ((selectedReservoir a ha h).drop (slackAttemptCount a)).filter
    fun v ↦ v ∉ used

/-- Fill lists retained after the first `n` branch attempts.  A failed
attempt contributes the empty list; a successful one contributes exactly
the first `a⁴` positive neighbours in its scan. -/
def selectedBranchFills (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) : ℕ →
    List (List (Vertex (slackQueryBudget a)))
  | 0 => []
  | n + 1 =>
      let prior := selectedBranchFills a ha h n
      let candidates :=
        (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
      let root := selectedRoot a ha h n
      let positives := candidates.filter fun v ↦ (s(root, v), true) ∈ h
      let chosen := if slackFillSize a ≤ positives.length then
        positives.take (slackFillSize a) else []
      prior ++ [chosen]
termination_by n => n

/-- Candidate list used by branch attempt `n`.  It depends only on fills
retained in earlier attempts. -/
def selectedBranchCandidates (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) (n : ℕ) :
    List (Vertex (slackQueryBudget a)) :=
  (availableBranchPool a ha h
    (selectedBranchFills a ha h n).flatten).take (slackBranchScan a)

/-- The successful branch attempts, retaining each attempt number together
with its fill list. -/
def successfulBranchTrials (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    List (ℕ × List (Vertex (slackQueryBudget a))) :=
  ((selectedBranchFills a ha h (slackAttemptCount a)).zipIdx.map
    fun trial ↦ (trial.2, trial.1)).filter
      fun trial ↦ trial.2.length = slackFillSize a

/-- The successful fill lists, in branch-attempt order. -/
def successfulBranchFills (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    List (List (Vertex (slackQueryBudget a))) :=
  (selectedBranchFills a ha h (slackAttemptCount a)).filter
    fun fill ↦ fill.length = slackFillSize a

/-- Attempt number belonging to retained fill trial `i`. -/
def selectedFillAttempt (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (i : Fin (slackTrialCount a)) : ℕ :=
  let fill := (successfulBranchFills a ha h).getD i.1 []
  (selectedBranchFills a ha h (slackAttemptCount a)).idxOf fill

/-- Root belonging to retained fill trial `i`. -/
def selectedFillRoot (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (i : Fin (slackTrialCount a)) : Vertex (slackQueryBudget a) :=
  selectedRoot a ha h (selectedFillAttempt a ha h i)

/-- Flattened vertices of the first retained fill trials. -/
def selectedFillVertices (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    List (Vertex (slackQueryBudget a)) :=
  ((successfulBranchFills a ha h).take (slackTrialCount a)).flatten

/-- Vertex `x` of retained fill trial `i`, with a bad-path default.  Linear
product indexing makes global injectivity a direct consequence of the
flattened-list no-duplicates invariant. -/
def selectedFillVertex (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    Vertex (slackQueryBudget a) :=
  (selectedFillVertices a ha h).getD
    (finProdFinEquiv (i, x)).1 (slackCenter a ha)

theorem positiveStarIndices_nodup (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    (positiveStarIndices a ha h).Nodup := by
  unfold positiveStarIndices
  exact Finset.nodup_toList _

theorem selectedReservoir_nodup (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    (selectedReservoir a ha h).Nodup := by
  unfold selectedReservoir
  exact ((positiveStarIndices_nodup a ha h).map
    (slackStarVertex_injective a ha)).take

theorem mem_positiveStarIndices_iff
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (i : Fin (slackStarQueries a)) :
    i ∈ positiveStarIndices a ha h ↔
      (s(slackCenter a ha, slackStarVertex a ha i), true) ∈ h := by
  simp [positiveStarIndices]

theorem mem_selectedReservoir_center_positive
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    {v : Vertex (slackQueryBudget a)}
    (hv : v ∈ selectedReservoir a ha h) :
    (s(slackCenter a ha, v), true) ∈ h := by
  have hvmap : v ∈
      (positiveStarIndices a ha h).map (slackStarVertex a ha) := by
    exact List.mem_of_mem_take hv
  rw [List.mem_map] at hvmap
  obtain ⟨i, hi, rfl⟩ := hvmap
  exact (mem_positiveStarIndices_iff a ha h i).mp hi

theorem mem_selectedReservoir_center_ne
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    {v : Vertex (slackQueryBudget a)}
    (hv : v ∈ selectedReservoir a ha h) :
    slackCenter a ha ≠ v := by
  have hvmap : v ∈
      (positiveStarIndices a ha h).map (slackStarVertex a ha) :=
    List.mem_of_mem_take hv
  rw [List.mem_map] at hvmap
  obtain ⟨i, _hi, rfl⟩ := hvmap
  exact slackCenter_ne_starVertex a ha i

theorem selectedReservoir_length_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackReservoirSize a ≤ (positiveStarIndices a ha h).length) :
    (selectedReservoir a ha h).length = slackReservoirSize a := by
  unfold selectedReservoir
  simp only [List.length_take, List.length_map]
  exact Nat.min_eq_left hready

theorem slackAttemptCount_le_reservoirSize (a : ℕ) :
    slackAttemptCount a ≤ slackReservoirSize a := by
  have hm : slackAttemptCount a ≤
      slackAttemptCount a * (slackFillSize a + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold slackReservoirSize
  omega

theorem selectedRoot_mem_reservoir_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : ℕ) (hi : i < slackAttemptCount a) :
    selectedRoot a ha h i ∈ selectedReservoir a ha h := by
  have hlen := selectedReservoir_length_of_ready a ha h hready
  have hiR : i < slackReservoirSize a :=
    hi.trans_le (slackAttemptCount_le_reservoirSize a)
  have hiLen : i < (selectedReservoir a ha h).length := by
    simpa [hlen] using hiR
  rw [selectedRoot, List.getD_eq_getElem _ _ hiLen]
  exact List.getElem_mem hiLen

theorem selectedRoot_center_positive_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : ℕ) (hi : i < slackAttemptCount a) :
    (s(slackCenter a ha, selectedRoot a ha h i), true) ∈ h :=
  mem_selectedReservoir_center_positive a ha h
    (selectedRoot_mem_reservoir_of_ready a ha h hready i hi)

theorem selectedRoot_center_ne_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : ℕ) (hi : i < slackAttemptCount a) :
    slackCenter a ha ≠ selectedRoot a ha h i :=
  mem_selectedReservoir_center_ne a ha h
    (selectedRoot_mem_reservoir_of_ready a ha h hready i hi)

theorem availableBranchPool_nodup (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (used : List (Vertex (slackQueryBudget a))) :
    (availableBranchPool a ha h used).Nodup := by
  unfold availableBranchPool
  exact (selectedReservoir_nodup a ha h).drop.filter _

theorem mem_availableBranchPool_not_used
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (used : List (Vertex (slackQueryBudget a)))
    {v : Vertex (slackQueryBudget a)}
    (hv : v ∈ availableBranchPool a ha h used) : v ∉ used := by
  have hv' : v ∈ (selectedReservoir a ha h).drop (slackAttemptCount a) ∧
      v ∉ used := by
    simpa [availableBranchPool] using hv
  exact hv'.2

theorem selectedBranchFills_length (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) (n : ℕ) :
    (selectedBranchFills a ha h n).length = n := by
  induction n with
  | zero => simp [selectedBranchFills]
  | succ n ih =>
      simp [selectedBranchFills, ih]

/-- Every retained leaf of attempt `k` was, by construction, observed
positive against the root of that same attempt. -/
theorem selectedBranchFill_root_positive
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    ∀ n k, k < n → ∀ {v},
      v ∈ (selectedBranchFills a ha h n).getD k [] →
        (s(selectedRoot a ha h k, v), true) ∈ h := by
  intro n
  induction n with
  | zero =>
      intro k hk
      omega
  | succ n ih =>
      intro k hk v hv
      let prior := selectedBranchFills a ha h n
      let candidates :=
        (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
      let root := selectedRoot a ha h n
      let positives := candidates.filter fun w ↦ (s(root, w), true) ∈ h
      let chosen := if slackFillSize a ≤ positives.length then
        positives.take (slackFillSize a) else []
      have hstep : selectedBranchFills a ha h (n + 1) =
          prior ++ [chosen] := by
        simp only [selectedBranchFills]
        rfl
      by_cases hkOld : k < n
      · have hkPrior : k < prior.length := by
          simpa [prior, selectedBranchFills_length] using hkOld
        rw [hstep] at hv
        rw [List.getD_append prior [chosen] [] k hkPrior] at hv
        have hvPrior : v ∈ prior.getD k [] := hv
        exact ih k hkOld hvPrior
      · have hkn : k = n := by omega
        subst k
        have hpriorLen : prior.length = n := by
          exact selectedBranchFills_length a ha h n
        rw [hstep] at hv
        rw [List.getD_append_right prior [chosen] [] n (by omega)] at hv
        have hvChosen : v ∈ chosen := by simpa [hpriorLen] using hv
        by_cases hsize : slackFillSize a ≤ positives.length
        · have hvPos : v ∈ positives := by
            exact List.mem_of_mem_take (by simpa [chosen, hsize] using hvChosen)
          exact of_decide_eq_true (List.mem_filter.mp hvPos).2
        · simp [chosen, hsize] at hvChosen

/-- All leaves retained across the first `n` attempts are distinct. -/
theorem selectedBranchFills_flatten_nodup
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) (n : ℕ) :
    (selectedBranchFills a ha h n).flatten.Nodup := by
  induction n with
  | zero => simp [selectedBranchFills]
  | succ n ih =>
      let prior := selectedBranchFills a ha h n
      let candidates :=
        (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
      let root := selectedRoot a ha h n
      let positives := candidates.filter fun v ↦ (s(root, v), true) ∈ h
      let chosen := if slackFillSize a ≤ positives.length then
        positives.take (slackFillSize a) else []
      have hcandidates : candidates.Nodup := by
        exact (availableBranchPool_nodup a ha h prior.flatten).take
      have hpositives : positives.Nodup := hcandidates.filter _
      have hchosen : chosen.Nodup := by
        by_cases hsize : slackFillSize a ≤ positives.length
        · simpa [chosen, hsize] using hpositives.take
        · simp [chosen, hsize]
      have hdisjoint : List.Disjoint prior.flatten chosen := by
        rw [List.disjoint_left]
        intro v hvprior hvchosen
        by_cases hsize : slackFillSize a ≤ positives.length
        · have hvpos : v ∈ positives := by
            apply List.mem_of_mem_take
            simpa [chosen, hsize] using hvchosen
          have hvcand : v ∈ candidates := (List.mem_filter.mp hvpos).1
          have hvavail : v ∈ availableBranchPool a ha h prior.flatten :=
            List.mem_of_mem_take hvcand
          exact (mem_availableBranchPool_not_used a ha h prior.flatten hvavail)
            hvprior
        · simp [chosen, hsize] at hvchosen
      have happend : (prior.flatten ++ chosen).Nodup :=
        ih.append hchosen hdisjoint
      simpa [selectedBranchFills, prior, candidates, root, positives,
        chosen, List.flatten_append] using happend

/-- Every retained leaf is one of the centre-positive reservoir vertices. -/
theorem selectedBranchFills_flatten_subset_reservoir
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) (n : ℕ) :
    ∀ {v}, v ∈ (selectedBranchFills a ha h n).flatten →
      v ∈ selectedReservoir a ha h := by
  induction n with
  | zero => simp [selectedBranchFills]
  | succ n ih =>
      let prior := selectedBranchFills a ha h n
      let candidates :=
        (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
      let root := selectedRoot a ha h n
      let positives := candidates.filter fun v ↦ (s(root, v), true) ∈ h
      let chosen := if slackFillSize a ≤ positives.length then
        positives.take (slackFillSize a) else []
      have hchosen : ∀ {v}, v ∈ chosen → v ∈ selectedReservoir a ha h := by
        intro v hv
        by_cases hsize : slackFillSize a ≤ positives.length
        · have hvpos : v ∈ positives := by
            apply List.mem_of_mem_take
            simpa [chosen, hsize] using hv
          have hvcand : v ∈ candidates := (List.mem_filter.mp hvpos).1
          have hvavail : v ∈ availableBranchPool a ha h prior.flatten :=
            List.mem_of_mem_take hvcand
          have hvavailable : v ∈
              (selectedReservoir a ha h).drop (slackAttemptCount a) ∧
              v ∉ prior.flatten := by
            simpa [availableBranchPool] using hvavail
          have hvdrop : v ∈
              (selectedReservoir a ha h).drop (slackAttemptCount a) :=
            hvavailable.1
          exact (List.drop_sublist _ _).subset hvdrop
        · simp [chosen, hsize] at hv
      intro v hv
      have hv' : v ∈ prior.flatten ∨ v ∈ chosen := by
        simpa [selectedBranchFills, prior, candidates, root, positives,
          chosen, List.flatten_append] using hv
      exact hv'.elim ih hchosen

theorem selectedBranchFills_flatten_subset_reservoirDrop
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) (n : ℕ) :
    ∀ {v}, v ∈ (selectedBranchFills a ha h n).flatten →
      v ∈ (selectedReservoir a ha h).drop (slackAttemptCount a) := by
  induction n with
  | zero => simp [selectedBranchFills]
  | succ n ih =>
      let prior := selectedBranchFills a ha h n
      let candidates :=
        (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
      let root := selectedRoot a ha h n
      let positives := candidates.filter fun v ↦ (s(root, v), true) ∈ h
      let chosen := if slackFillSize a ≤ positives.length then
        positives.take (slackFillSize a) else []
      have hchosen : ∀ {v}, v ∈ chosen →
          v ∈ (selectedReservoir a ha h).drop (slackAttemptCount a) := by
        intro v hv
        by_cases hsize : slackFillSize a ≤ positives.length
        · have hvpos : v ∈ positives := by
            apply List.mem_of_mem_take
            simpa [chosen, hsize] using hv
          have hvcand : v ∈ candidates := (List.mem_filter.mp hvpos).1
          have hvavail : v ∈ availableBranchPool a ha h prior.flatten :=
            List.mem_of_mem_take hvcand
          have hvavailable : v ∈
              (selectedReservoir a ha h).drop (slackAttemptCount a) ∧
              v ∉ prior.flatten := by
            simpa [availableBranchPool] using hvavail
          exact hvavailable.1
        · simp [chosen, hsize] at hv
      intro v hv
      have hv' : v ∈ prior.flatten ∨ v ∈ chosen := by
        simpa [selectedBranchFills, prior, candidates, root, positives,
          chosen, List.flatten_append] using hv
      exact hv'.elim ih hchosen

theorem successfulBranchFills_all_length
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    {fill : List (Vertex (slackQueryBudget a))}
    (hfill : fill ∈ successfulBranchFills a ha h) :
    fill.length = slackFillSize a := by
  exact of_decide_eq_true (List.mem_filter.mp hfill).2

theorem selectedFillAttempt_lt_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) :
    selectedFillAttempt a ha h i < slackAttemptCount a := by
  have hi : i.1 < (successfulBranchFills a ha h).length :=
    i.2.trans_le hready
  let fill := (successfulBranchFills a ha h)[i.1]
  have hfillSuccess : fill ∈ successfulBranchFills a ha h :=
    List.getElem_mem hi
  have hfillAll : fill ∈
      selectedBranchFills a ha h (slackAttemptCount a) :=
    (List.mem_filter.mp hfillSuccess).1
  have hidx : (selectedBranchFills a ha h (slackAttemptCount a)).idxOf fill <
      (selectedBranchFills a ha h (slackAttemptCount a)).length :=
    List.idxOf_lt_length_iff.mpr hfillAll
  rw [selectedBranchFills_length] at hidx
  unfold selectedFillAttempt
  rw [List.getD_eq_getElem _ _ hi]
  exact hidx

private theorem getD_idxOf_eq_of_lt
    {X : Type*} [BEq X] [LawfulBEq X]
    (xs : List X) (x default : X) (hidx : xs.idxOf x < xs.length) :
    xs.getD (xs.idxOf x) default = x := by
  induction xs with
  | nil => simp at hidx
  | cons y ys ih =>
      by_cases hy : y == x
      · have hyx : y = x := eq_of_beq hy
        subst y
        simp
      · simp only [List.idxOf_cons, hy, if_false, List.length_cons,
          List.getD_cons_succ]
        apply ih
        simpa [List.idxOf_cons, hy] using hidx

theorem selectedFillAttempt_getD_eq_successfulFill_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) :
    (selectedBranchFills a ha h (slackAttemptCount a)).getD
        (selectedFillAttempt a ha h i) [] =
      (successfulBranchFills a ha h).getD i.1 [] := by
  have hi : i.1 < (successfulBranchFills a ha h).length :=
    i.2.trans_le hready
  have hidx := selectedFillAttempt_lt_of_ready a ha h hready i
  have hidxLength : selectedFillAttempt a ha h i <
      (selectedBranchFills a ha h (slackAttemptCount a)).length := by
    simpa [selectedBranchFills_length] using hidx
  let fills := selectedBranchFills a ha h (slackAttemptCount a)
  let fill := (successfulBranchFills a ha h).getD i.1 []
  have hattempt : selectedFillAttempt a ha h i = fills.idxOf fill := by
    rfl
  have hidx' : fills.idxOf fill < fills.length := by
    simpa [hattempt, fills] using hidxLength
  rw [hattempt]
  exact getD_idxOf_eq_of_lt fills fill [] hidx'

theorem successfulBranchFills_flatten_nodup
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    (successfulBranchFills a ha h).flatten.Nodup := by
  have hsub : List.Sublist (successfulBranchFills a ha h)
      (selectedBranchFills a ha h (slackAttemptCount a)) := by
    exact List.filter_sublist
  exact (selectedBranchFills_flatten_nodup a ha h _).sublist hsub.flatten

theorem selectedFillVertices_nodup
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    (selectedFillVertices a ha h).Nodup := by
  unfold selectedFillVertices
  exact (successfulBranchFills_flatten_nodup a ha h).sublist
    (List.take_sublist _ _).flatten

private theorem length_flatten_take_of_forall_length
    {V : Type*} (fills : List (List V)) (t s : ℕ)
    (hready : t ≤ fills.length)
    (hall : ∀ fill ∈ fills, fill.length = s) :
    (fills.take t).flatten.length = t * s := by
  induction t generalizing fills with
  | zero => simp
  | succ t ih =>
      cases fills with
      | nil => simp at hready
      | cons fill fills =>
          have hfill : fill.length = s := hall fill (by simp)
          have htail : t ≤ fills.length := by simpa using hready
          have hallTail : ∀ l ∈ fills, l.length = s := by
            intro l hl
            exact hall l (by simp [hl])
          simp [ih fills htail hallTail, hfill, Nat.succ_mul, Nat.add_comm]

/-- In a list of equal-sized blocks, row-major indexing into the flattened
list agrees with first selecting the block and then the entry in that block.
The defaults make the statement total, while the hypotheses ensure that they
are never used. -/
private theorem getD_flatten_eq_getD_getD_of_forall_length
    {V : Type*} (fills : List (List V)) (s i x : ℕ) (default : V)
    (hi : i < fills.length)
    (hx : x < s)
    (hall : ∀ fill ∈ fills, fill.length = s) :
    fills.flatten.getD (x + s * i) default =
      (fills.getD i []).getD x default := by
  induction fills generalizing i with
  | nil => simp at hi
  | cons fill fills ih =>
      have hfill : fill.length = s := hall fill (by simp)
      have hallTail : ∀ l ∈ fills, l.length = s := by
        intro l hl
        exact hall l (by simp [hl])
      cases i with
      | zero =>
          simpa [hfill] using
            List.getD_append fill fills.flatten default x (by simpa [hfill])
      | succ i =>
          have hiTail : i < fills.length := by simpa using hi
          have hsle : fill.length ≤ x + s * (i + 1) := by
            rw [hfill, Nat.mul_succ]
            omega
          rw [List.flatten_cons,
            List.getD_append_right fill fills.flatten default _ hsle]
          have hsub : x + s * (i + 1) - fill.length = x + s * i := by
            rw [hfill, Nat.mul_succ]
            omega
          rw [hsub, ih i hiTail hallTail]
          simp

theorem selectedFillVertices_length
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length) :
    (selectedFillVertices a ha h).length =
      slackTrialCount a * slackFillSize a := by
  unfold selectedFillVertices
  apply length_flatten_take_of_forall_length _ _ _ hready
  intro fill hfill
  exact successfulBranchFills_all_length a ha h hfill

/-- Row-major indexing really selects vertex `x` from retained trial `i`.
This makes the connection between the globally flattened injective map and
the branch attempt from which each retained fill arose explicit. -/
theorem selectedFillVertex_eq_successfulFill_getD_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    selectedFillVertex a ha h i x =
      ((successfulBranchFills a ha h).getD i.1 []).getD x.1
        (slackCenter a ha) := by
  let fills := (successfulBranchFills a ha h).take (slackTrialCount a)
  have hlen : fills.length = slackTrialCount a := by
    simp [fills, Nat.min_eq_left hready]
  have hi : i.1 < fills.length := by simpa [hlen] using i.2
  have hall : ∀ fill ∈ fills, fill.length = slackFillSize a := by
    intro fill hfill
    exact successfulBranchFills_all_length a ha h
      ((List.take_sublist _ _).subset hfill)
  have hflat := getD_flatten_eq_getD_getD_of_forall_length
    fills (slackFillSize a) i.1 x.1 (slackCenter a ha) hi x.2 hall
  have hiAll : i.1 < (successfulBranchFills a ha h).length :=
    i.2.trans_le hready
  have htakeGet : fills.getD i.1 [] =
      (successfulBranchFills a ha h).getD i.1 [] := by
    rw [List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ hiAll]
    exact List.getElem_take
  unfold selectedFillVertex selectedFillVertices
  change fills.flatten.getD (x.1 + slackFillSize a * i.1)
      (slackCenter a ha) = _
  rw [hflat, htakeGet]

theorem selectedFillVertex_mem_successfulFill_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    selectedFillVertex a ha h i x ∈
      (successfulBranchFills a ha h).getD i.1 [] := by
  have hi : i.1 < (successfulBranchFills a ha h).length :=
    i.2.trans_le hready
  let fill := (successfulBranchFills a ha h)[i.1]
  have hfillMem : fill ∈ successfulBranchFills a ha h :=
    List.getElem_mem hi
  have hfillLength : fill.length = slackFillSize a :=
    successfulBranchFills_all_length a ha h hfillMem
  have hx : x.1 < fill.length := by
    rw [hfillLength]
    exact x.2
  rw [selectedFillVertex_eq_successfulFill_getD_of_ready a ha h hready i x,
    List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ hx]
  exact List.getElem_mem hx

/-- Root-to-fill positivity is not extra path data: it follows from the
actual branch filter once enough retained trials exist. -/
theorem selectedFillRoot_fill_positive_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    (s(selectedFillRoot a ha h i, selectedFillVertex a ha h i x), true) ∈ h := by
  unfold selectedFillRoot
  apply selectedBranchFill_root_positive a ha h (slackAttemptCount a)
    (selectedFillAttempt a ha h i)
    (selectedFillAttempt_lt_of_ready a ha h hready i)
  rw [selectedFillAttempt_getD_eq_successfulFill_of_ready a ha h hready i]
  exact selectedFillVertex_mem_successfulFill_of_ready a ha h hready i x

/-- Once enough successful branch trials exist, global disjointness of the
actual selected fill vertices follows automatically from the allocator. -/
theorem selectedFillVertex_pair_injective
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length) :
    Function.Injective
      (fun ix : Fin (slackTrialCount a) × TrialVertex a ↦
        selectedFillVertex a ha h ix.1 ix.2) := by
  intro ix jy heq
  have hlength := selectedFillVertices_length a ha h hready
  have hix : (finProdFinEquiv (ix.1, ix.2)).1 <
      (selectedFillVertices a ha h).length := by
    rw [hlength]
    exact (finProdFinEquiv (ix.1, ix.2)).2
  have hjy : (finProdFinEquiv (jy.1, jy.2)).1 <
      (selectedFillVertices a ha h).length := by
    rw [hlength]
    exact (finProdFinEquiv (jy.1, jy.2)).2
  change (selectedFillVertices a ha h).getD
      (finProdFinEquiv (ix.1, ix.2)).1 (slackCenter a ha) =
    (selectedFillVertices a ha h).getD
      (finProdFinEquiv (jy.1, jy.2)).1 (slackCenter a ha) at heq
  rw [List.getD_eq_getElem _ _ hix,
    List.getD_eq_getElem _ _ hjy] at heq
  have hval : (finProdFinEquiv (ix.1, ix.2)).1 =
      (finProdFinEquiv (jy.1, jy.2)).1 :=
    (selectedFillVertices_nodup a ha h).getElem_inj_iff.mp heq
  exact finProdFinEquiv.injective (Fin.ext hval)

theorem selectedFillVertex_mem_reservoir_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    selectedFillVertex a ha h i x ∈ selectedReservoir a ha h := by
  have hlength := selectedFillVertices_length a ha h hready
  have hix : (finProdFinEquiv (i, x)).1 <
      (selectedFillVertices a ha h).length := by
    rw [hlength]
    exact (finProdFinEquiv (i, x)).2
  have hmemSelected : selectedFillVertex a ha h i x ∈
      selectedFillVertices a ha h := by
    rw [selectedFillVertex, List.getD_eq_getElem _ _ hix]
    exact List.getElem_mem hix
  have hmemSuccess : selectedFillVertex a ha h i x ∈
      (successfulBranchFills a ha h).flatten :=
    (List.take_sublist _ _).flatten.subset hmemSelected
  have hmemAll : selectedFillVertex a ha h i x ∈
      (selectedBranchFills a ha h (slackAttemptCount a)).flatten :=
    List.filter_sublist.flatten.subset hmemSuccess
  exact selectedBranchFills_flatten_subset_reservoir a ha h _ hmemAll

theorem selectedFillVertex_mem_reservoirDrop_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    selectedFillVertex a ha h i x ∈
      (selectedReservoir a ha h).drop (slackAttemptCount a) := by
  have hlength := selectedFillVertices_length a ha h hready
  have hix : (finProdFinEquiv (i, x)).1 <
      (selectedFillVertices a ha h).length := by
    rw [hlength]
    exact (finProdFinEquiv (i, x)).2
  have hmemSelected : selectedFillVertex a ha h i x ∈
      selectedFillVertices a ha h := by
    rw [selectedFillVertex, List.getD_eq_getElem _ _ hix]
    exact List.getElem_mem hix
  have hmemSuccess : selectedFillVertex a ha h i x ∈
      (successfulBranchFills a ha h).flatten :=
    (List.take_sublist _ _).flatten.subset hmemSelected
  have hmemAll : selectedFillVertex a ha h i x ∈
      (selectedBranchFills a ha h (slackAttemptCount a)).flatten :=
    List.filter_sublist.flatten.subset hmemSuccess
  exact selectedBranchFills_flatten_subset_reservoirDrop a ha h _ hmemAll

theorem selectedRoot_ne_selectedFillVertex_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hreservoir : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (hbranch : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (j : ℕ) (hj : j < slackAttemptCount a)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    selectedRoot a ha h j ≠ selectedFillVertex a ha h i x := by
  have hlen := selectedReservoir_length_of_ready a ha h hreservoir
  have hjR : j < slackReservoirSize a :=
    hj.trans_le (slackAttemptCount_le_reservoirSize a)
  have hjLen : j < (selectedReservoir a ha h).length := by
    simpa [hlen] using hjR
  have hjTakeLen : j <
      ((selectedReservoir a ha h).take (slackAttemptCount a)).length := by
    simp only [List.length_take]
    rw [Nat.min_eq_left]
    · exact hj
    · rw [hlen]
      exact slackAttemptCount_le_reservoirSize a
  have hrootTake : selectedRoot a ha h j ∈
      (selectedReservoir a ha h).take (slackAttemptCount a) := by
    rw [selectedRoot, List.getD_eq_getElem _ _ hjLen]
    have hm := List.getElem_mem hjTakeLen
    simpa using hm
  have hfillDrop := selectedFillVertex_mem_reservoirDrop_of_ready
    a ha h hbranch i x
  have happend : ((selectedReservoir a ha h).take (slackAttemptCount a) ++
      (selectedReservoir a ha h).drop (slackAttemptCount a)).Nodup := by
    simpa using selectedReservoir_nodup a ha h
  have hdisjoint := List.disjoint_of_nodup_append happend
  rw [List.disjoint_left] at hdisjoint
  intro heq
  rw [heq] at hrootTake
  exact hdisjoint hrootTake hfillDrop

theorem selectedFillVertex_center_positive_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    (s(slackCenter a ha, selectedFillVertex a ha h i x), true) ∈ h :=
  mem_selectedReservoir_center_positive a ha h
    (selectedFillVertex_mem_reservoir_of_ready a ha h hready i x)

theorem selectedFillVertex_center_ne_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hready : slackTrialCount a ≤ (successfulBranchFills a ha h).length)
    (i : Fin (slackTrialCount a)) (x : TrialVertex a) :
    slackCenter a ha ≠ selectedFillVertex a ha h i x :=
  mem_selectedReservoir_center_ne a ha h
    (selectedFillVertex_mem_reservoir_of_ready a ha h hready i x)

/-- Oldest pre-fill part of a transcript.  During the fill phase this drops
all answers already obtained inside fills and therefore freezes the adaptive
reservoir allocation. -/
def slackBranchPrefix (a : ℕ)
    (h : Transcript (Query (slackQueryBudget a))) :
    Transcript (Query (slackQueryBudget a)) :=
  h.drop (h.length - slackFillStart a)

theorem slackBranchPrefix_eq_self_of_length
    (a : ℕ) (h : Transcript (Query (slackQueryBudget a)))
    (hlen : h.length = slackFillStart a) :
    slackBranchPrefix a h = h := by
  simp [slackBranchPrefix, hlen]

theorem slackBranchPrefix_cons_of_fillStart_le
    (a : ℕ) (h : Transcript (Query (slackQueryBudget a)))
    (entry : Query (slackQueryBudget a) × Bool)
    (hlen : slackFillStart a ≤ h.length) :
    slackBranchPrefix a (entry :: h) = slackBranchPrefix a h := by
  unfold slackBranchPrefix
  simp only [List.length_cons]
  have hsub : h.length + 1 - slackFillStart a =
      (h.length - slackFillStart a) + 1 := by omega
  rw [hsub, List.drop_succ_cons]

theorem slackBranchPrefix_sublist (a : ℕ)
    (h : Transcript (Query (slackQueryBudget a))) :
    (slackBranchPrefix a h).Sublist h := by
  exact List.drop_sublist _ _

/-- Fill coordinate attached to a newest-first answer position, with all
selected vertices read from the frozen pre-fill transcript. -/
noncomputable def slackFillQuery (a : ℕ) (ha : 1 ≤ a)
    (base : Transcript (Query (slackQueryBudget a)))
    (j : Fin (slackFillQueryCount a)) : Query (slackQueryBudget a) :=
  let iq := slackFillCoordEquiv a j
  Sym2.map (selectedFillVertex a ha base iq.1) iq.2

/-- Concrete centre-star / branch / fill program before global legalization. -/
noncomputable def proposedSlackStrategy (a : ℕ) (ha : 1 ≤ a) :
    K6Strategy (slackQueryBudget a) := fun h ↦
  if hstar : h.length < slackStarQueries a then
    s(slackCenter a ha,
      slackStarVertex a ha ⟨h.length, hstar⟩)
  else if hbranch : h.length <
      slackStarQueries a + slackAttemptCount a * slackBranchScan a then
    let offset : Fin (slackAttemptCount a * slackBranchScan a) :=
      ⟨h.length - slackStarQueries a, by omega⟩
    let ik : Fin (slackAttemptCount a) × Fin (slackBranchScan a) :=
      finProdFinEquiv.symm offset
    s(selectedRoot a ha h ik.1.1,
      (selectedBranchCandidates a ha h ik.1.1).getD ik.2.1
        (slackCenter a ha))
  else if hbudget : h.length < slackQueryBudget a then
    let offset : Fin (slackFillQueryCount a) :=
      ⟨h.length - slackFillStart a, by
        unfold slackQueryBudget at hbudget
        unfold slackFillStart slackFillQueryCount
        omega⟩
    slackFillQuery a ha (slackBranchPrefix a h) (Fin.rev offset)
  else
    s(slackCenter a ha, slackCenter a ha)

/-- The fixed reverse schedule used after a pre-fill transcript has frozen
the selected trial vertices. -/
noncomputable def slackFillContinuation (a : ℕ) (ha : 1 ≤ a)
    (base : Transcript (Query (slackQueryBudget a))) :
    Strategy (Query (slackQueryBudget a)) := fun h ↦
  if hlen : h.length < slackFillQueryCount a then
    slackFillQuery a ha base (Fin.rev ⟨h.length, hlen⟩)
  else
    s(slackCenter a ha, slackCenter a ha)

@[simp] theorem slackFillContinuation_of_length_lt
    (a : ℕ) (ha : 1 ≤ a)
    (base : Transcript (Query (slackQueryBudget a)))
    (h : Transcript (Query (slackQueryBudget a)))
    (hlen : h.length < slackFillQueryCount a) :
    slackFillContinuation a ha base h =
      slackFillQuery a ha base (Fin.rev ⟨h.length, hlen⟩) := by
  simp [slackFillContinuation, hlen]

theorem proposedSlackStrategy_fill
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hstart : slackFillStart a ≤ h.length)
    (hbudget : h.length < slackQueryBudget a) :
    proposedSlackStrategy a ha h =
      slackFillQuery a ha (slackBranchPrefix a h)
        (Fin.rev ⟨h.length - slackFillStart a, by
          have hbudget' : h.length <
              slackFillStart a + slackFillQueryCount a := by
            calc
              h.length < slackQueryBudget a := hbudget
              _ = slackFillStart a + slackFillQueryCount a :=
                slackQueryBudget_eq_fillStart_add a
          omega⟩) := by
  have hstar : ¬ h.length < slackStarQueries a := by
    unfold slackFillStart at hstart
    omega
  have hbranch : ¬ h.length <
      slackStarQueries a + slackAttemptCount a * slackBranchScan a := by
    simpa [slackFillStart] using (not_lt.mpr hstart)
  simp [proposedSlackStrategy, hstar, hbranch, hbudget, slackFillStart,
    slackFillQueryCount]

/-- The frozen fill continuation is exactly the generic reverse schedule.
Consequently a complete newest-first fill answer vector is replayed in its
canonical row-major coordinate order. -/
theorem replay_slackFillContinuation_ofFn
    (a : ℕ) (ha : 1 ≤ a)
    (base : Transcript (Query (slackQueryBudget a)))
    (bits : Fin (slackFillQueryCount a) → Bool) :
    replay (slackFillContinuation a ha base) (List.ofFn bits) =
      List.ofFn (fun j ↦ (slackFillQuery a ha base j, bits j)) := by
  simpa only [slackFillContinuation,
    BaselineStrategy.reverseScheduleStrategy] using
    (BaselineStrategy.replay_reverseSchedule_ofFn
      (slackFillQueryCount a) (slackFillQuery a ha base)
      s(slackCenter a ha, slackCenter a ha) bits)

/-- Every canonical fill coordinate occurs with the corresponding answer in
the replay of the frozen continuation. -/
theorem slackFillQuery_get_mem_replay
    (a : ℕ) (ha : 1 ≤ a)
    (base : Transcript (Query (slackQueryBudget a)))
    (bits : List.Vector Bool (slackFillQueryCount a))
    (j : Fin (slackFillQueryCount a)) :
    (slackFillQuery a ha base j, bits.get j) ∈
      replay (slackFillContinuation a ha base) bits.toList := by
  simpa only [slackFillContinuation,
    BaselineStrategy.reverseScheduleStrategy] using
    (BaselineStrategy.schedule_get_mem_replay
      (slackFillQueryCount a) (slackFillQuery a ha base)
      s(slackCenter a ha, slackCenter a ha) bits j)

/-- Dropping the newest fill answers from a transcript whose oldest suffix
has exactly the pre-fill length recovers that suffix. -/
theorem slackBranchPrefix_append_of_length
    (a : ℕ)
    (fill base : Transcript (Query (slackQueryBudget a)))
    (hbase : base.length = slackFillStart a) :
    slackBranchPrefix a (fill ++ base) = base := by
  unfold slackBranchPrefix
  rw [List.length_append, hbase]
  have hsub : fill.length + slackFillStart a - slackFillStart a =
      fill.length := by omega
  rw [hsub, List.drop_left]

/-- Once the pre-fill transcript has been completed, the actual proposed
strategy agrees pathwise with the frozen continuation.  The answer lists are
newest-first, hence the fill answers are prepended to the pre-fill answers. -/
theorem replay_proposedSlackStrategy_fill_append
    (a : ℕ) (ha : 1 ≤ a)
    (baseBits fillBits : List Bool)
    (hbase : baseBits.length = slackFillStart a)
    (hfill : fillBits.length ≤ slackFillQueryCount a) :
    replay (proposedSlackStrategy a ha) (fillBits ++ baseBits) =
      replay (slackFillContinuation a ha
        (replay (proposedSlackStrategy a ha) baseBits)) fillBits ++
      replay (proposedSlackStrategy a ha) baseBits := by
  induction fillBits with
  | nil => simp
  | cons bit tail ih =>
      have htail : tail.length < slackFillQueryCount a := by
        simpa using hfill
      have htailLe : tail.length ≤ slackFillQueryCount a :=
        Nat.le_of_lt htail
      rw [List.cons_append, replay_cons, ih htailLe,
        replay_cons]
      let base := replay (proposedSlackStrategy a ha) baseBits
      let fill := replay (slackFillContinuation a ha base) tail
      have hbaseReplay : base.length = slackFillStart a := by
        simp [base, hbase]
      have hfillReplay : fill.length = tail.length := by
        simp [fill]
      have hstart : slackFillStart a ≤ (fill ++ base).length := by
        simp [hbaseReplay]
      have hbudget : (fill ++ base).length < slackQueryBudget a := by
        rw [List.length_append, hfillReplay, hbaseReplay,
          slackQueryBudget_eq_fillStart_add]
        omega
      rw [proposedSlackStrategy_fill a ha (fill ++ base) hstart hbudget]
      rw [slackBranchPrefix_append_of_length a fill base hbaseReplay]
      have hfillLt : fill.length < slackFillQueryCount a := by
        simpa [hfillReplay] using htail
      rw [slackFillContinuation_of_length_lt a ha base fill hfillLt]
      apply congrArg (fun q : Query (slackQueryBudget a) ↦
        (q, bit) :: fill ++ base)
      apply congrArg (slackFillQuery a ha base)
      apply congrArg Fin.rev
      apply Fin.ext
      simp only [List.length_append, hfillReplay, hbaseReplay]
      omega

theorem slackFillQueryCount_le_budget (a : ℕ) :
    slackFillQueryCount a ≤ slackQueryBudget a := by
  rw [slackQueryBudget_eq_fillStart_add]
  omega

/-- The newest `slackFillQueryCount` answers in a complete path, packaged as
the canonical row-major fill answer vector. -/
def slackFillAnswerVector (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    List.Vector Bool (slackFillQueryCount a) :=
  ⟨bits.toList.take (slackFillQueryCount a), by
    simp only [List.length_take, List.Vector.toList_length]
    exact Nat.min_eq_left (slackFillQueryCount_le_budget a)⟩

/-- The oldest pre-fill answers in a complete newest-first answer vector. -/
def slackBranchAnswerList (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) : List Bool :=
  bits.toList.drop (slackFillQueryCount a)

theorem slackBranchAnswerList_length (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    (slackBranchAnswerList a bits).length = slackFillStart a := by
  simp only [slackBranchAnswerList, List.length_drop,
    List.Vector.toList_length]
  rw [slackQueryBudget_eq_fillStart_add]
  omega

/-- Vector form of the pre-fill suffix. -/
def slackBranchAnswerVector (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    List.Vector Bool (slackFillStart a) :=
  ⟨slackBranchAnswerList a bits, slackBranchAnswerList_length a bits⟩

theorem slackFill_branch_answer_decomposition (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    (slackFillAnswerVector a bits).toList ++
      slackBranchAnswerList a bits = bits.toList := by
  exact List.take_append_drop (slackFillQueryCount a) bits.toList

/-- Recombine a fill vector and a pre-fill vector into one complete
newest-first answer vector. -/
def combineSlackAnswers (a : ℕ)
    (pair : List.Vector Bool (slackFillQueryCount a) ×
      List.Vector Bool (slackFillStart a)) :
    List.Vector Bool (slackQueryBudget a) :=
  ⟨pair.1.toList ++ pair.2.toList, by
    simp only [List.length_append, List.Vector.toList_length]
    rw [slackQueryBudget_eq_fillStart_add]
    omega⟩

theorem combine_split_slackAnswers (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    combineSlackAnswers a
      (slackFillAnswerVector a bits, slackBranchAnswerVector a bits) = bits := by
  apply List.Vector.eq
  exact slackFill_branch_answer_decomposition a bits

theorem split_combine_slackAnswers (a : ℕ)
    (pair : List.Vector Bool (slackFillQueryCount a) ×
      List.Vector Bool (slackFillStart a)) :
    (slackFillAnswerVector a (combineSlackAnswers a pair),
      slackBranchAnswerVector a (combineSlackAnswers a pair)) = pair := by
  rcases pair with ⟨fill, base⟩
  apply Prod.ext
  · apply List.Vector.eq
    change (fill.toList ++ base.toList).take (slackFillQueryCount a) =
      fill.toList
    simpa only [List.Vector.toList_length] using
      (List.take_left (l₁ := fill.toList) (l₂ := base.toList))
  · apply List.Vector.eq
    change (fill.toList ++ base.toList).drop (slackFillQueryCount a) =
      base.toList
    simpa only [List.Vector.toList_length] using
      (List.drop_left (l₁ := fill.toList) (l₂ := base.toList))

/-- Canonical split of a complete path into its final-fill prefix and its
older reservoir/branch suffix. -/
def slackAnswerSplitEquiv (a : ℕ) :
    List.Vector Bool (slackQueryBudget a) ≃
      (List.Vector Bool (slackFillQueryCount a) ×
        List.Vector Bool (slackFillStart a)) where
  toFun bits := (slackFillAnswerVector a bits, slackBranchAnswerVector a bits)
  invFun := combineSlackAnswers a
  left_inv := combine_split_slackAnswers a
  right_inv := split_combine_slackAnswers a

/-- Bernoulli weights factor exactly across the fill/pre-fill split. -/
theorem slackAnswerSplitEquiv_weight (p : ℝ≥0∞) (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    (bits.toList.map (bernoulliWeight p)).prod =
      (((slackAnswerSplitEquiv a bits).1.toList.map
        (bernoulliWeight p)).prod) *
      (((slackAnswerSplitEquiv a bits).2.toList.map
        (bernoulliWeight p)).prod) := by
  rw [← slackFill_branch_answer_decomposition a bits,
    List.map_append, List.prod_append]
  rfl

/-- On a complete path, freezing the transcript at the fill boundary is the
same as replaying only the oldest pre-fill answer suffix. -/
theorem slackBranchPrefix_replay_eq
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList) =
      replay (proposedSlackStrategy a ha) (slackBranchAnswerList a bits) := by
  let fillBits := (slackFillAnswerVector a bits).toList
  let baseBits := slackBranchAnswerList a bits
  let base := replay (proposedSlackStrategy a ha) baseBits
  let fill := replay (slackFillContinuation a ha base) fillBits
  have hbaseBits : baseBits.length = slackFillStart a := by
    exact slackBranchAnswerList_length a bits
  have hfillBits : fillBits.length ≤ slackFillQueryCount a := by
    simp [fillBits]
  have hdecomp : fillBits ++ baseBits = bits.toList := by
    exact slackFill_branch_answer_decomposition a bits
  have hrep := replay_proposedSlackStrategy_fill_append a ha
    baseBits fillBits hbaseBits hfillBits
  rw [hdecomp] at hrep
  have hbase : base.length = slackFillStart a := by
    simp [base, hbaseBits]
  calc
    slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList) =
      slackBranchPrefix a (fill ++ base) := congrArg (slackBranchPrefix a) hrep
    _ = base := slackBranchPrefix_append_of_length a fill base hbase

/-- Canonical fill boards extracted directly from the fill segment of a
complete answer vector. -/
noncomputable def slackFillBoards (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) :
    Fin (slackTrialCount a) → Board (OffDiagTrialQuery a) :=
  fun i q ↦ (slackFillAnswerVector a bits).get
    ((slackFillCoordEquiv a).symm (i, q))

/-- Pack a stand-alone fill answer vector using exactly the coordinate
enumeration used by the concrete slack strategy. -/
noncomputable def packSlackFillAnswers (a : ℕ)
    (bits : List.Vector Bool (slackFillQueryCount a)) :
    Fin (slackTrialCount a) → Board (OffDiagTrialQuery a) :=
  fun i q ↦ bits.get ((slackFillCoordEquiv a).symm (i, q))

noncomputable def unpackSlackFillAnswers (a : ℕ)
    (boards : Fin (slackTrialCount a) → Board (OffDiagTrialQuery a)) :
    List.Vector Bool (slackFillQueryCount a) :=
  List.Vector.ofFn fun j ↦
    let iq := slackFillCoordEquiv a j
    boards iq.1 iq.2

theorem unpack_pack_slackFillAnswers (a : ℕ)
    (bits : List.Vector Bool (slackFillQueryCount a)) :
    unpackSlackFillAnswers a (packSlackFillAnswers a bits) = bits := by
  apply List.Vector.ext
  intro j
  simp only [unpackSlackFillAnswers, List.Vector.get_ofFn,
    packSlackFillAnswers]
  exact congrArg bits.get (Equiv.symm_apply_apply (slackFillCoordEquiv a) j)

theorem pack_unpack_slackFillAnswers (a : ℕ)
    (boards : Fin (slackTrialCount a) → Board (OffDiagTrialQuery a)) :
    packSlackFillAnswers a (unpackSlackFillAnswers a boards) = boards := by
  funext i q
  simp [packSlackFillAnswers, unpackSlackFillAnswers]

/-- Exact answer-vector/product-board equivalence for the implemented fill
schedule (including its concrete cardinality cast). -/
noncomputable def slackFillAnswerEquiv (a : ℕ) :
    List.Vector Bool (slackFillQueryCount a) ≃
      (Fin (slackTrialCount a) → Board (OffDiagTrialQuery a)) where
  toFun := packSlackFillAnswers a
  invFun := unpackSlackFillAnswers a
  left_inv := unpack_pack_slackFillAnswers a
  right_inv := pack_unpack_slackFillAnswers a

@[simp] theorem slackFillBoards_eq_slackFillAnswerEquiv
    (a : ℕ) (bits : List.Vector Bool (slackQueryBudget a)) :
    slackFillBoards a bits =
      slackFillAnswerEquiv a (slackFillAnswerVector a bits) := rfl

/-- The Bernoulli weight of the actual fill segment is exactly the product
point mass of its extracted trial boards. -/
theorem slackFillAnswerEquiv_weight (p : ℝ≥0∞) (a : ℕ)
    (bits : List.Vector Bool (slackFillQueryCount a)) :
    (bits.toList.map (bernoulliWeight p)).prod =
      outcomeVectorWeight
        (fun board : Board (OffDiagTrialQuery a) ↦
          boardWeight (bernoulliWeight p) board)
        (slackFillAnswerEquiv a bits) := by
  have hlist : bits.toList = List.ofFn bits.get := by
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  simp only [outcomeVectorWeight, boardWeight, slackFillAnswerEquiv,
    packSlackFillAnswers]
  rw [hlist, List.map_ofFn, List.prod_ofFn]
  change (∏ j : Fin (slackFillQueryCount a),
      bernoulliWeight p (bits.get j)) =
    ∏ i : Fin (slackTrialCount a), ∏ q : OffDiagTrialQuery a,
      bernoulliWeight p
        (bits.get ((slackFillCoordEquiv a).symm (i, q)))
  rw [Fintype.prod_equiv (slackFillCoordEquiv a)
    (fun j : Fin (slackFillQueryCount a) ↦
      bernoulliWeight p (bits.get j))
    (fun iq : Fin (slackTrialCount a) × OffDiagTrialQuery a ↦
      bernoulliWeight p
        (bits.get ((slackFillCoordEquiv a).symm iq))) (by
          intro j
          exact congrArg (fun z ↦ bernoulliWeight p (bits.get z))
            (Equiv.symm_apply_apply (slackFillCoordEquiv a) j).symm)]
  rw [Fintype.prod_prod_type]

/-- Exact amplified failure mass for the canonical fill segment of the
implemented strategy. -/
theorem slackFill_allFailure_weight_eq (a : ℕ) :
    (∑ bits : List.Vector Bool (slackFillQueryCount a),
      if slackFillAnswerEquiv a bits ∈
          allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a) then
        (bits.toList.map (bernoulliWeight (densityENN a))).prod else 0) =
      repeatedOffDiagK4FailureMass a (slackTrialCount a) := by
  unfold repeatedOffDiagK4FailureMass finiteOutcomeProductMass
  apply Fintype.sum_equiv (slackFillAnswerEquiv a)
  intro bits
  by_cases hfail : slackFillAnswerEquiv a bits ∈
      allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a)
  · simp [hfail, slackFillAnswerEquiv_weight]
  · simp [hfail]

/-- Exact product law for arbitrary events on the fill and pre-fill answer
segments.  This is purely a finite answer-vector theorem and therefore does
not require a host-board coupling or any independence assumption. -/
theorem slackAnswerSplit_event_weight_eq
    (p : ℝ≥0∞) (a : ℕ)
    (Pfill : List.Vector Bool (slackFillQueryCount a) → Prop)
    (Pbase : List.Vector Bool (slackFillStart a) → Prop)
    [DecidablePred Pfill] [DecidablePred Pbase] :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if Pfill (slackFillAnswerVector a bits) ∧
          Pbase (slackBranchAnswerVector a bits) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      (∑ fill : List.Vector Bool (slackFillQueryCount a),
        if Pfill fill then
          (fill.toList.map (bernoulliWeight p)).prod else 0) *
      (∑ base : List.Vector Bool (slackFillStart a),
        if Pbase base then
          (base.toList.map (bernoulliWeight p)).prod else 0) := by
  calc
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if Pfill (slackFillAnswerVector a bits) ∧
          Pbase (slackBranchAnswerVector a bits) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
        ∑ pair : List.Vector Bool (slackFillQueryCount a) ×
            List.Vector Bool (slackFillStart a),
          if Pfill pair.1 ∧ Pbase pair.2 then
            (pair.1.toList.map (bernoulliWeight p)).prod *
              (pair.2.toList.map (bernoulliWeight p)).prod else 0 := by
      apply Fintype.sum_equiv (slackAnswerSplitEquiv a)
      intro bits
      rw [slackAnswerSplitEquiv_weight]
      rfl
    _ = ∑ fill : List.Vector Bool (slackFillQueryCount a),
          ∑ base : List.Vector Bool (slackFillStart a),
            if Pfill fill ∧ Pbase base then
              (fill.toList.map (bernoulliWeight p)).prod *
                (base.toList.map (bernoulliWeight p)).prod else 0 := by
      rw [Fintype.sum_prod_type]
    _ = (∑ fill : List.Vector Bool (slackFillQueryCount a),
          if Pfill fill then
            (fill.toList.map (bernoulliWeight p)).prod else 0) *
        (∑ base : List.Vector Bool (slackFillStart a),
          if Pbase base then
            (base.toList.map (bernoulliWeight p)).prod else 0) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro fill _hfill
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro base _hbase
      by_cases hf : Pfill fill <;> by_cases hb : Pbase base <;>
        simp [hf, hb]

/-- In particular, conditioned on any pre-fill answer event, the complete
canonical fill-family failure mass is exactly the amplified off-diagonal
failure mass times the weight of that pre-fill event. -/
theorem slackFullFailure_with_prefix_weight_eq
    (a : ℕ)
    (Pbase : List.Vector Bool (slackFillStart a) → Prop)
    [DecidablePred Pbase] :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if slackFillAnswerEquiv a (slackFillAnswerVector a bits) ∈
            allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a) ∧
          Pbase (slackBranchAnswerVector a bits) then
        (bits.toList.map (bernoulliWeight (densityENN a))).prod else 0) =
      repeatedOffDiagK4FailureMass a (slackTrialCount a) *
        (∑ base : List.Vector Bool (slackFillStart a),
          if Pbase base then
            (base.toList.map (bernoulliWeight (densityENN a))).prod else 0) := by
  have hsplit := slackAnswerSplit_event_weight_eq (densityENN a) a
    (fun fill ↦ slackFillAnswerEquiv a fill ∈
      allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a)) Pbase
  rw [slackFill_allFailure_weight_eq] at hsplit
  exact hsplit

/-! ### A reusable first-moment tail for repeated scan outcomes -/

def badOutcomeCount {Ω : Type*} [Fintype Ω]
    (bad : Ω → Prop) {t : ℕ} (outcomes : Fin t → Ω) : ℕ :=
  ((Finset.univ : Finset (Fin t)).filter fun i ↦ bad (outcomes i)).card

def badOutcomeUpperTailEvent {Ω : Type*} [Fintype Ω]
    (bad : Ω → Prop) (t R : ℕ) :
    Set (Fin t → Ω) :=
  {outcomes | R ≤ badOutcomeCount bad outcomes}

/-- A single coordinate of a normalized finite product has its prescribed
one-coordinate marginal, stated in the indicator form needed below. -/
theorem outcomeVector_badCoordinate_mass
    {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ≥0∞) (hnormalized : (∑ x, weight x) = 1)
    (bad : Ω → Prop) (t : ℕ) (i : Fin t) :
    (∑ outcomes : Fin t → Ω,
      if bad (outcomes i) then outcomeVectorWeight weight outcomes else 0) =
      ∑ x : Ω, if bad x then weight x else 0 := by
  classical
  unfold outcomeVectorWeight
  calc
    (∑ outcomes : Fin t → Ω,
      if bad (outcomes i) then ∏ j, weight (outcomes j) else 0) =
        ∑ outcomes : Fin t → Ω,
          ∏ j, if j = i then
            (if bad (outcomes j) then weight (outcomes j) else 0)
          else weight (outcomes j) := by
      apply Finset.sum_congr rfl
      intro outcomes _houtcomes
      by_cases hb : bad (outcomes i)
      · rw [if_pos hb]
        apply Finset.prod_congr rfl
        intro j _hj
        by_cases hji : j = i
        · subst j
          simp [hb]
        · simp [hji]
      · rw [if_neg hb]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hb]
    _ = ∏ j : Fin t,
        ∑ x : Ω, if j = i then
          (if bad x then weight x else 0) else weight x := by
      simpa using (Fintype.prod_sum (fun j : Fin t ↦ fun x : Ω ↦
        if j = i then (if bad x then weight x else 0) else weight x)).symm
    _ = ∑ x : Ω, if bad x then weight x else 0 := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _hj hji
        simp [hji, hnormalized]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))

/-- Markov's inequality for the number of bad outcomes in an arbitrary
normalized finite product.  No independence argument remains implicit: the
whole calculation is an equality/inequality between explicit finite sums. -/
theorem badOutcomeUpperTail_mul_le
    {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ≥0∞) (hnormalized : (∑ x, weight x) = 1)
    (bad : Ω → Prop) (t R : ℕ) :
    (R : ℝ≥0∞) * finiteOutcomeProductMass weight t
        (badOutcomeUpperTailEvent bad t R) ≤
      (t : ℝ≥0∞) * (∑ x : Ω, if bad x then weight x else 0) := by
  classical
  unfold finiteOutcomeProductMass badOutcomeUpperTailEvent
  simp only [Set.mem_setOf_eq]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ outcomes : Fin t → Ω,
        outcomeVectorWeight weight outcomes *
          (badOutcomeCount bad outcomes : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro outcomes _houtcomes
      by_cases htail : R ≤ badOutcomeCount bad outcomes
      · rw [if_pos htail]
        have hcast : (R : ℝ≥0∞) ≤
            (badOutcomeCount bad outcomes : ℝ≥0∞) := by
          exact_mod_cast htail
        simpa [mul_comm] using mul_le_mul_right'
          hcast (outcomeVectorWeight weight outcomes)
      · simp [htail]
    _ = ∑ i : Fin t, ∑ outcomes : Fin t → Ω,
        if bad (outcomes i) then outcomeVectorWeight weight outcomes else 0 := by
      have hcount (outcomes : Fin t → Ω) :
          (badOutcomeCount bad outcomes : ℝ≥0∞) =
            ∑ i : Fin t, if bad (outcomes i) then 1 else 0 := by
        unfold badOutcomeCount
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        simp
      calc
        _ = ∑ outcomes : Fin t → Ω, ∑ i : Fin t,
            if bad (outcomes i) then
              outcomeVectorWeight weight outcomes else 0 := by
          apply Finset.sum_congr rfl
          intro outcomes _houtcomes
          rw [hcount outcomes, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hb : bad (outcomes i) <;> simp [hb]
        _ = _ := Finset.sum_comm
    _ = ∑ _i : Fin t, ∑ x : Ω, if bad x then weight x else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact outcomeVector_badCoordinate_mass weight hnormalized bad t i
    _ = (t : ℝ≥0∞) * (∑ x : Ω, if bad x then weight x else 0) := by
      simp

/-- If `2T` independent grouped scans are made and a single scan is bad
with the `2⁻⁶³` bound above, then the chance that at least `T` scans are bad
is at most twice that bound.  Crucially, the estimate is independent of `T`.
-/
theorem repeatedGroupedScanHalfTail_le
    (a T : ℕ) (ha : 2 ≤ a) (hT : 0 < T)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    finiteOutcomeProductMass
        (fun board : Board
            (Fin (2 * slackFillSize a) × Fin (slackBlockSize a)) ↦
          boardWeight (bernoulliWeight p) board)
        (2 * T)
        (badOutcomeUpperTailEvent
          (fun board : Board
              (Fin (2 * slackFillSize a) × Fin (slackBlockSize a)) ↦
            board ∈ emptyBlockUpperTailEvent
              (2 * slackFillSize a) (slackBlockSize a)
              (slackFillSize a))
          (2 * T) T) ≤
      (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  let scanWeight : Board
      (Fin (2 * slackFillSize a) × Fin (slackBlockSize a)) → ℝ≥0∞ :=
    fun board ↦ boardWeight (bernoulliWeight p) board
  let bad : Board
      (Fin (2 * slackFillSize a) × Fin (slackBlockSize a)) → Prop :=
    fun board ↦ board ∈ emptyBlockUpperTailEvent
      (2 * slackFillSize a) (slackBlockSize a) (slackFillSize a)
  have hnormalized : (∑ board, scanWeight board) = 1 := by
    exact sum_boardWeight (bernoulliWeight p) (sum_bernoulliWeight p hp)
  have hfillPos : 0 < slackFillSize a := by
    unfold slackFillSize
    positivity
  have hone : (∑ board, if bad board then scanWeight board else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
    exact emptyBlockHalfTail_le a (slackFillSize a) ha hfillPos
      p hp hdensity
  have hmarkov := badOutcomeUpperTail_mul_le scanWeight hnormalized bad
    (2 * T) T
  have hscaled : (T : ℝ≥0∞) *
      finiteOutcomeProductMass scanWeight (2 * T)
        (badOutcomeUpperTailEvent bad (2 * T) T) ≤
      (T : ℝ≥0∞) *
        ((2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63) := by
    calc
      (T : ℝ≥0∞) * finiteOutcomeProductMass scanWeight (2 * T)
          (badOutcomeUpperTailEvent bad (2 * T) T) ≤
          ((2 * T : ℕ) : ℝ≥0∞) *
            (∑ board, if bad board then scanWeight board else 0) := hmarkov
      _ ≤ ((2 * T : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 :=
        mul_le_mul_left' hone _
      _ = (T : ℝ≥0∞) *
          ((2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63) := by
        push_cast
        ring
  exact (ENNReal.mul_le_mul_left (by exact_mod_cast (Nat.ne_of_gt hT))
    (by simp : (T : ℝ≥0∞) ≠ ⊤)).mp hscaled

/-! ### Turning the block tail into positive-answer supply -/

def trueBoardCount {Q : Type*} [Fintype Q] (board : Board Q) : ℕ :=
  ((Finset.univ : Finset Q).filter fun q ↦ board q = true).card

/-- Each nonempty block supplies a distinct positive coordinate. -/
theorem groups_sub_emptyBlockCount_le_trueBoardCount
    (groups blockSize : ℕ)
    (board : Board (Fin groups × Fin blockSize)) :
    groups - emptyBlockCount board ≤ trueBoardCount board := by
  classical
  let positives : Finset (Fin groups × Fin blockSize) :=
    Finset.univ.filter fun q ↦ board q = true
  let nonempty : Finset (Fin groups) :=
    Finset.univ.filter fun i ↦ ¬EmptyBlock board i
  have himage : positives.image Prod.fst = nonempty := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨q, hq, hqi⟩
      rcases q with ⟨q₁, q₂⟩
      simp only [positives, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [nonempty, Finset.mem_filter, Finset.mem_univ, true_and]
      subst i
      intro hempty
      rw [hempty q₂] at hq
      contradiction
    · intro hi
      simp only [nonempty, Finset.mem_filter, Finset.mem_univ, true_and,
        EmptyBlock] at hi
      push_neg at hi
      obtain ⟨j, hj⟩ := hi
      have hjtrue : board (i, j) = true := by
        cases hval : board (i, j) <;> simp [hval] at hj ⊢
      apply Finset.mem_image.mpr
      refine ⟨(i, j), ?_, rfl⟩
      simp [positives, hjtrue]
  have hnonempty_le : nonempty.card ≤ positives.card := by
    rw [← himage]
    exact Finset.card_image_le
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin groups)))
    (fun i ↦ EmptyBlock board i)
  have hempty : ((Finset.univ : Finset (Fin groups)).filter
      fun i ↦ EmptyBlock board i).card = emptyBlockCount board := rfl
  have hnonempty : ((Finset.univ : Finset (Fin groups)).filter
      fun i ↦ ¬EmptyBlock board i).card = nonempty.card := rfl
  have hpositive : positives.card = trueBoardCount board := rfl
  simp only [hempty, hnonempty, Finset.card_univ, Fintype.card_fin] at hpartition
  omega

/-- Packing a grouped answer vector preserves its number of positive
coordinates. -/
theorem trueBoardCount_groupedScanAnswerEquiv
    (groups blockSize : ℕ)
    (bits : List.Vector Bool (groupedScanAnswerCount groups blockSize)) :
    trueBoardCount (groupedScanAnswerEquiv groups blockSize bits) =
      bits.toList.count true := by
  classical
  let support := trueSupport bits
  let positives : Finset (Fin groups × Fin blockSize) :=
    Finset.univ.filter fun q ↦
      groupedScanAnswerEquiv groups blockSize bits q = true
  have himage : support.image finProdFinEquiv.symm = positives := by
    ext q
    simp only [support, trueSupport, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, positives]
    constructor
    · rintro ⟨j, hj, rfl⟩
      change bits.get (finProdFinEquiv (finProdFinEquiv.symm j)) = true
      rwa [Equiv.apply_symm_apply]
    · intro hq
      refine ⟨finProdFinEquiv q, ?_, Equiv.apply_symm_apply _ q⟩
      change bits.get (finProdFinEquiv q) = true at hq
      exact hq
  have hcardImage := Finset.card_image_of_injective support
    finProdFinEquiv.symm.injective
  rw [himage] at hcardImage
  calc
    trueBoardCount (groupedScanAnswerEquiv groups blockSize bits) =
        positives.card := rfl
    _ = support.card := hcardImage
    _ = bits.toList.count true := card_trueSupport bits

/-- A grouped scan with fewer than `R` positive answers necessarily lies in
the empty-block upper-tail event. -/
theorem groupedScan_fewTrue_mem_emptyBlockUpperTail
    (R blockSize : ℕ)
    (bits : List.Vector Bool (groupedScanAnswerCount (2 * R) blockSize))
    (hfew : bits.toList.count true < R) :
    groupedScanAnswerEquiv (2 * R) blockSize bits ∈
      emptyBlockUpperTailEvent (2 * R) blockSize R := by
  change R ≤ emptyBlockCount
    (groupedScanAnswerEquiv (2 * R) blockSize bits)
  have hsupply := groups_sub_emptyBlockCount_le_trueBoardCount
    (2 * R) blockSize (groupedScanAnswerEquiv (2 * R) blockSize bits)
  rw [trueBoardCount_groupedScanAnswerEquiv] at hsupply
  have hemptyLe : emptyBlockCount
      (groupedScanAnswerEquiv (2 * R) blockSize bits) ≤ 2 * R := by
    unfold emptyBlockCount
    calc
      ((Finset.univ : Finset (Fin (2 * R))).filter fun i ↦
          EmptyBlock (groupedScanAnswerEquiv (2 * R) blockSize bits) i).card ≤
          (Finset.univ : Finset (Fin (2 * R))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 * R := by simp
  omega

/-- Hence a grouped scan has fewer than `R` positives with mass at most
`2⁻⁶³` at every density in the bucket. -/
theorem groupedScan_fewTrue_weight_le
    (a R : ℕ) (ha : 2 ≤ a) (hR : 0 < R)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ bits : List.Vector Bool
        (groupedScanAnswerCount (2 * R) (slackBlockSize a)),
      if bits.toList.count true < R then
        (bits.toList.map (bernoulliWeight p)).prod else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  calc
    _ ≤ ∑ bits : List.Vector Bool
        (groupedScanAnswerCount (2 * R) (slackBlockSize a)),
      if groupedScanAnswerEquiv (2 * R) (slackBlockSize a) bits ∈
          emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R then
        (bits.toList.map (bernoulliWeight p)).prod else 0 := by
      apply Finset.sum_le_sum
      intro bits _hbits
      by_cases hfew : bits.toList.count true < R
      · rw [if_pos hfew, if_pos
          (groupedScan_fewTrue_mem_emptyBlockUpperTail R
            (slackBlockSize a) bits hfew)]
      · simp [hfew]
    _ = finiteBoardMass (bernoulliWeight p)
        (emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R) := by
      symm
      unfold finiteBoardMass
      apply Fintype.sum_equiv
        (groupedScanAnswerEquiv (2 * R) (slackBlockSize a)).symm
      intro board
      by_cases hbad : board ∈
          emptyBlockUpperTailEvent (2 * R) (slackBlockSize a) R
      · simp [hbad, groupedScanAnswerEquiv_weight]
      · simp [hbad]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ 63 :=
      emptyBlockHalfTail_le a R ha hR p hp hdensity

/-! ### Raw star answers imply allocator reservoir readiness -/

/-- Replaying an older answer suffix always produces a sublist of the
transcript obtained after prepending further (newer) answers. -/
theorem replay_suffix_sublist {Q : Type*} (strategy : Strategy Q)
    (newer older : List Bool) :
    (replay strategy older).Sublist (replay strategy (newer ++ older)) := by
  induction newer with
  | nil => simp
  | cons bit tail ih =>
      rw [List.cons_append, replay_cons]
      exact ih.trans (List.sublist_cons_self _ _)

/-- Exact coordinate formula for newest-first replay: entry `j` uses the
answer at `j`, while its query is chosen from the transcript generated by
the strictly older suffix. -/
theorem replay_getElem_eq_query_on_drop {Q : Type*}
    (strategy : Strategy Q) (bits : List Bool)
    (j : ℕ) (hj : j < bits.length) :
    (replay strategy bits)[j]'(by simpa using hj) =
      (strategy (replay strategy (bits.drop (j + 1))), bits[j]'hj) := by
  induction bits generalizing j with
  | nil => simp at hj
  | cons bit tail ih =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [replay_cons, List.getElem_cons_succ]
          have hjTail : j < tail.length := by simpa using hj
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using ih j hjTail

/-- In particular, the replay entry at any valid newest-first coordinate is
literally present in the completed transcript. -/
theorem replay_query_on_drop_mem {Q : Type*}
    (strategy : Strategy Q) (bits : List Bool)
    (j : ℕ) (hj : j < bits.length) :
    (strategy (replay strategy (bits.drop (j + 1))), bits[j]'hj) ∈
      replay strategy bits := by
  rw [← replay_getElem_eq_query_on_drop strategy bits j hj]
  exact List.getElem_mem (by simpa using hj)

/-- Final-vector schedule for the initial centre-star phase. -/
def slackStarFinalSchedule (a : ℕ) (ha : 1 ≤ a)
    (j : Fin (slackStarQueries a)) : Query (slackQueryBudget a) :=
  s(slackCenter a ha, slackStarVertex a ha (Fin.rev j))

noncomputable def slackStarContinuation (a : ℕ) (ha : 1 ≤ a) :
    Strategy (Query (slackQueryBudget a)) :=
  BaselineStrategy.reverseScheduleStrategy (slackStarQueries a)
    (slackStarFinalSchedule a ha) s(slackCenter a ha, slackCenter a ha)

/-- On every short star-only answer list, the proposed adaptive strategy is
exactly the static centre-star schedule. -/
theorem replay_proposedSlackStrategy_star_eq
    (a : ℕ) (ha : 1 ≤ a) (starBits : List Bool)
    (hlen : starBits.length ≤ slackStarQueries a) :
    replay (proposedSlackStrategy a ha) starBits =
      replay (slackStarContinuation a ha) starBits := by
  induction starBits with
  | nil => rfl
  | cons bit tail ih =>
      have htail : tail.length < slackStarQueries a := by simpa using hlen
      rw [replay_cons, replay_cons, ih (Nat.le_of_lt htail)]
      rw [show proposedSlackStrategy a ha
          (replay (slackStarContinuation a ha) tail) =
          s(slackCenter a ha,
            slackStarVertex a ha
              ⟨(replay (slackStarContinuation a ha) tail).length,
                by simpa using htail⟩) by
        simp [proposedSlackStrategy, htail]]
      have hReplayLen :
          (replay (slackStarContinuation a ha) tail).length <
            slackStarQueries a := by simpa using htail
      rw [show slackStarContinuation a ha
          (replay (slackStarContinuation a ha) tail) =
          slackStarFinalSchedule a ha
            (Fin.rev ⟨(replay (slackStarContinuation a ha) tail).length,
              hReplayLen⟩) by
        exact BaselineStrategy.reverseScheduleStrategy_of_length_lt
          (slackStarQueries a) (slackStarFinalSchedule a ha)
          s(slackCenter a ha, slackCenter a ha) _ hReplayLen]
      congr 3
      simp [slackStarFinalSchedule]

/-- The initial centre-star segment is legal on every complete answer path.
This supplies the base case for the later adaptive branch-path legality
induction. -/
theorem proposedPathLegal_star
    (a : ℕ) (ha : 1 ≤ a)
    (star : List.Vector Bool (slackStarQueries a)) :
    ProposedPathLegal (proposedSlackStrategy a ha) star.toList := by
  have hscheduleInjective : Function.Injective (slackStarFinalSchedule a ha) := by
    intro i j hij
    have hcenterStar (k : Fin (slackStarQueries a)) :
        slackCenter a ha ≠ slackStarVertex a ha (Fin.rev k) :=
      slackCenter_ne_starVertex a ha (Fin.rev k)
    simp only [slackStarFinalSchedule, Sym2.eq_iff] at hij
    rcases hij with hij | hij
    · exact Fin.rev_injective
        (slackStarVertex_injective a ha hij.2)
    · exact False.elim ((hcenterStar j) hij.1)
  have hfresh : FreshPath (slackStarContinuation a ha) star.toList :=
    BaselineStrategy.reverseScheduleStrategy_fresh
      (slackStarQueries a) (slackStarFinalSchedule a ha)
      s(slackCenter a ha, slackCenter a ha) hscheduleInjective star
  apply proposedPathLegal_of_replay_nodup_nonloop
  · rw [replay_proposedSlackStrategy_star_eq a ha star.toList (by simp)]
    exact hfresh
  · intro q hq
    rw [replay_proposedSlackStrategy_star_eq a ha star.toList (by simp)] at hq
    have hstarList : star.toList = List.ofFn star.get := by
      rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
    rw [hstarList] at hq
    unfold slackStarContinuation at hq
    rw [BaselineStrategy.replay_reverseSchedule_ofFn] at hq
    simp only [queries, List.map_ofFn, Function.comp_apply] at hq
    obtain ⟨i, hi⟩ := (List.mem_ofFn' _ _).mp hq
    subst q
    simpa [slackStarFinalSchedule, Sym2.mk_isDiag_iff] using
      slackCenter_ne_starVertex a ha (Fin.rev i)

/-- Every raw positive star bit is present at the corresponding reversed
star index in the proposed replay. -/
theorem slackStarAnswer_mem_replay
    (a : ℕ) (ha : 1 ≤ a)
    (starBits : List.Vector Bool (slackStarQueries a))
    (j : Fin (slackStarQueries a)) :
    (s(slackCenter a ha, slackStarVertex a ha (Fin.rev j)),
      starBits.get j) ∈
      replay (proposedSlackStrategy a ha) starBits.toList := by
  rw [replay_proposedSlackStrategy_star_eq a ha starBits.toList (by simp)]
  exact BaselineStrategy.schedule_get_mem_replay
    (slackStarQueries a) (slackStarFinalSchedule a ha)
    s(slackCenter a ha, slackCenter a ha) starBits j

/-- Positive raw star answers inject into the allocator's list of positive
star indices, even after arbitrary newer answers have been replayed. -/
theorem trueStarCount_le_positiveStarIndices_length
    (a : ℕ) (ha : 1 ≤ a)
    (newer : List Bool)
    (starBits : List.Vector Bool (slackStarQueries a)) :
    starBits.toList.count true ≤
      (positiveStarIndices a ha
        (replay (proposedSlackStrategy a ha)
          (newer ++ starBits.toList))).length := by
  classical
  let support := trueSupport starBits
  let image : Finset (Fin (slackStarQueries a)) := support.image Fin.rev
  let positives := positiveStarIndices a ha
    (replay (proposedSlackStrategy a ha) (newer ++ starBits.toList))
  have hsubReplay := replay_suffix_sublist (proposedSlackStrategy a ha)
    newer starBits.toList
  have himage : image ⊆ positives.toFinset := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    rw [List.mem_toFinset, mem_positiveStarIndices_iff]
    apply hsubReplay.subset
    have hjtrue : starBits.get j = true := (mem_trueSupport starBits j).mp hj
    simpa [hjtrue] using slackStarAnswer_mem_replay a ha starBits j
  have hcardImage := Finset.card_image_of_injective support
    (fun _ _ h ↦ Fin.rev_injective h)
  have hcardPos := List.toFinset_card_of_nodup
    (positiveStarIndices_nodup a ha
      (replay (proposedSlackStrategy a ha) (newer ++ starBits.toList)))
  calc
    starBits.toList.count true = support.card := (card_trueSupport starBits).symm
    _ = image.card := hcardImage.symm
    _ ≤ positives.toFinset.card := Finset.card_le_card himage
    _ = positives.length := hcardPos

def slackBranchPhaseQueries (a : ℕ) : ℕ :=
  slackAttemptCount a * slackBranchScan a

/-- Newest-first branch phase inside a complete pre-fill vector. -/
def slackBaseBranchAnswerVector (a : ℕ)
    (base : List.Vector Bool (slackFillStart a)) :
    List.Vector Bool (slackBranchPhaseQueries a) :=
  ⟨base.toList.take (slackBranchPhaseQueries a), by
    rw [List.length_take, List.Vector.toList_length]
    unfold slackFillStart slackBranchPhaseQueries
    rw [Nat.min_eq_left]
    omega⟩

/-- Oldest centre-star phase inside a complete pre-fill vector. -/
def slackBaseStarAnswerVector (a : ℕ)
    (base : List.Vector Bool (slackFillStart a)) :
    List.Vector Bool (slackStarQueries a) :=
  ⟨base.toList.drop (slackBranchPhaseQueries a), by
    simp only [List.length_drop, List.Vector.toList_length]
    unfold slackFillStart slackBranchPhaseQueries
    omega⟩

theorem slackBase_branch_star_decomposition (a : ℕ)
    (base : List.Vector Bool (slackFillStart a)) :
    (slackBaseBranchAnswerVector a base).toList ++
      (slackBaseStarAnswerVector a base).toList = base.toList := by
  exact List.take_append_drop (slackBranchPhaseQueries a) base.toList

/-- A raw supply of enough positive star answers is already the exact
`reservoir_ready` field required by the concrete allocator certificate. -/
theorem reservoir_ready_of_baseStar_trueCount
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (htrue : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true) :
    slackReservoirSize a ≤
      (positiveStarIndices a ha
        (replay (proposedSlackStrategy a ha) base.toList)).length := by
  rw [← slackBase_branch_star_decomposition a base]
  exact htrue.trans (trueStarCount_le_positiveStarIndices_length a ha
    (slackBaseBranchAnswerVector a base).toList
    (slackBaseStarAnswerVector a base))

theorem slackReservoirSize_pos (a : ℕ) (ha : 1 ≤ a) :
    0 < slackReservoirSize a := by
  unfold slackReservoirSize slackBranchScan slackBranchGroups slackBlockSize
  positivity

/-- The raw star phase fails to supply the target reservoir with mass at
most `2⁻⁶³`. -/
theorem slackStar_fewTrue_weight_le
    (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ bits : List.Vector Bool (slackStarQueries a),
      if bits.toList.count true < slackReservoirSize a then
        (bits.toList.map (bernoulliWeight p)).prod else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  simpa only [groupedScanAnswerCount, slackStarQueries] using
    groupedScan_fewTrue_weight_le a (slackReservoirSize a) ha
      (slackReservoirSize_pos a (by omega)) p hp hdensity

/-! ### Canonical product interpretation of all branch scans -/

noncomputable def slackBranchCoordEquiv (a : ℕ) :
    Fin (slackBranchPhaseQueries a) ≃
      Fin (slackAttemptCount a) ×
        (Fin (slackBranchGroups a) × Fin (slackBlockSize a)) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

noncomputable def packSlackBranchAnswers (a : ℕ)
    (bits : List.Vector Bool (slackBranchPhaseQueries a)) :
    Fin (slackAttemptCount a) →
      Board (Fin (slackBranchGroups a) × Fin (slackBlockSize a)) :=
  fun i q ↦ bits.get ((slackBranchCoordEquiv a).symm (i, q))

noncomputable def unpackSlackBranchAnswers (a : ℕ)
    (scans : Fin (slackAttemptCount a) →
      Board (Fin (slackBranchGroups a) × Fin (slackBlockSize a))) :
    List.Vector Bool (slackBranchPhaseQueries a) :=
  List.Vector.ofFn fun j ↦
    let iq := slackBranchCoordEquiv a j
    scans iq.1 iq.2

theorem unpack_pack_slackBranchAnswers (a : ℕ)
    (bits : List.Vector Bool (slackBranchPhaseQueries a)) :
    unpackSlackBranchAnswers a (packSlackBranchAnswers a bits) = bits := by
  apply List.Vector.ext
  intro j
  simp only [unpackSlackBranchAnswers, List.Vector.get_ofFn,
    packSlackBranchAnswers]
  exact congrArg bits.get (Equiv.symm_apply_apply (slackBranchCoordEquiv a) j)

theorem pack_unpack_slackBranchAnswers (a : ℕ)
    (scans : Fin (slackAttemptCount a) →
      Board (Fin (slackBranchGroups a) × Fin (slackBlockSize a))) :
    packSlackBranchAnswers a (unpackSlackBranchAnswers a scans) = scans := by
  funext i q
  simp [packSlackBranchAnswers, unpackSlackBranchAnswers]

noncomputable def slackBranchAnswerEquiv (a : ℕ) :
    List.Vector Bool (slackBranchPhaseQueries a) ≃
      (Fin (slackAttemptCount a) →
        Board (Fin (slackBranchGroups a) × Fin (slackBlockSize a))) where
  toFun := packSlackBranchAnswers a
  invFun := unpackSlackBranchAnswers a
  left_inv := unpack_pack_slackBranchAnswers a
  right_inv := pack_unpack_slackBranchAnswers a

theorem slackBranchAnswerEquiv_weight (p : ℝ≥0∞) (a : ℕ)
    (bits : List.Vector Bool (slackBranchPhaseQueries a)) :
    (bits.toList.map (bernoulliWeight p)).prod =
      outcomeVectorWeight
        (fun scan : Board
            (Fin (slackBranchGroups a) × Fin (slackBlockSize a)) ↦
          boardWeight (bernoulliWeight p) scan)
        (slackBranchAnswerEquiv a bits) := by
  have hlist : bits.toList = List.ofFn bits.get := by
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  simp only [outcomeVectorWeight, boardWeight, slackBranchAnswerEquiv,
    packSlackBranchAnswers]
  rw [hlist, List.map_ofFn, List.prod_ofFn]
  change (∏ j : Fin (slackBranchPhaseQueries a),
      bernoulliWeight p (bits.get j)) =
    ∏ i : Fin (slackAttemptCount a),
      ∏ q : Fin (slackBranchGroups a) × Fin (slackBlockSize a),
        bernoulliWeight p
          (bits.get ((slackBranchCoordEquiv a).symm (i, q)))
  rw [Fintype.prod_equiv (slackBranchCoordEquiv a)
    (fun j : Fin (slackBranchPhaseQueries a) ↦
      bernoulliWeight p (bits.get j))
    (fun iq : Fin (slackAttemptCount a) ×
        (Fin (slackBranchGroups a) × Fin (slackBlockSize a)) ↦
      bernoulliWeight p
        (bits.get ((slackBranchCoordEquiv a).symm iq))) (by
          intro j
          exact congrArg (fun z ↦ bernoulliWeight p (bits.get z))
            (Equiv.symm_apply_apply (slackBranchCoordEquiv a) j).symm)]
  rw [Fintype.prod_prod_type]

def SlackBranchScanBad (a : ℕ)
    (scan : Board (Fin (slackBranchGroups a) × Fin (slackBlockSize a))) :
    Prop :=
  scan ∈ emptyBlockUpperTailEvent
    (slackBranchGroups a) (slackBlockSize a) (slackFillSize a)

def SlackBranchRawReady (a : ℕ)
    (bits : List.Vector Bool (slackBranchPhaseQueries a)) : Prop :=
  badOutcomeCount (SlackBranchScanBad a)
    (slackBranchAnswerEquiv a bits) < slackTrialCount a

/-- Exact answer-vector form of the repeated-scan Markov estimate. -/
theorem slackBranch_not_rawReady_weight_le
    (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ bits : List.Vector Bool (slackBranchPhaseQueries a),
      if ¬SlackBranchRawReady a bits then
        (bits.toList.map (bernoulliWeight p)).prod else 0) ≤
      (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  have htrial : 0 < slackTrialCount a := by
    unfold slackTrialCount K6Upper.momentAmplification
    positivity
  calc
    _ = finiteOutcomeProductMass
        (fun scan : Board
            (Fin (slackBranchGroups a) × Fin (slackBlockSize a)) ↦
          boardWeight (bernoulliWeight p) scan)
        (slackAttemptCount a)
        (badOutcomeUpperTailEvent (SlackBranchScanBad a)
          (slackAttemptCount a) (slackTrialCount a)) := by
      unfold finiteOutcomeProductMass SlackBranchRawReady
      apply Fintype.sum_equiv (slackBranchAnswerEquiv a)
      intro bits
      by_cases hbad : slackTrialCount a ≤ badOutcomeCount
          (SlackBranchScanBad a) (slackBranchAnswerEquiv a bits)
      · simp [hbad, slackBranchAnswerEquiv_weight,
          badOutcomeUpperTailEvent]
      · simp [hbad, slackBranchAnswerEquiv_weight,
          badOutcomeUpperTailEvent]
    _ ≤ (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
      simpa only [slackAttemptCount, slackBranchGroups] using
        repeatedGroupedScanHalfTail_le a (slackTrialCount a) ha htrial
          p hp hdensity

/-! ### Exact base-vector splitting and reservoir failure mass -/

def combineSlackBaseAnswers (a : ℕ)
    (pair : List.Vector Bool (slackBranchPhaseQueries a) ×
      List.Vector Bool (slackStarQueries a)) :
    List.Vector Bool (slackFillStart a) :=
  ⟨pair.1.toList ++ pair.2.toList, by
    simp only [List.length_append, List.Vector.toList_length]
    unfold slackFillStart slackBranchPhaseQueries
    omega⟩

theorem combine_split_slackBaseAnswers (a : ℕ)
    (base : List.Vector Bool (slackFillStart a)) :
    combineSlackBaseAnswers a
      (slackBaseBranchAnswerVector a base,
        slackBaseStarAnswerVector a base) = base := by
  apply List.Vector.eq
  exact slackBase_branch_star_decomposition a base

theorem split_combine_slackBaseAnswers (a : ℕ)
    (pair : List.Vector Bool (slackBranchPhaseQueries a) ×
      List.Vector Bool (slackStarQueries a)) :
    (slackBaseBranchAnswerVector a (combineSlackBaseAnswers a pair),
      slackBaseStarAnswerVector a (combineSlackBaseAnswers a pair)) = pair := by
  rcases pair with ⟨branch, star⟩
  apply Prod.ext
  · apply List.Vector.eq
    change (branch.toList ++ star.toList).take
        (slackBranchPhaseQueries a) = branch.toList
    simpa only [List.Vector.toList_length] using
      (List.take_left (l₁ := branch.toList) (l₂ := star.toList))
  · apply List.Vector.eq
    change (branch.toList ++ star.toList).drop
        (slackBranchPhaseQueries a) = star.toList
    simpa only [List.Vector.toList_length] using
      (List.drop_left (l₁ := branch.toList) (l₂ := star.toList))

def slackBaseAnswerSplitEquiv (a : ℕ) :
    List.Vector Bool (slackFillStart a) ≃
      (List.Vector Bool (slackBranchPhaseQueries a) ×
        List.Vector Bool (slackStarQueries a)) where
  toFun base :=
    (slackBaseBranchAnswerVector a base, slackBaseStarAnswerVector a base)
  invFun := combineSlackBaseAnswers a
  left_inv := combine_split_slackBaseAnswers a
  right_inv := split_combine_slackBaseAnswers a

theorem slackBaseAnswerSplitEquiv_weight (p : ℝ≥0∞) (a : ℕ)
    (base : List.Vector Bool (slackFillStart a)) :
    (base.toList.map (bernoulliWeight p)).prod =
      (((slackBaseAnswerSplitEquiv a base).1.toList.map
        (bernoulliWeight p)).prod) *
      (((slackBaseAnswerSplitEquiv a base).2.toList.map
        (bernoulliWeight p)).prod) := by
  rw [← slackBase_branch_star_decomposition a base,
    List.map_append, List.prod_append]
  rfl

def vectorFunctionEquiv (n : ℕ) :
    List.Vector Bool n ≃ (Fin n → Bool) where
  toFun bits := bits.get
  invFun := List.Vector.ofFn
  left_inv := List.Vector.ofFn_get
  right_inv bits := by funext i; simp

theorem sum_boolVector_weight (p : ℝ≥0∞) (hp : p ≤ 1) (n : ℕ) :
    (∑ bits : List.Vector Bool n,
      (bits.toList.map (bernoulliWeight p)).prod) = 1 := by
  calc
    _ = ∑ assignment : Fin n → Bool,
        ∏ i, bernoulliWeight p (assignment i) := by
      apply Fintype.sum_equiv (vectorFunctionEquiv n)
      intro bits
      have hlist : bits.toList = List.ofFn bits.get := by
        rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
      rw [hlist, List.map_ofFn, List.prod_ofFn]
      rfl
    _ = ∏ _i : Fin n, ∑ bit : Bool, bernoulliWeight p bit := by
      exact (Fintype.prod_sum
        (fun _i : Fin n ↦ fun bit : Bool ↦ bernoulliWeight p bit)).symm
    _ = 1 := by
      have hsum : bernoulliWeight p true + bernoulliWeight p false = 1 := by
        simpa [add_comm] using sum_bernoulliWeight p hp
      simp [hsum]

def SlackBaseReservoirReady (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a)) : Prop :=
  slackReservoirSize a ≤
    (positiveStarIndices a ha
      (replay (proposedSlackStrategy a ha) base.toList)).length

/-- The actual allocator's reservoir-readiness failure has unconditional
mass at most `2⁻⁶³`; there is no semantic readiness hypothesis left here. -/
theorem slackBase_not_reservoirReady_weight_le
    (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ base : List.Vector Bool (slackFillStart a),
      if ¬SlackBaseReservoirReady a (by omega) base then
        (base.toList.map (bernoulliWeight p)).prod else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  calc
    _ ≤ ∑ base : List.Vector Bool (slackFillStart a),
      if (slackBaseStarAnswerVector a base).toList.count true <
          slackReservoirSize a then
        (base.toList.map (bernoulliWeight p)).prod else 0 := by
      apply Finset.sum_le_sum
      intro base _hbase
      by_cases hnot : ¬SlackBaseReservoirReady a (by omega) base
      · rw [if_pos hnot]
        have hfew : (slackBaseStarAnswerVector a base).toList.count true <
            slackReservoirSize a := by
          by_contra h
          apply hnot
          exact reservoir_ready_of_baseStar_trueCount a (by omega) base
            (Nat.le_of_not_gt h)
        rw [if_pos hfew]
      · simp [hnot]
    _ = (∑ branch : List.Vector Bool (slackBranchPhaseQueries a),
          (branch.toList.map (bernoulliWeight p)).prod) *
        (∑ star : List.Vector Bool (slackStarQueries a),
          if star.toList.count true < slackReservoirSize a then
            (star.toList.map (bernoulliWeight p)).prod else 0) := by
      calc
        _ = ∑ pair : List.Vector Bool (slackBranchPhaseQueries a) ×
              List.Vector Bool (slackStarQueries a),
            if pair.2.toList.count true < slackReservoirSize a then
              (pair.1.toList.map (bernoulliWeight p)).prod *
                (pair.2.toList.map (bernoulliWeight p)).prod else 0 := by
          apply Fintype.sum_equiv (slackBaseAnswerSplitEquiv a)
          intro base
          rw [slackBaseAnswerSplitEquiv_weight]
          rfl
        _ = ∑ branch : List.Vector Bool (slackBranchPhaseQueries a),
            ∑ star : List.Vector Bool (slackStarQueries a),
              if star.toList.count true < slackReservoirSize a then
                (branch.toList.map (bernoulliWeight p)).prod *
                  (star.toList.map (bernoulliWeight p)).prod else 0 := by
          rw [Fintype.sum_prod_type]
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro branch _hbranch
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro star _hstar
          by_cases hfew : star.toList.count true < slackReservoirSize a <;>
            simp [hfew]
    _ = ∑ star : List.Vector Bool (slackStarQueries a),
          if star.toList.count true < slackReservoirSize a then
            (star.toList.map (bernoulliWeight p)).prod else 0 := by
      rw [sum_boolVector_weight p hp]
      simp
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ 63 :=
      slackStar_fewTrue_weight_le a ha p hp hdensity

/-- The raw branch-scan readiness failure has the same mass inside the full
pre-fill vector, since the older star segment has total mass one. -/
theorem slackBase_not_rawBranchReady_weight_le
    (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ base : List.Vector Bool (slackFillStart a),
      if ¬SlackBranchRawReady a (slackBaseBranchAnswerVector a base) then
        (base.toList.map (bernoulliWeight p)).prod else 0) ≤
      (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  calc
    _ = (∑ branch : List.Vector Bool (slackBranchPhaseQueries a),
          if ¬SlackBranchRawReady a branch then
            (branch.toList.map (bernoulliWeight p)).prod else 0) *
        (∑ star : List.Vector Bool (slackStarQueries a),
          (star.toList.map (bernoulliWeight p)).prod) := by
      calc
        _ = ∑ pair : List.Vector Bool (slackBranchPhaseQueries a) ×
              List.Vector Bool (slackStarQueries a),
            if ¬SlackBranchRawReady a pair.1 then
              (pair.1.toList.map (bernoulliWeight p)).prod *
                (pair.2.toList.map (bernoulliWeight p)).prod else 0 := by
          apply Fintype.sum_equiv (slackBaseAnswerSplitEquiv a)
          intro base
          rw [slackBaseAnswerSplitEquiv_weight]
          rfl
        _ = ∑ branch : List.Vector Bool (slackBranchPhaseQueries a),
            ∑ star : List.Vector Bool (slackStarQueries a),
              if ¬SlackBranchRawReady a branch then
                (branch.toList.map (bernoulliWeight p)).prod *
                  (star.toList.map (bernoulliWeight p)).prod else 0 := by
          rw [Fintype.sum_prod_type]
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro branch _hbranch
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro star _hstar
          by_cases hbad : ¬SlackBranchRawReady a branch <;> simp [hbad]
    _ = ∑ branch : List.Vector Bool (slackBranchPhaseQueries a),
          if ¬SlackBranchRawReady a branch then
            (branch.toList.map (bernoulliWeight p)).prod else 0 := by
      rw [sum_boolVector_weight p hp]
      simp
    _ ≤ (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 :=
      slackBranch_not_rawReady_weight_le a ha p hp hdensity

def SlackBaseRawGood (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a)) : Prop :=
  SlackBaseReservoirReady a ha base ∧
    SlackBranchRawReady a (slackBaseBranchAnswerVector a base)

/-- Fully explicit union bound for the two pre-fill supply failures. -/
theorem slackBase_not_rawGood_weight_le
    (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ base : List.Vector Bool (slackFillStart a),
      if ¬SlackBaseRawGood a (by omega) base then
        (base.toList.map (bernoulliWeight p)).prod else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 +
        (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  calc
    _ ≤ (∑ base : List.Vector Bool (slackFillStart a),
          if ¬SlackBaseReservoirReady a (by omega) base then
            (base.toList.map (bernoulliWeight p)).prod else 0) +
        (∑ base : List.Vector Bool (slackFillStart a),
          if ¬SlackBranchRawReady a (slackBaseBranchAnswerVector a base) then
            (base.toList.map (bernoulliWeight p)).prod else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro base _hbase
      by_cases hr : SlackBaseReservoirReady a (by omega) base <;>
        by_cases hb : SlackBranchRawReady a
          (slackBaseBranchAnswerVector a base) <;> simp [SlackBaseRawGood, hr, hb]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ 63 +
        (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 :=
      add_le_add
        (slackBase_not_reservoirReady_weight_le a ha p hp hdensity)
        (slackBase_not_rawBranchReady_weight_le a ha p hp hdensity)

/-- Marginalization of an arbitrary event depending only on the raw star
segment of the pre-fill answer vector. -/
theorem slackBase_starEvent_weight_eq
    (a : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1)
    (P : List.Vector Bool (slackStarQueries a) → Prop) [DecidablePred P] :
    (∑ base : List.Vector Bool (slackFillStart a),
      if P (slackBaseStarAnswerVector a base) then
        (base.toList.map (bernoulliWeight p)).prod else 0) =
      ∑ star : List.Vector Bool (slackStarQueries a),
        if P star then (star.toList.map (bernoulliWeight p)).prod else 0 := by
  calc
    _ = (∑ branch : List.Vector Bool (slackBranchPhaseQueries a),
          (branch.toList.map (bernoulliWeight p)).prod) *
        (∑ star : List.Vector Bool (slackStarQueries a),
          if P star then
            (star.toList.map (bernoulliWeight p)).prod else 0) := by
      calc
        _ = ∑ pair : List.Vector Bool (slackBranchPhaseQueries a) ×
              List.Vector Bool (slackStarQueries a),
            if P pair.2 then
              (pair.1.toList.map (bernoulliWeight p)).prod *
                (pair.2.toList.map (bernoulliWeight p)).prod else 0 := by
          apply Fintype.sum_equiv (slackBaseAnswerSplitEquiv a)
          intro base
          rw [slackBaseAnswerSplitEquiv_weight]
          rfl
        _ = ∑ branch : List.Vector Bool (slackBranchPhaseQueries a),
            ∑ star : List.Vector Bool (slackStarQueries a),
              if P star then
                (branch.toList.map (bernoulliWeight p)).prod *
                  (star.toList.map (bernoulliWeight p)).prod else 0 := by
          rw [Fintype.sum_prod_type]
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro branch _hbranch
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro star _hstar
          by_cases hP : P star <;> simp [hP]
    _ = _ := by rw [sum_boolVector_weight p hp]; simp

def SlackBaseSupplyGood (a : ℕ)
    (base : List.Vector Bool (slackFillStart a)) : Prop :=
  slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true ∧
    SlackBranchRawReady a (slackBaseBranchAnswerVector a base)

theorem slackBase_starSupplyFailure_weight_le
    (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ base : List.Vector Bool (slackFillStart a),
      if (slackBaseStarAnswerVector a base).toList.count true <
          slackReservoirSize a then
        (base.toList.map (bernoulliWeight p)).prod else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  rw [slackBase_starEvent_weight_eq a p hp
    (fun star ↦ star.toList.count true < slackReservoirSize a)]
  exact slackStar_fewTrue_weight_le a ha p hp hdensity

/-- The exact raw supply event requested by the deterministic
selector-stability proof fails with mass at most `3·2⁻⁶³`. -/
theorem slackBase_not_supplyGood_weight_le
    (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (∑ base : List.Vector Bool (slackFillStart a),
      if ¬SlackBaseSupplyGood a base then
        (base.toList.map (bernoulliWeight p)).prod else 0) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 63 +
        (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 := by
  calc
    _ ≤ (∑ base : List.Vector Bool (slackFillStart a),
          if (slackBaseStarAnswerVector a base).toList.count true <
              slackReservoirSize a then
            (base.toList.map (bernoulliWeight p)).prod else 0) +
        (∑ base : List.Vector Bool (slackFillStart a),
          if ¬SlackBranchRawReady a (slackBaseBranchAnswerVector a base) then
            (base.toList.map (bernoulliWeight p)).prod else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro base _hbase
      by_cases hs : slackReservoirSize a ≤
          (slackBaseStarAnswerVector a base).toList.count true
      · by_cases hb : SlackBranchRawReady a
            (slackBaseBranchAnswerVector a base) <;>
          simp [SlackBaseSupplyGood, hs, hb]
      · have hsfew : (slackBaseStarAnswerVector a base).toList.count true <
            slackReservoirSize a := Nat.lt_of_not_ge hs
        by_cases hb : SlackBranchRawReady a
            (slackBaseBranchAnswerVector a base) <;>
          simp [SlackBaseSupplyGood, hs, hb, hsfew]
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ 63 +
        (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 :=
      add_le_add
        (slackBase_starSupplyFailure_weight_le a ha p hp hdensity)
        (slackBase_not_rawBranchReady_weight_le a ha p hp hdensity)

/-! ### Generic success compiler from independent fill/prefix events -/

theorem slackFull_baseEvent_weight_eq
    (p : ℝ≥0∞) (hp : p ≤ 1) (a : ℕ)
    (Pbase : List.Vector Bool (slackFillStart a) → Prop)
    [DecidablePred Pbase] :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if Pbase (slackBranchAnswerVector a bits) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      ∑ base : List.Vector Bool (slackFillStart a),
        if Pbase base then
          (base.toList.map (bernoulliWeight p)).prod else 0 := by
  have hsplit := slackAnswerSplit_event_weight_eq p a
    (fun _fill : List.Vector Bool (slackFillQueryCount a) ↦ True) Pbase
  simpa [sum_boolVector_weight p hp] using hsplit

theorem slackFull_fillEvent_weight_eq
    (p : ℝ≥0∞) (hp : p ≤ 1) (a : ℕ)
    (Pfill : List.Vector Bool (slackFillQueryCount a) → Prop)
    [DecidablePred Pfill] :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if Pfill (slackFillAnswerVector a bits) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      ∑ fill : List.Vector Bool (slackFillQueryCount a),
        if Pfill fill then
          (fill.toList.map (bernoulliWeight p)).prod else 0 := by
  have hsplit := slackAnswerSplit_event_weight_eq p a Pfill
    (fun _base : List.Vector Bool (slackFillStart a) ↦ True)
  simpa [sum_boolVector_weight p hp] using hsplit

/-- Union bound for failure of a conjunction of a fill event and a prefix
event, already marginalized to the two independent answer segments. -/
theorem slackFull_not_and_event_weight_le
    (p : ℝ≥0∞) (hp : p ≤ 1) (a : ℕ)
    (Pfill : List.Vector Bool (slackFillQueryCount a) → Prop)
    (Pbase : List.Vector Bool (slackFillStart a) → Prop)
    [DecidablePred Pfill] [DecidablePred Pbase] :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if ¬(Pfill (slackFillAnswerVector a bits) ∧
          Pbase (slackBranchAnswerVector a bits)) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) ≤
      (∑ fill : List.Vector Bool (slackFillQueryCount a),
        if ¬Pfill fill then
          (fill.toList.map (bernoulliWeight p)).prod else 0) +
      (∑ base : List.Vector Bool (slackFillStart a),
        if ¬Pbase base then
          (base.toList.map (bernoulliWeight p)).prod else 0) := by
  calc
    _ ≤ (∑ bits : List.Vector Bool (slackQueryBudget a),
          if ¬Pfill (slackFillAnswerVector a bits) then
            (bits.toList.map (bernoulliWeight p)).prod else 0) +
        (∑ bits : List.Vector Bool (slackQueryBudget a),
          if ¬Pbase (slackBranchAnswerVector a bits) then
            (bits.toList.map (bernoulliWeight p)).prod else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro bits _hbits
      by_cases hf : Pfill (slackFillAnswerVector a bits) <;>
        by_cases hb : Pbase (slackBranchAnswerVector a bits) <;>
        simp [hf, hb]
    _ = _ := by
      rw [slackFull_fillEvent_weight_eq p hp a (fun fill ↦ ¬Pfill fill),
        slackFull_baseEvent_weight_eq p hp a (fun base ↦ ¬Pbase base)]

/-- In a normalized Boolean product, any event whose complement has mass at
most one half itself has mass at least the query-complexity threshold. -/
theorem threshold_le_vectorEventWeight_of_complement_le
    (p : ℝ≥0∞) (hp : p ≤ 1) (n : ℕ)
    (P : List.Vector Bool n → Prop) [DecidablePred P]
    (hbad : (∑ bits : List.Vector Bool n,
      if ¬P bits then (bits.toList.map (bernoulliWeight p)).prod else 0) ≤
        threshold) :
    threshold ≤ ∑ bits : List.Vector Bool n,
      if P bits then (bits.toList.map (bernoulliWeight p)).prod else 0 := by
  let good : ℝ≥0∞ := ∑ bits : List.Vector Bool n,
    if P bits then (bits.toList.map (bernoulliWeight p)).prod else 0
  let bad : ℝ≥0∞ := ∑ bits : List.Vector Bool n,
    if ¬P bits then (bits.toList.map (bernoulliWeight p)).prod else 0
  have hpartition : good + bad = 1 := by
    rw [← sum_boolVector_weight p hp n]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bits _hbits
    by_cases hP : P bits <;> simp [good, bad, hP]
  have hthreshold : threshold + threshold = 1 := by
    unfold threshold
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hcancel : bad + threshold ≤ bad + good := by
    calc
      bad + threshold ≤ threshold + threshold := add_le_add_right hbad _
      _ = 1 := hthreshold
      _ = bad + good := by simpa [add_comm] using hpartition.symm
  exact (ENNReal.add_le_add_iff_left (by
    exact ne_top_of_le_ne_top (by simp [threshold] : threshold ≠ ⊤) hbad)).mp hcancel

/-- The two explicit prefix errors consume at most one eighth of total
probability, leaving exactly the slack required by the sharp `3/8` fill
amplification theorem. -/
theorem slackSupplyError_le_one_eighth :
    ((2 : ℝ≥0∞)⁻¹) ^ 63 +
        (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 ≤
      (8 : ℝ≥0∞)⁻¹ := by
  have hpow : ((2 : ℝ≥0∞)⁻¹) ^ 63 ≠ ⊤ :=
    ENNReal.pow_ne_top (by simp)
  have hmul : (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hpow
  apply (ENNReal.toReal_le_toReal
    (ENNReal.add_ne_top.2 ⟨hpow, hmul⟩) (by simp)).mp
  rw [ENNReal.toReal_add hpow hmul]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

@[simp] theorem slackFillQuery_coord_symm
    (a : ℕ) (ha : 1 ≤ a)
    (base : Transcript (Query (slackQueryBudget a)))
    (i : Fin (slackTrialCount a)) (q : OffDiagTrialQuery a) :
    slackFillQuery a ha base ((slackFillCoordEquiv a).symm (i, q)) =
      Sym2.map (selectedFillVertex a ha base i) (q : Sym2 (TrialVertex a)) := by
  simp [slackFillQuery]

/-- No semantic coupling premise is needed for fill answers: every entry of
every canonical fill board is literally present in the actual replay. -/
theorem slackFillBoards_answer_mem_replay
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (i : Fin (slackTrialCount a)) (q : OffDiagTrialQuery a) :
    (Sym2.map (selectedFillVertex a ha
        (slackBranchPrefix a
          (replay (proposedSlackStrategy a ha) bits.toList)) i)
      (q : Sym2 (TrialVertex a)), slackFillBoards a bits i q) ∈
        replay (proposedSlackStrategy a ha) bits.toList := by
  let fillBits := slackFillAnswerVector a bits
  let baseBits := slackBranchAnswerList a bits
  let base := replay (proposedSlackStrategy a ha) baseBits
  let fill := replay (slackFillContinuation a ha base) fillBits.toList
  let j : Fin (slackFillQueryCount a) :=
    (slackFillCoordEquiv a).symm (i, q)
  have hbaseBits : baseBits.length = slackFillStart a := by
    exact slackBranchAnswerList_length a bits
  have hdecomp : fillBits.toList ++ baseBits = bits.toList := by
    exact slackFill_branch_answer_decomposition a bits
  have hrep := replay_proposedSlackStrategy_fill_append a ha
    baseBits fillBits.toList hbaseBits (by simp [fillBits])
  rw [hdecomp] at hrep
  have hmem : (slackFillQuery a ha base j, fillBits.get j) ∈ fill := by
    exact slackFillQuery_get_mem_replay a ha base fillBits j
  have hprefix : slackBranchPrefix a
      (replay (proposedSlackStrategy a ha) bits.toList) = base := by
    exact slackBranchPrefix_replay_eq a ha bits
  rw [hprefix]
  rw [hrep]
  apply List.mem_append_left
  rw [← slackFillQuery_coord_symm a ha base i q]
  exact hmem

/-- The actual admissible slack strategy. -/
noncomputable def slackStrategy (a : ℕ) (ha : 1 ≤ a) :
    K6Strategy (slackQueryBudget a) :=
  legalizeStrategy (slackQueryBudget_pos a ha) (proposedSlackStrategy a ha)

theorem slackStrategy_admissible (a : ℕ) (ha : 1 ≤ a) :
    Admissible (slackStrategy a ha) :=
  legalizeStrategy_admissible (slackQueryBudget_pos a ha)
    (proposedSlackStrategy a ha)

@[simp] theorem proposedSlackStrategy_star (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hstar : h.length < slackStarQueries a) :
    proposedSlackStrategy a ha h =
      s(slackCenter a ha, slackStarVertex a ha ⟨h.length, hstar⟩) := by
  simp [proposedSlackStrategy, hstar]

/-- Concrete path event used by the probability layer: the proposed program
is legal and its completed transcript carries the exact embedded family of
amplified off-diagonal trial boards.  This is strictly stronger data than
`answerVectorSucceeds`; no success probability is assumed in the definition.
-/
def SlackCoupledPath (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a)) : Prop :=
  ProposedPathLegal (proposedSlackStrategy a ha) bits.toList ∧
    ∃ boards : Fin (slackTrialCount a) → Board (OffDiagTrialQuery a),
      ∃ family : EmbeddedTrialFamily
          (replay (proposedSlackStrategy a ha) bits.toList) boards,
        ∃ i, offDiagTrialSucceeds a (boards i)

theorem answerVectorSucceeds_slackStrategy_of_coupledPath
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (hgood : SlackCoupledPath a ha bits) :
    answerVectorSucceeds (slackStrategy a ha) bits := by
  rcases hgood with ⟨hlegal, boards, family, htrial⟩
  apply answerVectorSucceeds_legalizeStrategy_of_proposed
    (slackQueryBudget_pos a ha) (proposedSlackStrategy a ha) bits hlegal
  exact family.transcriptSucceeds_of_exists htrial

/-- Exact conditional `Achievable` bridge for the concrete strategy.  The
remaining upper-bound problem is now solely the displayed finite Bernoulli
mass inequality for `SlackCoupledPath`. -/
theorem achievable_slack_of_coupledPath_mass
    (a : ℕ) (ha : 1 ≤ a) (p : ℝ≥0∞) (hp : p ≤ 1)
    (hmass : threshold ≤
      ∑ bits : List.Vector Bool (slackQueryBudget a),
        if SlackCoupledPath a ha bits then
          (bits.toList.map (bernoulliWeight p)).prod else 0) :
    Achievable p (slackQueryBudget a) := by
  refine ⟨hp, slackStrategy a ha, slackStrategy_admissible a ha, ?_⟩
  rw [successProbability_eq_answer_sum p hp _ (slackStrategy a ha)
    (slackStrategy_admissible a ha).1]
  exact hmass.trans (Finset.sum_le_sum fun bits _ ↦ by
    by_cases hgood : SlackCoupledPath a ha bits
    · have hs := answerVectorSucceeds_slackStrategy_of_coupledPath
        a ha bits hgood
      simp [hgood, hs]
    · simp [hgood])

/-! ### A concrete good-path certificate for the implemented allocator -/

/-- All data in this certificate are expressed using the actual deterministic
selectors above.  Thus the probability layer need not guess embeddings: it
only proves that the selected reservoir and branch lists are long enough,
that their deterministic disjointness invariants hold, and that the final
fill answers contain a successful trial. -/
structure ConcreteSlackPathData (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a)) where
  legal : ProposedPathLegal (proposedSlackStrategy a ha) bits.toList
  reservoir_ready : slackReservoirSize a ≤
    (positiveStarIndices a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList))).length
  branch_ready : slackTrialCount a ≤
    (successfulBranchFills a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList))).length
  trial_success : ∃ i, offDiagTrialSucceeds a (slackFillBoards a bits i)

/-- The concrete selected vertices and answers assemble into the generic
embedded-trial family used by the deterministic `K₆` correctness theorem. -/
def ConcreteSlackPathData.embeddedTrialFamily
    {a : ℕ} {ha : 1 ≤ a}
    {bits : List.Vector Bool (slackQueryBudget a)}
    (d : ConcreteSlackPathData a ha bits) :
    EmbeddedTrialFamily
      (replay (proposedSlackStrategy a ha) bits.toList)
      (slackFillBoards a bits) where
  embed i :=
    { toFun := selectedFillVertex a ha
        (slackBranchPrefix a
          (replay (proposedSlackStrategy a ha) bits.toList)) i
      inj' := by
        intro x y hxy
        have hp := selectedFillVertex_pair_injective a ha
          (slackBranchPrefix a
            (replay (proposedSlackStrategy a ha) bits.toList)) d.branch_ready
          (a₁ := (i, x)) (a₂ := (i, y)) hxy
        exact congrArg Prod.snd hp }
  center _ := slackCenter a ha
  root i := selectedFillRoot a ha
    (slackBranchPrefix a
      (replay (proposedSlackStrategy a ha) bits.toList)) i
  center_ne_root := by
    intro i
    exact selectedRoot_center_ne_of_ready a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList)) d.reservoir_ready
      (selectedFillAttempt a ha
        (slackBranchPrefix a
          (replay (proposedSlackStrategy a ha) bits.toList)) i)
      (selectedFillAttempt_lt_of_ready a ha
        (slackBranchPrefix a
          (replay (proposedSlackStrategy a ha) bits.toList)) d.branch_ready i)
  center_ne_fill := by
    intro i x
    exact selectedFillVertex_center_ne_of_ready a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList)) d.branch_ready i x
  root_ne_fill := by
    intro i x
    exact selectedRoot_ne_selectedFillVertex_of_ready a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList))
      d.reservoir_ready d.branch_ready
      (selectedFillAttempt a ha
        (slackBranchPrefix a
          (replay (proposedSlackStrategy a ha) bits.toList)) i)
      (selectedFillAttempt_lt_of_ready a ha
        (slackBranchPrefix a
          (replay (proposedSlackStrategy a ha) bits.toList)) d.branch_ready i) i x
  center_root_positive := by
    intro i
    apply (slackBranchPrefix_sublist a
      (replay (proposedSlackStrategy a ha) bits.toList)).subset
    exact selectedRoot_center_positive_of_ready a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList)) d.reservoir_ready
      (selectedFillAttempt a ha (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList)) i)
      (selectedFillAttempt_lt_of_ready a ha (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList)) d.branch_ready i)
  center_fill_positive := by
    intro i x
    apply (slackBranchPrefix_sublist a
      (replay (proposedSlackStrategy a ha) bits.toList)).subset
    exact selectedFillVertex_center_positive_of_ready a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList)) d.branch_ready i x
  root_fill_positive := by
    intro i x
    apply (slackBranchPrefix_sublist a
      (replay (proposedSlackStrategy a ha) bits.toList)).subset
    exact selectedFillRoot_fill_positive_of_ready a ha
      (slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList)) d.branch_ready i x
  fill_answers := slackFillBoards_answer_mem_replay a ha bits

/-- Concrete good-path predicate for the implemented strategy. -/
def ConcreteSlackCoupledPath (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a)) : Prop :=
  Nonempty (ConcreteSlackPathData a ha bits)

theorem answerVectorSucceeds_slackStrategy_of_concretePath
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (hgood : ConcreteSlackCoupledPath a ha bits) :
    answerVectorSucceeds (slackStrategy a ha) bits := by
  obtain ⟨d⟩ := hgood
  apply answerVectorSucceeds_legalizeStrategy_of_proposed
    (slackQueryBudget_pos a ha) (proposedSlackStrategy a ha) bits d.legal
  exact d.embeddedTrialFamily.transcriptSucceeds_of_exists d.trial_success

/-- `Achievable` compiler whose sole premise is the finite Bernoulli mass of
the concrete allocator certificate. -/
theorem achievable_slack_of_concretePath_mass
    (a : ℕ) (ha : 1 ≤ a) (p : ℝ≥0∞) (hp : p ≤ 1)
    (hmass : threshold ≤
      ∑ bits : List.Vector Bool (slackQueryBudget a),
        if ConcreteSlackCoupledPath a ha bits then
          (bits.toList.map (bernoulliWeight p)).prod else 0) :
    Achievable p (slackQueryBudget a) := by
  refine ⟨hp, slackStrategy a ha, slackStrategy_admissible a ha, ?_⟩
  rw [successProbability_eq_answer_sum p hp _ (slackStrategy a ha)
    (slackStrategy_admissible a ha).1]
  exact hmass.trans (Finset.sum_le_sum fun bits _ ↦ by
    by_cases hgood : ConcreteSlackCoupledPath a ha bits
    · have hs := answerVectorSucceeds_slackStrategy_of_concretePath
        a ha bits hgood
      simp [hgood, hs]
    · simp [hgood])

end
end UpperStrategy
end OnlineRamsey
