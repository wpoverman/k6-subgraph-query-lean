import OnlineRamsey.UpperStrategy

/-!
# Monotonicity of the finite query budget

An admissible strategy on the canonical `n`-query board can be run, without
changing its first `n` answer paths, on every larger canonical board.  We
embed the old vertices into the new vertex set, replay the old strategy from
the answer history, and use `UpperStrategy.legalizeStrategy` only outside the
embedded legal paths.  The resulting construction proves that
`QueryComplexity.Achievable p n` is monotone in the query budget.
-/

namespace OnlineRamsey
namespace BudgetMonotonicity

open scoped ENNReal
open QueryComplexity UpperStrategy

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-! ## Embedding the smaller canonical board -/

/-- The initial-segment embedding from the smaller canonical vertex set into
the larger one. -/
def vertexEmbedding {n N : ℕ} (hnN : n ≤ N) : Vertex n ↪ Vertex N where
  toFun v := ⟨v.val, by
    change v.val < 2 * N
    have hv : v.val < 2 * n := v.isLt
    omega⟩
  inj' := by
    intro u v huv
    exact Fin.ext (congrArg (fun w : Vertex N ↦ w.val) huv)

/-- The induced injection on unordered query coordinates. -/
def queryEmbedding {n N : ℕ} (hnN : n ≤ N) : Query n ↪ Query N :=
  (vertexEmbedding hnN).sym2Map

@[simp] theorem queryEmbedding_apply_pair {n N : ℕ} (hnN : n ≤ N)
    (u v : Vertex n) :
    queryEmbedding hnN s(u, v) =
      s(vertexEmbedding hnN u, vertexEmbedding hnN v) := by
  simp [queryEmbedding, Function.Embedding.sym2Map_apply]

theorem queryEmbedding_not_diag {n N : ℕ} (hnN : n ≤ N)
    {q : Query n} (hq : ¬q.IsDiag) :
    ¬(queryEmbedding hnN q).IsDiag := by
  simpa [queryEmbedding, Function.Embedding.sym2Map_apply,
    Sym2.isDiag_map (vertexEmbedding hnN).injective] using hq

/-- Pointwise embedding of a transcript, preserving all answers. -/
def embedTranscript {n N : ℕ} (hnN : n ≤ N)
    (h : Transcript (Query n)) : Transcript (Query N) :=
  h.map fun entry ↦ (queryEmbedding hnN entry.1, entry.2)

@[simp] theorem embedTranscript_nil {n N : ℕ} (hnN : n ≤ N) :
    embedTranscript hnN [] = [] := rfl

@[simp] theorem embedTranscript_cons {n N : ℕ} (hnN : n ≤ N)
    (entry : Query n × Bool) (h : Transcript (Query n)) :
    embedTranscript hnN (entry :: h) =
      (queryEmbedding hnN entry.1, entry.2) :: embedTranscript hnN h := rfl

@[simp] theorem answers_embedTranscript {n N : ℕ} (hnN : n ≤ N)
    (h : Transcript (Query n)) :
    answers (embedTranscript hnN h) = answers h := by
  simp [embedTranscript, answers]

@[simp] theorem queries_embedTranscript {n N : ℕ} (hnN : n ≤ N)
    (h : Transcript (Query n)) :
    queries (embedTranscript hnN h) = (queries h).map (queryEmbedding hnN) := by
  simp [embedTranscript, queries, Function.comp_def]

theorem embedTranscript_queries_nodup {n N : ℕ} (hnN : n ≤ N)
    {h : Transcript (Query n)} (hfresh : (queries h).Nodup) :
    (queries (embedTranscript hnN h)).Nodup := by
  rw [queries_embedTranscript]
  exact hfresh.map (queryEmbedding hnN).injective

theorem embedTranscript_queries_nonloop {n N : ℕ} (hnN : n ≤ N)
    {h : Transcript (Query n)}
    (hnonloop : ∀ q ∈ queries h, ¬q.IsDiag) :
    ∀ q ∈ queries (embedTranscript hnN h), ¬q.IsDiag := by
  intro q hq
  rw [queries_embedTranscript] at hq
  rcases List.mem_map.mp hq with ⟨q', hq', rfl⟩
  exact queryEmbedding_not_diag hnN (hnonloop q' hq')

/-! ## A path-exact lifted strategy -/

/-- Proposed strategy on the larger board.  Only the answer history is fed
back to the smaller strategy; its next query is then embedded. -/
def proposedLift {n N : ℕ} (hnN : n ≤ N) (strategy : K6Strategy n) :
    K6Strategy N := fun h ↦
  queryEmbedding hnN (strategy (replay strategy (answers h)))

/-- Every prescribed answer path of the proposed lift is exactly the
pointwise embedding of the corresponding smaller replay. -/
theorem replay_proposedLift {n N : ℕ} (hnN : n ≤ N)
    (strategy : K6Strategy n) (bits : List Bool) :
    replay (proposedLift hnN strategy) bits =
      embedTranscript hnN (replay strategy bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [replay_cons, ih, proposedLift, answers_embedTranscript,
        answers_replay, embedTranscript_cons]

private theorem freshPath_of_append_left
    {Q : Type*} (strategy : Strategy Q) (extension bits : List Bool)
    (hfresh : FreshPath strategy (extension ++ bits)) :
    FreshPath strategy bits := by
  induction extension with
  | nil => simpa using hfresh
  | cons bit extension ih =>
      exact ih (((freshPath_cons strategy bit (extension ++ bits)).mp hfresh).2)

/-- Full-budget freshness implies freshness on every shorter prescribed
answer list. -/
theorem freshPath_of_freshForBudget {n : ℕ}
    (strategy : K6Strategy n) (hfresh : FreshForBudget strategy)
    (bits : List Bool) (hbits : bits.length ≤ n) :
    FreshPath strategy bits := by
  let extension := List.replicate (n - bits.length) false
  let fullList := extension ++ bits
  have hlength : fullList.length = n := by
    simp [fullList, extension]
    omega
  let full : List.Vector Bool n := ⟨fullList, hlength⟩
  apply freshPath_of_append_left strategy extension bits
  change FreshPath strategy full.toList
  exact hfresh full

/-- A nonloop-at-every-reachable-history strategy has only nonloop queries
on every shorter replay. -/
theorem replay_queries_nonloop_of_budget {n : ℕ}
    (strategy : K6Strategy n) (hnonloop : NonloopForBudget strategy)
    (bits : List Bool) (hbits : bits.length ≤ n) :
    ∀ q ∈ queries (replay strategy bits), ¬q.IsDiag := by
  induction bits with
  | nil => simp [queries]
  | cons bit bits ih =>
      simp only [List.length_cons] at hbits
      have htail : bits.length < n := by omega
      intro q hq
      simp only [replay_cons, queries, List.map_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hnonloop _ (by simpa using htail)
      · exact ih (Nat.le_of_lt htail) q hq

/-- The proposed lift is legal along every path of length at most the old
budget. -/
theorem proposedLift_pathLegal {n N : ℕ} (hnN : n ≤ N)
    (strategy : K6Strategy n) (hadm : Admissible strategy)
    (bits : List Bool) (hbits : bits.length ≤ n) :
    ProposedPathLegal (proposedLift hnN strategy) bits := by
  apply proposedPathLegal_of_replay_nodup_nonloop
  · rw [replay_proposedLift]
    exact embedTranscript_queries_nodup hnN
      (freshPath_of_freshForBudget strategy hadm.1 bits hbits)
  · rw [replay_proposedLift]
    exact embedTranscript_queries_nonloop hnN
      (replay_queries_nonloop_of_budget strategy hadm.2 bits hbits)

/-- Any inhabited strategy on the canonical query type has positive budget.
This is used only to supply the harmless fallback branch of legalization. -/
theorem budget_pos_of_strategy {n : ℕ} (strategy : K6Strategy n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  let q := strategy []
  induction q using Sym2.inductionOn with
  | _ u _ => exact Fin.elim0 u

/-- The globally admissible large-board realization of a smaller strategy. -/
def liftStrategy {n N : ℕ} (hnN : n ≤ N) (strategy : K6Strategy n) :
    K6Strategy N :=
  legalizeStrategy (lt_of_lt_of_le (budget_pos_of_strategy strategy) hnN)
    (proposedLift hnN strategy)

theorem liftStrategy_admissible {n N : ℕ} (hnN : n ≤ N)
    (strategy : K6Strategy n) :
    Admissible (liftStrategy hnN strategy) := by
  exact legalizeStrategy_admissible
    (lt_of_lt_of_le (budget_pos_of_strategy strategy) hnN) _

/-- On the old time horizon, legalization never changes the lifted path. -/
theorem replay_liftStrategy {n N : ℕ} (hnN : n ≤ N)
    (strategy : K6Strategy n) (hadm : Admissible strategy)
    (bits : List Bool) (hbits : bits.length ≤ n) :
    replay (liftStrategy hnN strategy) bits =
      embedTranscript hnN (replay strategy bits) := by
  rw [liftStrategy,
    replay_legalizeStrategy_eq_of_proposedPathLegal
      (lt_of_lt_of_le (budget_pos_of_strategy strategy) hnN)
      (proposedLift hnN strategy) bits
      (proposedLift_pathLegal hnN strategy hadm bits hbits)]
  exact replay_proposedLift hnN strategy bits

/-! ## Transporting success and probability -/

/-- A successful smaller transcript remains successful after embedding it in
the larger canonical board. -/
theorem transcriptSucceeds_embed {n N : ℕ} (hnN : n ≤ N)
    {h : Transcript (Query n)} (hsuccess : TranscriptSucceeds h) :
    TranscriptSucceeds (embedTranscript hnN h) := by
  rcases hsuccess with ⟨copy⟩
  let emb := vertexEmbedding hnN
  let hom : positiveGraph h →g positiveGraph (embedTranscript hnN h) :=
    { toFun := emb
      map_rel' := by
        intro u v huv
        rw [positiveGraph_adj] at huv ⊢
        refine ⟨emb.injective.ne huv.1, ?_⟩
        apply List.mem_map.mpr
        refine ⟨(s(u, v), true), huv.2, ?_⟩
        simp [embedTranscript, queryEmbedding_apply_pair, emb] }
  let embeddedCopy : SimpleGraph.Copy (positiveGraph h)
      (positiveGraph (embedTranscript hnN h)) := ⟨hom, emb.injective⟩
  exact ⟨embeddedCopy.comp copy⟩

/-- A shorter run is a suffix of a longer newest-first run. -/
private theorem run_eq_append_of_le {Q : Type*}
    (strategy : Strategy Q) (board : Board Q) {m N : ℕ} (hmN : m ≤ N) :
    ∃ pre : Transcript Q, run strategy board N = pre ++ run strategy board m := by
  induction N, hmN using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ N hmN ih =>
      rcases ih with ⟨pre, hrun⟩
      exact ⟨(strategy (run strategy board N),
        board (strategy (run strategy board N))) :: pre, by
          simp only [run_succ, List.cons_append, hrun]⟩

/-- Success by time `m` implies success at every later horizon. -/
theorem transcriptSucceeds_run_mono {N m : ℕ} (hmN : m ≤ N)
    (strategy : K6Strategy N) (board : Board (Query N))
    (hsuccess : TranscriptSucceeds (run strategy board m)) :
    TranscriptSucceeds (run strategy board N) := by
  rcases run_eq_append_of_le strategy board hmN with ⟨pre, hrun⟩
  apply transcriptSucceeds_mono_of_mem (h := run strategy board m)
      (h' := run strategy board N) _ hsuccess
  intro entry hentry
  rw [hrun]
  exact List.mem_append.mpr (Or.inr hentry)

/-- The mass of the length-`n` success event of a lifted strategy is exactly
the smaller strategy's success probability. -/
theorem lifted_prefix_mass_eq {p : ℝ≥0∞} (hp : p ≤ 1)
    {n N : ℕ} (hnN : n ≤ N) (strategy : K6Strategy n)
    (hadm : Admissible strategy) :
    finiteBoardMass (bernoulliWeight p)
        {board : Board (Query N) |
          answerVectorSucceeds strategy
            (answerVector (liftStrategy hnN strategy) board n)} =
      successProbability p n strategy := by
  rw [finiteProduct_answerVector_event_mass
    (bernoulliWeight p) (sum_bernoulliWeight p hp)
    (liftStrategy hnN strategy) n (answerVectorSucceeds strategy)]
  · symm
    exact successProbability_eq_answer_sum p hp n strategy hadm.1
  · intro bits
    exact freshPath_of_freshForBudget _
      (liftStrategy_admissible hnN strategy).1 bits.toList (by simpa using hnN)

/-- Achievability is monotone under enlargement of the query budget. -/
theorem achievable_mono_budget {p : ℝ≥0∞} {n N : ℕ}
    (hnN : n ≤ N) (hsmall : Achievable p n) : Achievable p N := by
  rcases hsmall with ⟨hp, strategy, hadm, hprob⟩
  refine ⟨hp, liftStrategy hnN strategy,
    liftStrategy_admissible hnN strategy, ?_⟩
  calc
    threshold ≤ successProbability p n strategy := hprob
    _ = finiteBoardMass (bernoulliWeight p)
        {board : Board (Query N) |
          answerVectorSucceeds strategy
            (answerVector (liftStrategy hnN strategy) board n)} :=
      (lifted_prefix_mass_eq hp hnN strategy hadm).symm
    _ ≤ successProbability p N (liftStrategy hnN strategy) := by
      unfold successProbability finiteBoardMass
      apply Finset.sum_le_sum
      intro board _
      by_cases hprefix : answerVectorSucceeds strategy
          (answerVector (liftStrategy hnN strategy) board n)
      · have hsmallReplay : TranscriptSucceeds
            (replay strategy
              (answerVector (liftStrategy hnN strategy) board n).toList) :=
          hprefix
        have hembed : TranscriptSucceeds
            (embedTranscript hnN
              (replay strategy
                (answerVector (liftStrategy hnN strategy) board n).toList)) :=
          transcriptSucceeds_embed hnN hsmallReplay
        have hrunN : TranscriptSucceeds
            (run (liftStrategy hnN strategy) board N) := by
          apply transcriptSucceeds_run_mono hnN
          have hpath := replay_liftStrategy hnN strategy hadm
            (answerVector (liftStrategy hnN strategy) board n).toList (by simp)
          rw [answerVector_toList, replay_answers_run] at hpath
          rw [hpath]
          exact hembed
        have hmem : board ∈ successEvent N (liftStrategy hnN strategy) := hrunN
        simp [hprefix, hmem]
      · simp [hprefix]

end
end BudgetMonotonicity
end OnlineRamsey
