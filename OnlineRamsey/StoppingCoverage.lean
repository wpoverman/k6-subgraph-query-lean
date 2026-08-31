import OnlineRamsey.StoppingHistory

/-!
# Coverage of concrete ordered stopping histories

This file relates the query-time data in `StoppingHistory` to actual prefixes
of an adaptive run.  Under the pathwise no-repeated-query condition, every
completed labelled copy belongs to the concrete completion event indexed by
its uniquely derived relative order and prefix-completion time.
-/

open scoped BigOperators ENNReal

namespace OnlineRamsey
namespace StoppingCoverage

open QueryComplexity LowerAssembly StoppingHistory

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

universe u

theorem sum_event_weight_eq_weight_mul_card
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (weight : Ω → ℝ≥0∞) (event : I → Ω → Prop) :
    (∑ i : I, ∑ ω : Ω, if event i ω then weight ω else 0) =
      ∑ ω : Ω, weight ω *
        (Fintype.card {i : I // event i ω} : ℝ≥0∞) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _hω
  calc
    (∑ i : I, if event i ω then weight ω else 0) =
        (Finset.univ.filter (fun i : I ↦ event i ω)).card * weight ω := by
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul]
    _ = (Fintype.card {i : I // event i ω} : ℝ≥0∞) * weight ω := by
      rw [Fintype.card_subtype]
    _ = weight ω * (Fintype.card {i : I // event i ω} : ℝ≥0∞) := by
      rw [mul_comm]

/-- Exact mass partition for a finite, board-dependent family of objects.
This abstract statement is deliberately what the final assembly should
instantiate: keeping `Order` abstract avoids elaborating the `15!` concrete
permutation enumeration. -/
theorem dependent_fiber_mass_partition
    {Ω Order : Type*} [Fintype Ω] [Fintype Order]
    (Object : Ω → Type*) [∀ ω, Fintype (Object ω)]
    (classify : ∀ ω, Object ω → Order) (weight : Ω → ℝ≥0∞) :
    (∑ ω, weight ω * (Fintype.card (Object ω) : ℝ≥0∞)) =
      ∑ order : Order, ∑ ω,
        weight ω *
          (Fintype.card {x : Object ω // classify ω x = order} : ℝ≥0∞) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _hω
  have h := Fintype.sum_fiberwise (classify ω)
    (fun _x : Object ω ↦ weight ω)
  simpa [nsmul_eq_mul, mul_comm] using h.symm

/-- A small generic wrapper around the cardinality monotonicity theorem.  It
keeps the particular `Fintype` implementation hidden inside
`labelledCopyCount`, which is important for keeping the large `K₆` instance
opaque during later elaboration. -/
theorem labelledCopyCount_le_card_of_embedding
    {V W X : Type*} [Fintype V] [Fintype W] [Fintype X]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (f : SimpleGraph.Copy H G ↪ X) :
    G.labelledCopyCount H ≤ Fintype.card X := by
  unfold SimpleGraph.labelledCopyCount
  exact Fintype.card_le_of_injective f f.injective

/-! ## Exact prefixes of a run -/

variable {Q : Type u}

/-- A shorter run is literally a suffix of a longer newest-first run. -/
theorem run_eq_append_of_le (strategy : Strategy Q) (board : Board Q)
    {m n : ℕ} (hmn : m ≤ n) :
    ∃ pre : Transcript Q,
      run strategy board n = pre ++ run strategy board m ∧
        pre.length = n - m := by
  induction n, hmn using Nat.le_induction with
  | base =>
      exact ⟨[], by simp, by simp⟩
  | succ n hmn ih =>
      rcases ih with ⟨pre, hrun, hlen⟩
      refine ⟨(strategy (run strategy board n),
        board (strategy (run strategy board n))) :: pre, ?_, ?_⟩
      · simp only [run_succ, List.cons_append, hrun]
      · simp only [List.length_cons, hlen]
        omega

/-- Query-list form of `run_eq_append_of_le`. -/
theorem queries_run_eq_append_of_le (strategy : Strategy Q)
    (board : Board Q) {m n : ℕ} (hmn : m ≤ n) :
    ∃ pre : List Q,
      queries (run strategy board n) =
          pre ++ queries (run strategy board m) ∧
        pre.length = n - m := by
  rcases run_eq_append_of_le strategy board hmn with ⟨pre, hrun, hlen⟩
  refine ⟨queries pre, ?_, ?_⟩
  · rw [hrun]
    simp [queries]
  · simpa using hlen

/-- Exact membership criterion for the chronological time obtained by
reversing `idxOf` in a fresh newest-first run. -/
theorem mem_queries_run_iff_queryTime_le [DecidableEq Q]
    (strategy : Strategy Q) (board : Board Q) (N k : ℕ) (q : Q)
    (hk : k ≤ N)
    (hnodup : (queries (run strategy board N)).Nodup)
    (hq : q ∈ queries (run strategy board N)) :
    q ∈ queries (run strategy board k) ↔
      N - (queries (run strategy board N)).idxOf q ≤ k := by
  rcases queries_run_eq_append_of_le strategy board hk with
    ⟨pre, hdecomp, hlen⟩
  have hnappend : (pre ++ queries (run strategy board k)).Nodup := by
    simpa [hdecomp] using hnodup
  constructor
  · intro hqk
    have hqpre : q ∉ pre := by
      intro hqp
      exact (List.nodup_append.mp hnappend).2.2 q hqp q hqk rfl
    rw [hdecomp, List.idxOf_append_of_notMem hqpre]
    have hidx := List.idxOf_le_length
      (l := queries (run strategy board k)) (a := q)
    simp only [length_queries, length_run] at hidx
    omega
  · intro htime
    by_contra hqk
    have hqpre : q ∈ pre := by
      rw [hdecomp, List.mem_append] at hq
      exact hq.resolve_right hqk
    rw [hdecomp, List.idxOf_append_of_mem hqpre] at htime
    have hidx : pre.idxOf q < pre.length :=
      List.idxOf_lt_length_iff.mpr hqpre
    omega

/-- Once a coordinate is known to be queried, consistency turns its board
value into the corresponding transcript entry. -/
theorem pair_mem_run_of_query_mem_of_board_eq [DecidableEq Q]
    (strategy : Strategy Q) (board : Board Q) (k : ℕ)
    (q : Q) (bit : Bool) (hq : q ∈ queries (run strategy board k))
    (hbit : board q = bit) :
    (q, bit) ∈ run strategy board k := by
  rcases List.mem_map.mp hq with ⟨⟨q', bit'⟩, hentry, heq⟩
  change q' = q at heq
  subst q'
  have hconsistent := consistent_run strategy board k (q, bit') hentry
  have : bit' = bit := hconsistent.symm.trans hbit
  subst bit'
  exact hentry

/-- The coordinate at its derived positive time is the head of that run. -/
theorem run_at_queryTime_starts_with [DecidableEq Q]
    (strategy : Strategy Q) (board : Board Q) (N : ℕ)
    (q : Q) (bit : Bool)
    (hnodup : (queries (run strategy board N)).Nodup)
    (hentry : (q, bit) ∈ run strategy board N) :
    let t := N - (queries (run strategy board N)).idxOf q
    ∃ tail, run strategy board t = (q, bit) :: tail := by
  dsimp only
  let t := N - (queries (run strategy board N)).idxOf q
  have hq : q ∈ queries (run strategy board N) :=
    List.mem_map.mpr ⟨(q, bit), hentry, rfl⟩
  have hidx : (queries (run strategy board N)).idxOf q < N := by
    simpa using (List.idxOf_lt_length_iff.mpr hq)
  have htpos : 0 < t := by
    dsimp [t]
    omega
  obtain ⟨k, htk⟩ : ∃ k, t = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero htpos.ne'
  have hkN : k ≤ N := by
    dsimp [t] at *
    omega
  have hnotTail : q ∉ queries (run strategy board k) := by
    rw [mem_queries_run_iff_queryTime_le strategy board N k q hkN hnodup hq]
    dsimp [t] at *
    omega
  have hmemNow : q ∈ queries (run strategy board (k + 1)) := by
    rw [mem_queries_run_iff_queryTime_le strategy board N (k + 1) q
      (by omega) hnodup hq]
    dsimp [t] at *
    omega
  have hhead : strategy (run strategy board k) = q := by
    change q ∈ strategy (run strategy board k) ::
      queries (run strategy board k) at hmemNow
    simp only [List.mem_cons] at hmemNow
    rcases hmemNow with hnow | hpast
    · exact hnow.symm
    · exact (hnotTail hpast).elim
  have hbit : board q = bit :=
    consistent_run strategy board N (q, bit) hentry
  change ∃ tail, run strategy board t = (q, bit) :: tail
  rw [htk]
  refine ⟨run strategy board k, ?_⟩
  simp [run_succ, hhead, hbit]

/-! ## Coverage of a completed copy -/

private theorem copy_queryTime_eq_embeddingQueryTime {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) (i : Fin 15) :
    queryTime c i = embeddingQueryTime h (copyEmbedding c) i := rfl

private theorem copy_relativeOrder_eq_embeddingRelativeOrder {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) :
    relativeOrder c = embeddingRelativeOrder h (copyEmbedding c) := rfl

theorem queries_run_nodup_of_freshForBudget {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    (board : Board (QueryComplexity.Query N)) :
    (queries (run strategy board N)).Nodup := by
  have h := hfresh (answerVector strategy board N)
  change (queries (replay strategy
    (answerVector strategy board N).toList)).Nodup at h
  rw [answerVector_toList, replay_answers_run] at h
  exact h

theorem prefixCompletionTime_le_budget {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (hh : h.length = N)
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h))
    (π : K6EdgeOrder) (r : K6PrefixLength) :
    prefixCompletionTime c π r ≤ N := by
  by_cases hr : 0 < r.val
  · simp only [prefixCompletionTime, hr, dite_true, queryTime]
    rw [hh]
    exact Nat.sub_le _ _
  · simp [prefixCompletionTime, hr]

/-- Every completed copy belongs to the concrete event indexed by its actual
relative edge order and its derived `r`-edge completion time. -/
theorem copy_mem_completionAtEvent {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph (run strategy board N)))
    (r : K6PrefixLength)
    (hnodup : (queries (run strategy board N)).Nodup) :
    board ∈ completionAtEvent strategy (copyEmbedding c) (relativeOrder c) r
      (prefixCompletionTime c (relativeOrder c) r) := by
  let π := relativeOrder c
  let f := copyEmbedding c
  have hcompleted : EmbeddingCompleted (run strategy board N) f := by
    intro i
    exact copyEdge_mem c i
  have hpositive : board ∈ allPositiveOn (remainingEdges f π r) := by
    intro q hq
    rw [remainingEdges, Finset.mem_image] at hq
    rcases hq with ⟨j, _hj, rfl⟩
    have hentry := copyEdge_mem c (π (suffixIndex r j))
    exact consistent_run strategy board N _ hentry
  have horder : embeddingRelativeOrder (run strategy board N) f = π := by
    exact (copy_relativeOrder_eq_embeddingRelativeOrder c).symm
  refine ⟨?_, hpositive, hcompleted, horder⟩
  change prefixAccept f π r
      (run strategy board (prefixCompletionTime c π r)) ∧
    Avoids (run strategy board (prefixCompletionTime c π r))
      (remainingEdges f π r)
  by_cases hr : 0 < r.val
  · let last : Fin 15 := ⟨r.val - 1, by omega⟩
    let t := queryTime c (π last)
    have ht : prefixCompletionTime c π r = t := by
      simp [prefixCompletionTime, hr, t, last]
    have hstart := run_at_queryTime_starts_with strategy board N
      (copyEdge c (π last)) true hnodup (copyEdge_mem c (π last))
    dsimp only at hstart
    have hstart' : ∃ tail,
        run strategy board (queryTime c (π last)) =
          (copyEdge c (π last), true) :: tail := by
      simpa [queryTime] using hstart
    rcases hstart' with ⟨tail, htail⟩
    have htpos : 0 < t := by
      have hmem := copyEdge_mem_queries c (π last)
      have hidx := List.idxOf_lt_length_iff.mpr hmem
      dsimp [t, queryTime]
      simp only [length_queries, length_run] at hidx ⊢
      omega
    have htN : t ≤ N := by
      dsimp [t, queryTime]
      simp only [length_run]
      omega
    have htailEq : tail = run strategy board (t - 1) := by
      change run strategy board t =
        (copyEdge c (π last), true) :: tail at htail
      have hlen := congrArg List.length htail
      have htsucc : t - 1 + 1 = t := by omega
      rw [← htsucc, run_succ] at htail
      simp only [List.cons.injEq] at htail
      exact htail.2.symm
    constructor
    · rw [ht]
      simp only [prefixAccept, hr, dite_true]
      refine ⟨tail, ?_, ?_⟩
      · simpa [copyEdge, f, last] using htail
      · intro j
        let a : Fin 15 := prefixIndex r ⟨j.val, by omega⟩
        have htime : queryTime c (π a) < t := by
          have hab : a < last := by
            apply Fin.mk_lt_mk.mpr
            dsimp [a, last, prefixIndex]
            omega
          exact queryTime_strictMono_relativeOrder c hab
        have hqfull : copyEdge c (π a) ∈
            queries (run strategy board N) := copyEdge_mem_queries c (π a)
        have hmem : copyEdge c (π a) ∈
            queries (run strategy board (t - 1)) := by
          rw [mem_queries_run_iff_queryTime_le strategy board N (t - 1)
            (copyEdge c (π a)) (by omega) hnodup hqfull]
          simpa [queryTime, t] using (show queryTime c (π a) ≤ t - 1 by omega)
        have hboard : board (copyEdge c (π a)) = true :=
          consistent_run strategy board N _ (copyEdge_mem c (π a))
        have hp := pair_mem_run_of_query_mem_of_board_eq strategy board
          (t - 1) (copyEdge c (π a)) true hmem hboard
        rw [htailEq]
        simpa [copyEdge, f, a, prefixIndex]
    · rw [ht]
      intro q hqrun hqrem
      rw [remainingEdges, Finset.mem_image] at hqrem
      rcases hqrem with ⟨j, _hj, rfl⟩
      let a : Fin 15 := suffixIndex r j
      have hlastlt : last < a := by
        apply Fin.mk_lt_mk.mpr
        dsimp [last, a, suffixIndex]
        omega
      have htime : t < queryTime c (π a) :=
        queryTime_strictMono_relativeOrder c hlastlt
      have hqfull : copyEdge c (π a) ∈
          queries (run strategy board N) := copyEdge_mem_queries c (π a)
      have hmemIff := mem_queries_run_iff_queryTime_le strategy board N t
        (copyEdge c (π a)) htN hnodup hqfull
      have hle := hmemIff.mp (by
        simpa [copyEdge, f, a] using hqrun)
      have hle' : queryTime c (π a) ≤ t := by
        simpa [queryTime] using hle
      exact (not_le_of_gt htime hle').elim
  · have hrzero : r.val = 0 := Nat.eq_zero_of_not_pos hr
    have ht : prefixCompletionTime c π r = 0 := by
      simp [prefixCompletionTime, hr]
    rw [ht]
    constructor
    · simp [prefixAccept, hr]
    · intro q hq
      simp [queries] at hq

/-! ## Summing the fixed histories -/

abbrev CompletionHistoryKey (N : ℕ) :=
  (Fin 6 ↪ QueryComplexity.Vertex N) × Fin (N + 1)

def completionEventForKey {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (z : CompletionHistoryKey N) :
    Set (Board (QueryComplexity.Query N)) :=
  completionAtEvent strategy z.1 π r z.2.val

abbrev CompletionHistoryIndex {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    (π : K6EdgeOrder) (r : K6PrefixLength) :=
  {z : CompletionHistoryKey N // board ∈ completionEventForKey strategy π r z}

def completionHistoryCount {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    (π : K6EdgeOrder) (r : K6PrefixLength) : ℕ :=
  Fintype.card (CompletionHistoryIndex strategy board π r)

/-- A completed copy of order `π` maps injectively to its vertex embedding
and uniquely derived prefix-completion time. -/
def orderedCopyToCompletionHistoryIndex {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    (π : K6EdgeOrder) (r : K6PrefixLength)
    (hnodup : (queries (run strategy board N)).Nodup) :
    OrderedCopy (run strategy board N) π ↪
      CompletionHistoryIndex strategy board π r where
  toFun c := by
    let t := prefixCompletionTime c.1 π r
    have ht : t ≤ N := prefixCompletionTime_le_budget
      (length_run strategy board N) c.1 π r
    refine ⟨(copyEmbedding c.1, ⟨t, Nat.lt_succ_of_le ht⟩), ?_⟩
    have hc := copy_mem_completionAtEvent strategy board c.1 r hnodup
    rw [c.2] at hc
    exact hc
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply SimpleGraph.Copy.ext
    intro v
    have hf : copyEmbedding c.1 = copyEmbedding d.1 := by
      have := congrArg
        (fun z : CompletionHistoryIndex strategy board π r ↦ z.1.1) hcd
      exact this
    exact DFunLike.congr_fun hf v

theorem orderedCopyCount_le_completionHistoryCount {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    (π : K6EdgeOrder) (r : K6PrefixLength)
    (hnodup : (queries (run strategy board N)).Nodup) :
    orderedCopyCount (run strategy board N) π ≤
      completionHistoryCount strategy board π r := by
  unfold orderedCopyCount completionHistoryCount
  exact Fintype.card_le_of_injective
    (orderedCopyToCompletionHistoryIndex strategy board π r hnodup)
    (orderedCopyToCompletionHistoryIndex strategy board π r hnodup).injective

/-! ### Global coverage without enumerating the relative orders -/

abbrev ReindexedCompletionHistoryKey (N : ℕ) (Order : Type*) :=
  Order × CompletionHistoryKey N

def reindexedCompletionEventForKey {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    {Order : Type*} (e : Order ≃ K6EdgeOrder)
    (r : Order → K6PrefixLength)
    (z : ReindexedCompletionHistoryKey N Order) :
    Set (Board (QueryComplexity.Query N)) :=
  completionAtEvent strategy z.2.1 (e z.1) (r z.1) z.2.2.val

abbrev ReindexedCompletionHistoryIndex {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    {Order : Type*} (e : Order ≃ K6EdgeOrder)
    (r : Order → K6PrefixLength) :=
  {z : ReindexedCompletionHistoryKey N Order //
    board ∈ reindexedCompletionEventForKey strategy e r z}

def reindexedCompletionHistoryCount {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (r : Order → K6PrefixLength) : ℕ :=
  Fintype.card (ReindexedCompletionHistoryIndex strategy board e r)

/-- Every completed labelled copy maps to the history having its actual
relative order, embedding, and derived prefix-completion time.  This is the
global multiplicity-preserving coverage map; its abstract `Order` argument
avoids constructing the `15!`-element concrete order enumeration. -/
def copyToReindexedCompletionHistoryIndex {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (r : Order → K6PrefixLength)
    (hnodup : (queries (run strategy board N)).Nodup) :
    SimpleGraph.Copy QueryComplexity.K6
        (QueryComplexity.positiveGraph (run strategy board N)) ↪
      ReindexedCompletionHistoryIndex strategy board e r where
  toFun c := by
    let order := e.symm (relativeOrder c)
    let selected := r order
    let t := prefixCompletionTime c (relativeOrder c) selected
    have ht : t ≤ N := prefixCompletionTime_le_budget
      (length_run strategy board N) c (relativeOrder c) selected
    refine ⟨(order, (copyEmbedding c, ⟨t, Nat.lt_succ_of_le ht⟩)), ?_⟩
    have hc := copy_mem_completionAtEvent strategy board c selected hnodup
    simpa [reindexedCompletionEventForKey, order, selected, t] using hc
  inj' := by
    intro c d hcd
    apply SimpleGraph.Copy.ext
    intro v
    have hf : copyEmbedding c = copyEmbedding d := by
      have := congrArg
        (fun z : ReindexedCompletionHistoryIndex strategy board e r ↦
          z.1.2.1) hcd
      exact this
    exact DFunLike.congr_fun hf v

theorem card_copy_le_card_reindexedCompletionHistoryIndex {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (r : Order → K6PrefixLength)
    (hnodup : (queries (run strategy board N)).Nodup) :
    Fintype.card (SimpleGraph.Copy QueryComplexity.K6
        (QueryComplexity.positiveGraph (run strategy board N))) ≤
      Fintype.card
        (ReindexedCompletionHistoryIndex strategy board e r) := by
  exact Fintype.card_le_of_injective
    (copyToReindexedCompletionHistoryIndex strategy board e r hnodup)
    (copyToReindexedCompletionHistoryIndex strategy board e r hnodup).injective

/-- Cardinal form of global coverage, stated using Mathlib's public labelled
copy count. -/
theorem labelledCopyCount_le_reindexedCompletionHistoryCount {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (board : Board (QueryComplexity.Query N))
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (r : Order → K6PrefixLength)
    (hnodup : (queries (run strategy board N)).Nodup) :
    (QueryComplexity.positiveGraph (run strategy board N)).labelledCopyCount
        QueryComplexity.K6 ≤
      reindexedCompletionHistoryCount strategy board e r := by
  unfold reindexedCompletionHistoryCount
  exact labelledCopyCount_le_card_of_embedding
    (QueryComplexity.positiveGraph (run strategy board N)) QueryComplexity.K6
    (copyToReindexedCompletionHistoryIndex strategy board e r hnodup)

/-- Sum of completed-event masses for one actual relative order and prefix
length, over every labelled vertex embedding and every possible completion
time `0,...,N`. -/
def orderCompletionHistoryMass {N : ℕ} (p : ℝ≥0∞)
    (strategy : QueryComplexity.K6Strategy N) (π : K6EdgeOrder)
    (r : K6PrefixLength) : ℝ≥0∞ :=
  ∑ f : Fin 6 ↪ QueryComplexity.Vertex N, ∑ t : Fin (N + 1),
    finiteBoardMass (bernoulliWeight p)
      (completionAtEvent strategy f π r t.val)

/-- The same completion-history mass with all relative orders bundled into
one product index.  This representation is convenient for applying the
generic event/cardinality identity exactly once. -/
def globalCompletionHistoryMass {N : ℕ} (p : ℝ≥0∞)
    (strategy : QueryComplexity.K6Strategy N)
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (r : Order → K6PrefixLength) : ℝ≥0∞ :=
  ∑ z : ReindexedCompletionHistoryKey N Order,
    finiteBoardMass (bernoulliWeight p)
      (reindexedCompletionEventForKey strategy e r z)

theorem globalCompletionHistoryMass_eq_sum_order {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (r : Order → K6PrefixLength) :
    globalCompletionHistoryMass p strategy e r =
      ∑ order : Order,
        orderCompletionHistoryMass p strategy (e order) (r order) := by
  unfold globalCompletionHistoryMass ReindexedCompletionHistoryKey
    orderCompletionHistoryMass
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rfl

set_option maxHeartbeats 400000 in
theorem globalCompletionHistoryMass_eq_weightedCount {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (r : Order → K6PrefixLength) :
    globalCompletionHistoryMass p strategy e r =
      ∑ board : Board (QueryComplexity.Query N),
        boardWeight (bernoulliWeight p) board *
          (reindexedCompletionHistoryCount strategy board e r : ℝ≥0∞) := by
  unfold globalCompletionHistoryMass reindexedCompletionHistoryCount
  unfold finiteBoardMass
  simpa using
    (sum_event_weight_eq_weight_mul_card
      (fun board : Board (QueryComplexity.Query N) ↦
        boardWeight (bernoulliWeight p) board)
      (fun z : ReindexedCompletionHistoryKey N Order ↦ fun board ↦
        board ∈ reindexedCompletionEventForKey strategy e r z))

/-- Global multiplicity coverage after averaging over all boards. -/
theorem completedCopyMass_le_globalCompletionHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (r : Order → K6PrefixLength) :
    completedCopyMass p strategy ≤
      globalCompletionHistoryMass p strategy e r := by
  rw [globalCompletionHistoryMass_eq_weightedCount]
  unfold completedCopyMass
  apply Finset.sum_le_sum
  intro board _hboard
  apply mul_le_mul_left'
  exact Nat.cast_le.mpr
    (labelledCopyCount_le_reindexedCompletionHistoryCount
      strategy board e r
        (queries_run_nodup_of_freshForBudget strategy hfresh board))

/-- Exact `hpartition` bridge for `LowerAssembly.allOrders_target_scale`:
every completed labelled copy is charged, with multiplicity, to the completion
history indexed by its unique relative order. -/
theorem completedCopyMass_le_sum_orderCompletionHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (r : Order → K6PrefixLength) :
    completedCopyMass p strategy ≤
      ∑ order : Order,
        orderCompletionHistoryMass p strategy (e order) (r order) := by
  rw [← globalCompletionHistoryMass_eq_sum_order]
  exact completedCopyMass_le_globalCompletionHistoryMass
    p strategy hfresh e r

/-- Corresponding sum of viable prefix-history masses. -/
def orderPrefixHistoryMass {N : ℕ} (p : ℝ≥0∞)
    (strategy : QueryComplexity.K6Strategy N) (π : K6EdgeOrder)
    (r : K6PrefixLength) : ℝ≥0∞ :=
  ∑ f : Fin 6 ↪ QueryComplexity.Vertex N, ∑ t : Fin (N + 1),
    finiteBoardMass (bernoulliWeight p)
      (prefixHistoryEvent strategy f π r t.val)

/-- Expected completed-copy contribution of one actual relative order. -/
def orderCopyMass {N : ℕ} (p : ℝ≥0∞)
    (strategy : QueryComplexity.K6Strategy N) (π : K6EdgeOrder) : ℝ≥0∞ :=
  ∑ board : Board (QueryComplexity.Query N),
    boardWeight (bernoulliWeight p) board *
      (orderedCopyCount (run strategy board N) π : ℝ≥0∞)

/- The completion-history mass is the board-weighted cardinality of the
concrete history index. -/
set_option maxHeartbeats 400000 in
theorem orderCompletionHistoryMass_eq_weightedCount {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    (π : K6EdgeOrder) (r : K6PrefixLength) :
    orderCompletionHistoryMass p strategy π r =
      ∑ board : Board (QueryComplexity.Query N),
        boardWeight (bernoulliWeight p) board *
          (completionHistoryCount strategy board π r : ℝ≥0∞) := by
  unfold orderCompletionHistoryMass completionHistoryCount
  rw [← Fintype.sum_prod_type (fun z : CompletionHistoryKey N ↦
    finiteBoardMass (bernoulliWeight p)
      (completionAtEvent strategy z.1 π r z.2.val))]
  unfold finiteBoardMass
  simpa [completionEventForKey] using
    (sum_event_weight_eq_weight_mul_card
      (fun board : Board (QueryComplexity.Query N) ↦
        boardWeight (bernoulliWeight p) board)
      (fun z : CompletionHistoryKey N ↦ fun board ↦
        board ∈ completionEventForKey strategy π r z))

theorem orderCopyMass_le_orderCompletionHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    (π : K6EdgeOrder) (r : K6PrefixLength) :
    orderCopyMass p strategy π ≤
      orderCompletionHistoryMass p strategy π r := by
  rw [orderCompletionHistoryMass_eq_weightedCount]
  unfold orderCopyMass
  apply Finset.sum_le_sum
  intro board _hboard
  apply mul_le_mul_left'
  exact Nat.cast_le.mpr
    (orderedCopyCount_le_completionHistoryCount strategy board π r
      (queries_run_nodup_of_freshForBudget strategy hfresh board))

/-- The concrete per-order stopping inequality obtained by summing the exact
one-history non-anticipation estimates. -/
theorem orderCompletionHistoryMass_le {N : ℕ}
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (strategy : QueryComplexity.K6Strategy N) (π : K6EdgeOrder)
    (r : K6PrefixLength) :
    orderCompletionHistoryMass p strategy π r ≤
      p ^ (15 - r.val) * orderPrefixHistoryMass p strategy π r := by
  unfold orderCompletionHistoryMass orderPrefixHistoryMass
  calc
    (∑ f : Fin 6 ↪ QueryComplexity.Vertex N, ∑ t : Fin (N + 1),
        finiteBoardMass (bernoulliWeight p)
          (completionAtEvent strategy f π r t.val)) ≤
      ∑ f : Fin 6 ↪ QueryComplexity.Vertex N, ∑ t : Fin (N + 1),
        p ^ (15 - r.val) * finiteBoardMass (bernoulliWeight p)
          (prefixHistoryEvent strategy f π r t.val) := by
      apply Finset.sum_le_sum
      intro f _hf
      apply Finset.sum_le_sum
      intro t _ht
      exact completionAtEvent_mass_le p hp strategy f π r t.val
    _ = p ^ (15 - r.val) *
        ∑ f : Fin 6 ↪ QueryComplexity.Vertex N, ∑ t : Fin (N + 1),
          finiteBoardMass (bernoulliWeight p)
            (prefixHistoryEvent strategy f π r t.val) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _hf
      rw [Finset.mul_sum]

/-! ## Direct inputs for the four-case lower assembly -/

/-- Nine prefix edges are used in the first three cases, and ten in the
shifted-bipartite case. -/
def casePrefixLength : LowerAssembly.PrefixCase → K6PrefixLength
  | .ordinary | .halfGraph | .almostCompleteFive => ⟨9, by omega⟩
  | .shiftedBipartite => ⟨10, by omega⟩

@[simp] theorem fifteen_sub_casePrefixLength_val
    (kind : LowerAssembly.PrefixCase) :
    15 - (casePrefixLength kind).val =
      LowerAssembly.completionExponent kind := by
  cases kind <;> rfl

/-- Per-order `hstop` in exactly the exponent convention expected by
`LowerAssembly.allOrders_target_scale`. -/
theorem orderCompletionHistoryMass_le_casePrefixHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (strategy : QueryComplexity.K6Strategy N) (π : K6EdgeOrder)
    (kind : LowerAssembly.PrefixCase) :
    orderCompletionHistoryMass p strategy π (casePrefixLength kind) ≤
      p ^ LowerAssembly.completionExponent kind *
        orderPrefixHistoryMass p strategy π (casePrefixLength kind) := by
  simpa using
    (orderCompletionHistoryMass_le p hp strategy π (casePrefixLength kind))

/-- Global `hpartition` with the prefix length selected independently for
each relative-order class. -/
theorem completedCopyMass_le_sum_caseCompletionHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (kind : Order → LowerAssembly.PrefixCase) :
    completedCopyMass p strategy ≤
      ∑ order : Order, orderCompletionHistoryMass p strategy (e order)
        (casePrefixLength (kind order)) := by
  exact completedCopyMass_le_sum_orderCompletionHistoryMass
    p strategy hfresh e (fun order ↦ casePrefixLength (kind order))

/-- The game-success endpoint composed with global stopping-history
coverage. -/
theorem successProbability_le_sum_caseCompletionHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (kind : Order → LowerAssembly.PrefixCase) :
    QueryComplexity.successProbability p N strategy ≤
      ∑ order : Order, orderCompletionHistoryMass p strategy (e order)
        (casePrefixLength (kind order)) :=
  (successProbability_le_completedCopyMass p strategy).trans
    (completedCopyMass_le_sum_caseCompletionHistoryMass
      p strategy hfresh e kind)

/-- Fully concrete ordered-prefix estimate: the expected contribution from
completed labelled copies of one relative order is at most `p^(15-r)` times
the summed viable prefix-history mass. -/
theorem orderCopyMass_le_prefixHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    (π : K6EdgeOrder) (r : K6PrefixLength) :
    orderCopyMass p strategy π ≤
      p ^ (15 - r.val) * orderPrefixHistoryMass p strategy π r :=
  (orderCopyMass_le_orderCompletionHistoryMass p strategy hfresh π r).trans
    (orderCompletionHistoryMass_le p hp strategy π r)

/-! ## Abstract reindexing for final assembly

The final theorem quantifies over an abstract finite type equivalent to the
`15!` relative edge orders.  The following equivalence connects that scalable
indexing convention to the concrete order used by the stopping events above.
No enumeration of `K6EdgeOrder` is materialized. -/

/-- A reindexed order fiber is the corresponding concrete order fiber. -/
def reindexedOrderedCopyEquiv {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    {Order : Type*} (e : Order ≃ K6EdgeOrder) (order : Order) :
    ReindexedOrderedCopy h e order ≃ OrderedCopy h (e order) where
  toFun c := ⟨c.1, by
    have hc := congrArg e c.2
    simpa using hc⟩
  invFun c := ⟨c.1, by
    rw [c.2]
    simp⟩
  left_inv c := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl

theorem reindexedOrderedCopyCount_eq {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (order : Order) :
    reindexedOrderedCopyCount h e order = orderedCopyCount h (e order) := by
  unfold reindexedOrderedCopyCount orderedCopyCount
  exact Fintype.card_congr (reindexedOrderedCopyEquiv h e order)

/-- Expected completed-copy contribution of one abstractly reindexed order. -/
def reindexedOrderCopyMass {N : ℕ} (p : ℝ≥0∞)
    (strategy : QueryComplexity.K6Strategy N)
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (order : Order) : ℝ≥0∞ :=
  ∑ board : Board (QueryComplexity.Query N),
    boardWeight (bernoulliWeight p) board *
      (reindexedOrderedCopyCount (run strategy board N) e order : ℝ≥0∞)

theorem reindexedOrderCopyMass_eq {N : ℕ} (p : ℝ≥0∞)
    (strategy : QueryComplexity.K6Strategy N)
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (order : Order) :
    reindexedOrderCopyMass p strategy e order =
      orderCopyMass p strategy (e order) := by
  unfold reindexedOrderCopyMass orderCopyMass
  apply Finset.sum_congr rfl
  intro board _hboard
  rw [reindexedOrderedCopyCount_eq]

/-- The concrete stopping estimate in the abstract order indexing used by
`LowerAssembly.allOrders_target_scale`. -/
theorem reindexedOrderCopyMass_le_prefixHistoryMass {N : ℕ}
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (strategy : QueryComplexity.K6Strategy N)
    (hfresh : QueryComplexity.FreshForBudget strategy)
    {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) (order : Order) (r : K6PrefixLength) :
    reindexedOrderCopyMass p strategy e order ≤
      p ^ (15 - r.val) * orderPrefixHistoryMass p strategy (e order) r := by
  rw [reindexedOrderCopyMass_eq]
  exact orderCopyMass_le_prefixHistoryMass p hp strategy hfresh (e order) r

end
end StoppingCoverage
end OnlineRamsey
