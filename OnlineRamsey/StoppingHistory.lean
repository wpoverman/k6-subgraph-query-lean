import OnlineRamsey.LowerAssembly
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Concrete stopping histories for ordered labelled `K₆` copies

This file supplies the finite indexing that is implicit in the usual
ordered-prefix argument.  A labelled copy determines fifteen distinct board
coordinates, hence fifteen distinct query times and a unique relative order.
We also prove a reusable non-anticipation theorem: a fixed-length history
event which avoids a set of coordinates ignores the values on that set.

All histories are still newest first.  `queryTime` reverses the list index, so
smaller positive times correspond to earlier queries.
-/

open scoped BigOperators ENNReal

namespace OnlineRamsey
namespace StoppingHistory

open QueryComplexity LowerAssembly

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## The fifteen abstract edges and their images -/

/-- The non-diagonal unordered pairs of the six labelled source vertices. -/
abbrev K6Edge := {e : Sym2 (Fin 6) // ¬ e.IsDiag}

theorem card_k6Edge : Fintype.card K6Edge = 15 := by
  rw [Sym2.card_subtype_not_diag]
  norm_num [Nat.choose]

/-- A fixed enumeration of the fifteen source edges. -/
def edgeEquiv : Fin 15 ≃ K6Edge :=
  Fintype.equivOfCardEq card_k6Edge.symm

/-- The board coordinate occupied by edge `i` under a labelled embedding. -/
def embeddedEdge {N : ℕ} (f : Fin 6 ↪ QueryComplexity.Vertex N)
    (i : Fin 15) : QueryComplexity.Query N :=
  f.sym2Map (edgeEquiv i).1

theorem embeddedEdge_injective {N : ℕ}
    (f : Fin 6 ↪ QueryComplexity.Vertex N) :
    Function.Injective (embeddedEdge f) := by
  intro i j hij
  apply edgeEquiv.injective
  apply Subtype.ext
  exact f.sym2Map.injective hij

theorem embeddedEdge_not_diag {N : ℕ}
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (i : Fin 15) :
    ¬(embeddedEdge f i).IsDiag := by
  rw [embeddedEdge, Function.Embedding.sym2Map_apply,
    Sym2.isDiag_map f.injective]
  exact (edgeEquiv i).2

/-- A fixed vertex embedding is completed positively in a transcript. -/
def EmbeddingCompleted {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    (f : Fin 6 ↪ QueryComplexity.Vertex N) : Prop :=
  ∀ i : Fin 15, (embeddedEdge f i, true) ∈ h

/-- Query time attached directly to a fixed vertex embedding.  This version
is defined even before the proof that the embedding is a graph copy. -/
def embeddingQueryTime {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (i : Fin 15) : ℕ :=
  h.length - (queries h).idxOf (embeddedEdge f i)

/-- Relative order attached directly to a fixed vertex embedding. -/
def embeddingRelativeOrder {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    (f : Fin 6 ↪ QueryComplexity.Vertex N) : K6EdgeOrder :=
  Tuple.sort (embeddingQueryTime h f)

/-- Position `j` among the first `r` edge labels. -/
def prefixIndex (r : K6PrefixLength) (j : Fin r.val) : Fin 15 :=
  ⟨j.val, by omega⟩

/-- Position `j` among the `15-r` suffix edge labels. -/
def suffixIndex (r : K6PrefixLength) (j : Fin (15 - r.val)) : Fin 15 :=
  ⟨r.val + j.val, by omega⟩

theorem suffixIndex_injective (r : K6PrefixLength) :
    Function.Injective (suffixIndex r) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val hij)

/-- The still-unexposed board coordinates after an `r`-edge prefix. -/
def remainingEdges {N : ℕ}
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) : Finset (QueryComplexity.Query N) :=
  Finset.univ.image
    (fun j : Fin (15 - r.val) ↦ embeddedEdge f (π (suffixIndex r j)))

@[simp] theorem card_remainingEdges {N : ℕ}
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) :
    (remainingEdges f π r).card = 15 - r.val := by
  unfold remainingEdges
  rw [Finset.card_image_of_injective]
  · simp
  · exact (embeddedEdge_injective f).comp
      (π.injective.comp (suffixIndex_injective r))

/-! ## Completed copies, query times, and relative orders -/

/-- The underlying vertex embedding of a completed labelled copy. -/
def copyEmbedding {N : ℕ} {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) :
    Fin 6 ↪ QueryComplexity.Vertex N := c.toEmbedding

/-- The coordinate occupied by a source edge in a completed graph copy. -/
def copyEdge {N : ℕ} {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) (i : Fin 15) :
    QueryComplexity.Query N := embeddedEdge (copyEmbedding c) i

/-- Every edge coordinate belonging to a completed copy occurs positively. -/
theorem copyEdge_mem {N : ℕ} {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) (i : Fin 15) :
    (copyEdge c i, true) ∈ h := by
  let e := edgeEquiv i
  obtain ⟨u, v, hne, huv⟩ : ∃ u v : Fin 6, u ≠ v ∧ e.1 = s(u, v) := by
    obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep e.1
    have hne : u ≠ v := by
      intro heq
      apply e.2
      rw [← huv]
      exact Sym2.mk_isDiag_iff.mpr heq
    exact ⟨u, v, hne, huv.symm⟩
  have hc := c.toHom.map_rel (show QueryComplexity.K6.Adj u v by
    simpa [QueryComplexity.K6] using hne)
  rw [QueryComplexity.positiveGraph_adj] at hc
  simpa [copyEdge, copyEmbedding, embeddedEdge,
    Function.Embedding.sym2Map_apply, e, huv] using hc.2

/-- Chronological query time, numbered from one.  The final transcript is
newest first, so this reverses `idxOf`. -/
def queryTime {N : ℕ} {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) (i : Fin 15) : ℕ :=
  h.length - (queries h).idxOf (copyEdge c i)

theorem copyEdge_mem_queries {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) (i : Fin 15) :
    copyEdge c i ∈ queries h := by
  exact List.mem_map.mpr ⟨(copyEdge c i, true), copyEdge_mem c i, rfl⟩

theorem idxOf_copyEdge_lt_length {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) (i : Fin 15) :
    (queries h).idxOf (copyEdge c i) < (queries h).length :=
  List.idxOf_lt_length_iff.mpr (copyEdge_mem_queries c i)

theorem idxOf_copyEdge_injective {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) :
    Function.Injective (fun i : Fin 15 ↦
      (queries h).idxOf (copyEdge c i)) := by
  intro i j hij
  have hi := idxOf_copyEdge_lt_length c i
  have hj := idxOf_copyEdge_lt_length c j
  have hgeti := List.getElem_idxOf hi
  have hgetj := List.getElem_idxOf hj
  have hedge : copyEdge c i = copyEdge c j := by
    rw [← hgeti, ← hgetj]
    congr
  exact embeddedEdge_injective (copyEmbedding c) hedge

theorem queryTime_injective {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) :
    Function.Injective (queryTime c) := by
  intro i j hij
  have hi := idxOf_copyEdge_lt_length c i
  have hj := idxOf_copyEdge_lt_length c j
  dsimp only [queryTime] at hij
  simp only [length_queries] at hi hj
  apply idxOf_copyEdge_injective c
  calc
    (queries h).idxOf (copyEdge c i) =
        h.length - (h.length - (queries h).idxOf (copyEdge c i)) := by omega
    _ = h.length - (h.length - (queries h).idxOf (copyEdge c j)) := by rw [hij]
    _ = (queries h).idxOf (copyEdge c j) := by omega

/-- The unique relative order of the fifteen queried coordinates. -/
def relativeOrder {N : ℕ} {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) : K6EdgeOrder :=
  Tuple.sort (queryTime c)

theorem queryTime_monotone_relativeOrder {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) :
    Monotone (queryTime c ∘ relativeOrder c) :=
  Tuple.monotone_sort (queryTime c)

theorem queryTime_strictMono_relativeOrder {N : ℕ}
    {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) :
    StrictMono (queryTime c ∘ relativeOrder c) :=
  (queryTime_monotone_relativeOrder c).strictMono_of_injective
    ((queryTime_injective c).comp (relativeOrder c).injective)

/-- Time at which the first `r` edges of an order have all appeared.  For a
completed copy and its actual order this is the time of edge `r-1`. -/
def prefixCompletionTime {N : ℕ} {h : Transcript (QueryComplexity.Query N)}
    (c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h)) (π : K6EdgeOrder)
    (r : K6PrefixLength) : ℕ :=
  if hr : 0 < r.val then queryTime c (π ⟨r.val - 1, by omega⟩) else 0

/-- A completed copy bundled with its relative edge order and every prefix
completion time.  The fields are data computed from the copy, not additional
probabilistic assumptions. -/
structure CompletionRecord {N : ℕ}
    (h : Transcript (QueryComplexity.Query N)) where
  copy : SimpleGraph.Copy QueryComplexity.K6
    (QueryComplexity.positiveGraph h)
  order : K6EdgeOrder := relativeOrder copy
  completionTime : K6PrefixLength → ℕ :=
    prefixCompletionTime copy order

/-! ## Exact partition by relative edge order -/

/-- Completed labelled copies having a fixed relative edge order. -/
abbrev OrderedCopy {N : ℕ} (h : Transcript (QueryComplexity.Query N))
    (π : K6EdgeOrder) :=
  {c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h) // relativeOrder c = π}

/-- The number of completed labelled copies in one order class. -/
def orderedCopyCount {N : ℕ} (h : Transcript (QueryComplexity.Query N))
    (π : K6EdgeOrder) : ℕ := Fintype.card (OrderedCopy h π)

/-- Every completed labelled copy lies in exactly one order fiber. -/
def orderedCopyPartitionEquiv {N : ℕ}
    (h : Transcript (QueryComplexity.Query N)) :
    (Σ π : K6EdgeOrder, OrderedCopy h π) ≃
      SimpleGraph.Copy QueryComplexity.K6
        (QueryComplexity.positiveGraph h) :=
  Equiv.sigmaFiberEquiv relativeOrder

private theorem card_eq_sum_fibers {α β : Type*}
    [Fintype α] [Fintype β] (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm

/-- Reindexed order fiber.  Keeping the finite order type abstract avoids
materializing the `15!`-element `Finset.univ` for permutations during kernel
elaboration, exactly as in `LowerAssembly.allOrders_target_scale`. -/
abbrev ReindexedOrderedCopy {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    {Order : Type*} (e : Order ≃ K6EdgeOrder) (π : Order) :=
  {c : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h) // e.symm (relativeOrder c) = π}

def reindexedOrderedCopyCount {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    (π : Order) : ℕ := Fintype.card (ReindexedOrderedCopy h e π)

/-- Exact multiplicity-preserving partition, stated without forcing Lean to
materialize the `15!`-element permutation enumeration. -/
def reindexedOrderedCopyPartitionEquiv {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    {Order : Type*} (e : Order ≃ K6EdgeOrder) :
    (Σ π : Order, ReindexedOrderedCopy h e π) ≃
      SimpleGraph.Copy QueryComplexity.K6
        (QueryComplexity.positiveGraph h) :=
  Equiv.sigmaFiberEquiv (fun c ↦ e.symm (relativeOrder c))

/-- Weighted form of the exact order partition.  This is the finite-sum
statement needed before exchanging the order sum with expectation. -/
theorem sum_reindexedOrderedCopyWeight_eq {N : ℕ}
    (h : Transcript (QueryComplexity.Query N))
    {Order : Type*} [Fintype Order] (e : Order ≃ K6EdgeOrder)
    {R : Type*} [AddCommMonoid R]
    (w : SimpleGraph.Copy QueryComplexity.K6
      (QueryComplexity.positiveGraph h) → R) :
    (∑ π : Order, ∑ c : ReindexedOrderedCopy h e π, w c.1) =
      ∑ c, w c := by
  exact Fintype.sum_fiberwise (fun c ↦ e.symm (relativeOrder c)) w

theorem card_reindexed_order {Order : Type*} [Fintype Order]
    (e : Order ≃ K6EdgeOrder) :
    Fintype.card Order = Nat.factorial 15 := by
  rw [Fintype.card_congr e, card_k6EdgeOrder]

/-- Expected labelled-copy count as an explicit finite board sum. -/
def completedCopyMass {N : ℕ} (p : ℝ≥0∞)
    (strategy : QueryComplexity.K6Strategy N) : ℝ≥0∞ :=
  ∑ b : Board (QueryComplexity.Query N),
    boardWeight (bernoulliWeight p) b *
      ((QueryComplexity.positiveGraph (run strategy b N)).labelledCopyCount
        QueryComplexity.K6 : ℝ≥0∞)

private theorem one_le_labelledCopyCount_of_nonempty
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (h : Nonempty (SimpleGraph.Copy H G)) :
    (1 : ℝ≥0∞) ≤ (G.labelledCopyCount H : ℝ≥0∞) := by
  unfold SimpleGraph.labelledCopyCount
  exact Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr h)

/- Success probability is bounded by the expected number of completed
labelled copies.  This is the exact finite-board Markov endpoint used as
`hsuccess` in lower assembly. -/
theorem successProbability_le_completedCopyMass {N : ℕ}
    (p : ℝ≥0∞) (strategy : QueryComplexity.K6Strategy N) :
    QueryComplexity.successProbability p N strategy ≤
      completedCopyMass p strategy := by
  rw [QueryComplexity.successProbability_eq_board_sum]
  unfold completedCopyMass
  apply Finset.sum_le_sum
  intro b _hb
  by_cases hs : QueryComplexity.TranscriptSucceeds (run strategy b N)
  · have hone := one_le_labelledCopyCount_of_nonempty
      (QueryComplexity.positiveGraph (run strategy b N))
      QueryComplexity.K6 hs
    simpa [hs] using
      (mul_le_mul_left' hone (boardWeight (bernoulliWeight p) b))
  · simp [hs]

/-! ## Fixed-history non-anticipation -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A transcript never queries a coordinate from `remaining`. -/
def Avoids (h : Transcript Q) (remaining : Finset Q) : Prop :=
  ∀ q ∈ queries h, q ∉ remaining

theorem avoids_tail {entry : Q × Bool} {h : Transcript Q}
    {remaining : Finset Q} (ha : Avoids (entry :: h) remaining) :
    Avoids h remaining := by
  intro q hq
  exact ha q (by
    change q ∈ entry.1 :: queries h
    exact List.mem_cons_of_mem _ hq)

/-- If a run has not queried `remaining`, changing precisely those board
coordinates leaves the whole past transcript unchanged. -/
theorem run_eq_of_agreeOutside_of_avoids
    (strategy : Strategy Q) (remaining : Finset Q)
    (b b' : Board Q) (n : ℕ)
    (hagree : LowerAssembly.AgreeOutside remaining b b')
    (havoid : Avoids (run strategy b n) remaining) :
    run strategy b' n = run strategy b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have htail : Avoids (run strategy b n) remaining := by
        exact avoids_tail havoid
      have hpast := ih htail
      have hnext : strategy (run strategy b n) ∉ remaining := by
        apply havoid (strategy (run strategy b n))
        simp [queries]
      rw [run_succ, run_succ, hpast]
      rw [hagree _ hnext]

/-- A fixed-length event described by a transcript predicate and explicitly
requiring avoidance of `remaining`. -/
def historyEvent (strategy : Strategy Q) (n : ℕ)
    (accept : Transcript Q → Prop) (remaining : Finset Q) : Set (Board Q) :=
  {b | accept (run strategy b n) ∧ Avoids (run strategy b n) remaining}

/-- Concrete non-anticipation for fixed stopping histories. -/
theorem historyEvent_ignores (strategy : Strategy Q) (n : ℕ)
    (accept : Transcript Q → Prop) (remaining : Finset Q) :
    LowerAssembly.EventIgnores
      (historyEvent strategy n accept remaining) remaining := by
  intro b b' hagree
  constructor
  · rintro ⟨haccept, havoid⟩
    have heq := run_eq_of_agreeOutside_of_avoids strategy remaining b b' n
      hagree havoid
    simpa [historyEvent, heq] using And.intro haccept havoid
  · rintro ⟨haccept, havoid⟩
    have hagree' : LowerAssembly.AgreeOutside remaining b' b := by
      intro q hq
      exact (hagree q hq).symm
    have heq := run_eq_of_agreeOutside_of_avoids strategy remaining b' b n
      hagree' havoid
    simpa [historyEvent, heq] using And.intro haccept havoid

/-! ## Concrete ordered-prefix events -/

/-- The transcript predicate saying that the `r`th prescribed positive edge
has just completed the prefix.  Earlier prescribed edges occur positively in
the prior transcript. -/
def prefixAccept {N : ℕ}
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (h : Transcript (QueryComplexity.Query N)) : Prop :=
  if hr : 0 < r.val then
    ∃ tail,
      h = (embeddedEdge f (π ⟨r.val - 1, by omega⟩), true) :: tail ∧
      ∀ j : Fin (r.val - 1),
        (embeddedEdge f (π (prefixIndex r ⟨j.val, by omega⟩)), true) ∈ tail
  else h = []

/-- A fixed completion history for one labelled embedding and one relative
order.  Avoidance of all suffix coordinates is part of the event. -/
def prefixHistoryEvent {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (t : ℕ) :
    Set (Board (QueryComplexity.Query N)) :=
  historyEvent strategy t (prefixAccept f π r) (remainingEdges f π r)

theorem prefixHistoryEvent_ignores {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (t : ℕ) :
    LowerAssembly.EventIgnores (prefixHistoryEvent strategy f π r t)
      (remainingEdges f π r) :=
  historyEvent_ignores strategy t (prefixAccept f π r)
    (remainingEdges f π r)

/-- Boards on which a fixed prefix history is followed by a completed copy
with the stipulated final relative order. -/
def completionAtEvent {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (t : ℕ) :
    Set (Board (QueryComplexity.Query N)) :=
  {b | b ∈ prefixHistoryEvent strategy f π r t ∧
    b ∈ LowerAssembly.allPositiveOn (remainingEdges f π r) ∧
    EmbeddingCompleted (run strategy b N) f ∧
      embeddingRelativeOrder (run strategy b N) f = π}

theorem completionAtEvent_subset {N : ℕ}
    (strategy : QueryComplexity.K6Strategy N)
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (t : ℕ) :
    completionAtEvent strategy f π r t ⊆
      prefixHistoryEvent strategy f π r t ∩
        LowerAssembly.allPositiveOn (remainingEdges f π r) := by
  intro b hb
  exact ⟨hb.1, hb.2.1⟩

/-- Concrete ordered-prefix mass inequality at one labelled completion
history.  The exponent is exactly the number of suffix edges. -/
theorem completionAtEvent_mass_le {N : ℕ}
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (strategy : QueryComplexity.K6Strategy N)
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (t : ℕ) :
    finiteBoardMass (bernoulliWeight p)
        (completionAtEvent strategy f π r t) ≤
      p ^ (15 - r.val) * finiteBoardMass (bernoulliWeight p)
        (prefixHistoryEvent strategy f π r t) := by
  have h := LowerAssembly.stoppingPrefix_event_mass_le p hp
    (completionAtEvent strategy f π r t)
    (prefixHistoryEvent strategy f π r t) (remainingEdges f π r)
    (completionAtEvent_subset strategy f π r t)
    (prefixHistoryEvent_ignores strategy f π r t)
  simpa using h

end
end StoppingHistory
end OnlineRamsey
