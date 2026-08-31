import OnlineRamsey.StoppingCoverage
import OnlineRamsey.RecurrenceInstantiation

open scoped BigOperators NNReal ENNReal

namespace OnlineRamsey
namespace OrdinaryHistoryCount

open QueryComplexity StoppingHistory StoppingCoverage
open PrefixSoundness RecurrenceInstantiation

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The edge numbering used by the finite recurrence, regarded as an
unordered non-diagonal pair. -/
def recurrenceEdge (e : PrefixSoundness.K6Edge) : StoppingHistory.K6Edge :=
  ⟨RecurrenceInstantiation.edgeCoord e, by
    rw [RecurrenceInstantiation.edgeCoord, Sym2.mk_isDiag_iff]
    exact (RecurrenceInstantiation.edgeLo_lt_edgeHi e).ne⟩

theorem recurrenceEdge_injective : Function.Injective recurrenceEdge := by
  intro e d hed
  apply RecurrenceInstantiation.edgeCoord_injective
  exact congrArg Subtype.val hed

/-- The exact permutation relating the lexicographic edge numbering in the
finite recurrence to the abstract edge numbering used by stopping histories. -/
def recurrenceEdgeEquiv : PrefixSoundness.K6Edge ≃ StoppingHistory.K6Edge :=
  Equiv.ofBijective recurrenceEdge <|
    (Fintype.bijective_iff_injective_and_card recurrenceEdge).2 ⟨
      recurrenceEdge_injective, by
        change Fintype.card (Fin 15) = Fintype.card StoppingHistory.K6Edge
        simpa using StoppingHistory.card_k6Edge.symm⟩

/-- A recurrence edge, written as the corresponding stopping-history index. -/
def recurrenceToStoppingIndex : PrefixSoundness.K6Edge ≃ Fin 15 :=
  recurrenceEdgeEquiv.trans StoppingHistory.edgeEquiv.symm

theorem edgeEquiv_recurrenceToStoppingIndex
    (e : PrefixSoundness.K6Edge) :
    StoppingHistory.edgeEquiv (recurrenceToStoppingIndex e) = recurrenceEdge e := by
  change StoppingHistory.edgeEquiv
      (StoppingHistory.edgeEquiv.symm (recurrenceEdgeEquiv e)) = _
  rw [StoppingHistory.edgeEquiv.apply_symm_apply]
  rfl

theorem embeddedEdge_recurrenceToStoppingIndex {N : ℕ}
    (f : Fin 6 ↪ QueryComplexity.Vertex N) (e : PrefixSoundness.K6Edge) :
    embeddedEdge f (recurrenceToStoppingIndex e) =
      s(f (RecurrenceInstantiation.edgeLo e),
        f (RecurrenceInstantiation.edgeHi e)) := by
  simp only [embeddedEdge, edgeEquiv_recurrenceToStoppingIndex, recurrenceEdge,
    RecurrenceInstantiation.edgeCoord, Function.Embedding.sym2Map_apply,
    Sym2.map_pair_eq]

/-- The recurrence edge set corresponding to the first `r` positions of a
stopping-history order. -/
def orderedPrefixEdges (pi : K6EdgeOrder) (r : K6PrefixLength) :
    Finset PrefixSoundness.K6Edge :=
  Finset.univ.image (fun j : Fin r.val ↦
    recurrenceToStoppingIndex.symm (pi (prefixIndex r j)))

@[simp] theorem card_orderedPrefixEdges (pi : K6EdgeOrder)
    (r : K6PrefixLength) : (orderedPrefixEdges pi r).card = r.val := by
  unfold orderedPrefixEdges
  rw [Finset.card_image_of_injective]
  · simp
  · exact recurrenceToStoppingIndex.symm.injective.comp
      (pi.injective.comp (by
        intro i j hij
        apply Fin.ext
        simpa [prefixIndex] using congrArg Fin.val hij))

theorem mem_orderedPrefixEdges_iff (pi : K6EdgeOrder)
    (r : K6PrefixLength) (e : PrefixSoundness.K6Edge) :
    e ∈ orderedPrefixEdges pi r ↔
      ∃ j : Fin r.val,
        recurrenceToStoppingIndex e = pi (prefixIndex r j) := by
  simp only [orderedPrefixEdges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, by simp⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    apply recurrenceToStoppingIndex.injective
    simpa using hj.symm

theorem edgeFinsetOfMask_injective :
    Function.Injective PrefixSoundness.edgeFinsetOfMask := by
  intro g g' hgg'
  apply Fin.ext
  calc
    g.1 = edgeFinsetMask (edgeFinsetOfMask g) := (edgeMask_roundtrip g).symm
    _ = edgeFinsetMask (edgeFinsetOfMask g') := by rw [hgg']
    _ = g'.1 := edgeMask_roundtrip g'

/-- Bit masks and finite subsets of the fifteen recurrence edge positions are
equivalent.  This is extracted from the already-proved mask round trip. -/
def graphMaskEdgeFinsetEquiv :
    Fin K6Prefix.graphCount ≃ Finset PrefixSoundness.K6Edge :=
  Equiv.ofBijective edgeFinsetOfMask <|
    (Fintype.bijective_iff_injective_and_card edgeFinsetOfMask).2 ⟨
      edgeFinsetOfMask_injective, by
        change Fintype.card (Fin 32768) = Fintype.card (Finset (Fin 15))
        simp [Fintype.card_finset]⟩

/-- The unique executable graph mask represented by the first `r` positions
of an arbitrary stopping-history order. -/
def orderedPrefixMask (pi : K6EdgeOrder) (r : K6PrefixLength) :
    Fin K6Prefix.graphCount :=
  graphMaskEdgeFinsetEquiv.symm (orderedPrefixEdges pi r)

@[simp] theorem edgeFinsetOfMask_orderedPrefixMask
    (pi : K6EdgeOrder) (r : K6PrefixLength) :
    edgeFinsetOfMask (orderedPrefixMask pi r) = orderedPrefixEdges pi r := by
  exact graphMaskEdgeFinsetEquiv.apply_symm_apply _

@[simp] theorem orderedPrefixPattern_edges
    (pi : K6EdgeOrder) (r : K6PrefixLength) :
    (finitePatternOfMasks fullVertexMask (orderedPrefixMask pi r)).edges =
      orderedPrefixEdges pi r := by
  exact edgeFinsetOfMask_orderedPrefixMask pi r

theorem countBits_eq_card_edgeFinsetOfMask :
    ∀ g : Fin K6Prefix.graphCount,
      K6Prefix.countBits K6Prefix.edgeCount g.1 =
        (edgeFinsetOfMask g).card := by
  native_decide

theorem countBits_orderedPrefixMask (pi : K6EdgeOrder)
    (r : K6PrefixLength) :
    K6Prefix.countBits K6Prefix.edgeCount (orderedPrefixMask pi r).1 =
      r.val := by
  rw [countBits_eq_card_edgeFinsetOfMask,
    edgeFinsetOfMask_orderedPrefixMask, card_orderedPrefixEdges]

/-! ## A history creates one recurrence prefix embedding -/

theorem activeLabels_fullPattern
    (g : Fin K6Prefix.graphCount) :
    activeLabels (finitePatternOfMasks fullVertexMask g) = Finset.univ := by
  ext v
  simp only [mem_activeLabels, Finset.mem_univ, iff_true]
  change fullVertexMask.1.testBit v.1 = true
  fin_cases v <;> native_decide

theorem valid_fullPattern (g : Fin K6Prefix.graphCount) :
    ValidPattern (finitePatternOfMasks fullVertexMask g) := by
  intro e _he
  change edgeAllowedBy fullVertexMask.1 e = true
  fin_cases e <;> native_decide

theorem canonicalMap_fullPattern {N : ℕ} (hN : 0 < N)
    (g : Fin K6Prefix.graphCount) (f : Fin 6 → Vertex N) :
    CanonicalMap hN (finitePatternOfMasks fullVertexMask g) f := by
  intro v hv
  exfalso
  apply hv
  rw [activeLabels_fullPattern]
  exact Finset.mem_univ v

/-- Every one of the prescribed prefix coordinates occurs positively when
`prefixAccept` holds. -/
theorem prefixAccept_edge_mem {N : ℕ}
    (f : Fin 6 ↪ Vertex N) (pi : K6EdgeOrder) (r : K6PrefixLength)
    (h : Transcript (Query N)) (hr : 0 < r.val)
    (ha : prefixAccept f pi r h) (j : Fin r.val) :
    (embeddedEdge f (pi (prefixIndex r j)), true) ∈ h := by
  simp only [prefixAccept, hr, dite_true] at ha
  rcases ha with ⟨tail, rfl, hearlier⟩
  by_cases hj : j.val = r.val - 1
  · have hidx : prefixIndex r j = ⟨r.val - 1, by omega⟩ := by
      apply Fin.ext
      simpa [prefixIndex] using hj
    rw [hidx]
    exact List.mem_cons_self
  · right
    have hjlt : j.val < r.val - 1 := by omega
    have hm := hearlier ⟨j.val, hjlt⟩
    simpa [prefixIndex] using hm

/-- In a no-repeated-query run, a transcript that starts with `q` determines
its time uniquely. -/
theorem time_eq_sub_idxOf_of_run_starts_with
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (strategy : Strategy Q) (board : Board Q) (N t : ℕ)
    (q : Q) (bit : Bool) (tail : Transcript Q)
    (htN : t ≤ N)
    (hnodup : (queries (run strategy board N)).Nodup)
    (hstart : run strategy board t = (q, bit) :: tail) :
    t = N - (queries (run strategy board N)).idxOf q := by
  rcases queries_run_eq_append_of_le strategy board htN with
    ⟨pre, hdecomp, hlen⟩
  have hnappend : (pre ++ queries (run strategy board t)).Nodup := by
    simpa [hdecomp] using hnodup
  have hqtail : q ∈ queries (run strategy board t) := by
    rw [hstart]
    simp [queries]
  have hqpre : q ∉ pre := by
    intro hqp
    exact (List.nodup_append.mp hnappend).2.2 q hqp q hqtail rfl
  rw [hdecomp, List.idxOf_append_of_notMem hqpre, hstart]
  simp only [queries, List.map_cons, List.idxOf_cons_self, Nat.add_zero]
  omega

/-- The time component of a positive prefix-history index carries no
multiplicity: for fixed embedding and order it is unique. -/
theorem prefixHistory_time_unique {N : ℕ}
    (strategy : K6Strategy N) (board : Board (Query N))
    (f : Fin 6 ↪ Vertex N) (pi : K6EdgeOrder) (r : K6PrefixLength)
    (hr : 0 < r.val)
    (hnodup : (queries (run strategy board N)).Nodup)
    (t u : Fin (N + 1))
    (ht : board ∈ prefixHistoryEvent strategy f pi r t.val)
    (hu : board ∈ prefixHistoryEvent strategy f pi r u.val) :
    t = u := by
  have hat := ht.1
  have hau := hu.1
  simp only [prefixAccept, hr, dite_true] at hat hau
  rcases hat with ⟨tail, htail, _⟩
  rcases hau with ⟨tail', htail', _⟩
  have htval := time_eq_sub_idxOf_of_run_starts_with strategy board N t.val
    (embeddedEdge f (pi ⟨r.val - 1, by omega⟩)) true tail
    (Nat.le_of_lt_succ t.isLt) hnodup htail
  have huval := time_eq_sub_idxOf_of_run_starts_with strategy board N u.val
    (embeddedEdge f (pi ⟨r.val - 1, by omega⟩)) true tail'
    (Nat.le_of_lt_succ u.isLt) hnodup htail'
  apply Fin.ext
  exact htval.trans huval.symm

/-- Fixed-board prefix histories for one relative order. -/
abbrev PrefixHistoryIndex {N : ℕ}
    (strategy : K6Strategy N) (board : Board (Query N))
    (pi : K6EdgeOrder) (r : K6PrefixLength) :=
  {z : (Fin 6 ↪ Vertex N) × Fin (N + 1) //
    board ∈ prefixHistoryEvent strategy z.1 pi r z.2.val}

/-- Forgetting the (unique) completion time sends an ordered prefix history
to the corresponding labelled prefix embedding. -/
def prefixHistoryToPrefixEmbedding {N : ℕ}
    (hN : 0 < N) (strategy : K6Strategy N)
    (board : Board (Query N)) (pi : K6EdgeOrder) (r : K6PrefixLength)
    (hr : 0 < r.val) (g : Fin K6Prefix.graphCount)
    (hEdges : (finitePatternOfMasks fullVertexMask g).edges =
      orderedPrefixEdges pi r)
    (hnodup : (queries (run strategy board N)).Nodup) :
    PrefixHistoryIndex strategy board pi r ↪
      PrefixEmbedding hN (finitePatternOfMasks fullVertexMask g)
        (run strategy board N) where
  toFun z := ⟨z.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    valid_fullPattern g,
    canonicalMap_fullPattern hN g z.1.1,
    fun _u _hu _v _hv huv ↦ z.1.1.injective huv,
    by
      intro e he
      have he' : e ∈ orderedPrefixEdges pi r := by
        rw [← hEdges]
        exact he
      rcases (mem_orderedPrefixEdges_iff pi r e).mp he' with ⟨j, hj⟩
      have hprefix := prefixAccept_edge_mem z.1.1 pi r
        (run strategy board z.1.2.val) hr z.2.1 j
      have htN : z.1.2.val ≤ N := Nat.le_of_lt_succ z.1.2.isLt
      rcases run_eq_append_of_le strategy board htN with
        ⟨pre, hrun, _hlen⟩
      have hfull :
          (embeddedEdge z.1.1 (pi (prefixIndex r j)), true) ∈
            run strategy board N := by
        rw [hrun]
        exact List.mem_append_right pre hprefix
      rw [positiveGraph_adj]
      refine ⟨?_, ?_⟩
      · intro huv
        exact (edgeLo_lt_edgeHi e).ne (z.1.1.injective huv)
      · rw [← embeddedEdge_recurrenceToStoppingIndex z.1.1 e, hj]
        exact hfull⟩⟩
  inj' := by
    intro z w hzw
    have hf : z.1.1 = w.1.1 := by
      apply Function.Embedding.ext
      intro v
      exact congrArg
        (fun x : PrefixEmbedding hN (finitePatternOfMasks fullVertexMask g)
          (run strategy board N) ↦ x.1 v) hzw
    have hw := w.2
    rw [← hf] at hw
    have ht : z.1.2 = w.1.2 :=
      prefixHistory_time_unique strategy board z.1.1 pi r hr hnodup
        z.1.2 w.1.2 z.2 hw
    apply Subtype.ext
    exact Prod.ext hf ht

theorem card_prefixHistoryIndex_le_prefixCopyCount {N : ℕ}
    (hN : 0 < N) (strategy : K6Strategy N)
    (board : Board (Query N)) (pi : K6EdgeOrder) (r : K6PrefixLength)
    (hr : 0 < r.val) (g : Fin K6Prefix.graphCount)
    (hEdges : (finitePatternOfMasks fullVertexMask g).edges =
      orderedPrefixEdges pi r)
    (hnodup : (queries (run strategy board N)).Nodup) :
    Fintype.card (PrefixHistoryIndex strategy board pi r) ≤
      prefixCopyCount hN (finitePatternOfMasks fullVertexMask g)
        (run strategy board N) := by
  have hcard := Fintype.card_le_of_injective
    (prefixHistoryToPrefixEmbedding hN strategy board pi r hr g hEdges hnodup)
    (prefixHistoryToPrefixEmbedding hN strategy board pi r hr g hEdges hnodup).injective
  simpa [prefixCopyCount] using hcard

/-! ## Exact mass comparison -/

set_option maxHeartbeats 400000 in
theorem orderPrefixHistoryMass_eq_weightedCount {N : ℕ}
    (p : ℝ≥0∞) (strategy : K6Strategy N)
    (pi : K6EdgeOrder) (r : K6PrefixLength) :
    orderPrefixHistoryMass p strategy pi r =
      ∑ board : Board (Query N),
        boardWeight (bernoulliWeight p) board *
          (Fintype.card (PrefixHistoryIndex strategy board pi r) : ℝ≥0∞) := by
  unfold orderPrefixHistoryMass
  rw [← Fintype.sum_prod_type
    (fun z : (Fin 6 ↪ Vertex N) × Fin (N + 1) ↦
      finiteBoardMass (bernoulliWeight p)
        (prefixHistoryEvent strategy z.1 pi r z.2.val))]
  unfold finiteBoardMass
  simpa using
    (sum_event_weight_eq_weight_mul_card
      (fun board : Board (Query N) ↦ boardWeight (bernoulliWeight p) board)
      (fun z : (Fin 6 ↪ Vertex N) × Fin (N + 1) ↦ fun board ↦
        board ∈ prefixHistoryEvent strategy z.1 pi r z.2.val))

/-- Finite product boards push forward to the product law on the complete
adaptive answer vector, for arbitrary nonnegative observables. -/
theorem boardExpectation_eq_answerVectorSum
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (weight : Bool → ℝ≥0∞) (hnormalized : ∑ bit, weight bit = 1)
    (strategy : Strategy Q) (n : ℕ)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList)
    (X : List.Vector Bool n → ℝ≥0∞) :
    (∑ board : Board Q,
      boardWeight weight board * X (answerVector strategy board n)) =
      ∑ bits : List.Vector Bool n,
        (bits.toList.map weight).prod * X bits := by
  calc
    (∑ board : Board Q,
        boardWeight weight board * X (answerVector strategy board n)) =
        ∑ board : Board Q, ∑ bits : List.Vector Bool n,
          if answerVector strategy board n = bits then
            boardWeight weight board * X bits else 0 := by
      apply Finset.sum_congr rfl
      intro board _hboard
      rw [Fintype.sum_eq_single (answerVector strategy board n)]
      · simp
      · intro bits hne
        have hne' : answerVector strategy board n ≠ bits := hne.symm
        simp [hne']
    _ = ∑ bits : List.Vector Bool n, ∑ board : Board Q,
          if answerVector strategy board n = bits then
            boardWeight weight board * X bits else 0 := Finset.sum_comm
    _ = ∑ bits : List.Vector Bool n,
          (∑ board : Board Q,
            if answerVector strategy board n = bits then
              boardWeight weight board else 0) * X bits := by
      apply Finset.sum_congr rfl
      intro bits _hbits
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro board _hboard
      by_cases hb : answerVector strategy board n = bits <;> simp [hb]
    _ = ∑ bits : List.Vector Bool n,
        (bits.toList.map weight).prod * X bits := by
      apply Finset.sum_congr rfl
      intro bits _hbits
      congr 1
      have hpath := finiteProduct_adaptive_path_mass weight hnormalized
        strategy bits.toList (hfresh bits)
      unfold finiteBoardMass at hpath
      calc
        (∑ board : Board Q,
            if answerVector strategy board n = bits then
              boardWeight weight board else 0) =
            ∑ board : Board Q,
              if board ∈ pathEvent strategy bits.toList then
                boardWeight weight board else 0 := by
          apply Finset.sum_congr rfl
          intro board _hboard
          have hbiff : answerVector strategy board n = bits ↔
              board ∈ pathEvent strategy bits.toList := by
            simpa [vectorPathEvent] using
              (mem_vectorPathEvent_iff strategy board bits).symm
          by_cases hb : answerVector strategy board n = bits
          · simp [hb, hbiff.mp hb]
          · have hnot := mt hbiff.mpr hb
            simp [hb, hnot]
        _ = _ := hpath

theorem coe_strategyExpectedPrefixCopies_eq_answerVectorSum
    (p : ℝ≥0) {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) :
    (strategyExpectedPrefixCopies p hN strategy H : ℝ≥0∞) =
      ∑ bits : List.Vector Bool N,
        (bits.toList.map (bernoulliWeight (p : ℝ≥0∞))).prod *
          (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0∞) := by
  rw [strategyExpectedPrefixCopies_eq_vectorSum]
  push_cast
  apply Finset.sum_congr rfl
  intro bits _hbits
  congr 1
  change ((bits.toList.map (nnBernoulliWeight p)).prod : ℝ≥0∞) = _
  induction bits.toList with
  | nil => simp
  | cons bit tail ih =>
      simp only [List.map_cons, List.prod_cons, ENNReal.coe_mul, ih,
        coe_nnBernoulliWeight]

/-- A fixed relative order contributes at most the genuine expected labelled
prefix-copy count for its recurrence pattern.  There is no time multiplicity
factor: freshness makes the completion time unique. -/
theorem orderPrefixHistoryMass_le_strategyExpectedPrefixCopies
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (pi : K6EdgeOrder) (r : K6PrefixLength) (hr : 0 < r.val)
    (g : Fin K6Prefix.graphCount)
    (hEdges : (finitePatternOfMasks fullVertexMask g).edges =
      orderedPrefixEdges pi r) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy pi r ≤
      (strategyExpectedPrefixCopies p hN strategy
        (finitePatternOfMasks fullVertexMask g) : ℝ≥0∞) := by
  let H := finitePatternOfMasks fullVertexMask g
  rw [orderPrefixHistoryMass_eq_weightedCount]
  calc
    (∑ board : Board (Query N),
        boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
          (Fintype.card (PrefixHistoryIndex strategy board pi r) : ℝ≥0∞)) ≤
        ∑ board : Board (Query N),
          boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
            (prefixCopyCount hN H (run strategy board N) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro board _hboard
      apply mul_le_mul_left'
      exact_mod_cast card_prefixHistoryIndex_le_prefixCopyCount
        hN strategy board pi r hr g hEdges
          (queries_run_nodup_of_freshForBudget strategy hfresh board)
    _ = ∑ bits : List.Vector Bool N,
          (bits.toList.map (bernoulliWeight (p : ℝ≥0∞))).prod *
            (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0∞) := by
      have hpush := boardExpectation_eq_answerVectorSum
        (bernoulliWeight (p : ℝ≥0∞))
        (sum_bernoulliWeight (p : ℝ≥0∞) (by exact_mod_cast hp))
        strategy N hfresh
        (fun bits : List.Vector Bool N ↦
          (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0∞))
      simpa [answerVector_toList, replay_answers_run] using hpush
    _ = (strategyExpectedPrefixCopies p hN strategy H : ℝ≥0∞) :=
      (coe_strategyExpectedPrefixCopies_eq_answerVectorSum
        p hN strategy H).symm

/-- The same bridge to the actual supremal semantic value used by
`finitePrefixSemantics`. -/
theorem orderPrefixHistoryMass_le_extremalExpectedPrefixCopies
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (pi : K6EdgeOrder) (r : K6PrefixLength) (hr : 0 < r.val)
    (g : Fin K6Prefix.graphCount)
    (hEdges : (finitePatternOfMasks fullVertexMask g).edges =
      orderedPrefixEdges pi r) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy pi r ≤
      (extremalExpectedPrefixCopies p hN
        (finitePatternOfMasks fullVertexMask g) : ℝ≥0∞) := by
  exact (orderPrefixHistoryMass_le_strategyExpectedPrefixCopies
    p hp hN strategy hfresh pi r hr g hEdges).trans <| by
      exact_mod_cast strategyExpectedPrefixCopies_le_extremal
        p hp hN strategy hfresh (finitePatternOfMasks fullVertexMask g)

def ninePrefixLength : K6PrefixLength := ⟨9, by omega⟩

@[simp] theorem ninePrefixLength_val : ninePrefixLength.val = 9 := rfl

/-- Canonical fixed-order version: its right side is definitionally the
`value` field of the fully instantiated recurrence semantics. -/
theorem nineEdge_orderPrefixHistoryMass_le_finiteSemanticValue
    (kappa p : ℝ≥0) (hkappa : 1 ≤ kappa) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (pi : K6EdgeOrder) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy pi ninePrefixLength ≤
      ((finitePrefixSemantics kappa p hkappa hp hN).value
        (finitePatternOfMasks fullVertexMask
          (orderedPrefixMask pi ninePrefixLength)) : ℝ≥0∞) := by
  exact orderPrefixHistoryMass_le_extremalExpectedPrefixCopies
    p hp hN strategy hfresh pi ninePrefixLength (by norm_num)
      (orderedPrefixMask pi ninePrefixLength)
      (orderedPrefixPattern_edges pi ninePrefixLength)

/-- Complete ordinary-nine-edge `hcount`: one fixed order's prefix-history
mass is bounded by the checked recurrence certificate, with multiplicity one
and the full accumulated pair tail retained. -/
theorem ordinaryNineEdge_orderPrefixHistoryMass_bound
    (kappa p : ℝ≥0) (hkappa : 1 ≤ kappa) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (pi : K6EdgeOrder)
    (hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask pi ninePrefixLength).1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask
          (orderedPrefixMask pi ninePrefixLength)) a,
      4 ≤ a ∧
      orderPrefixHistoryMass (p : ℝ≥0∞) strategy pi ninePrefixLength ≤
        (Derivation.coefficient (S := k6FinitePrefixSystem) D *
            p ^ 4 * (kappa * (N : ℝ≥0)) ^ 3 +
          Derivation.tail (S := k6FinitePrefixSystem)
            (M := finitePrefixSemantics kappa p hkappa hp hN) D : ℝ≥0) := by
  let g := orderedPrefixMask pi ninePrefixLength
  have hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9 := by
    simpa [g] using countBits_orderedPrefixMask pi ninePrefixLength
  rcases ordinaryNineEdge_finiteSemantic_bound
      kappa p hkappa hp hN g hNine (by simpa [g] using hOrdinary) with
    ⟨a, D, hFour, hvalue⟩
  refine ⟨a, D, hFour, ?_⟩
  refine (nineEdge_orderPrefixHistoryMass_le_finiteSemanticValue
    kappa p hkappa hp hN strategy hfresh pi).trans ?_
  exact_mod_cast hvalue

end
end OrdinaryHistoryCount
end OnlineRamsey
