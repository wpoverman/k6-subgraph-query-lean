import OnlineRamsey.StoppingCoverage
import OnlineRamsey.RecurrenceInstantiation

open scoped BigOperators ENNReal NNReal

namespace OnlineRamsey
namespace StoppingPrefixCount

open QueryComplexity LowerAssembly StoppingHistory StoppingCoverage
  PrefixSoundness RecurrenceInstantiation

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

universe u

theorem finiteProduct_answerVector_weighted_sum
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (strategy : Strategy Q) (n : ℕ) (F : List.Vector Bool n → ℝ≥0∞)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    (∑ board : Board Q,
        boardWeight weight board * F (answerVector strategy board n)) =
      ∑ bits : List.Vector Bool n,
        (bits.toList.map weight).prod * F bits := by
  calc
    (∑ board : Board Q,
        boardWeight weight board * F (answerVector strategy board n)) =
      ∑ board : Board Q, ∑ bits : List.Vector Bool n,
        if answerVector strategy board n = bits then
          boardWeight weight board * F bits else 0 := by
      apply Finset.sum_congr rfl
      intro board _hboard
      rw [Fintype.sum_eq_single (answerVector strategy board n)]
      · simp
      · intro bits hne
        simp [Ne.symm hne]
    _ = ∑ bits : List.Vector Bool n, ∑ board : Board Q,
        if answerVector strategy board n = bits then
          boardWeight weight board * F bits else 0 := Finset.sum_comm
    _ = ∑ bits : List.Vector Bool n,
        (bits.toList.map weight).prod * F bits := by
      apply Finset.sum_congr rfl
      intro bits _hbits
      have hmass := finiteProduct_answerVector_event_mass weight hnormalized
        strategy n (fun bits' ↦ bits' = bits) hfresh
      have hmass' :
          finiteBoardMass weight
              {board | answerVector strategy board n = bits} =
            (bits.toList.map weight).prod := by
        simpa using hmass
      calc
        (∑ board : Board Q,
            if answerVector strategy board n = bits then
              boardWeight weight board * F bits else 0) =
          finiteBoardMass weight
              {board | answerVector strategy board n = bits} * F bits := by
            unfold finiteBoardMass
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro board _hboard
            by_cases hb : answerVector strategy board n = bits
            · simp [hb]
            · simp [hb]
        _ = (bits.toList.map weight).prod * F bits := by rw [hmass']

@[simp] theorem coe_nnBernoulliWeight (p : ℝ≥0) (bit : Bool) :
    (nnBernoulliWeight p bit : ℝ≥0∞) =
      bernoulliWeight (p : ℝ≥0∞) bit := by
  cases bit <;> simp [nnBernoulliWeight, bernoulliWeight, ENNReal.coe_sub]

@[simp] theorem coe_vectorWeight (p : ℝ≥0) {n : ℕ}
    (bits : List.Vector Bool n) :
    (vectorWeight p bits : ℝ≥0∞) =
      (bits.toList.map (bernoulliWeight (p : ℝ≥0∞))).prod := by
  have hlist : ∀ l : List Bool,
      ((l.map (nnBernoulliWeight p)).prod : ℝ≥0∞) =
        (l.map (bernoulliWeight (p : ℝ≥0∞))).prod := by
    intro l
    induction l with
    | nil => simp
    | cons bit l ih => simp [ih]
  exact hlist bits.toList

theorem boardExpectedPrefixCopyCount_eq {N : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (H : K6FinitePattern) :
    (∑ board : Board (Query N),
        boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
          (prefixCopyCount hN H (run strategy board N) : ℝ≥0∞)) =
      (strategyExpectedPrefixCopies p hN strategy H : ℝ≥0∞) := by
  have hpush := finiteProduct_answerVector_weighted_sum
    (bernoulliWeight (p : ℝ≥0∞))
    (sum_bernoulliWeight (p : ℝ≥0∞) (by exact_mod_cast hp))
    strategy N
    (fun bits : List.Vector Bool N ↦
      (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0∞))
    hfresh
  have hrun : ∀ board : Board (Query N),
      replay strategy (answerVector strategy board N).toList =
        run strategy board N := by
    intro board
    exact replay_answers_run strategy board N
  rw [show (∑ board : Board (Query N),
      boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
        (prefixCopyCount hN H (run strategy board N) : ℝ≥0∞)) =
      ∑ board : Board (Query N),
      boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
        (prefixCopyCount hN H
          (replay strategy (answerVector strategy board N).toList) : ℝ≥0∞) by
        apply Finset.sum_congr rfl
        intro board _
        rw [hrun board]]
  rw [hpush]
  have hvec := answerPath_weighted_sum_eq_vectorSum p N
    (fun bits : List Bool ↦
      (prefixCopyCount hN H (replay strategy bits) : ℝ≥0))
  have hcast := congrArg (fun x : ℝ≥0 ↦ (x : ℝ≥0∞)) hvec
  simpa [strategyExpectedPrefixCopies] using hcast.symm

theorem prefixAccept_edge_mem {N : ℕ}
    (f : Fin 6 ↪ Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (h : Transcript (Query N))
    (hr : 0 < r.val) (ha : prefixAccept f π r h)
    (j : Fin r.val) :
    (embeddedEdge f (π (prefixIndex r j)), true) ∈ h := by
  simp only [prefixAccept, hr, dite_true] at ha
  rcases ha with ⟨tail, rfl, hpast⟩
  by_cases hj : j.val = r.val - 1
  · have hindex : prefixIndex r j = ⟨r.val - 1, by omega⟩ := by
      apply Fin.ext
      exact hj
    simp [hindex]
  · have hjlt : j.val < r.val - 1 := by omega
    have hm := hpast ⟨j.val, hjlt⟩
    exact List.mem_cons_of_mem _ (by simpa [prefixIndex] using hm)

theorem prefixAccept_time_eq {N : ℕ}
    (strategy : K6Strategy N) (board : Board (Query N))
    (f : Fin 6 ↪ Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (hr : 0 < r.val)
    (hnodup : (queries (run strategy board N)).Nodup)
    {t : ℕ} (htN : t ≤ N)
    (ha : prefixAccept f π r (run strategy board t)) :
    t = N - (queries (run strategy board N)).idxOf
      (embeddedEdge f (π ⟨r.val - 1, by omega⟩)) := by
  let q := embeddedEdge f (π ⟨r.val - 1, by omega⟩)
  simp only [prefixAccept, hr, dite_true] at ha
  rcases ha with ⟨tail, hrun, _hpast⟩
  have hqueries : queries (run strategy board t) = q :: queries tail := by
    rw [hrun]
    rfl
  have hqtail : q ∈ queries (run strategy board t) := by
    rw [hqueries]
    simp
  rcases queries_run_eq_append_of_le strategy board htN with
    ⟨pre, hdecomp, hlen⟩
  have hnappend : (pre ++ queries (run strategy board t)).Nodup := by
    simpa [hdecomp] using hnodup
  have hqpre : q ∉ pre := by
    intro hqp
    exact (List.nodup_append.mp hnappend).2.2 q hqp q hqtail rfl
  have hidx : (queries (run strategy board N)).idxOf q = pre.length := by
    rw [hdecomp, List.idxOf_append_of_notMem hqpre, hqueries]
    simp
  dsimp [q] at hidx ⊢
  rw [hidx, hlen]
  omega

theorem prefixAccept_time_unique {N : ℕ}
    (strategy : K6Strategy N) (board : Board (Query N))
    (f : Fin 6 ↪ Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (hr : 0 < r.val)
    (hnodup : (queries (run strategy board N)).Nodup)
    {t u : ℕ} (htN : t ≤ N) (huN : u ≤ N)
    (ht : prefixAccept f π r (run strategy board t))
    (hu : prefixAccept f π r (run strategy board u)) :
    t = u := by
  rw [prefixAccept_time_eq strategy board f π r hr hnodup htN ht,
    prefixAccept_time_eq strategy board f π r hr hnodup huN hu]

/-- The executable pattern consists precisely of the first `r` source edges
in the stipulated relative order. -/
def PatternMatchesOrderPrefix (H : K6FinitePattern) (π : K6EdgeOrder)
    (r : K6PrefixLength) : Prop :=
  H.vertices = fullVertexMask ∧
    ∀ d : PrefixSoundness.K6Edge, d ∈ H.edges ↔
      ∃ j : Fin r.val,
        edgeCoord d = (StoppingHistory.edgeEquiv (π (prefixIndex r j))).1

theorem activeLabels_eq_univ_of_matches {H : K6FinitePattern}
    {π : K6EdgeOrder} {r : K6PrefixLength}
    (hmatch : PatternMatchesOrderPrefix H π r) :
    activeLabels H = Finset.univ := by
  ext v
  simp only [mem_activeLabels, Finset.mem_univ, iff_true]
  rw [hmatch.1]
  fin_cases v <;> native_decide

theorem validPattern_of_matches {H : K6FinitePattern}
    {π : K6EdgeOrder} {r : K6PrefixLength}
    (hmatch : PatternMatchesOrderPrefix H π r) :
    ValidPattern H := by
  intro d _hd
  rw [edgeAllowedBy_iff_mem_activeLabels,
    activeLabels_eq_univ_of_matches hmatch]
  simp

theorem isPrefixEmbedding_of_prefixAccept {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (board : Board (Query N))
    (H : K6FinitePattern) (f : Fin 6 ↪ Vertex N) (π : K6EdgeOrder)
    (r : K6PrefixLength) (hr : 0 < r.val)
    (hmatch : PatternMatchesOrderPrefix H π r)
    {t : ℕ} (htN : t ≤ N)
    (ha : prefixAccept f π r (run strategy board t)) :
    IsPrefixEmbedding hN H (run strategy board N) f := by
  have hactive := activeLabels_eq_univ_of_matches hmatch
  refine ⟨validPattern_of_matches hmatch, ?_, ?_, ?_⟩
  · intro v hv
    exfalso
    apply hv
    rw [hactive]
    exact Finset.mem_univ v
  · intro u _hu v _hv huv
    exact f.injective huv
  · intro d hd
    rcases (hmatch.2 d).mp hd with ⟨j, hcoord⟩
    have hedge_t := prefixAccept_edge_mem f π r
      (run strategy board t) hr ha j
    rcases run_eq_append_of_le strategy board htN with
      ⟨pre, hdecomp, _hlen⟩
    have hedge_N :
        (embeddedEdge f (π (prefixIndex r j)), true) ∈
          run strategy board N := by
      rw [hdecomp]
      exact List.mem_append_right pre hedge_t
    have hmapped :
        s(f (edgeLo d), f (edgeHi d)) =
          embeddedEdge f (π (prefixIndex r j)) := by
      have h := congrArg f.sym2Map hcoord
      simpa [edgeCoord, embeddedEdge,
        Function.Embedding.sym2Map_apply] using h
    rw [positiveGraph_adj]
    refine ⟨fun heq ↦ (ne_of_lt (edgeLo_lt_edgeHi d)) (f.injective heq), ?_⟩
    rwa [hmapped]

abbrev PrefixHistoryIndex {N : ℕ}
    (strategy : K6Strategy N) (board : Board (Query N))
    (π : K6EdgeOrder) (r : K6PrefixLength) :=
  {z : CompletionHistoryKey N //
    board ∈ prefixHistoryEvent strategy z.1 π r z.2.val}

def prefixHistoryCount {N : ℕ}
    (strategy : K6Strategy N) (board : Board (Query N))
    (π : K6EdgeOrder) (r : K6PrefixLength) : ℕ :=
  Fintype.card (PrefixHistoryIndex strategy board π r)

set_option maxHeartbeats 400000 in
theorem orderPrefixHistoryMass_eq_weightedCount {N : ℕ}
    (p : ℝ≥0∞) (strategy : K6Strategy N)
    (π : K6EdgeOrder) (r : K6PrefixLength) :
    orderPrefixHistoryMass p strategy π r =
      ∑ board : Board (Query N),
        boardWeight (bernoulliWeight p) board *
          (prefixHistoryCount strategy board π r : ℝ≥0∞) := by
  unfold orderPrefixHistoryMass prefixHistoryCount
  rw [← Fintype.sum_prod_type (fun z : CompletionHistoryKey N ↦
    finiteBoardMass (bernoulliWeight p)
      (prefixHistoryEvent strategy z.1 π r z.2.val))]
  unfold finiteBoardMass
  simpa using
    (sum_event_weight_eq_weight_mul_card
      (fun board : Board (Query N) ↦
        boardWeight (bernoulliWeight p) board)
      (fun z : CompletionHistoryKey N ↦ fun board ↦
        board ∈ prefixHistoryEvent strategy z.1 π r z.2.val))

def prefixHistoryToPrefixEmbedding {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (board : Board (Query N))
    (H : K6FinitePattern) (π : K6EdgeOrder) (r : K6PrefixLength)
    (hr : 0 < r.val) (hmatch : PatternMatchesOrderPrefix H π r)
    (hnodup : (queries (run strategy board N)).Nodup) :
    PrefixHistoryIndex strategy board π r ↪
      PrefixEmbedding hN H (run strategy board N) where
  toFun z := by
    refine ⟨z.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact isPrefixEmbedding_of_prefixAccept hN strategy board H z.1.1 π r
      hr hmatch (Nat.le_of_lt_succ z.1.2.isLt) z.2.1
  inj' := by
    intro z w hzw
    rcases z with ⟨⟨fz, tz⟩, hz⟩
    rcases w with ⟨⟨fw, tw⟩, hw⟩
    have hfun : (fz : Fin 6 → Vertex N) = (fw : Fin 6 → Vertex N) :=
      congrArg (fun x : PrefixEmbedding hN H (run strategy board N) ↦ x.1) hzw
    have hf : fz = fw := by
      apply DFunLike.ext _ _
      exact congrFun hfun
    subst fw
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact prefixAccept_time_unique strategy board fz π r hr hnodup
        (Nat.le_of_lt_succ tz.isLt) (Nat.le_of_lt_succ tw.isLt)
        hz.1 hw.1

theorem card_le_finset_card_of_embedding {A B : Type*}
    [Fintype A] [DecidableEq B] (s : Finset B)
    (f : A ↪ {b : B // b ∈ s}) :
    Fintype.card A ≤ s.card := by
  simpa using Fintype.card_le_of_injective f f.injective

theorem prefixHistoryCount_le_prefixCopyCount {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (board : Board (Query N))
    (H : K6FinitePattern) (π : K6EdgeOrder) (r : K6PrefixLength)
    (hr : 0 < r.val) (hmatch : PatternMatchesOrderPrefix H π r)
    (hnodup : (queries (run strategy board N)).Nodup) :
    prefixHistoryCount strategy board π r ≤
      prefixCopyCount hN H (run strategy board N) := by
  unfold prefixHistoryCount prefixCopyCount
  exact card_le_finset_card_of_embedding
    (prefixEmbeddingFinset hN H (run strategy board N))
    (prefixHistoryToPrefixEmbedding hN strategy board H π r hr hmatch hnodup)

theorem orderPrefixHistoryMass_le_strategyExpectedPrefixCopies {N : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (H : K6FinitePattern) (π : K6EdgeOrder) (r : K6PrefixLength)
    (hr : 0 < r.val) (hmatch : PatternMatchesOrderPrefix H π r) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy π r ≤
      (strategyExpectedPrefixCopies p hN strategy H : ℝ≥0∞) := by
  rw [orderPrefixHistoryMass_eq_weightedCount,
    ← boardExpectedPrefixCopyCount_eq p hp hN strategy hfresh H]
  apply Finset.sum_le_sum
  intro board _hboard
  apply mul_le_mul_left'
  exact Nat.cast_le.mpr
    (prefixHistoryCount_le_prefixCopyCount hN strategy board H π r hr
      hmatch (queries_run_nodup_of_freshForBudget strategy hfresh board))

theorem orderPrefixHistoryMass_le_extremalExpectedPrefixCopies {N : ℕ}
    (p : ℝ≥0) (hp : p ≤ 1) (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (H : K6FinitePattern) (π : K6EdgeOrder) (r : K6PrefixLength)
    (hr : 0 < r.val) (hmatch : PatternMatchesOrderPrefix H π r) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy π r ≤
      (extremalExpectedPrefixCopies p hN H : ℝ≥0∞) := by
  refine (orderPrefixHistoryMass_le_strategyExpectedPrefixCopies
    p hp hN strategy hfresh H π r hr hmatch).trans ?_
  exact_mod_cast strategyExpectedPrefixCopies_le_extremal
    p hp hN strategy hfresh H

/-- Ordinary nine-edge prefix mass bounded by the fully instantiated checked
recurrence certificate. -/
theorem ordinary_orderPrefixHistoryMass_finiteSemantic_bound
    (kappa p : ℝ≥0) (hkappa : 1 ≤ kappa) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder) (g : Fin K6Prefix.graphCount)
    (hmatch : PatternMatchesOrderPrefix
      (finitePatternOfMasks fullVertexMask g) π ⟨9, by decide⟩)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      4 ≤ a ∧
      orderPrefixHistoryMass (p : ℝ≥0∞) strategy π ⟨9, by decide⟩ ≤
        (Derivation.coefficient (S := k6FinitePrefixSystem) D : ℝ≥0∞) *
            (p : ℝ≥0∞) ^ 4 * (kappa * (N : ℝ≥0) : ℝ≥0∞) ^ 3 +
          (Derivation.tail (S := k6FinitePrefixSystem)
            (M := finitePrefixSemantics kappa p hkappa hp hN) D : ℝ≥0∞) := by
  rcases ordinaryNineEdge_finiteSemantic_bound kappa p hkappa hp hN g
      hNine hOrdinary with ⟨a, D, hFour, hvalue⟩
  refine ⟨a, D, hFour,
    (orderPrefixHistoryMass_le_extremalExpectedPrefixCopies p hp hN
      strategy hfresh (finitePatternOfMasks fullVertexMask g) π
      ⟨9, by decide⟩ (by norm_num) hmatch).trans ?_⟩
  exact_mod_cast hvalue

end
end StoppingPrefixCount
end OnlineRamsey
