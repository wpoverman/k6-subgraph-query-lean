import OnlineRamsey.ExceptionalPrefixBounds
import OnlineRamsey.HostGoodProbability

/-!
# Coupling adaptive transcripts to the sampled random host

For the canonical finite query game, the pre-sampled Boolean board is itself
a `G(2N,p)` host.  This module records the exact bridges needed to split an
adaptive prefix expectation into good-host and bad-host contributions.
-/

open scoped BigOperators ENNReal NNReal

namespace OnlineRamsey
namespace AdaptiveHostTruncation

open QueryComplexity PrefixSoundness RecurrenceInstantiation AsymptoticScale

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-- The native product measure of a singleton board is its explicit finite
product weight. -/
theorem bitBoardMeasure_singleton_eq_boardWeight
    {E : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (board : Board E) :
    RandomBoard.bitBoardMeasure E p {board} =
      boardWeight (bernoulliWeight
        (unitInterval.toNNReal p : ℝ≥0∞)) board := by
  have hsingleton : ({board} : Set (Board E)) =
      Set.univ.pi (fun e : E => ({board e} : Set Bool)) := by
    ext other
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_setOf_eq]
    exact ⟨fun h e => congrFun h e, fun h => funext h⟩
  rw [hsingleton, RandomBoard.bitBoardMeasure, MeasureTheory.Measure.pi_pi]
  simp [boardWeight, RandomBoard.bernoulliBit_singleton]

/-- On a finite board, the measure-theoretic product law agrees exactly with
the explicit sum used by the adaptive-query semantics, for every event. -/
theorem bitBoardMeasure_eq_finiteBoardMass
    {E : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (event : Set (Board E)) :
    RandomBoard.bitBoardMeasure E p event =
      finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal p : ℝ≥0∞)) event := by
  classical
  let s : Finset (Board E) := Set.toFinite event |>.toFinset
  have hs : (s : Set (Board E)) = event := by
    exact Set.Finite.coe_toFinset (Set.toFinite event)
  calc
    RandomBoard.bitBoardMeasure E p event =
        RandomBoard.bitBoardMeasure E p (s : Set (Board E)) := by rw [hs]
    _ = ∑ board ∈ s, RandomBoard.bitBoardMeasure E p {board} := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = ∑ board ∈ s,
        boardWeight (bernoulliWeight
          (unitInterval.toNNReal p : ℝ≥0∞)) board := by
      apply Finset.sum_congr rfl
      intro board _
      rw [bitBoardMeasure_singleton_eq_boardWeight]
    _ = finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal p : ℝ≥0∞)) event := by
      unfold finiteBoardMass
      rw [← hs]
      simp

/-- Exact push-forward identity for a nonnegative statistic of the complete
adaptive answer vector. -/
theorem finiteProduct_answerVector_weighted_sum
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (strategy : Strategy Q) (n : ℕ) (F : List.Vector Bool n → ℝ≥0∞)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    (∑ board : Board Q,
        boardWeight weight board * F (answerVector strategy board n)) =
      ∑ bits : List.Vector Bool n,
        (bits.toList.map weight).prod * F bits := by
  classical
  calc
    _ = ∑ board : Board Q, ∑ bits : List.Vector Bool n,
          if board ∈ vectorPathEvent strategy bits then
            boardWeight weight board * F bits else 0 := by
      apply Finset.sum_congr rfl
      intro board _
      rw [Fintype.sum_eq_single (answerVector strategy board n)]
      · simp [mem_vectorPathEvent_iff]
      · intro bits hne
        have hnotmem : board ∉ vectorPathEvent strategy bits := by
          intro hmem
          apply hne
          exact (mem_vectorPathEvent_iff strategy board bits).mp hmem |>.symm
        simp [hnotmem]
    _ = ∑ bits : List.Vector Bool n, ∑ board : Board Q,
          if board ∈ vectorPathEvent strategy bits then
            boardWeight weight board * F bits else 0 := Finset.sum_comm
    _ = ∑ bits : List.Vector Bool n,
        (bits.toList.map weight).prod * F bits := by
      apply Finset.sum_congr rfl
      intro bits _
      have hpath := finiteProduct_adaptive_path_mass weight hnormalized
        strategy bits.toList (hfresh bits)
      calc
        (∑ board : Board Q,
            if board ∈ vectorPathEvent strategy bits then
              boardWeight weight board * F bits else 0) =
            (∑ board : Board Q,
              if board ∈ vectorPathEvent strategy bits then
                boardWeight weight board else 0) * F bits := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro board _
              by_cases hmem : board ∈ vectorPathEvent strategy bits <;>
                simp [hmem]
        _ = (bits.toList.map weight).prod * F bits := by
          exact congrArg (fun x => x * F bits) hpath

private theorem prod_bernoulliWeight_eq_coe_nn
    (p : ℝ≥0) (bits : List Bool) :
    (bits.map (bernoulliWeight (p : ℝ≥0∞))).prod =
      ((bits.map (nnBernoulliWeight p)).prod : ℝ≥0∞) := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
      simp only [List.map_cons, List.prod_cons]
      change bernoulliWeight (p : ℝ≥0∞) bit *
          (bits.map (bernoulliWeight (p : ℝ≥0∞))).prod =
        (nnBernoulliWeight p bit : ℝ≥0∞) *
          ((bits.map (nnBernoulliWeight p)).prod : ℝ≥0∞)
      rw [coe_nnBernoulliWeight, ih]

/-- Board-sum form of the executable prefix expectation. -/
theorem strategyExpectedPrefixCopies_coe_eq_boardSum
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (H : K6FinitePattern) :
    (strategyExpectedPrefixCopies p hN strategy H : ℝ≥0∞) =
      ∑ board : Board (Query N),
        boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
          (prefixCopyCount hN H (run strategy board N) : ℝ≥0∞) := by
  rw [strategyExpectedPrefixCopies_eq_vectorSum]
  push_cast
  have hpush := finiteProduct_answerVector_weighted_sum
    (bernoulliWeight (p : ℝ≥0∞))
    (sum_bernoulliWeight (p : ℝ≥0∞) (by exact_mod_cast hp))
    strategy N (fun bits =>
      (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0∞))
    (fun bits =>
      freshPath_of_freshForBudget strategy hfresh bits.toList (by simp))
  symm
  calc
    (∑ board : Board (Query N),
        boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
          (prefixCopyCount hN H (run strategy board N) : ℝ≥0∞)) =
      ∑ board : Board (Query N),
        boardWeight (bernoulliWeight (p : ℝ≥0∞)) board *
          (prefixCopyCount hN H
            (replay strategy (answerVector strategy board N).toList) : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro board _
      rw [answerVector_toList, replay_answers_run]
    _ = ∑ bits : List.Vector Bool N,
        (bits.toList.map (bernoulliWeight (p : ℝ≥0∞))).prod *
          (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0∞) := hpush
    _ = ∑ bits : List.Vector Bool N,
        (vectorWeight p bits : ℝ≥0∞) *
          (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro bits _
      congr 1
      exact prod_bernoulliWeight_eq_coe_nn p bits.toList

/-- Every positive edge revealed by a strategy is an edge of the board graph
from which its answer was read. -/
theorem positiveGraph_run_le_randomHost {N n : ℕ}
    (strategy : K6Strategy N) (board : Board (Query N)) :
    positiveGraph (run strategy board n) ≤
      RandomBoard.randomHost (2 * N) board := by
  intro u v huv
  rw [positiveGraph_adj] at huv
  rw [RandomBoard.randomHost_adj]
  refine ⟨?_, huv.1⟩
  exact consistent_run strategy board n _ huv.2

/-! ## Finite good/bad truncation -/

theorem finiteBoardMass_mono {E : Type*} [Fintype E] [DecidableEq E]
    (weight : Bool → ℝ≥0∞) {A B : Set (Board E)} (hAB : A ⊆ B) :
    finiteBoardMass weight A ≤ finiteBoardMass weight B := by
  unfold finiteBoardMass
  apply Finset.sum_le_sum
  intro board _
  by_cases hA : board ∈ A
  · simp [hA, hAB hA]
  · simp [hA]

theorem finiteBoardMass_union_le {E : Type*} [Fintype E] [DecidableEq E]
    (weight : Bool → ℝ≥0∞) (A B : Set (Board E)) :
    finiteBoardMass weight (A ∪ B) ≤
      finiteBoardMass weight A + finiteBoardMass weight B := by
  unfold finiteBoardMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro board _
  by_cases hA : board ∈ A <;> by_cases hB : board ∈ B <;>
    simp [hA, hB]

/-- De Morgan's union bound, factored generically so that large concrete
events do not get unfolded by elaboration. -/
theorem finiteBoardMass_inter_compl_le {E : Type*} [Fintype E] [DecidableEq E]
    (weight : Bool → ℝ≥0∞) (A B : Set (Board E)) :
    finiteBoardMass weight (A ∩ B)ᶜ ≤
      finiteBoardMass weight Aᶜ + finiteBoardMass weight Bᶜ := by
  have hsubset : (A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ := by
    intro board hboard
    by_cases hA : board ∈ A
    · right
      exact fun hB ↦ hboard ⟨hA, hB⟩
    · exact Or.inl hA
  exact (finiteBoardMass_mono weight hsubset).trans
    (finiteBoardMass_union_le weight Aᶜ Bᶜ)

/-- A bounded statistic costs its good-event bound plus its crude bound
times the bad-event probability. -/
theorem weightedCount_le_goodBound_add_badMass
    {E : Type*} [Fintype E] [DecidableEq E]
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (count : Board E → ℕ) (good : Set (Board E)) (B R : ℕ)
    (hgood : ∀ board ∈ good, count board ≤ B)
    (hcrude : ∀ board, count board ≤ R) :
    (∑ board : Board E, boardWeight weight board * (count board : ℝ≥0∞)) ≤
      (B : ℝ≥0∞) + (R : ℝ≥0∞) * finiteBoardMass weight goodᶜ := by
  calc
    (∑ board : Board E,
        boardWeight weight board * (count board : ℝ≥0∞)) ≤
      ∑ board : Board E, boardWeight weight board *
        ((B : ℝ≥0∞) + if board ∈ goodᶜ then (R : ℝ≥0∞) else 0) := by
      apply Finset.sum_le_sum
      intro board _
      apply mul_le_mul_left'
      by_cases hg : board ∈ good
      · have hc : (count board : ℝ≥0∞) ≤ B := by exact_mod_cast hgood board hg
        simpa [hg] using hc
      · have hc : (count board : ℝ≥0∞) ≤ R := by exact_mod_cast hcrude board
        exact hc.trans (by simp [hg])
    _ = (B : ℝ≥0∞) +
        (R : ℝ≥0∞) * finiteBoardMass weight goodᶜ := by
      have htotal : (∑ board : Board E, boardWeight weight board) = 1 :=
        sum_boardWeight weight hnormalized
      calc
        (∑ board : Board E, boardWeight weight board *
            ((B : ℝ≥0∞) + if board ∈ goodᶜ then (R : ℝ≥0∞) else 0)) =
          (∑ board : Board E, boardWeight weight board) * (B : ℝ≥0∞) +
            ∑ board : Board E, boardWeight weight board *
              (if board ∈ goodᶜ then (R : ℝ≥0∞) else 0) := by
            simp only [mul_add, Finset.sum_add_distrib]
            rw [Finset.sum_mul]
        _ = (B : ℝ≥0∞) +
            ∑ board : Board E, boardWeight weight board *
              (if board ∈ goodᶜ then (R : ℝ≥0∞) else 0) := by
            rw [htotal, one_mul]
        _ = (B : ℝ≥0∞) +
            (R : ℝ≥0∞) * finiteBoardMass weight goodᶜ := by
            congr 1
            unfold finiteBoardMass
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro board _
            by_cases hbad : board ∈ goodᶜ <;> simp [hbad, mul_comm]

/-- Boards on which the final positive transcript stays within the prescribed
edge budget. -/
def transcriptEdgeGoodEvent {N : ℕ} (strategy : K6Strategy N) (M : ℕ) :
    Set (Board (Query N)) :=
  {board | edgeCount (positiveGraph (run strategy board N)) ≤ M}

/-- Failure of the transcript edge budget forces the corresponding adaptive
binomial upper-tail event. -/
theorem transcriptEdgeGoodEvent_compl_subset_upperTail {N M : ℕ}
    (strategy : K6Strategy N) :
    (transcriptEdgeGoodEvent strategy M)ᶜ ⊆
      adaptiveUpperTailEvent strategy N (M + 1) := by
  intro board hbad
  change ¬edgeCount (positiveGraph (run strategy board N)) ≤ M at hbad
  change M + 1 ≤ trueAnswerCount strategy board N
  have hedge : edgeCount (positiveGraph (run strategy board N)) ≤
      trueAnswerCount strategy board N := by
    simpa [edgeCount, trueAnswerCount] using
      positiveGraph_edgeCount_le_trueCount (run strategy board N)
  omega

/-- Exact adaptive binomial control of edge-budget failure. -/
theorem transcriptEdgeGoodEvent_compl_mass_le {N M : ℕ}
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : K6Strategy N)
    (hfresh : FreshForBudget strategy) :
    finiteBoardMass (bernoulliWeight p)
        (transcriptEdgeGoodEvent strategy M)ᶜ ≤
      bernoulliUpperTail p N (M + 1) := by
  calc
    finiteBoardMass (bernoulliWeight p)
        (transcriptEdgeGoodEvent strategy M)ᶜ ≤
      finiteBoardMass (bernoulliWeight p)
        (adaptiveUpperTailEvent strategy N (M + 1)) := by
      unfold finiteBoardMass
      apply Finset.sum_le_sum
      intro board _
      by_cases hbad : board ∈ (transcriptEdgeGoodEvent strategy M)ᶜ
      · have htail := transcriptEdgeGoodEvent_compl_subset_upperTail
          strategy hbad
        simp [hbad, htail]
      · simp [hbad]
    _ = bernoulliUpperTail p N (M + 1) :=
      bernoulli_adaptiveUpperTail_mass p hp strategy N (M + 1)
        (fun bits => hfresh bits)

/-- The complement of simultaneous host and transcript goodness is bounded
by the two individual bad-event masses.  The generic De Morgan estimate is
kept opaque here; this prevents the large `HostGood` predicate from being
expanded during elaboration. -/
theorem hostEdgeGood_compl_mass_le {N M D L c₂ c₃ : ℕ}
    (p : unitInterval) (strategy : K6Strategy N)
    (hfresh : FreshForBudget strategy) :
    finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal p : ℝ≥0∞))
        (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃ ∩
          transcriptEdgeGoodEvent strategy M)ᶜ ≤
      RandomBoard.bitBoardMeasure (Query N) p
          (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃)ᶜ +
        bernoulliUpperTail (unitInterval.toNNReal p : ℝ≥0∞) N (M + 1) := by
  letI : DecidableEq (Query N) :=
    @Sym2.instDecidableEq (Fin (2 * N)) (instDecidableEqFin _)
  let weight : Bool → ℝ≥0∞ :=
    bernoulliWeight (unitInterval.toNNReal p : ℝ≥0∞)
  let hostGood : Set (Board (Query N)) :=
    RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃
  let edgeGood : Set (Board (Query N)) :=
    transcriptEdgeGoodEvent strategy M
  have hinter := finiteBoardMass_inter_compl_le weight hostGood edgeGood
  have hhost : finiteBoardMass weight hostGoodᶜ =
      RandomBoard.bitBoardMeasure (Query N) p hostGoodᶜ := by
    symm
    exact bitBoardMeasure_eq_finiteBoardMass p hostGoodᶜ
  have hedge : finiteBoardMass weight edgeGoodᶜ ≤
      bernoulliUpperTail (unitInterval.toNNReal p : ℝ≥0∞) N (M + 1) := by
    exact transcriptEdgeGoodEvent_compl_mass_le
      (unitInterval.toNNReal p : ℝ≥0∞)
      (by exact_mod_cast RandomBoard.toNNReal_le_one p) strategy hfresh
  dsimp only [weight, hostGood, edgeGood] at hinter hhost hedge ⊢
  calc
    finiteBoardMass (bernoulliWeight
        (unitInterval.toNNReal p : ℝ≥0∞))
        (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃ ∩
          transcriptEdgeGoodEvent strategy M)ᶜ ≤
      finiteBoardMass (bernoulliWeight
          (unitInterval.toNNReal p : ℝ≥0∞))
          (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃)ᶜ +
        finiteBoardMass (bernoulliWeight
          (unitInterval.toNNReal p : ℝ≥0∞))
          (transcriptEdgeGoodEvent strategy M)ᶜ := by
      simpa only using hinter
    _ = RandomBoard.bitBoardMeasure (Query N) p
          (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃)ᶜ +
        finiteBoardMass (bernoulliWeight
          (unitInterval.toNNReal p : ℝ≥0∞))
          (transcriptEdgeGoodEvent strategy M)ᶜ := by
      exact congrArg (fun x ↦ x + finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal p : ℝ≥0∞))
        (transcriptEdgeGoodEvent strategy M)ᶜ) hhost
    _ ≤ RandomBoard.bitBoardMeasure (Query N) p
          (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃)ᶜ +
        bernoulliUpperTail (unitInterval.toNNReal p : ℝ≥0∞) N (M + 1) :=
      add_le_add_left hedge _

/-! ## Numeric cubic-scale specialization -/

/-- The rounded edge budget is at least the least integer strictly above
`8 p N`, for the cubic substitution `p=q³`. -/
theorem numericPairThreshold_le_edgeBudget_add_one
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (N : ℕ) :
    pairThreshold 8 (unitInterval.toNNReal
      (HostGoodProbability.cubeProbability q hq.le hq1)) N ≤
        edgeBudget q 8 N + 1 := by
  unfold pairThreshold edgeBudget
  apply Nat.add_le_add_right
  change ⌊(8 : ℝ) * q ^ 3 * (N : ℝ)⌋₊ ≤
    ⌈(8 : ℝ) * q ^ 3 * (N : ℝ)⌉₊
  calc
    ⌊(8 : ℝ) * q ^ 3 * (N : ℝ)⌋₊ ≤
        ⌊(⌈(8 : ℝ) * q ^ 3 * (N : ℝ)⌉₊ : ℝ)⌋₊ := by
      apply Nat.floor_le_floor
      exact Nat.le_ceil _
    _ = ⌈(8 : ℝ) * q ^ 3 * (N : ℝ)⌉₊ := by simp

/-- At arbitrary normalized query scale `ell`, simultaneous host and
adaptive-edge failure is bounded by the sampled-host failure plus the exact
pair bad mass.  All floor/ceiling effects are included. -/
theorem scaledHostEdgeGood_compl_mass_le_pairBadMass
    {q ell A B₂ B₃ : ℝ} {L : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy) :
    let N := queryBudget q ell
    let pUI := HostGoodProbability.cubeProbability q hq.le hq1
    let M := edgeBudget q 8 N
    let D := degeneracyBudget q A M
    let c₂ := HostGoodProbability.scaledPairBound q B₂ N
    let c₃ := HostGoodProbability.scaledTripleBound q B₃ N
    finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal pUI : ℝ≥0∞))
        (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃ ∩
          transcriptEdgeGoodEvent strategy M)ᶜ ≤
      RandomBoard.bitBoardMeasure (Query N) pUI
          (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃)ᶜ +
        (pairBadMass 8 (unitInterval.toNNReal pUI) N : ℝ≥0∞) := by
  dsimp only
  let pUI := HostGoodProbability.cubeProbability q hq.le hq1
  let N := queryBudget q ell
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q A M
  let c₂ := HostGoodProbability.scaledPairBound q B₂ N
  let c₃ := HostGoodProbability.scaledTripleBound q B₃ N
  let p : ℝ≥0 := unitInterval.toNNReal pUI
  have hmain := hostEdgeGood_compl_mass_le
    (N := N) (M := M) (D := D) (L := L) (c₂ := c₂) (c₃ := c₃)
    pUI strategy hfresh
  have hthreshold : pairThreshold 8 p N ≤ M + 1 := by
    simpa [p, pUI, M, N] using
      numericPairThreshold_le_edgeBudget_add_one hq hq1 N
  have htail : bernoulliUpperTail (p : ℝ≥0∞) N (M + 1) ≤
      (pairBadMass 8 p N : ℝ≥0∞) :=
    bernoulliUpperTail_le_coe_pairBadMass 8 p N _ hthreshold
  dsimp only [pUI, N, M, D, c₂, c₃, p] at hmain htail ⊢
  exact hmain.trans (add_le_add_left htail _)

/-- The preceding generic bound after applying the crude number `(2N)^6`
of labelled maps.  The adaptive term is exactly the already-formalized
`pairTail`. -/
theorem scaledHostEdgeGood_crudeSixVertex_le
    {q ell A B₂ B₃ : ℝ} {L : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy) (H : K6FinitePattern) :
    let N := queryBudget q ell
    let pUI := HostGoodProbability.cubeProbability q hq.le hq1
    let M := edgeBudget q 8 N
    let D := degeneracyBudget q A M
    let c₂ := HostGoodProbability.scaledPairBound q B₂ N
    let c₃ := HostGoodProbability.scaledTripleBound q B₃ N
    (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
      finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal pUI : ℝ≥0∞))
        (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃ ∩
          transcriptEdgeGoodEvent strategy M)ᶜ ≤
      (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
        RandomBoard.bitBoardMeasure (Query N) pUI
          (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃)ᶜ +
        (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞) := by
  dsimp only
  let N := queryBudget q ell
  let pUI := HostGoodProbability.cubeProbability q hq.le hq1
  let crude : ℝ≥0∞ := (((2 * N) ^ 6 : ℕ) : ℝ≥0∞)
  have hmain := scaledHostEdgeGood_compl_mass_le_pairBadMass
    (ell := ell) (A := A) (B₂ := B₂) (B₃ := B₃) (L := L)
    hq hq1 strategy hfresh
  have hmul := mul_le_mul_left' hmain crude
  rw [mul_add] at hmul
  dsimp only at hmain
  dsimp only [N, pUI, crude] at hmul ⊢
  simpa [pairTail] using hmul

/-- The binomial overflow at the rounded edge budget has the same geometric
half-power decay as the finite pair recurrence. -/
theorem numericBernoulliUpperTail_le_halfPow
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (N : ℕ) :
    bernoulliUpperTail
        (unitInterval.toNNReal
          (HostGoodProbability.cubeProbability q hq.le hq1) : ℝ≥0∞)
        N (edgeBudget q 8 N + 1) ≤
      (((2 : ℝ≥0)⁻¹ ^ pairThreshold 8
        (unitInterval.toNNReal
          (HostGoodProbability.cubeProbability q hq.le hq1)) N : ℝ≥0) : ℝ≥0∞) := by
  let p : ℝ≥0 := unitInterval.toNNReal
    (HostGoodProbability.cubeProbability q hq.le hq1)
  have hp : p ≤ 1 := RandomBoard.toNNReal_le_one _
  have hthreshold : pairThreshold 8 p N ≤ edgeBudget q 8 N + 1 := by
    simpa [p] using numericPairThreshold_le_edgeBudget_add_one hq hq1 N
  have hpair : bernoulliUpperTail (p : ℝ≥0∞) N
      (edgeBudget q 8 N + 1) ≤ (pairBadMass 8 p N : ℝ≥0∞) :=
    bernoulliUpperTail_le_coe_pairBadMass 8 p N _ hthreshold
  have hhalfNN := pairBadMass_eight_le_half_pow p hp N
  have hhalf : (pairBadMass 8 p N : ℝ≥0∞) ≤
      (((2 : ℝ≥0)⁻¹ ^ pairThreshold 8 p N : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hhalfNN
  simpa [p] using hpair.trans hhalf

/-- The adaptive positive-edge overflow at the paper's rounded budget has
the same geometric half-power decay as the finite pair recurrence. -/
theorem numericTranscriptEdgeBadMass_le_halfPow
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {N : ℕ}
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy) :
    finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal
          (HostGoodProbability.cubeProbability q hq.le hq1) : ℝ≥0∞))
        (transcriptEdgeGoodEvent strategy (edgeBudget q 8 N))ᶜ ≤
      (((2 : ℝ≥0)⁻¹ ^ pairThreshold 8
        (unitInterval.toNNReal
          (HostGoodProbability.cubeProbability q hq.le hq1)) N : ℝ≥0) : ℝ≥0∞) := by
  have hmass := transcriptEdgeGoodEvent_compl_mass_le
    (unitInterval.toNNReal
      (HostGoodProbability.cubeProbability q hq.le hq1) : ℝ≥0∞)
    (by
      exact_mod_cast RandomBoard.toNNReal_le_one
        (HostGoodProbability.cubeProbability q hq.le hq1)) strategy hfresh
      (M := edgeBudget q 8 N)
  exact hmass.trans (numericBernoulliUpperTail_le_halfPow hq hq1 N)

/-- Fully instantiated simultaneous host/transcript bad-mass estimate.  The
first term is the explicit `q^70` random-host error, while the second is the
adaptive binomial overflow. -/
theorem numericHostEdgeGood_compl_mass_le
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 10000)
    (strategy : K6Strategy (queryBudget q 1))
    (hfresh : FreshForBudget strategy) :
    finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal
          (HostGoodProbability.cubeProbability q hq.le
            (hqsmall.le.trans (by norm_num))) : ℝ≥0∞))
        (RandomBoard.randomHostGoodEvent (2 * queryBudget q 1)
          (edgeBudget q 8 (queryBudget q 1))
          (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 90
          (HostGoodProbability.scaledPairBound q 12 (queryBudget q 1))
          (HostGoodProbability.scaledTripleBound q 512 (queryBudget q 1)) ∩
        transcriptEdgeGoodEvent strategy
          (edgeBudget q 8 (queryBudget q 1)))ᶜ ≤
      ENNReal.ofReal (q ^ 70) +
        (((2 : ℝ≥0)⁻¹ ^ pairThreshold 8
          (unitInterval.toNNReal (HostGoodProbability.cubeProbability q hq.le
            (hqsmall.le.trans (by norm_num)))) (queryBudget q 1) : ℝ≥0) : ℝ≥0∞) := by
  let pUI := HostGoodProbability.cubeProbability q hq.le
    (hqsmall.le.trans (by norm_num))
  let N := queryBudget q 1
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := HostGoodProbability.scaledPairBound q 12 N
  let c₃ := HostGoodProbability.scaledTripleBound q 512 N
  have hmain := hostEdgeGood_compl_mass_le
    (N := N) (M := M) (D := D) (L := 90) (c₂ := c₂) (c₃ := c₃)
    pUI strategy hfresh
  have hhost :=
    HostGoodProbability.measure_numericRandomHostGoodEvent_c8_compl_le_ofReal_q70
      hq hqsmall
  have hedge := numericBernoulliUpperTail_le_halfPow hq
    (hqsmall.le.trans (by norm_num)) N
  dsimp only [pUI, N, M, D, c₂, c₃] at hmain hhost hedge ⊢
  exact hmain.trans (add_le_add hhost hedge)

/-- The numeric simultaneous bad mass after the crude six-vertex map count
has been applied.  This is the exact error term consumed by each exceptional
prefix estimate. -/
theorem numericHostEdgeGood_crudeSixVertex_le
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 10000)
    (strategy : K6Strategy (queryBudget q 1))
    (hfresh : FreshForBudget strategy) :
    (((2 * queryBudget q 1) ^ 6 : ℕ) : ℝ≥0∞) *
      finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal
          (HostGoodProbability.cubeProbability q hq.le
            (hqsmall.le.trans (by norm_num))) : ℝ≥0∞))
        (RandomBoard.randomHostGoodEvent (2 * queryBudget q 1)
          (edgeBudget q 8 (queryBudget q 1))
          (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 90
          (HostGoodProbability.scaledPairBound q 12 (queryBudget q 1))
          (HostGoodProbability.scaledTripleBound q 512 (queryBudget q 1)) ∩
        transcriptEdgeGoodEvent strategy
          (edgeBudget q 8 (queryBudget q 1)))ᶜ ≤
      ENNReal.ofReal (64 * q ^ 10) +
        (((2 * queryBudget q 1) ^ 6 : ℕ) : ℝ≥0∞) *
          (((2 : ℝ≥0)⁻¹ ^ pairThreshold 8
            (unitInterval.toNNReal (HostGoodProbability.cubeProbability q hq.le
              (hqsmall.le.trans (by norm_num))))
              (queryBudget q 1) : ℝ≥0) : ℝ≥0∞) := by
  let pUI := HostGoodProbability.cubeProbability q hq.le
    (hqsmall.le.trans (by norm_num))
  let N := queryBudget q 1
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := HostGoodProbability.scaledPairBound q 12 N
  let c₃ := HostGoodProbability.scaledTripleBound q 512 N
  let crude : ℝ≥0∞ := (((2 * N) ^ 6 : ℕ) : ℝ≥0∞)
  have hmain := hostEdgeGood_compl_mass_le
    (N := N) (M := M) (D := D) (L := 90) (c₂ := c₂) (c₃ := c₃)
    pUI strategy hfresh
  have hhost :=
    HostGoodProbability.measure_numericRandomHostGoodEvent_c8_crudeSixVertex_le_ofReal
      hq hqsmall
  have hedge := numericBernoulliUpperTail_le_halfPow hq
    (hqsmall.le.trans (by norm_num)) N
  have hmul := mul_le_mul_left' hmain crude
  rw [mul_add] at hmul
  dsimp only [pUI, N, M, D, c₂, c₃, crude] at hmul hhost hedge ⊢
  exact hmul.trans (add_le_add hhost (mul_le_mul_left' hedge _))

end
end AdaptiveHostTruncation
end OnlineRamsey
