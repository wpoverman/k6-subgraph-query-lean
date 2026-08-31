import OnlineRamsey.SlackBranchReady
import OnlineRamsey.UpperProbabilityAssembly

/-!
# Deterministic assembly of the slack upper-strategy certificate

This file isolates the two pathwise facts needed after the probabilistic
supply event has occurred: legality of the proposed replay, and domination
of each raw branch scan by the completed allocator scan.
-/

namespace OnlineRamsey
namespace UpperDeterministicAssembly

open QueryComplexity UpperStrategy UpperProbabilityAssembly

noncomputable section

private theorem replay_nodup_of_proposedPathLegal
    {N : ℕ} (proposed : K6Strategy N) (bits : List Bool)
    (hlegal : ProposedPathLegal proposed bits) :
    (queries (replay proposed bits)).Nodup := by
  induction bits with
  | nil => simp [replay, queries]
  | cons bit tail ih =>
      rcases hlegal with ⟨⟨_nonloop, hfresh⟩, htail⟩
      simp only [replay_cons, queries, List.map_cons, List.nodup_cons]
      exact ⟨hfresh, ih htail⟩

private theorem replay_nonloop_of_proposedPathLegal
    {N : ℕ} (proposed : K6Strategy N) (bits : List Bool)
    (hlegal : ProposedPathLegal proposed bits) :
    ∀ q ∈ queries (replay proposed bits), ¬q.IsDiag := by
  induction bits with
  | nil => simp [replay, queries]
  | cons bit tail ih =>
      rcases hlegal with ⟨⟨hnonloop, _fresh⟩, htail⟩
      intro q hq
      simp only [replay_cons, queries, List.map_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hnonloop
      · exact ih htail q hq

/-- Star supply and allocator readiness make the complete branch-and-fill
path legal.  The proof embeds all fill queries and all older star/branch
queries into different summands of the same `SlackQueryGeometry`. -/
theorem proposedPathLegal_of_starSupply_of_branchReady
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a
        (slackBranchAnswerVector a bits)).toList.count true)
    (hbranch : slackTrialCount a ≤
      (successfulBranchFills a ha
        (replay (proposedSlackStrategy a ha)
          (slackBranchAnswerVector a bits).toList)).length) :
    ProposedPathLegal (proposedSlackStrategy a ha) bits.toList := by
  let base := slackBranchAnswerVector a bits
  let fill := slackFillAnswerVector a bits
  let hbase := replay (proposedSlackStrategy a ha) base.toList
  have hres : slackReservoirSize a ≤
      (positiveStarIndices a ha hbase).length := by
    exact reservoir_ready_of_baseStar_trueCount a ha base hstar
  let g := UpperPathGeometry.readySlackQueryGeometry a ha hbase hres hbranch
  have hbaseLegal : ProposedPathLegal
      (proposedSlackStrategy a ha) base.toList :=
    UpperPathGeometry.proposedPathLegal_branchStar_of_starSupply
      a ha base hstar
  have hbaseNodup : (queries hbase).Nodup := by
    exact replay_nodup_of_proposedPathLegal
      (proposedSlackStrategy a ha) base.toList hbaseLegal
  have hbaseNonloop : ∀ q ∈ queries hbase, ¬q.IsDiag := by
    exact replay_nonloop_of_proposedPathLegal
      (proposedSlackStrategy a ha) base.toList hbaseLegal
  have hfillList : fill.toList = List.ofFn fill.get := by
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  let hfill := replay (slackFillContinuation a ha hbase) fill.toList
  have hfillReplay : hfill =
      List.ofFn (fun j ↦ (slackFillQuery a ha hbase j, fill.get j)) := by
    dsimp only [hfill]
    rw [hfillList]
    exact replay_slackFillContinuation_ofFn a ha hbase fill.get
  have hfillQueries : queries hfill =
      List.ofFn (slackFillQuery a ha hbase) := by
    rw [hfillReplay]
    simp only [queries, List.map_ofFn, Function.comp_def]
  have hfillGeom (j : Fin (slackFillQueryCount a)) :
      slackFillQuery a ha hbase j =
        g.query (Sum.inr (Sum.inr (slackFillCoordEquiv a j))) := by
    rfl
  have hfillInjective : Function.Injective
      (slackFillQuery a ha hbase) := by
    intro j k hjk
    have hgeomEq :
        g.query (Sum.inr (Sum.inr (slackFillCoordEquiv a j))) =
          g.query (Sum.inr (Sum.inr (slackFillCoordEquiv a k))) := by
      calc
        _ = slackFillQuery a ha hbase j := (hfillGeom j).symm
        _ = slackFillQuery a ha hbase k := hjk
        _ = _ := hfillGeom k
    have hcoord := g.query_injective hgeomEq
    have hiq : slackFillCoordEquiv a j = slackFillCoordEquiv a k := by
      exact Sum.inr.inj (Sum.inr.inj hcoord)
    exact (slackFillCoordEquiv a).injective hiq
  have hfillNodup : (queries hfill).Nodup := by
    rw [hfillQueries]
    exact List.nodup_ofFn.mpr hfillInjective
  have hfillNonloop : ∀ q ∈ queries hfill, ¬q.IsDiag := by
    intro q hq
    rw [hfillQueries] at hq
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hq
    rw [hfillGeom]
    exact g.query_nonloop _
  have hbaseRepresentation : ∀ r ∈ queries hbase,
      (∃ j : Fin (slackStarQueries a),
          r = s(slackCenter a ha, slackStarVertex a ha j)) ∨
        ∃ z : Fin (slackBranchPhaseQueries a),
          z.1 < (slackBaseBranchAnswerVector a base).toList.length ∧
            r = UpperPathGeometry.readyBranchSchedule a ha hbase z := by
    have hrep :=
      (UpperPathGeometry.branchStar_legal_and_query_representation
        a ha (slackBaseStarAnswerVector a base) hstar
        (slackBaseBranchAnswerVector a base).toList (by simp)).2
    rw [slackBase_branch_star_decomposition a base] at hrep
    exact hrep
  have hdisjoint : List.Disjoint (queries hfill) (queries hbase) := by
    rw [List.disjoint_left]
    intro q hqFill hqBase
    rw [hfillQueries] at hqFill
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hqFill
    rcases hbaseRepresentation _ hqBase with hstarQuery | hbranchQuery
    · obtain ⟨i, hi⟩ := hstarQuery
      have hgeomEq :
          g.query (Sum.inr (Sum.inr (slackFillCoordEquiv a j))) =
            g.query (Sum.inl i) := by
        calc
          _ = slackFillQuery a ha hbase j := (hfillGeom j).symm
          _ = s(slackCenter a ha, slackStarVertex a ha i) := hi
          _ = _ := by rfl
      have hcoord :
          (Sum.inr (Sum.inr (slackFillCoordEquiv a j)) :
              SlackQueryCoord a) = Sum.inl i :=
        g.query_injective hgeomEq
      exact Sum.noConfusion hcoord
    · obtain ⟨z, _hz, hz⟩ := hbranchQuery
      have hgeomEq :
          g.query (Sum.inr (Sum.inr (slackFillCoordEquiv a j))) =
            g.query (Sum.inr (Sum.inl (finProdFinEquiv.symm z))) := by
        calc
          _ = slackFillQuery a ha hbase j := (hfillGeom j).symm
          _ = UpperPathGeometry.readyBranchSchedule a ha hbase z := hz
          _ = _ := by rfl
      have hcoord :
          (Sum.inr (Sum.inr (slackFillCoordEquiv a j)) :
              SlackQueryCoord a) =
            Sum.inr (Sum.inl (finProdFinEquiv.symm z)) :=
        g.query_injective hgeomEq
      exact Sum.noConfusion (Sum.inr.inj hcoord)
  have hdecomp : fill.toList ++ base.toList = bits.toList := by
    exact slackFill_branch_answer_decomposition a bits
  have hfullReplay : replay (proposedSlackStrategy a ha) bits.toList =
      hfill ++ hbase := by
    have hrep := replay_proposedSlackStrategy_fill_append a ha
      base.toList fill.toList (by simp [base]) (by simp [fill])
    rw [hdecomp] at hrep
    exact hrep
  have hfullQueries :
      queries (replay (proposedSlackStrategy a ha) bits.toList) =
        queries hfill ++ queries hbase := by
    rw [hfullReplay, queries, List.map_append]
    rfl
  apply proposedPathLegal_of_replay_nodup_nonloop
  · rw [hfullQueries]
    exact List.Nodup.append hfillNodup hbaseNodup hdisjoint
  · intro q hq
    rw [hfullQueries] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hfillNonloop q hq
    · exact hbaseNonloop q hq

/-- The stable chronological branch replay identifies every raw positive bit
with its final reverse-chronological allocator coordinate. -/
theorem slackBranchRawAnswersEmbedded_of_starSupply
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true) :
    SlackBranchRawAnswersEmbedded a ha base := by
  dsimp only [SlackBranchRawAnswersEmbedded]
  let h := replay (proposedSlackStrategy a ha) base.toList
  intro i q htrue
  let j := (slackBranchCoordEquiv a).symm (i, q)
  have hmem := UpperPathGeometry.slackBaseBranch_get_mem_readySchedule
    a ha base hstar j
  have hbit : (slackBaseBranchAnswerVector a base).get j = true := by
    change slackBranchAnswerEquiv a
      (slackBaseBranchAnswerVector a base) i q = true
    exact htrue
  have hcoord : finProdFinEquiv.symm (Fin.rev j) =
      (Fin.rev i, Fin.rev (finProdFinEquiv q)) := by
    simpa only [j] using slackBranchCoordEquiv_symm_rev_apply a i q
  have hquery : UpperPathGeometry.readyBranchSchedule a ha h (Fin.rev j) =
      s(selectedRoot a ha h (Fin.rev i).1,
        (selectedBranchCandidates a ha h (Fin.rev i).1).getD
          (Fin.rev (finProdFinEquiv q)).1 (slackCenter a ha)) := by
    simp only [UpperPathGeometry.readyBranchSchedule,
      UpperPathGeometry.readyBranchQuery]
    rw [hcoord]
  simpa only [h, hquery, hbit] using hmem

/-- The full supply event produces the concrete successful-path certificate
once legality and the raw-to-allocator replay comparison are known. -/
theorem concreteSlackCoupledPath_of_supplySuccess_of_legal_of_dominates
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (hsupply : SlackFullSupplySuccess a bits)
    (hlegal : ProposedPathLegal
      (proposedSlackStrategy a ha) bits.toList)
    (hdom : SlackBranchRawDominatesAllocator a ha
      (slackBranchAnswerVector a bits)) :
    ConcreteSlackCoupledPath a ha bits := by
  rcases hsupply with ⟨⟨hstar, hraw⟩, htrial⟩
  let base := slackBranchAnswerVector a bits
  have hresBase : slackReservoirSize a ≤
      (positiveStarIndices a ha
        (replay (proposedSlackStrategy a ha) base.toList)).length :=
    reservoir_ready_of_baseStar_trueCount a ha base hstar
  have hbranchBase : slackTrialCount a ≤
      (successfulBranchFills a ha
        (replay (proposedSlackStrategy a ha) base.toList)).length :=
    branch_ready_of_rawReady_of_dominates a ha base hraw hdom
  have hprefix : slackBranchPrefix a
        (replay (proposedSlackStrategy a ha) bits.toList) =
      replay (proposedSlackStrategy a ha) base.toList := by
    simpa [base, slackBranchAnswerVector] using
      slackBranchPrefix_replay_eq a ha bits
  refine ⟨⟨hlegal, ?_, ?_, htrial⟩⟩
  · simpa [hprefix] using hresBase
  · simpa [hprefix] using hbranchBase

/-- Aggregate raw-to-allocator domination is now the only extra input:
the supply event itself also implies legality of the complete fill path. -/
theorem concreteSlackCoupledPath_of_supplySuccess_of_dominates
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (hsupply : SlackFullSupplySuccess a bits)
    (hdom : SlackBranchRawDominatesAllocator a ha
      (slackBranchAnswerVector a bits)) :
    ConcreteSlackCoupledPath a ha bits := by
  have hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a
        (slackBranchAnswerVector a bits)).toList.count true :=
    hsupply.1.1
  have hraw : SlackBranchRawReady a
      (slackBaseBranchAnswerVector a
        (slackBranchAnswerVector a bits)) := hsupply.1.2
  have hbranch : slackTrialCount a ≤
      (successfulBranchFills a ha
        (replay (proposedSlackStrategy a ha)
          (slackBranchAnswerVector a bits).toList)).length :=
    branch_ready_of_rawReady_of_dominates a ha
      (slackBranchAnswerVector a bits) hraw hdom
  have hlegal : ProposedPathLegal
      (proposedSlackStrategy a ha) bits.toList :=
    proposedPathLegal_of_starSupply_of_branchReady
      a ha bits hstar hbranch
  exact concreteSlackCoupledPath_of_supplySuccess_of_legal_of_dominates
    a ha bits hsupply hlegal hdom

/-- A semantic answer-embedding invariant is a convenient stronger input
than aggregate domination. -/
theorem concreteSlackCoupledPath_of_supplySuccess_of_legal_of_embedded
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (hsupply : SlackFullSupplySuccess a bits)
    (hlegal : ProposedPathLegal
      (proposedSlackStrategy a ha) bits.toList)
    (hembed : SlackBranchRawAnswersEmbedded a ha
      (slackBranchAnswerVector a bits)) :
    ConcreteSlackCoupledPath a ha bits := by
  have hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a
        (slackBranchAnswerVector a bits)).toList.count true :=
    hsupply.1.1
  have hdom : SlackBranchRawDominatesAllocator a ha
      (slackBranchAnswerVector a bits) :=
    rawDominates_of_starSupply_of_answersEmbedded a ha
      (slackBranchAnswerVector a bits) hstar hembed
  exact concreteSlackCoupledPath_of_supplySuccess_of_legal_of_dominates
    a ha bits hsupply hlegal hdom

/-- Pointwise raw-answer embedding is the natural final replay invariant;
the rest of the concrete certificate follows without further hypotheses. -/
theorem concreteSlackCoupledPath_of_supplySuccess_of_embedded
    (a : ℕ) (ha : 1 ≤ a)
    (bits : List.Vector Bool (slackQueryBudget a))
    (hsupply : SlackFullSupplySuccess a bits)
    (hembed : SlackBranchRawAnswersEmbedded a ha
      (slackBranchAnswerVector a bits)) :
    ConcreteSlackCoupledPath a ha bits := by
  have hdom : SlackBranchRawDominatesAllocator a ha
      (slackBranchAnswerVector a bits) :=
    rawDominates_of_starSupply_of_answersEmbedded a ha
      (slackBranchAnswerVector a bits) hsupply.1.1 hembed
  exact concreteSlackCoupledPath_of_supplySuccess_of_dominates
    a ha bits hsupply hdom

end
end UpperDeterministicAssembly
end OnlineRamsey
