import OnlineRamsey.UpperPathGeometry

/-!
# From raw branch scans to allocator readiness

This module isolates the deterministic counting part of the slack upper
strategy.  It is deliberately separate from `UpperStrategy.lean`: the latter
contains the adaptive program, while the results here turn sufficiently many
good raw scan outcomes into sufficiently many retained allocator fills.
-/

namespace OnlineRamsey
namespace UpperStrategy

open QueryComplexity UpperPathGeometry

noncomputable section

local instance slackBranchReadyPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

set_option maxHeartbeats 800000

/-- Reversing a row-major product coordinate reverses both product
coordinates. -/
theorem finProdFinEquiv_symm_rev_apply
    (m n : ℕ) (i : Fin m) (q : Fin n) :
    finProdFinEquiv.symm (Fin.rev (finProdFinEquiv (i, q))) =
      (Fin.rev i, Fin.rev q) := by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  simp [finProdFinEquiv, Fin.rev]
  rw [Nat.mul_sub_left_distrib]
  have hi : n * (i.1 + 1) ≤ n * m :=
    Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr i.2)
  have hq : q.1 + 1 ≤ n := Nat.succ_le_iff.mpr q.2
  ring_nf at hi ⊢
  omega

/-- The nested branch packing uses row-major order twice, so a global
newest-first reversal is componentwise reversal of the attempt and flattened
within-scan coordinates. -/
theorem slackBranchCoordEquiv_symm_rev_apply
    (a : ℕ) (i : Fin (slackAttemptCount a))
    (q : Fin (slackBranchGroups a) × Fin (slackBlockSize a)) :
    finProdFinEquiv.symm
        (Fin.rev ((slackBranchCoordEquiv a).symm (i, q))) =
      (Fin.rev i, Fin.rev (finProdFinEquiv q)) := by
  have hcoord : (slackBranchCoordEquiv a).symm (i, q) =
      finProdFinEquiv (i, finProdFinEquiv q) := by
    simp [slackBranchCoordEquiv]
    rfl
  rw [hcoord]
  exact finProdFinEquiv_symm_rev_apply _ _ i (finProdFinEquiv q)

/-- A nonbad grouped branch scan contains at least `a^4` positive answers. -/
theorem slackFillSize_le_trueBoardCount_of_not_scanBad
    (a : ℕ)
    (scan : Board (Fin (slackBranchGroups a) × Fin (slackBlockSize a)))
    (hgood : ¬SlackBranchScanBad a scan) :
    slackFillSize a ≤ trueBoardCount scan := by
  have hempty : emptyBlockCount scan < slackFillSize a := by
    simpa [SlackBranchScanBad, emptyBlockUpperTailEvent] using hgood
  have hsupply := groups_sub_emptyBlockCount_le_trueBoardCount
    (slackBranchGroups a) (slackBlockSize a) scan
  have hsupply' : 2 * slackFillSize a - emptyBlockCount scan ≤
      trueBoardCount scan := by
    simpa [slackBranchGroups, slackFillSize] using hsupply
  have hremaining : slackFillSize a ≤
      2 * slackFillSize a - emptyBlockCount scan := by omega
  exact hremaining.trans hsupply'

/-- The raw positive count of scan `i` is no larger than the number of
positive candidates seen by the final deterministic allocator at the
reverse-chronological attempt corresponding to `i`.

This is the exact, pointwise coupling obligation between a raw answer vector
and the history-dependent candidate selector.  It is stated only in terms of
finite executable objects and is strictly weaker than allocator readiness. -/
def SlackBranchRawDominatesAllocator
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a)) : Prop :=
  let h := replay (proposedSlackStrategy a ha) base.toList
  let raw := slackBranchAnswerEquiv a (slackBaseBranchAnswerVector a base)
  ∀ i : Fin (slackAttemptCount a),
    trueBoardCount (raw i) ≤
      ((selectedBranchCandidates a ha h (Fin.rev i).1).filter fun v ↦
        (s(selectedRoot a ha h (Fin.rev i).1, v), true) ∈ h).length

/-- Pointwise semantic form of the branch coupling.  A positive coordinate
in raw (newest-first) scan `i` occurs in the completed replay at the
candidate obtained by reversing both the scan and within-scan coordinates.

Unlike `SlackBranchRawDominatesAllocator`, this condition remembers the
actual query carrying each answer.  It is therefore the natural invariant
to establish by induction through the adaptive branch replay. -/
def SlackBranchRawAnswersEmbedded
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a)) : Prop :=
  let h := replay (proposedSlackStrategy a ha) base.toList
  let raw := slackBranchAnswerEquiv a (slackBaseBranchAnswerVector a base)
  ∀ i : Fin (slackAttemptCount a),
    ∀ q : Fin (slackBranchGroups a) × Fin (slackBlockSize a),
      raw i q = true →
        (s(selectedRoot a ha h (Fin.rev i).1,
            (selectedBranchCandidates a ha h (Fin.rev i).1).getD
              (Fin.rev (finProdFinEquiv q)).1 (slackCenter a ha)), true) ∈ h

/-- The pointwise replay invariant implies the aggregate domination needed
by the raw-readiness counting argument.  The only supply premise is the
directly checkable number of true centre-star answers. -/
theorem rawDominates_of_starSupply_of_answersEmbedded
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true)
    (hembed : SlackBranchRawAnswersEmbedded a ha base) :
    SlackBranchRawDominatesAllocator a ha base := by
  classical
  let h := replay (proposedSlackStrategy a ha) base.toList
  let raw := slackBranchAnswerEquiv a (slackBaseBranchAnswerVector a base)
  have hres : slackReservoirSize a ≤
      (positiveStarIndices a ha h).length := by
    exact reservoir_ready_of_baseStar_trueCount a ha base hstar
  intro i
  let rawPositive : Finset
      (Fin (slackBranchGroups a) × Fin (slackBlockSize a)) :=
    Finset.univ.filter fun q ↦ raw i q = true
  let candidate :
      (Fin (slackBranchGroups a) × Fin (slackBlockSize a)) →
        Vertex (slackQueryBudget a) := fun q ↦
    (selectedBranchCandidates a ha h (Fin.rev i).1).getD
      (Fin.rev (finProdFinEquiv q)).1 (slackCenter a ha)
  let allocatorPositive : List (Vertex (slackQueryBudget a)) :=
    (selectedBranchCandidates a ha h (Fin.rev i).1).filter fun v ↦
      (s(selectedRoot a ha h (Fin.rev i).1, v), true) ∈ h
  have hcandidateInjective : Function.Injective candidate := by
    have hsel := selectedBranchCandidate_injective_of_ready
      a ha h hres (Fin.rev i)
    exact hsel.comp (Fin.rev_injective.comp finProdFinEquiv.injective)
  have himage : rawPositive.image candidate ⊆
      allocatorPositive.toFinset := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨q, hq, rfl⟩
    rw [List.mem_toFinset]
    have hqTrue : raw i q = true := (Finset.mem_filter.mp hq).2
    have hanswer := hembed i q hqTrue
    have hk : (Fin.rev (finProdFinEquiv q)).1 <
        (selectedBranchCandidates a ha h (Fin.rev i).1).length := by
      rw [selectedBranchCandidates_length_of_reservoir_ready
        a ha h hres (Fin.rev i).1 (Fin.rev i).2]
      exact (Fin.rev (finProdFinEquiv q)).2
    apply List.mem_filter.mpr
    constructor
    · change (selectedBranchCandidates a ha h (Fin.rev i).1).getD
          (Fin.rev (finProdFinEquiv q)).1 (slackCenter a ha) ∈
        selectedBranchCandidates a ha h (Fin.rev i).1
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    · simpa [candidate] using hanswer
  have hrawCard : rawPositive.card = trueBoardCount (raw i) := rfl
  have hallocatorNodup : allocatorPositive.Nodup := by
    unfold allocatorPositive selectedBranchCandidates
    exact (availableBranchPool_nodup a ha h
      (selectedBranchFills a ha h (Fin.rev i).1).flatten).take.filter _
  calc
    trueBoardCount (raw i) = rawPositive.card := hrawCard.symm
    _ = (rawPositive.image candidate).card :=
      (Finset.card_image_of_injective rawPositive hcandidateInjective).symm
    _ ≤ allocatorPositive.toFinset.card := Finset.card_le_card himage
    _ = allocatorPositive.length :=
      List.toFinset_card_of_nodup hallocatorNodup

/-- In a ready allocator state, a query from attempt `i` is distinct from
every query belonging to a strictly earlier attempt. -/
theorem readyBranchQuery_ne_earlier
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i j : Fin (slackAttemptCount a)) (hji : j.1 < i.1)
    (k l : Fin (slackBranchScan a)) :
    s(selectedRoot a ha h i.1,
        (selectedBranchCandidates a ha h i.1).getD k.1
          (slackCenter a ha)) ≠
      s(selectedRoot a ha h j.1,
        (selectedBranchCandidates a ha h j.1).getD l.1
          (slackCenter a ha)) := by
  intro heq
  have hrootInj := selectedRoot_injective_of_ready a ha h hres
  have hcandINeRootJ := selectedBranchCandidate_ne_root_of_ready
    a ha h hres i k j
  have hcandJNeRootI := selectedBranchCandidate_ne_root_of_ready
    a ha h hres j l i
  simp only [Sym2.eq_iff] at heq
  rcases heq with hsame | hswap
  · have hij : i = j := hrootInj hsame.1
    omega
  · exact hcandINeRootJ hswap.2

/-- Entry `n` in the completed list of attempted fills is the choice made
at attempt `n`. -/
theorem selectedBranchFills_getD_eq_attemptChoice
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    {m n : ℕ} (hnm : n < m) :
    (selectedBranchFills a ha h m).getD n [] =
      let prior := selectedBranchFills a ha h n
      let candidates :=
        (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
      let root := selectedRoot a ha h n
      let positives := candidates.filter fun v ↦ (s(root, v), true) ∈ h
      if slackFillSize a ≤ positives.length then
        positives.take (slackFillSize a) else [] := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hnm' : n < m
      · have hpriorLen :
          (selectedBranchFills a ha h m).length = m :=
          selectedBranchFills_length a ha h m
        rw [show selectedBranchFills a ha h (m + 1) =
            selectedBranchFills a ha h m ++
              [let prior := selectedBranchFills a ha h m
               let candidates :=
                 (availableBranchPool a ha h prior.flatten).take
                   (slackBranchScan a)
               let root := selectedRoot a ha h m
               let positives := candidates.filter fun v ↦
                 (s(root, v), true) ∈ h
               if slackFillSize a ≤ positives.length then
                 positives.take (slackFillSize a) else []] by
          simp only [selectedBranchFills]]
        rw [List.getD_append _ _ _ _ (by simpa [hpriorLen] using hnm')]
        exact ih hnm'
      · have hnmEq : n = m := by omega
        subst n
        let prior := selectedBranchFills a ha h m
        let candidates :=
          (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
        let root := selectedRoot a ha h m
        let positives := candidates.filter fun v ↦ (s(root, v), true) ∈ h
        let chosen := if slackFillSize a ≤ positives.length then
          positives.take (slackFillSize a) else []
        have hpriorLen : prior.length = m :=
          selectedBranchFills_length a ha h m
        rw [show selectedBranchFills a ha h (m + 1) = prior ++ [chosen] by
          simp only [selectedBranchFills]
          rfl]
        rw [List.getD_append_right prior [chosen] [] m (by omega)]
        simp [prior, candidates, root, positives, chosen, hpriorLen]

/-- If the raw count for an attempt is at least the fill target and is
dominated by the allocator's positive-candidate count, that attempt is
retained as a full fill. -/
theorem attemptChoice_length_eq_fillSize_of_rawCount
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (i : Fin (slackAttemptCount a))
    (hrawCount : slackFillSize a ≤
      trueBoardCount
        (slackBranchAnswerEquiv a
          (slackBaseBranchAnswerVector a base) i))
    (hdom : SlackBranchRawDominatesAllocator a ha base) :
    let h := replay (proposedSlackStrategy a ha) base.toList
    ((selectedBranchFills a ha h (slackAttemptCount a)).getD
      (Fin.rev i).1 []).length = slackFillSize a := by
  dsimp only
  let h := replay (proposedSlackStrategy a ha) base.toList
  let n := (Fin.rev i).1
  have hn : n < slackAttemptCount a := (Fin.rev i).2
  have hpositive : slackFillSize a ≤
      ((selectedBranchCandidates a ha h n).filter fun v ↦
        (s(selectedRoot a ha h n, v), true) ∈ h).length := by
    exact hrawCount.trans (hdom i)
  rw [selectedBranchFills_getD_eq_attemptChoice a ha h hn]
  change slackFillSize a ≤
      ((List.take (slackBranchScan a)
        (availableBranchPool a ha h
          (selectedBranchFills a ha h n).flatten)).filter fun v ↦
          (s(selectedRoot a ha h n, v), true) ∈ h).length at hpositive
  rw [if_pos hpositive, List.length_take, Nat.min_eq_left hpositive]

private def selectedFillVector
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    List.Vector (List (Vertex (slackQueryBudget a))) (slackAttemptCount a) :=
  ⟨selectedBranchFills a ha h (slackAttemptCount a),
    selectedBranchFills_length a ha h _⟩

private def selectedFillSuccessBits
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    List.Vector Bool (slackAttemptCount a) :=
  (selectedFillVector a ha h).map fun fill ↦
    decide (fill.length = slackFillSize a)

private theorem selectedFillSuccessBits_count_true
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    (selectedFillSuccessBits a ha h).toList.count true =
      (successfulBranchFills a ha h).length := by
  let fills := selectedBranchFills a ha h (slackAttemptCount a)
  have haux : (fills.map fun fill ↦
      decide (fill.length = slackFillSize a)).count true =
      (fills.filter fun fill ↦ fill.length = slackFillSize a).length := by
    induction fills with
    | nil => simp
    | cons fill fills ih =>
        by_cases hfill : fill.length = slackFillSize a <;>
          simp [hfill, ih]
  simpa [selectedFillSuccessBits, selectedFillVector,
    successfulBranchFills, fills] using haux

/-- Pure finite counting: if every nonbad raw scan yields a successful
reverse-chronological allocator attempt, then raw readiness implies the
allocator has at least the target number of full fills. -/
theorem branch_ready_of_rawReady_of_dominates
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (hraw : SlackBranchRawReady a (slackBaseBranchAnswerVector a base))
    (hdom : SlackBranchRawDominatesAllocator a ha base) :
    slackTrialCount a ≤
      (successfulBranchFills a ha
        (replay (proposedSlackStrategy a ha) base.toList)).length := by
  let raw := slackBranchAnswerEquiv a (slackBaseBranchAnswerVector a base)
  let h := replay (proposedSlackStrategy a ha) base.toList
  let good : Finset (Fin (slackAttemptCount a)) :=
    Finset.univ.filter fun i ↦ ¬SlackBranchScanBad a (raw i)
  let success : Finset (Fin (slackAttemptCount a)) :=
    Finset.univ.filter fun i ↦
      (selectedFillSuccessBits a ha h).get i = true
  let revEmb : Fin (slackAttemptCount a) ↪ Fin (slackAttemptCount a) :=
    ⟨Fin.rev, Fin.rev_injective⟩
  have hgoodCard : slackTrialCount a ≤ good.card := by
    have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
      (fun i : Fin (slackAttemptCount a) ↦ SlackBranchScanBad a (raw i))
      (s := Finset.univ)
    change badOutcomeCount (SlackBranchScanBad a) raw <
      slackTrialCount a at hraw
    unfold badOutcomeCount at hraw
    change ((Finset.univ.filter fun i ↦
      SlackBranchScanBad a (raw i)).card) < slackTrialCount a at hraw
    change slackTrialCount a ≤
      (Finset.univ.filter fun i ↦ ¬SlackBranchScanBad a (raw i)).card
    have hsum :
        (Finset.univ.filter fun i ↦ SlackBranchScanBad a (raw i)).card +
          (Finset.univ.filter fun i ↦ ¬SlackBranchScanBad a (raw i)).card =
            2 * slackTrialCount a := by
      simpa [slackAttemptCount] using hpartition
    omega
  have himageSub : good.image revEmb ⊆ success := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    have hiGood : ¬SlackBranchScanBad a (raw i) :=
      (Finset.mem_filter.mp hi).2
    have hcount : slackFillSize a ≤ trueBoardCount (raw i) :=
      slackFillSize_le_trueBoardCount_of_not_scanBad a (raw i) hiGood
    have hlength := attemptChoice_length_eq_fillSize_of_rawCount
      a ha base i hcount hdom
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hiBound : (Fin.rev i).1 <
        (selectedBranchFills a ha h (slackAttemptCount a)).length := by
      simpa [selectedBranchFills_length] using (Fin.rev i).2
    have hfillLength :
        (selectedBranchFills a ha h (slackAttemptCount a))[(Fin.rev i).1].length =
          slackFillSize a := by
      rw [← List.getD_eq_getElem _ [] hiBound]
      simpa [h] using hlength
    rw [show (selectedFillSuccessBits a ha h).get (revEmb i) =
        decide (((selectedFillVector a ha h).get (Fin.rev i)).length =
          slackFillSize a) by
      simp [selectedFillSuccessBits, revEmb]]
    have hvectorLength :
        ((selectedFillVector a ha h).get (Fin.rev i)).length =
          slackFillSize a := by
      simpa [selectedFillVector] using hfillLength
    simp [hvectorLength]
  have hgoodLeSuccess : good.card ≤ success.card := by
    calc
      good.card = (good.image revEmb).card :=
        (Finset.card_image_of_injective good revEmb.injective).symm
      _ ≤ success.card := Finset.card_le_card himageSub
  have hsuccessCard : success.card =
      (successfulBranchFills a ha h).length := by
    calc
      success.card =
          (selectedFillSuccessBits a ha h).toList.count true := by
        exact Fin.card_filter_univ_eq_vector_get_eq_count true
          (selectedFillSuccessBits a ha h)
      _ = (successfulBranchFills a ha h).length :=
        selectedFillSuccessBits_count_true a ha h
  exact hgoodCard.trans (hgoodLeSuccess.trans_eq hsuccessCard)

end
end UpperStrategy
end OnlineRamsey
