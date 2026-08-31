import OnlineRamsey.UpperStrategy

/-!
# Raw branch coordinates in the adaptive replay

This module connects the product coordinates used by the branch probability
estimate to literal entries of the adaptive pre-fill replay.  It deliberately
does not assert selector stability; the query is stated at its exact older
history, leaving that separate deterministic induction honest.
-/

namespace OnlineRamsey
namespace UpperStrategy

open QueryComplexity

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- A raw branch-board bit is the bit at the corresponding newest-first
coordinate of the complete pre-fill answer list. -/
theorem slackBranchAnswerEquiv_base_eq_getElem
    (a : ℕ) (base : List.Vector Bool (slackFillStart a))
    (i : Fin (slackAttemptCount a))
    (q : Fin (slackBranchGroups a) × Fin (slackBlockSize a)) :
    slackBranchAnswerEquiv a (slackBaseBranchAnswerVector a base) i q =
      base.toList[((slackBranchCoordEquiv a).symm (i, q)).1]'(by
        have hj := ((slackBranchCoordEquiv a).symm (i, q)).2
        rw [List.Vector.toList_length]
        unfold slackFillStart slackBranchPhaseQueries at *
        omega) := by
  let j := (slackBranchCoordEquiv a).symm (i, q)
  have hjTake : j.1 <
      (base.toList.take (slackBranchPhaseQueries a)).length := by
    rw [List.length_take, List.Vector.toList_length, Nat.min_eq_left]
    · exact j.2
    · unfold slackFillStart slackBranchPhaseQueries
      omega
  change (base.toList.take (slackBranchPhaseQueries a))[j.1]'hjTake = _
  rw [List.getElem_take]

/-- Every raw branch-board coordinate is literally the answer on the query
chosen by the proposed strategy from its exact strictly older history. -/
theorem slackRawBranch_entry_mem_replay
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (i : Fin (slackAttemptCount a))
    (q : Fin (slackBranchGroups a) × Fin (slackBlockSize a)) :
    let j := (slackBranchCoordEquiv a).symm (i, q)
    (proposedSlackStrategy a ha
        (replay (proposedSlackStrategy a ha)
          (base.toList.drop (j.1 + 1))),
      slackBranchAnswerEquiv a
        (slackBaseBranchAnswerVector a base) i q) ∈
      replay (proposedSlackStrategy a ha) base.toList := by
  dsimp only
  let j := (slackBranchCoordEquiv a).symm (i, q)
  have hjBase : j.1 < base.toList.length := by
    rw [List.Vector.toList_length]
    have hj := j.2
    unfold slackFillStart slackBranchPhaseQueries at *
    omega
  have hm := replay_query_on_drop_mem (proposedSlackStrategy a ha)
    base.toList j.1 hjBase
  rw [slackBranchAnswerEquiv_base_eq_getElem a base i q]
  exact hm

end
end UpperStrategy
end OnlineRamsey
