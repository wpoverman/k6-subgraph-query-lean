import OnlineRamsey.SlackBranchReady

/-!
# Closing the raw branch replay invariant

This module identifies the product coordinates used by the branch probability
estimate with the final, stable allocator coordinates in the completed replay.
-/

namespace OnlineRamsey
namespace UpperStrategy

open QueryComplexity UpperPathGeometry

noncomputable section

local instance rawEmbeddingClosurePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A sufficient raw star supply forces every positive raw branch bit to be
present on the corresponding final allocator query. -/
theorem slackBranchRawAnswersEmbedded_of_starSupply
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true) :
    SlackBranchRawAnswersEmbedded a ha base := by
  let h := replay (proposedSlackStrategy a ha) base.toList
  let raw := slackBranchAnswerEquiv a (slackBaseBranchAnswerVector a base)
  intro i q htrue
  let j : Fin (slackBranchPhaseQueries a) :=
    (slackBranchCoordEquiv a).symm (i, q)
  have hmem := slackBaseBranch_get_mem_readySchedule a ha base hstar j
  have hbit : (slackBaseBranchAnswerVector a base).get j = true := by
    simpa [raw, j, slackBranchAnswerEquiv, packSlackBranchAnswers] using htrue
  have hcoord : finProdFinEquiv.symm (Fin.rev j) =
      (Fin.rev i, Fin.rev (finProdFinEquiv q)) := by
    simpa [j] using slackBranchCoordEquiv_symm_rev_apply a i q
  rw [hbit] at hmem
  simpa [h, readyBranchSchedule, readyBranchQuery, hcoord] using hmem

/-- Consequently the aggregate raw scan is dominated by the completed
allocator scan, with no semantic premise beyond raw star supply. -/
theorem slackBranchRawDominatesAllocator_of_starSupply
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true) :
    SlackBranchRawDominatesAllocator a ha base := by
  exact rawDominates_of_starSupply_of_answersEmbedded a ha base hstar
    (slackBranchRawAnswersEmbedded_of_starSupply a ha base hstar)

end
end UpperStrategy
end OnlineRamsey
