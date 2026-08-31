import OnlineRamsey.UpperDeterministicAssembly
import OnlineRamsey.FinalPowerLaw

/-!
# Final upper-bound assembly

The probability, legality, allocator-counting, budget, and global power-law
layers are all assembled here.  The parameter in the two compiler theorems
is exactly the remaining finite replay invariant: raw positive branch bits
are embedded at the corresponding completed allocator coordinates.
-/

namespace OnlineRamsey
namespace UnconditionalUpper

open scoped ENNReal
open QueryComplexity K4OneTrial UpperStrategy
open UpperProbabilityAssembly UpperDeterministicAssembly

noncomputable section

/-- The single replay invariant needed to close every density bucket. -/
theorem slackBucketAchievable_of_rawAnswersEmbedded
    (hembed : ∀ (a : ℕ) (ha : 1 ≤ a)
      (base : List.Vector Bool (slackFillStart a)),
      slackReservoirSize a ≤
          (slackBaseStarAnswerVector a base).toList.count true →
        SlackBranchRawAnswersEmbedded a ha base) :
    ∀ (a : ℕ), 2 ≤ a → ∀ p : ℝ≥0∞,
      densityENN a ≤ p → p ≤ 1 →
        Achievable p (slackQueryBudget a) := by
  intro a ha p hdensity hp
  apply achievable_slack_of_supplySuccess_implies_concrete
    a ha p hp hdensity
  intro bits hsupply
  apply concreteSlackCoupledPath_of_supplySuccess_of_embedded
    a (by omega) bits hsupply
  exact hembed a (by omega) (slackBranchAnswerVector a bits) hsupply.1.1

/-- Unconditional bucketwise achievability of the implemented slack
strategy. -/
theorem slackBucketAchievable :
    ∀ (a : ℕ), 2 ≤ a → ∀ p : ℝ≥0∞,
      densityENN a ≤ p → p ≤ 1 →
        Achievable p (slackQueryBudget a) := by
  apply slackBucketAchievable_of_rawAnswersEmbedded
  intro a ha base hstar
  exact slackBranchRawAnswersEmbedded_of_starSupply a ha base hstar

/-- The same finite replay invariant compiles all the way to the complete
finite cubic power law. -/
theorem exists_finiteCubicPowerLaw_of_rawAnswersEmbedded
    (hembed : ∀ (a : ℕ) (ha : 1 ≤ a)
      (base : List.Vector Bool (slackFillStart a)),
      slackReservoirSize a ≤
          (slackBaseStarAnswerVector a base).toList.count true →
        SlackBranchRawAnswersEmbedded a ha base) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      FiniteCubicPowerLaw Achievable c
        ((UpperBudgetUniversal.slackUniversalUpperConstant * 2 ^ 10 : ℕ) :
          ℝ≥0∞) := by
  apply FinalPowerLaw.exists_finiteCubicPowerLaw_of_slackBucketAchievable
  exact slackBucketAchievable_of_rawAnswersEmbedded hembed

/-- The complete unconditional finite cubic power law for the `K₆`
subgraph-query game, with a positive lower constant and an explicit finite
upper constant. -/
theorem exists_finiteCubicPowerLaw :
    ∃ c : ℝ≥0∞, 0 < c ∧
      FiniteCubicPowerLaw Achievable c
        ((UpperBudgetUniversal.slackUniversalUpperConstant * 2 ^ 10 : ℕ) :
          ℝ≥0∞) := by
  exact FinalPowerLaw.exists_finiteCubicPowerLaw_of_slackBucketAchievable
    slackBucketAchievable

end
end UnconditionalUpper
end OnlineRamsey
