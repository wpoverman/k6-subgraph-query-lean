import OnlineRamsey.UnconditionalLower
import OnlineRamsey.UpperHypothesisPackaging

/-!
# Final upper/lower assembly for the finite cubic power law

This module contains only the last logical wrapper.  Its sole construction
input is bucketwise achievability of the concrete slack budget; the global
positive lower constant and all minimization and rounding bookkeeping come
from already proved theorems.
-/

namespace OnlineRamsey
namespace FinalPowerLaw

open scoped ENNReal
open QueryComplexity K4OneTrial UpperStrategy
open UpperBudgetUniversal

/-- Bucketwise achievability of the implemented slack strategy implies the
complete finite `q⁻¹⁰` (equivalently `p⁻¹⁰⁄³`) power law, with an existential
positive lower constant and the explicit universal upper constant. -/
theorem exists_finiteCubicPowerLaw_of_slackBucketAchievable
    (hbucket : ∀ (a : ℕ), 2 ≤ a → ∀ p : ℝ≥0∞,
      densityENN a ≤ p → p ≤ 1 → Achievable p (slackQueryBudget a)) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      FiniteCubicPowerLaw Achievable c
        ((slackUniversalUpperConstant * 2 ^ 10 : ℕ) : ℝ≥0∞) := by
  rcases UnconditionalLower.exists_global_queryBudget_lower_constant with
    ⟨c, hc, hlower⟩
  refine ⟨c, hc, ?_⟩
  exact k6_powerLaw_of_matching_bounds c
    ((slackUniversalUpperConstant * 2 ^ 10 : ℕ) : ℝ≥0∞)
    hlower
    (UpperHypothesisPackaging.upperHypothesis_of_slackBucketAchievable hbucket)

end FinalPowerLaw
end OnlineRamsey
