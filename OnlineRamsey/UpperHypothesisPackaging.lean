import OnlineRamsey.DensityPackaging
import OnlineRamsey.UpperBudgetUniversal

/-!
# Packaging a bucket-robust slack strategy as the global upper hypothesis
-/

namespace OnlineRamsey
namespace UpperHypothesisPackaging

open scoped ENNReal
open QueryComplexity K4OneTrial UpperStrategy
open DensityPackaging UpperBudgetUniversal

/-- Once the implemented slack budget is achievable throughout every bucket,
the exact upper premise of `FiniteCubicPowerLaw` follows with the universal
polynomial coefficient and the standard integer-scale rounding loss. -/
theorem upperHypothesis_of_slackBucketAchievable
    (hbucket : ∀ (a : ℕ), 2 ≤ a → ∀ p : ℝ≥0∞,
      densityENN a ≤ p → p ≤ 1 → Achievable p (slackQueryBudget a)) :
    ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∃ N, Achievable (q ^ 3) N ∧
        (N : ℝ≥0∞) * q ^ 10 ≤
          ((slackUniversalUpperConstant * 2 ^ 10 : ℕ) : ℝ≥0∞) := by
  intro q hq hq1
  let a := integerScale q
  have ha : 2 ≤ a := integerScale_ge_two q
  have hdensity : densityENN a ≤ cubicDensity q :=
    integerScale_density_le_cubicDensity hq hq1
  have hp : cubicDensity q ≤ 1 := cubicDensity_le_one hq1
  refine ⟨slackQueryBudget a, ?_, ?_⟩
  · simpa [cubicDensity, a] using hbucket a ha (cubicDensity q) hdensity hp
  · apply normalized_le_of_budget_le slackUniversalUpperConstant
      (slackQueryBudget a) hq hq1
    simpa [a] using slackQueryBudget_le_universal a (by omega)

end UpperHypothesisPackaging
end OnlineRamsey
