import OnlineRamsey.InfinitePolicyBridge
import OnlineRamsey.UnconditionalUpper

/-!
# Unconditional power law in the standard countably infinite formulation

This module transports the unconditional finite-board theorem across the
coherent policy equivalence proved in `InfinitePolicyBridge.lean`.  The final
theorem is therefore stated directly for policies querying unordered pairs of
natural-number vertices, with their finite-horizon Bernoulli answer-vector
law.
-/

namespace OnlineRamsey
namespace InfiniteUnconditional

open scoped ENNReal
open QueryComplexity InfinitePolicyBridge

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Pointwise equivalent budget predicates have the same least-budget cubic
power law.  `Nat.find_congr'` records that their least witnesses agree. -/
theorem finiteCubicPowerLaw_of_iff
    {P Q : ℝ≥0∞ → ℕ → Prop} {c C : ℝ≥0∞}
    (hQP : ∀ p N, Q p N ↔ P p N)
    (hP : FiniteCubicPowerLaw P c C) :
    FiniteCubicPowerLaw Q c C := by
  intro q hq hq1
  rcases hP q hq hq1 with ⟨hexistsP, hlower, hupper⟩
  let hexistsQ : ∃ N, Q (q ^ 3) N := by
    rcases hexistsP with ⟨N, hN⟩
    exact ⟨N, (hQP (q ^ 3) N).mpr hN⟩
  have hfind : Nat.find hexistsQ = Nat.find hexistsP :=
    Nat.find_congr' (fun {N} => hQP (q ^ 3) N)
  refine ⟨hexistsQ, ?_⟩
  simpa only [hfind] using And.intro hlower hupper

/-- The complete unconditional cubic-scale power law in the standard
countably infinite subgraph-query game.  This is the formal endpoint
corresponding directly to `f(K₆,p) = Θ(p⁻¹⁰⁄³)`. -/
theorem exists_infiniteCubicPowerLaw :
    ∃ c : ℝ≥0∞, 0 < c ∧
      FiniteCubicPowerLaw InfiniteAchievable c
        ((UpperBudgetUniversal.slackUniversalUpperConstant * 2 ^ 10 : ℕ) :
          ℝ≥0∞) := by
  rcases UnconditionalUpper.exists_finiteCubicPowerLaw with
    ⟨c, hc, hfinite⟩
  refine ⟨c, hc, finiteCubicPowerLaw_of_iff ?_ hfinite⟩
  intro p N
  exact infiniteAchievable_iff_achievable p N

end
end InfiniteUnconditional
end OnlineRamsey
