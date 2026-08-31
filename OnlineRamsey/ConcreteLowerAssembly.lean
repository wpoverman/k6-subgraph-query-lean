import OnlineRamsey.StoppingPrefixMask

/-!
# Unconditional stopping-history assembly for the finite query game

This module composes the concrete success-event coverage and stopping-time
factorization with the abstract four-case algebra.  Its only remaining input
is the per-order prefix-count estimate; there are no partition,
non-anticipation, or Markov hypotheses left for downstream callers.
-/

open scoped BigOperators ENNReal

namespace OnlineRamsey
namespace ConcreteLowerAssembly

open QueryComplexity LowerAssembly StoppingHistory StoppingCoverage
open StoppingPrefixCount

noncomputable section

/-- The four-way stopping case selected by the checked nine-edge
classification. -/
def prefixCaseOfOrder (π : K6EdgeOrder) : PrefixCase :=
  if K6Prefix.inExceptionalOrbit
      (orderPrefixMask π ninePrefixLength).1 = false then
    .ordinary
  else if K6Prefix.h3Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true then
    .halfGraph
  else if K6Prefix.k5MinusEdgePlusIsolateOrbit[
      (orderPrefixMask π ninePrefixLength).1]! = true then
    .almostCompleteFive
  else
    .shiftedBipartite

/-- Every order lands in its claimed checked classification branch. -/
theorem prefixCaseOfOrder_spec (π : K6EdgeOrder) :
    (prefixCaseOfOrder π = .ordinary ∧
      K6Prefix.inExceptionalOrbit
        (orderPrefixMask π ninePrefixLength).1 = false) ∨
    (prefixCaseOfOrder π = .halfGraph ∧
      K6Prefix.h3Orbit[
        (orderPrefixMask π ninePrefixLength).1]! = true) ∨
    (prefixCaseOfOrder π = .almostCompleteFive ∧
      K6Prefix.k5MinusEdgePlusIsolateOrbit[
        (orderPrefixMask π ninePrefixLength).1]! = true) ∨
    (prefixCaseOfOrder π = .shiftedBipartite ∧
      K6Prefix.b4Orbit[
        (orderPrefixMask π ninePrefixLength).1]! = true) := by
  by_cases hordinary : K6Prefix.inExceptionalOrbit
      (orderPrefixMask π ninePrefixLength).1 = false
  · exact Or.inl ⟨by simp [prefixCaseOfOrder, hordinary], hordinary⟩
  right
  by_cases hh3 : K6Prefix.h3Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true
  · exact Or.inl ⟨by simp [prefixCaseOfOrder, hordinary, hh3], hh3⟩
  right
  by_cases hk5 : K6Prefix.k5MinusEdgePlusIsolateOrbit[
      (orderPrefixMask π ninePrefixLength).1]! = true
  · exact Or.inl ⟨by simp [prefixCaseOfOrder, hordinary, hh3, hk5], hk5⟩
  right
  have hclassification := orderNinePrefix_classification π
  rcases hclassification with hord | hh3' | hk5' | hb4
  · exact False.elim (hordinary hord)
  · exact False.elim (hh3 hh3')
  · exact False.elim (hk5 hk5')
  · exact ⟨by simp [prefixCaseOfOrder, hordinary, hh3, hk5], hb4⟩

/-- Concrete all-orders upper bound for one fresh strategy. -/
theorem successProbability_le_of_prefixBounds
    {N : ℕ} (p C : ℝ≥0∞) (hp : p ≤ 1)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (kind : K6EdgeOrder → PrefixCase) (error : K6EdgeOrder → ℝ≥0∞)
    (hcount : ∀ π,
      orderPrefixHistoryMass p strategy π (casePrefixLength (kind π)) ≤
        C * p ^ prefixExponent (kind π) * (N : ℝ≥0∞) ^ 3 + error π) :
    successProbability p N strategy ≤
      (Nat.factorial 15 : ℝ≥0∞) *
          (C * p ^ 10 * (N : ℝ≥0∞) ^ 3) +
        ∑ π : K6EdgeOrder,
          p ^ completionExponent (kind π) * error π := by
  apply allOrders_target_scale
    (Order := K6EdgeOrder) card_k6EdgeOrder p (N : ℝ≥0∞) C
    (successProbability p N strategy) kind
    (fun π => orderCompletionHistoryMass p strategy π
      (casePrefixLength (kind π)))
    (fun π => orderPrefixHistoryMass p strategy π
      (casePrefixLength (kind π))) error
  · exact successProbability_le_sum_caseCompletionHistoryMass
      p strategy hfresh (Equiv.refl K6EdgeOrder) kind
  · intro π
    exact orderCompletionHistoryMass_le_casePrefixHistoryMass
      p hp strategy π (kind π)
  · exact hcount

/-- If the explicit all-orders expression is below one half, the strategy's
success probability is below the query-game threshold. -/
theorem successProbability_lt_threshold_of_prefixBounds
    {N : ℕ} (p C : ℝ≥0∞) (hp : p ≤ 1)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (kind : K6EdgeOrder → PrefixCase) (error : K6EdgeOrder → ℝ≥0∞)
    (hcount : ∀ π,
      orderPrefixHistoryMass p strategy π (casePrefixLength (kind π)) ≤
        C * p ^ prefixExponent (kind π) * (N : ℝ≥0∞) ^ 3 + error π)
    (hsmall :
      (Nat.factorial 15 : ℝ≥0∞) *
          (C * p ^ 10 * (N : ℝ≥0∞) ^ 3) +
        ∑ π : K6EdgeOrder,
          p ^ completionExponent (kind π) * error π < threshold) :
    successProbability p N strategy < threshold :=
  (successProbability_le_of_prefixBounds p C hp strategy hfresh kind error
    hcount).trans_lt hsmall

/-- Uniform prefix bounds whose assembled expression is below one half rule
out achievability at the given finite budget. -/
theorem not_achievable_of_uniform_prefixBounds
    {N : ℕ} (p C : ℝ≥0∞) (hp : p ≤ 1)
    (kind : K6EdgeOrder → PrefixCase) (error : K6EdgeOrder → ℝ≥0∞)
    (hcount : ∀ strategy : K6Strategy N, FreshForBudget strategy → ∀ π,
      orderPrefixHistoryMass p strategy π (casePrefixLength (kind π)) ≤
        C * p ^ prefixExponent (kind π) * (N : ℝ≥0∞) ^ 3 + error π)
    (hsmall :
      (Nat.factorial 15 : ℝ≥0∞) *
          (C * p ^ 10 * (N : ℝ≥0∞) ^ 3) +
        ∑ π : K6EdgeOrder,
          p ^ completionExponent (kind π) * error π < threshold) :
    ¬Achievable p N := by
  rintro ⟨_hp, strategy, hadmissible, hsuccess⟩
  have hlt := successProbability_lt_threshold_of_prefixBounds
    p C hp strategy hadmissible.1 kind error
    (hcount strategy hadmissible.1) hsmall
  exact (not_lt_of_ge hsuccess) hlt

end
end ConcreteLowerAssembly
end OnlineRamsey
