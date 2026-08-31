import OnlineRamsey.OrdinaryAllOrders
import OnlineRamsey.ExceptionalHistoryScale
import OnlineRamsey.B4SharpHistoryScale
import OnlineRamsey.SmallEllBadMass

/-!
# A uniform four-case stopping-prefix estimate

The checked nine-edge classifier selects one of four stopping rules for each
relative edge order.  This file packages the ordinary recurrence estimate and
the three exceptional host-counting estimates into the single `hcount`
premise consumed by `ConcreteLowerAssembly`.
-/

open scoped ENNReal NNReal

namespace OnlineRamsey
namespace AllCasesHistoryCount

open QueryComplexity LowerAssembly StoppingHistory StoppingCoverage
open StoppingPrefixCount ConcreteLowerAssembly RecurrenceInstantiation
open AsymptoticScale HostGoodProbability OrdinaryAllOrders
open ExceptionalHistoryScale B4SharpScale

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- A single coefficient dominating the four deterministic main terms.  Its
dependence on `ell` comes only from the isolated-vertex `K₅-e` branch. -/
def allCasesCoefficient (ell : ℝ≥0) : ℝ≥0∞ :=
  (ordinaryUniformCoefficient : ℝ≥0∞) + 13271040 +
    ENNReal.ofReal (13934592000 / (ell : ℝ)) + 3583180800

/-- The common exact good/bad truncation error for every exceptional order. -/
def exceptionalOrderError (q ell : ℝ≥0)
    (strategy : K6Strategy (nnrealQueryBudget q ell)) : ℝ≥0∞ :=
  let N := nnrealQueryBudget q ell
  (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
    exceptionalBadMass (q ^ 3) strategy
      (edgeBudget (q : ℝ) 8 N)
      (degeneracyBudget (q : ℝ) 4 (edgeBudget (q : ℝ) 8 N)) 90
      (scaledPairBound (q : ℝ) 12 N)
      (scaledTripleBound (q : ℝ) (560 / (ell : ℝ)) N)

/-- The selected error: the checked recurrence tail in the ordinary branch,
and the exact host/transcript bad mass in each exceptional branch. -/
def allCasesError (q ell : ℝ≥0) (hq1 : q ≤ 1)
    (hN : 0 < nnrealQueryBudget q ell)
    (strategy : K6Strategy (nnrealQueryBudget q ell))
    (π : K6EdgeOrder) : ℝ≥0∞ :=
  if prefixCaseOfOrder π = .ordinary then
    (ordinaryTail q hq1 hN π : ℝ≥0∞)
  else
    exceptionalOrderError q ell strategy

theorem ordinaryCoefficient_le_allCasesCoefficient (ell : ℝ≥0) :
    (ordinaryUniformCoefficient : ℝ≥0∞) ≤ allCasesCoefficient ell := by
  unfold allCasesCoefficient
  exact (le_add_of_nonneg_right (zero_le (13271040 : ℝ≥0∞))).trans
    ((le_add_of_nonneg_right
      (zero_le (ENNReal.ofReal (13934592000 / (ell : ℝ))))).trans
        (le_add_of_nonneg_right (zero_le (3583180800 : ℝ≥0∞))))

theorem h3Coefficient_le_allCasesCoefficient (ell : ℝ≥0) :
    (13271040 : ℝ≥0∞) ≤ allCasesCoefficient ell := by
  unfold allCasesCoefficient
  exact (le_add_of_nonneg_left
      (zero_le (ordinaryUniformCoefficient : ℝ≥0∞))).trans
    ((le_add_of_nonneg_right
      (zero_le (ENNReal.ofReal (13934592000 / (ell : ℝ))))).trans
        (le_add_of_nonneg_right (zero_le (3583180800 : ℝ≥0∞))))

theorem k5Coefficient_le_allCasesCoefficient (ell : ℝ≥0) :
    ENNReal.ofReal (13934592000 / (ell : ℝ)) ≤
      allCasesCoefficient ell := by
  unfold allCasesCoefficient
  exact (le_add_of_nonneg_left
      (zero_le ((ordinaryUniformCoefficient : ℝ≥0∞) + 13271040))).trans
    (le_add_of_nonneg_right (zero_le (3583180800 : ℝ≥0∞)))

theorem b4Coefficient_le_allCasesCoefficient (ell : ℝ≥0) :
    (3583180800 : ℝ≥0∞) ≤ allCasesCoefficient ell := by
  unfold allCasesCoefficient
  exact le_add_of_nonneg_left (zero_le
    ((ordinaryUniformCoefficient : ℝ≥0∞) + 13271040 +
      ENNReal.ofReal (13934592000 / (ell : ℝ))))

/-- The concrete, classifier-indexed `hcount` for every one of the `15!`
relative edge orders. -/
theorem allCases_prefixHistoryMass_le
    (q ell : ℝ≥0) (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (nnrealQueryBudget q ell))
    (hfresh : FreshForBudget strategy) (π : K6EdgeOrder) :
    orderPrefixHistoryMass ((q ^ 3 : ℝ≥0) : ℝ≥0∞) strategy π
        (casePrefixLength (prefixCaseOfOrder π)) ≤
      allCasesCoefficient ell *
          ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ prefixExponent (prefixCaseOfOrder π) *
          (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3 +
        allCasesError q ell hq1 (nnrealQueryBudget_pos hq hfloor)
          strategy π := by
  let N := nnrealQueryBudget q ell
  have hN : 0 < N := nnrealQueryBudget_pos hq hfloor
  have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1Real : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  have hellReal : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hfloorReal : 2 * (q : ℝ) ^ 10 ≤ (ell : ℝ) := by
    exact_mod_cast hfloor
  have hpairReal : 2 * (q : ℝ) ^ 4 ≤ 12 * (ell : ℝ) := by
    exact_mod_cast hpairSmall
  have hedgeReal : 2 * (q : ℝ) ^ 7 ≤ 8 * (ell : ℝ) := by
    exact_mod_cast hedgeSmall
  have hpCube : unitInterval.toNNReal
      (cubeProbability (q : ℝ) hqReal.le hq1Real) = q ^ 3 :=
    SmallEllBadMass.toNNReal_cubeProbability_eq q hq1
  rcases prefixCaseOfOrder_spec π with hord | hh3 | hk5 | hb4
  · have hraw := ordinaryCase_hcount q hq1 hN strategy hfresh π hord.1
    calc
      orderPrefixHistoryMass ((q ^ 3 : ℝ≥0) : ℝ≥0∞) strategy π
          (casePrefixLength (prefixCaseOfOrder π)) ≤
        (ordinaryUniformCoefficient : ℝ≥0∞) *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ prefixExponent (prefixCaseOfOrder π) *
              (N : ℝ≥0∞) ^ 3 +
          (ordinaryTail q hq1 hN π : ℝ≥0∞) := hraw
      _ ≤ allCasesCoefficient ell *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ prefixExponent (prefixCaseOfOrder π) *
              (N : ℝ≥0∞) ^ 3 +
          (ordinaryTail q hq1 hN π : ℝ≥0∞) := by
        gcongr
        exact ordinaryCoefficient_le_allCasesCoefficient ell
      _ = _ := by
        simp [allCasesError, hord.1, N]
  · have hraw := h3_orderNinePrefixHistoryMass_cubicScale_le
      hqReal hq1Real hellReal hfloorReal hpairReal hedgeReal
        strategy hfresh π hh3.2
    rw [hpCube] at hraw
    have hscaled :
        orderPrefixHistoryMass ((q ^ 3 : ℝ≥0) : ℝ≥0∞) strategy π
            ninePrefixLength ≤
          allCasesCoefficient ell * ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 4 *
              (N : ℝ≥0∞) ^ 3 +
            exceptionalOrderError q ell strategy := by
      refine hraw.trans ?_
      dsimp only [exceptionalOrderError, N, nnrealQueryBudget]
      gcongr
      exact h3Coefficient_le_allCasesCoefficient ell
    simpa [allCasesError, hh3.1, casePrefixLength, prefixExponent, N] using hscaled
  · have hraw := k5_orderNinePrefixHistoryMass_cubicScale_le
      hqReal hq1Real hellReal hfloorReal hpairReal hedgeReal
        strategy hfresh π hk5.2
    rw [hpCube] at hraw
    have hscaled :
        orderPrefixHistoryMass ((q ^ 3 : ℝ≥0) : ℝ≥0∞) strategy π
            ninePrefixLength ≤
          allCasesCoefficient ell * ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 4 *
              (N : ℝ≥0∞) ^ 3 +
            exceptionalOrderError q ell strategy := by
      refine hraw.trans ?_
      dsimp only [exceptionalOrderError, N, nnrealQueryBudget]
      gcongr
      exact k5Coefficient_le_allCasesCoefficient ell
    simpa [allCasesError, hk5.1, casePrefixLength, prefixExponent, N] using hscaled
  · have hraw := b4_orderTenPrefixHistoryMass_cubicScale_le
      (B₃ := 560 / (ell : ℝ)) hqReal hq1Real hellReal hfloorReal
        hpairReal hedgeReal strategy hfresh π hb4.2
    rw [hpCube] at hraw
    have hscaled :
        orderPrefixHistoryMass ((q ^ 3 : ℝ≥0) : ℝ≥0∞) strategy π
            tenPrefixLength ≤
          allCasesCoefficient ell * ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 5 *
              (N : ℝ≥0∞) ^ 3 +
            exceptionalOrderError q ell strategy := by
      refine hraw.trans ?_
      dsimp only [exceptionalOrderError, N, nnrealQueryBudget]
      gcongr
      exact b4Coefficient_le_allCasesCoefficient ell
    simpa [allCasesError, hb4.1, casePrefixLength, prefixExponent, N] using hscaled

end
end AllCasesHistoryCount
end OnlineRamsey
