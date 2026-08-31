import OnlineRamsey.AllCasesHistoryCount
import OnlineRamsey.SmallEllErrorTendsToZero

/-!
# Uniform all-cases prefix bounds

This module replaces the branch-dependent error in the checked four-case
prefix estimate by the single nonnegative error whose finite sum is known to
vanish at the floored cubic query scale.  It then feeds that bound directly
into the concrete all-orders success-probability assembly.
-/

open scoped BigOperators ENNReal NNReal

namespace OnlineRamsey
namespace UnifiedAllCasesHCount

open QueryComplexity LowerAssembly StoppingHistory StoppingCoverage
open StoppingPrefixCount ConcreteLowerAssembly RecurrenceInstantiation
open AsymptoticScale HostGoodProbability OrdinaryAllOrders
open AllCasesHistoryCount SmallEllError

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-- The branch-dependent error from `AllCasesHistoryCount` is dominated by
the common error used in the small-density limit.  In the ordinary branch
this just adds two nonnegative terms.  In every exceptional branch it is the
small-`ell` sampled-host estimate plus the exact selected pair tail. -/
theorem allCasesError_le_coe_unifiedPerOrderError
    (q ell : ℝ≥0) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * (q : ℝ) ≤
      (4 : ℝ) * √(8 * (ell : ℝ) / 2))
    (strategy : K6Strategy (nnrealQueryBudget q ell))
    (hfresh : FreshForBudget strategy) (pi : K6EdgeOrder) :
    allCasesError q ell (hqhalf.trans (by norm_num))
        (nnrealQueryBudget_pos hq hfloor) strategy pi ≤
      (unifiedPerOrderError q ell (hqhalf.trans (by norm_num))
        (nnrealQueryBudget_pos hq hfloor) pi : ℝ≥0∞) := by
  let hq1 : q ≤ 1 := hqhalf.trans (by norm_num)
  let hN : 0 < nnrealQueryBudget q ell := nnrealQueryBudget_pos hq hfloor
  by_cases hord : prefixCaseOfOrder pi = .ordinary
  · simp only [allCasesError, hord, if_true]
    exact ENNReal.coe_le_coe.mpr (by
      simp only [unifiedPerOrderError]
      exact le_add_of_nonneg_left
        (zero_le (smallEllHostError q ell + selectedPairTail q ell pi)))
  · have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hqhalfReal : (q : ℝ) ≤ 1 / 2 := by exact_mod_cast hqhalf
    have hell0Real : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell0
    have hell1Real : (ell : ℝ) ≤ 1 := by exact_mod_cast hell1
    have hfloorReal : 2 * (q : ℝ) ^ 10 ≤ (ell : ℝ) := by
      exact_mod_cast hfloor
    have hpairScaleReal : 40 * (q : ℝ) ^ 3 ≤ (ell : ℝ) := by
      exact_mod_cast hpairScale
    have hbad := SmallEllBadMass.scaledSmallEllHostEdgeGood_crudeSixVertex_le
      hqReal hqhalfReal hell0Real hell1Real hfloorReal hpairScaleReal hdense
      strategy hfresh (selectedPrefixPattern pi)
    have hpCube : unitInterval.toNNReal
        (cubeProbability (q : ℝ) hqReal.le
          (hqhalfReal.trans (by norm_num))) = q ^ 3 :=
      SmallEllBadMass.toNNReal_cubeProbability_eq q hq1
    have hexceptional : exceptionalOrderError q ell strategy ≤
        (smallEllHostError q ell : ℝ≥0∞) +
          (selectedPairTail q ell pi : ℝ≥0∞) := by
      dsimp only at hbad
      rw [hpCube] at hbad
      simpa only [exceptionalOrderError, exceptionalBadMass,
        exceptionalGoodEvent, selectedPairTail,
        coe_smallEllHostError_eq_ofReal, nnrealQueryBudget] using hbad
    simp only [allCasesError, hord, if_false]
    refine hexceptional.trans ?_
    rw [← ENNReal.coe_add]
    exact ENNReal.coe_le_coe.mpr (by
      simp only [unifiedPerOrderError]
      exact le_add_of_nonneg_right (zero_le (ordinaryTail q hq1 hN pi)))

/-- Classifier-indexed prefix estimate with a strategy-independent error.
This is the exact `hcount` shape required by `ConcreteLowerAssembly`. -/
theorem unifiedAllCases_prefixHistoryMass_le
    (q ell : ℝ≥0) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * (q : ℝ) ≤
      (4 : ℝ) * √(8 * (ell : ℝ) / 2))
    (strategy : K6Strategy (nnrealQueryBudget q ell))
    (hfresh : FreshForBudget strategy) (pi : K6EdgeOrder) :
    orderPrefixHistoryMass ((q ^ 3 : ℝ≥0) : ℝ≥0∞) strategy pi
        (casePrefixLength (prefixCaseOfOrder pi)) ≤
      allCasesCoefficient ell *
          ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ prefixExponent (prefixCaseOfOrder pi) *
          (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3 +
        (unifiedPerOrderError q ell (hqhalf.trans (by norm_num))
          (nnrealQueryBudget_pos hq hfloor) pi : ℝ≥0∞) := by
  have hraw := allCases_prefixHistoryMass_le q ell hq
    (hqhalf.trans (by norm_num)) hell0 hfloor hpairSmall hedgeSmall
      strategy hfresh pi
  exact hraw.trans (add_le_add_left
    (allCasesError_le_coe_unifiedPerOrderError q ell hq hqhalf hell0
      hell1 hfloor hpairScale hdense strategy hfresh pi) _)

/-- Direct all-orders upper bound for the success probability of a fresh
strategy, with the one common vanishing error attached to each checked edge
order. -/
theorem successProbability_le_unifiedAllCases
    (q ell : ℝ≥0) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * (q : ℝ) ≤
      (4 : ℝ) * √(8 * (ell : ℝ) / 2))
    (strategy : K6Strategy (nnrealQueryBudget q ell))
    (hfresh : FreshForBudget strategy) :
    successProbability ((q ^ 3 : ℝ≥0) : ℝ≥0∞)
        (nnrealQueryBudget q ell) strategy ≤
      (Nat.factorial 15 : ℝ≥0∞) *
          (allCasesCoefficient ell *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10 *
            (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3) +
        ∑ pi : K6EdgeOrder,
          ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^
              completionExponent (prefixCaseOfOrder pi) *
            (unifiedPerOrderError q ell (hqhalf.trans (by norm_num))
              (nnrealQueryBudget_pos hq hfloor) pi : ℝ≥0∞) := by
  apply successProbability_le_of_prefixBounds
    ((q ^ 3 : ℝ≥0) : ℝ≥0∞) (allCasesCoefficient ell)
      (by
        exact_mod_cast pow_le_one₀ (zero_le q)
          (hqhalf.trans (by norm_num)) :
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ≤ 1)
      strategy hfresh prefixCaseOfOrder
      (fun pi ↦ (unifiedPerOrderError q ell
        (hqhalf.trans (by norm_num)) (nnrealQueryBudget_pos hq hfloor) pi :
          ℝ≥0∞))
  intro pi
  exact unifiedAllCases_prefixHistoryMass_le q ell hq hqhalf hell0 hell1
    hfloor hpairSmall hedgeSmall hpairScale hdense strategy hfresh pi

/-- The order-dependent sum is bounded by `15!` copies of the single
aggregate error.  This form separates the fixed deterministic main term from
one quantity already proved to tend to zero. -/
theorem successProbability_le_combinedError
    (q ell : ℝ≥0) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * (q : ℝ) ≤
      (4 : ℝ) * √(8 * (ell : ℝ) / 2))
    (strategy : K6Strategy (nnrealQueryBudget q ell))
    (hfresh : FreshForBudget strategy) :
    successProbability ((q ^ 3 : ℝ≥0) : ℝ≥0∞)
        (nnrealQueryBudget q ell) strategy ≤
      (Nat.factorial 15 : ℝ≥0∞) *
          (allCasesCoefficient ell *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10 *
            (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3) +
        (Nat.factorial 15 : ℝ≥0∞) *
          (smallEllCombinedError q ell (hqhalf.trans (by norm_num))
            (nnrealQueryBudget_pos hq hfloor) : ℝ≥0∞) := by
  let p : ℝ≥0∞ := ((q ^ 3 : ℝ≥0) : ℝ≥0∞)
  let hq1 : q ≤ 1 := hqhalf.trans (by norm_num)
  let hN : 0 < nnrealQueryBudget q ell := nnrealQueryBudget_pos hq hfloor
  let combined : ℝ≥0∞ :=
    (smallEllCombinedError q ell hq1 hN : ℝ≥0∞)
  have hp : p ≤ 1 := by
    dsimp only [p]
    exact_mod_cast pow_le_one₀ (zero_le q) hq1
  have hsum :
      ∑ pi : K6EdgeOrder,
          p ^ completionExponent (prefixCaseOfOrder pi) *
            (unifiedPerOrderError q ell hq1 hN pi : ℝ≥0∞) ≤
        (Nat.factorial 15 : ℝ≥0∞) * combined := by
    calc
      ∑ pi : K6EdgeOrder,
          p ^ completionExponent (prefixCaseOfOrder pi) *
            (unifiedPerOrderError q ell hq1 hN pi : ℝ≥0∞) ≤
          ∑ _pi : K6EdgeOrder, combined := by
        apply Finset.sum_le_sum
        intro pi _
        calc
          p ^ completionExponent (prefixCaseOfOrder pi) *
                (unifiedPerOrderError q ell hq1 hN pi : ℝ≥0∞) ≤
              1 * (unifiedPerOrderError q ell hq1 hN pi : ℝ≥0∞) := by
            gcongr
            exact pow_le_one₀ (zero_le p) hp
          _ ≤ 1 * combined := by
            gcongr
            exact ENNReal.coe_le_coe.mpr
              (unifiedPerOrderError_le_combined q ell hq1 hN pi)
          _ = combined := one_mul _
      _ = (Fintype.card K6EdgeOrder : ℝ≥0∞) * combined := by simp
      _ = (Nat.factorial 15 : ℝ≥0∞) * combined := by
        rw [card_k6EdgeOrder]
  have hraw := successProbability_le_unifiedAllCases q ell hq hqhalf
    hell0 hell1 hfloor hpairSmall hedgeSmall hpairScale hdense strategy hfresh
  dsimp only [p, hq1, hN, combined] at hsum ⊢
  exact hraw.trans (add_le_add_left hsum _)

/-- A finite, completely explicit smallness check for the deterministic term
and the aggregate error rules out the canonical floor budget. -/
theorem not_achievable_of_combinedError_lt_threshold
    (q ell : ℝ≥0) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * (q : ℝ) ≤
      (4 : ℝ) * √(8 * (ell : ℝ) / 2))
    (hsmall :
      (Nat.factorial 15 : ℝ≥0∞) *
          (allCasesCoefficient ell *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10 *
            (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3) +
        (Nat.factorial 15 : ℝ≥0∞) *
          (smallEllCombinedError q ell (hqhalf.trans (by norm_num))
            (nnrealQueryBudget_pos hq hfloor) : ℝ≥0∞) < threshold) :
    ¬ Achievable (((q ^ 3 : ℝ≥0) : ℝ≥0∞))
        (nnrealQueryBudget q ell) := by
  rintro ⟨_hp, strategy, hadmissible, hsuccess⟩
  have hupper := successProbability_le_combinedError q ell hq hqhalf
    hell0 hell1 hfloor hpairSmall hedgeSmall hpairScale hdense
      strategy hadmissible.1
  exact (not_lt_of_ge hsuccess) (hupper.trans_lt hsmall)

end
end UnifiedAllCasesHCount
end OnlineRamsey
