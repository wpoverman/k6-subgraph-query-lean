import OnlineRamsey.BudgetMonotonicity
import OnlineRamsey.LowerDensityPackaging

/-!
# From one forbidden floor budget to the normalized lower bound

The analytic lower-bound argument naturally rules out the canonical budget
`floor (ell / q^10)` for all sufficiently small `q`.  This module turns that
statement into the lower half of the query-complexity power law.  The only
game-theoretic ingredient is budget monotonicity: a successful smaller
strategy would lift to the forbidden canonical budget.
-/

namespace OnlineRamsey
namespace LowerBudgetTransfer

open scoped ENNReal NNReal
open QueryComplexity
open RecurrenceInstantiation

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- If a natural budget has normalized size strictly below `ell`, then it is
at most the canonical floor `floor (ell / q^10)`. -/
theorem le_nnrealQueryBudget_of_normalized_lt
    {q ell : ℝ≥0} (hq : 0 < q) {N : ℕ}
    (hN : q ^ 10 * (N : ℝ≥0) < ell) :
    N ≤ nnrealQueryBudget q ell := by
  have hq10 : 0 < (q : ℝ) ^ 10 := pow_pos (by exact_mod_cast hq) _
  have hreal : (N : ℝ) ≤ (ell : ℝ) / (q : ℝ) ^ 10 := by
    apply (le_div_iff₀ hq10).2
    have hcast : (q : ℝ) ^ 10 * (N : ℝ) < (ell : ℝ) := by
      exact_mod_cast hN
    simpa [mul_comm] using hcast.le
  unfold nnrealQueryBudget AsymptoticScale.queryBudget
  exact Nat.le_floor hreal

/-- Ruling out the canonical floor budget forces every achievable budget to
have normalized size at least `ell`. -/
theorem normalized_lower_of_queryBudget_not_achievable
    {q ell : ℝ≥0} (hq : 0 < q)
    (hforbidden : ¬Achievable ((q ^ 3 : ℝ≥0) : ℝ≥0∞)
      (nnrealQueryBudget q ell))
    {N : ℕ} (hN : Achievable ((q ^ 3 : ℝ≥0) : ℝ≥0∞) N) :
    (ell : ℝ≥0∞) ≤ (N : ℝ≥0∞) * (q : ℝ≥0∞) ^ 10 := by
  by_contra hnot
  have hltENN : (N : ℝ≥0∞) * (q : ℝ≥0∞) ^ 10 < ell :=
    lt_of_not_ge hnot
  have hltNN : q ^ 10 * (N : ℝ≥0) < ell := by
    have : (N : ℝ≥0) * q ^ 10 < ell := by
      exact_mod_cast hltENN
    simpa [mul_comm] using this
  have hbudget : N ≤ nnrealQueryBudget q ell :=
    le_nnrealQueryBudget_of_normalized_lt hq hltNN
  exact hforbidden
    (BudgetMonotonicity.achievable_mono_budget hbudget hN)

/-- A family of forbidden canonical budgets supplies the small-density lower
estimate in the `ENNReal` parameterization used by `FiniteCubicPowerLaw`. -/
theorem small_density_lower_of_queryBudget_obstruction
    (q₀ ell : ℝ≥0)
    (hforbidden : ∀ q : ℝ≥0, 0 < q → q ≤ 1 → q < q₀ →
      ¬Achievable ((q ^ 3 : ℝ≥0) : ℝ≥0∞)
        (nnrealQueryBudget q ell)) :
    ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 → q < (q₀ : ℝ≥0∞) →
      ∀ N, Achievable (q ^ 3) N →
        (ell : ℝ≥0∞) ≤ (N : ℝ≥0∞) * q ^ 10 := by
  intro q hq hq1 hqq₀ N hN
  have hqtop : q ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  let qnn : ℝ≥0 := q.toNNReal
  have hcoe : (qnn : ℝ≥0∞) = q := ENNReal.coe_toNNReal hqtop
  have hqnn : 0 < qnn := by
    exact_mod_cast (show (0 : ℝ≥0∞) < (qnn : ℝ≥0∞) by simpa [hcoe] using hq)
  have hqnn1 : qnn ≤ 1 := by
    exact_mod_cast (show (qnn : ℝ≥0∞) ≤ 1 by simpa [hcoe] using hq1)
  have hqnnq₀ : qnn < q₀ := by
    exact_mod_cast (show (qnn : ℝ≥0∞) < (q₀ : ℝ≥0∞) by
      simpa [hcoe] using hqq₀)
  have hforbid := hforbidden qnn hqnn hqnn1 hqnnq₀
  have hAch : Achievable ((qnn ^ 3 : ℝ≥0) : ℝ≥0∞) N := by
    simpa [hcoe] using hN
  have hlower := normalized_lower_of_queryBudget_not_achievable
    hqnn hforbid hAch
  simpa [hcoe] using hlower

/-- Complete all-density lower-bound packaging.  Below `q₀` it uses the
forbidden canonical budget; above `q₀` it uses the universal fact that a
successful `K₆` transcript contains at least fifteen queried edges. -/
theorem global_lower_of_queryBudget_obstruction
    (q₀ ell : ℝ≥0) (hq₀1 : q₀ ≤ 1)
    (hforbidden : ∀ q : ℝ≥0, 0 < q → q ≤ 1 → q < q₀ →
      ¬Achievable ((q ^ 3 : ℝ≥0) : ℝ≥0∞)
        (nnrealQueryBudget q ell)) :
    ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∀ N, Achievable (q ^ 3) N →
        min (ell : ℝ≥0∞) (15 * (q₀ : ℝ≥0∞) ^ 10) ≤
          (N : ℝ≥0∞) * q ^ 10 := by
  apply LowerDensityPackaging.global_lower_of_small_density
    (q₀ : ℝ≥0∞) (ell : ℝ≥0∞)
  · exact_mod_cast hq₀1
  · exact small_density_lower_of_queryBudget_obstruction q₀ ell hforbidden

/-- The constant returned by the preceding theorem is genuinely positive. -/
theorem global_queryBudget_lower_constant_pos
    {q₀ ell : ℝ≥0} (hq₀ : 0 < q₀) (hell : 0 < ell) :
    0 < min (ell : ℝ≥0∞) (15 * (q₀ : ℝ≥0∞) ^ 10) := by
  apply LowerDensityPackaging.global_lower_constant_pos
  · exact_mod_cast hq₀
  · exact_mod_cast hell

end
end LowerBudgetTransfer
end OnlineRamsey
