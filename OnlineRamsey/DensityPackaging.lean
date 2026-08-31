import OnlineRamsey.Amplification
import OnlineRamsey.AsymptoticScale
import OnlineRamsey.QueryComplexity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cubic-density packaging for the `K₆` upper bound

The probabilistic construction is naturally described with an integer scale
`a` and density comparable to `a⁻³`, whereas the query-complexity theorem is
stated at an arbitrary density `p = q³`.  This file performs the finite
rounding and minimization bookkeeping between those two descriptions.

For `0 < q ≤ 1` we choose

`a(q) = max 2 ⌈q⁻¹⌉`.

The maximum handles the bounded-density endpoint required by the finite
`K₄` moment calculation.  The two useful bucket inequalities are

* `a(q)⁻³ ≤ q³`;
* `a(q) q ≤ 2`.

Consequently the explicit branch-and-fill budget is at most
`368641 * 2¹⁰ * q⁻¹⁰`.

The final section exposes a strategy-construction interface.  It does not
assume the desired asymptotic upper bound: an implementation must supply an
actual deterministic strategy, at the fixed branch-and-fill budget, together
with pathwise admissibility and its success estimate throughout each density
bucket.  The theorems here turn such an implementation into
`QueryComplexity.Achievable` and into the exact `hupper` premise of the
top-level power-law theorem.
-/

namespace OnlineRamsey
namespace DensityPackaging

open scoped ENNReal

noncomputable section

/-- The density corresponding to the cubic-root parameter `q`. -/
def cubicDensity (q : ℝ≥0∞) : ℝ≥0∞ := q ^ 3

/-- Integer reciprocal scale, truncated below at two so that all finite
`K₄` moment estimates apply even at densities bounded away from zero. -/
noncomputable def integerScale (q : ℝ≥0∞) : ℕ :=
  max 2 ⌈(q.toReal)⁻¹⌉₊

/-- The explicit branch-and-fill query budget at density `q³`. -/
noncomputable def upperBudget (q : ℝ≥0∞) : ℕ :=
  K6Upper.scaledBranchFillQueries (integerScale q) K6Upper.momentAmplification

/-- A uniform normalized-budget constant. -/
def upperConstant : ℕ := 368641 * 2 ^ 10

theorem finite_q_of_le_one {q : ℝ≥0∞} (hq1 : q ≤ 1) : q ≠ ∞ := by
  exact (hq1.trans_lt ENNReal.one_lt_top).ne

theorem q_toReal_pos {q : ℝ≥0∞} (hq : 0 < q) (hq1 : q ≤ 1) :
    0 < q.toReal := by
  exact ENNReal.toReal_pos hq.ne' (finite_q_of_le_one hq1)

theorem q_toReal_le_one {q : ℝ≥0∞} (hq1 : q ≤ 1) :
    q.toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (by simp) hq1

theorem integerScale_ge_two (q : ℝ≥0∞) : 2 ≤ integerScale q := by
  exact Nat.le_max_left _ _

theorem ceil_reciprocal_le_integerScale (q : ℝ≥0∞) :
    ⌈(q.toReal)⁻¹⌉₊ ≤ integerScale q := by
  exact Nat.le_max_right _ _

/-- The lower half of the reciprocal bucket: `q⁻¹ ≤ a(q)`. -/
theorem reciprocal_le_integerScale_cast {q : ℝ≥0∞}
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (q.toReal)⁻¹ ≤ (integerScale q : ℝ) := by
  have hqR : 0 < q.toReal := q_toReal_pos hq hq1
  have hceil : (q.toReal)⁻¹ ≤ ((⌈(q.toReal)⁻¹⌉₊ : ℕ) : ℝ) := by
    exact Nat.le_ceil ((q.toReal)⁻¹)
  have hscale : ((⌈(q.toReal)⁻¹⌉₊ : ℕ) : ℝ) ≤
      (integerScale q : ℝ) := by
    exact_mod_cast ceil_reciprocal_le_integerScale q
  exact hceil.trans hscale

/-- The upper half of the reciprocal bucket, including the `max 2` endpoint:
`a(q) q ≤ 2`. -/
theorem integerScale_mul_q_toReal_le_two {q : ℝ≥0∞}
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (integerScale q : ℝ) * q.toReal ≤ 2 := by
  have hqR : 0 < q.toReal := q_toReal_pos hq hq1
  have hqR1 : q.toReal ≤ 1 := q_toReal_le_one hq1
  by_cases hlarge : 2 ≤ ⌈(q.toReal)⁻¹⌉₊
  · have hscale : integerScale q = ⌈(q.toReal)⁻¹⌉₊ := by
      exact Nat.max_eq_right hlarge
    rw [hscale]
    have hceil : (((⌈(q.toReal)⁻¹⌉₊ : ℕ) : ℝ)) <
        (q.toReal)⁻¹ + 1 :=
      Nat.ceil_lt_add_one (inv_nonneg.mpr hqR.le)
    calc
      (((⌈(q.toReal)⁻¹⌉₊ : ℕ) : ℝ)) * q.toReal ≤
          ((q.toReal)⁻¹ + 1) * q.toReal :=
        mul_le_mul_of_nonneg_right hceil.le hqR.le
      _ = 1 + q.toReal := by field_simp [ne_of_gt hqR]
      _ ≤ 2 := by linarith
  · have hsmall : ⌈(q.toReal)⁻¹⌉₊ ≤ 2 := by omega
    have hscale : integerScale q = 2 := by
      exact Nat.max_eq_left hsmall
    rw [hscale]
    norm_num
    linarith

/-- The selected integer bucket has density no larger than the target
density.  This is the exact relation used by a density-robust upper
construction. -/
theorem integerScale_density_le_cubicDensity {q : ℝ≥0∞}
    (hq : 0 < q) (hq1 : q ≤ 1) :
    K4OneTrial.densityENN (integerScale q) ≤ cubicDensity q := by
  have hqtop : q ≠ ∞ := finite_q_of_le_one hq1
  have hqR : 0 < q.toReal := q_toReal_pos hq hq1
  have haNat : 0 < integerScale q :=
    (by norm_num : 0 < 2).trans_le (integerScale_ge_two q)
  have haR : (0 : ℝ) < (integerScale q : ℝ) := by exact_mod_cast haNat
  have hrecip := reciprocal_le_integerScale_cast hq hq1
  have hone : 1 ≤ q.toReal * (integerScale q : ℝ) := by
    calc
      1 = (q.toReal)⁻¹ * q.toReal := by field_simp [ne_of_gt hqR]
      _ ≤ (integerScale q : ℝ) * q.toReal :=
        mul_le_mul_of_nonneg_right hrecip hqR.le
      _ = q.toReal * (integerScale q : ℝ) := by ring
  have hbase : 1 / (integerScale q : ℝ) ≤ q.toReal := by
    exact (div_le_iff₀ haR).2 (by simpa [mul_comm] using hone)
  have hreal : K4MomentBounds.density (integerScale q) ≤ q.toReal ^ 3 := by
    rw [K4MomentBounds.density]
    have hpow : (1 / (integerScale q : ℝ)) ^ 3 ≤ q.toReal ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hbase 3
    simpa [div_pow] using hpow
  apply (ENNReal.toReal_le_toReal (by simp [K4OneTrial.densityENN])
    (ENNReal.pow_ne_top hqtop)).mp
  simpa [K4OneTrial.densityENN, cubicDensity,
    K4OneTrial.density_nonneg] using hreal

theorem cubicDensity_le_one {q : ℝ≥0∞} (hq1 : q ≤ 1) :
    cubicDensity q ≤ 1 := by
  unfold cubicDensity
  exact pow_le_one₀ bot_le hq1

/-- Real form of the explicit normalized budget estimate. -/
theorem upperBudget_mul_q_toReal_pow_le {q : ℝ≥0∞}
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (upperBudget q : ℝ) * q.toReal ^ 10 ≤ (upperConstant : ℝ) := by
  have ha : 1 ≤ integerScale q :=
    (by norm_num : 1 ≤ 2).trans (integerScale_ge_two q)
  have hbudgetNat := K6Upper.scaledBranchFillQueries_explicit (integerScale q) ha
  have hbudget : (upperBudget q : ℝ) ≤
      368641 * (integerScale q : ℝ) ^ 10 := by
    exact_mod_cast hbudgetNat
  have hqR0 : 0 ≤ q.toReal := ENNReal.toReal_nonneg
  have hscale : (integerScale q : ℝ) * q.toReal ≤ 2 :=
    integerScale_mul_q_toReal_le_two hq hq1
  calc
    (upperBudget q : ℝ) * q.toReal ^ 10 ≤
        (368641 * (integerScale q : ℝ) ^ 10) * q.toReal ^ 10 :=
      mul_le_mul_of_nonneg_right hbudget (pow_nonneg hqR0 _)
    _ = 368641 * ((integerScale q : ℝ) * q.toReal) ^ 10 := by ring
    _ ≤ 368641 * 2 ^ 10 := by
      gcongr
    _ = (upperConstant : ℝ) := by norm_num [upperConstant]

/-- `ENNReal` form used by `QueryComplexity.FiniteCubicPowerLaw`. -/
theorem upperBudget_normalized_le {q : ℝ≥0∞}
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (upperBudget q : ℝ≥0∞) * q ^ 10 ≤ (upperConstant : ℝ≥0∞) := by
  have hqtop : q ≠ ∞ := finite_q_of_le_one hq1
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top hqtop)) (by simp)).mp
  simpa [ENNReal.toReal_mul, hqtop] using
    upperBudget_mul_q_toReal_pow_le hq hq1

/-! ## Strategy-construction interface -/

/-- Any budget bounded by `C a¹⁰` has normalized cubic-scale cost at most
`C 2¹⁰` in the rounded bucket selected above. -/
theorem normalized_le_of_budget_le
    (C N : ℕ) {q : ℝ≥0∞} (hq : 0 < q) (hq1 : q ≤ 1)
    (hN : N ≤ C * integerScale q ^ 10) :
    (N : ℝ≥0∞) * q ^ 10 ≤ ((C * 2 ^ 10 : ℕ) : ℝ≥0∞) := by
  have hqtop : q ≠ ∞ := finite_q_of_le_one hq1
  have hrealN : (N : ℝ) ≤ (C : ℝ) * (integerScale q : ℝ) ^ 10 := by
    exact_mod_cast hN
  have hqR0 : 0 ≤ q.toReal := ENNReal.toReal_nonneg
  have hscale := integerScale_mul_q_toReal_le_two hq hq1
  have hreal : (N : ℝ) * q.toReal ^ 10 ≤ (C : ℝ) * 2 ^ 10 := by
    calc
      (N : ℝ) * q.toReal ^ 10 ≤
          ((C : ℝ) * (integerScale q : ℝ) ^ 10) * q.toReal ^ 10 :=
        mul_le_mul_of_nonneg_right hrealN (pow_nonneg hqR0 _)
      _ = (C : ℝ) * ((integerScale q : ℝ) * q.toReal) ^ 10 := by ring
      _ ≤ (C : ℝ) * 2 ^ 10 := by
        gcongr
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top hqtop)) (by finiteness)).mp
  norm_num at hreal ⊢
  simpa [ENNReal.toReal_mul, hqtop] using hreal

/-- Flexible construction interface for a branch-and-fill implementation.

The construction chooses its own exact budget, so constant slack for
reservoir concentration, scans, and fill operations is available.  What is
fixed is the substantive polynomial certificate `budget ≤ C a¹⁰`, together
with an actual strategy at that budget and its pathwise/probabilistic
correctness throughout every density bucket. -/
structure BudgetedBucketStrategyFamily (C : ℕ) where
  budget : ℝ≥0∞ → ℕ → ℕ
  strategy : ∀ (p : ℝ≥0∞) (a : ℕ),
    QueryComplexity.K6Strategy (budget p a)
  budget_le : ∀ (p : ℝ≥0∞) (a : ℕ), 2 ≤ a →
    budget p a ≤ C * a ^ 10
  admissible : ∀ (p : ℝ≥0∞) (a : ℕ), 2 ≤ a →
    K4OneTrial.densityENN a ≤ p → p ≤ 1 →
      QueryComplexity.Admissible (strategy p a)
  succeeds : ∀ (p : ℝ≥0∞) (a : ℕ), 2 ≤ a →
    K4OneTrial.densityENN a ≤ p → p ≤ 1 →
      QueryComplexity.threshold ≤
        QueryComplexity.successProbability p (budget p a) (strategy p a)

/-- Instantiate a flexible construction at `p=q³`. -/
theorem achievable_of_budgetedBucketStrategyFamily
    {C : ℕ} (family : BudgetedBucketStrategyFamily C)
    {q : ℝ≥0∞} (hq : 0 < q) (hq1 : q ≤ 1) :
    QueryComplexity.Achievable (cubicDensity q)
      (family.budget (cubicDensity q) (integerScale q)) := by
  let a := integerScale q
  have ha : 2 ≤ a := integerScale_ge_two q
  have hdensity : K4OneTrial.densityENN a ≤ cubicDensity q :=
    integerScale_density_le_cubicDensity hq hq1
  have hp1 : cubicDensity q ≤ 1 := cubicDensity_le_one hq1
  exact ⟨hp1, family.strategy (cubicDensity q) a,
    family.admissible (cubicDensity q) a ha hdensity hp1,
    family.succeeds (cubicDensity q) a ha hdensity hp1⟩

/-- A flexible concrete family yields the exact top-level upper hypothesis;
its asymptotic constant is the construction's budget coefficient times the
rounding loss `2¹⁰`. -/
theorem upperHypothesis_of_budgetedBucketStrategyFamily
    {C : ℕ} (family : BudgetedBucketStrategyFamily C) :
    ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∃ N, QueryComplexity.Achievable (q ^ 3) N ∧
        (N : ℝ≥0∞) * q ^ 10 ≤ ((C * 2 ^ 10 : ℕ) : ℝ≥0∞) := by
  intro q hq hq1
  let a := integerScale q
  let N := family.budget (cubicDensity q) a
  refine ⟨N, ?_, ?_⟩
  · simpa [cubicDensity, N] using
      achievable_of_budgetedBucketStrategyFamily family hq hq1
  · apply normalized_le_of_budget_le C N hq hq1
    simpa [a, N] using family.budget_le (cubicDensity q) a (integerScale_ge_two q)

/-- Final upper/lower packaging using a flexible budgeted construction. -/
theorem finiteCubicPowerLaw_of_lower_and_budgetedBucketStrategyFamily
    (c : ℝ≥0∞) {C : ℕ}
    (hlower : ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∀ N, QueryComplexity.Achievable (q ^ 3) N →
        c ≤ (N : ℝ≥0∞) * q ^ 10)
    (family : BudgetedBucketStrategyFamily C) :
    QueryComplexity.FiniteCubicPowerLaw QueryComplexity.Achievable c
      ((C * 2 ^ 10 : ℕ) : ℝ≥0∞) :=
  QueryComplexity.k6_powerLaw_of_matching_bounds c
    ((C * 2 ^ 10 : ℕ) : ℝ≥0∞) hlower
    (upperHypothesis_of_budgetedBucketStrategyFamily family)

/-- A concrete branch-and-fill implementation supplies one deterministic
strategy for each input density and each integer bucket.  The budget is fixed
by the construction, rather than chosen existentially. -/
abbrev BucketStrategyFamily :=
  ∀ (_p : ℝ≥0∞) (a : ℕ),
    QueryComplexity.K6Strategy
      (K6Upper.scaledBranchFillQueries a K6Upper.momentAmplification)

/-- Correctness obligations for a bucketed strategy family.

The density lower bound `densityENN a ≤ p` is the substantive robustness
condition connecting the exact one-trial model at density `a⁻³` to the
actual input density. -/
structure ValidBucketStrategyFamily (family : BucketStrategyFamily) : Prop where
  admissible : ∀ (p : ℝ≥0∞) (a : ℕ), 2 ≤ a →
    K4OneTrial.densityENN a ≤ p → p ≤ 1 →
      QueryComplexity.Admissible (family p a)
  succeeds : ∀ (p : ℝ≥0∞) (a : ℕ), 2 ≤ a →
    K4OneTrial.densityENN a ≤ p → p ≤ 1 →
      QueryComplexity.threshold ≤
        QueryComplexity.successProbability p
          (K6Upper.scaledBranchFillQueries a K6Upper.momentAmplification)
          (family p a)

/-- Instantiate a valid bucketed construction at arbitrary `p=q³`. -/
theorem achievable_of_validBucketStrategyFamily
    (family : BucketStrategyFamily) (hfamily : ValidBucketStrategyFamily family)
    {q : ℝ≥0∞} (hq : 0 < q) (hq1 : q ≤ 1) :
    QueryComplexity.Achievable (cubicDensity q) (upperBudget q) := by
  let a := integerScale q
  have ha : 2 ≤ a := integerScale_ge_two q
  have hdensity : K4OneTrial.densityENN a ≤ cubicDensity q :=
    integerScale_density_le_cubicDensity hq hq1
  have hp1 : cubicDensity q ≤ 1 := cubicDensity_le_one hq1
  refine ⟨hp1, family (cubicDensity q) a, ?_, ?_⟩
  · exact hfamily.admissible (cubicDensity q) a ha hdensity hp1
  · exact hfamily.succeeds (cubicDensity q) a ha hdensity hp1

/-- A concrete bucketed strategy family supplies exactly the upper-bound
hypothesis required by the finite cubic power-law theorem, with an explicit
constant. -/
theorem upperHypothesis_of_validBucketStrategyFamily
    (family : BucketStrategyFamily) (hfamily : ValidBucketStrategyFamily family) :
    ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∃ N, QueryComplexity.Achievable (q ^ 3) N ∧
        (N : ℝ≥0∞) * q ^ 10 ≤ (upperConstant : ℝ≥0∞) := by
  intro q hq hq1
  refine ⟨upperBudget q, ?_, upperBudget_normalized_le hq hq1⟩
  simpa [cubicDensity] using
    achievable_of_validBucketStrategyFamily family hfamily hq hq1

/-- Top-level packaging: after the lower estimate has been established, an
actual bucketed upper strategy family gives the complete finite cubic-scale
power law. -/
theorem finiteCubicPowerLaw_of_lower_and_validBucketStrategyFamily
    (c : ℝ≥0∞)
    (hlower : ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∀ N, QueryComplexity.Achievable (q ^ 3) N →
        c ≤ (N : ℝ≥0∞) * q ^ 10)
    (family : BucketStrategyFamily) (hfamily : ValidBucketStrategyFamily family) :
    QueryComplexity.FiniteCubicPowerLaw QueryComplexity.Achievable c
      (upperConstant : ℝ≥0∞) :=
  QueryComplexity.k6_powerLaw_of_matching_bounds c
    (upperConstant : ℝ≥0∞) hlower
    (upperHypothesis_of_validBucketStrategyFamily family hfamily)

end
end DensityPackaging
end OnlineRamsey
