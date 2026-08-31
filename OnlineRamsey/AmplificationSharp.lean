import OnlineRamsey.Amplification
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical slack in the finite amplification bound

The elementary amplification module records the convenient estimate
`exp (-1) ≤ 1/2`.  The concrete branch-and-fill construction also has small
reservoir and scan failure probabilities, so it is useful to retain a little
of the numerical slack: in fact `exp (-1) < 3/8`.
-/

namespace OnlineRamsey
namespace Amplification

/-- A rational strengthening of `exp_neg_one_le_half`. -/
theorem exp_neg_one_lt_three_eighths :
    Real.exp (-1) < (3 : ℝ) / 8 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 1)).2
  have he : (8 : ℝ) / 3 < Real.exp 1 := by
    exact (by norm_num : (8 : ℝ) / 3 < 2.7182818283).trans
      Real.exp_one_gt_d9
  nlinarith [Real.exp_pos 1]

/-- The exact repeated `K₄` failure mass leaves a fixed positive margin
below one half. -/
theorem repeatedK4FailureMass_toReal_lt_three_eighths
    (a : ℕ) (ha : 2 ≤ a) :
    (repeatedK4FailureMass a
      (K6Upper.momentAmplification * a ^ 2)).toReal < (3 : ℝ) / 8 :=
  (repeatedK4FailureMass_toReal_le_exp_neg_one a ha).trans_lt
    exp_neg_one_lt_three_eighths

end Amplification
end OnlineRamsey
