import OnlineRamsey.UpperStrategy

/-!
# A universal polynomial budget for the slack strategy

The sharper coefficient in `UpperStrategy.lean` assumes the integer bucket
is at least the amplification constant.  For the unconditional theorem it is
cleaner to retain a larger coefficient which works for every `a ≥ 1`.
-/

namespace OnlineRamsey
namespace UpperBudgetUniversal

open UpperStrategy

/-- Absolute coefficient valid at every positive integer scale. -/
def slackUniversalUpperConstant : ℕ :=
  16384 + 769 * K6Upper.momentAmplification

theorem slackReservoirSize_le_universal
    (a : ℕ) (ha : 1 ≤ a) :
    slackReservoirSize a ≤
      (128 + 4 * K6Upper.momentAmplification) * a ^ 7 := by
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hp2p7 : a ^ 2 ≤ a ^ 7 := Nat.pow_le_pow_right ha0 (by omega)
  have hp6p7 : a ^ 6 ≤ a ^ 7 := Nat.pow_le_pow_right ha0 (by omega)
  rw [slackReservoirSize, slackBranchScan_eq]
  unfold slackAttemptCount slackTrialCount slackFillSize
  calc
    128 * a ^ 7 + 2 * (K6Upper.momentAmplification * a ^ 2) *
          (a ^ 4 + 1) =
        128 * a ^ 7 +
          2 * K6Upper.momentAmplification * a ^ 6 +
          2 * K6Upper.momentAmplification * a ^ 2 := by ring
    _ ≤ 128 * a ^ 7 +
          2 * K6Upper.momentAmplification * a ^ 7 +
          2 * K6Upper.momentAmplification * a ^ 7 := by
      gcongr
    _ = (128 + 4 * K6Upper.momentAmplification) * a ^ 7 := by ring

/-- The complete implemented slack construction uses at most one universal
constant times `a¹⁰`, with no large-`a` side condition. -/
theorem slackQueryBudget_le_universal
    (a : ℕ) (ha : 1 ≤ a) :
    slackQueryBudget a ≤ slackUniversalUpperConstant * a ^ 10 := by
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hpow9 : a ^ 9 ≤ a ^ 10 :=
    Nat.pow_le_pow_right ha0 (by omega)
  have hstar : slackStarQueries a ≤
      (16384 + 512 * K6Upper.momentAmplification) * a ^ 10 := by
    unfold slackStarQueries slackBlockSize
    calc
      2 * slackReservoirSize a * (64 * a ^ 3) ≤
          2 * ((128 + 4 * K6Upper.momentAmplification) * a ^ 7) *
            (64 * a ^ 3) := by
        gcongr
        exact slackReservoirSize_le_universal a ha
      _ = (16384 + 512 * K6Upper.momentAmplification) * a ^ 10 := by
        ring
  have hbranch : slackAttemptCount a * slackBranchScan a ≤
      (256 * K6Upper.momentAmplification) * a ^ 10 := by
    rw [slackBranchScan_eq]
    unfold slackAttemptCount slackTrialCount
    calc
      2 * (K6Upper.momentAmplification * a ^ 2) * (128 * a ^ 7) =
          (256 * K6Upper.momentAmplification) * a ^ 9 := by ring
      _ ≤ (256 * K6Upper.momentAmplification) * a ^ 10 :=
        Nat.mul_le_mul_left _ hpow9
  have hfill : slackTrialCount a * K6Upper.fillCost (slackFillSize a) ≤
      K6Upper.momentAmplification * a ^ 10 := by
    calc
      slackTrialCount a * K6Upper.fillCost (slackFillSize a) ≤
          slackTrialCount a * (slackFillSize a) ^ 2 :=
        Nat.mul_le_mul_left _ (K6Upper.fillCost_le_sq _)
      _ = K6Upper.momentAmplification * a ^ 10 := by
        unfold slackTrialCount slackFillSize
        ring
  unfold slackQueryBudget slackUniversalUpperConstant
  calc
    slackStarQueries a + slackAttemptCount a * slackBranchScan a +
          slackTrialCount a * K6Upper.fillCost (slackFillSize a) ≤
        (16384 + 512 * K6Upper.momentAmplification) * a ^ 10 +
          (256 * K6Upper.momentAmplification) * a ^ 10 +
          K6Upper.momentAmplification * a ^ 10 :=
      Nat.add_le_add (Nat.add_le_add hstar hbranch) hfill
    _ = (16384 + 769 * K6Upper.momentAmplification) * a ^ 10 := by ring

end UpperBudgetUniversal
end OnlineRamsey
