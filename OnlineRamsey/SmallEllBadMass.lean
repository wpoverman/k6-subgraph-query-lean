import OnlineRamsey.AdaptiveHostTruncation
import OnlineRamsey.ScaledHostSmallEll

/-!
# Uniform exceptional bad mass at a small cubic query scale

This module combines the polynomial random-host failure estimate at
`N=floor(ell/q^10)` with the exact adaptive positive-answer tail.  After the
crude six-vertex map count, the host term is at most
`64 * ell^6 * q^10`; the adaptive term is exactly the pair-recurrence tail.
-/

open scoped ENNReal NNReal

namespace OnlineRamsey
namespace SmallEllBadMass

open QueryComplexity RecurrenceInstantiation AdaptiveHostTruncation
open AsymptoticScale PrefixSoundness

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-- The `NNReal` parameter carried by `cubeProbability q` is exactly `q^3`. -/
theorem toNNReal_cubeProbability_eq (q : ℝ≥0) (hq1 : q ≤ 1) :
    unitInterval.toNNReal
      (HostGoodProbability.cubeProbability (q : ℝ) (zero_le q) (by exact_mod_cast hq1)) =
        q ^ 3 := by
  apply NNReal.eq
  simpa using HostGoodProbability.cubeProbability_coe
    (q : ℝ) (zero_le q) (by exact_mod_cast hq1)

/-- At arbitrary fixed `ell`, seventy powers of `q` from host failure absorb
the sixty powers lost to the crude number `(2N)^6` of labelled maps. -/
theorem measure_scaledRandomHostGoodEvent_smallEll_crudeSixVertex_toReal_le
    {q ell : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * q ≤ (4 : ℝ) * √(8 * ell / 2)) :
    (((2 * queryBudget q ell) ^ 6 : ℕ) : ℝ) *
      (RandomBoard.bitBoardMeasure
        (Sym2 (Fin (2 * queryBudget q ell)))
        (HostGoodProbability.cubeProbability q hq.le
          (hqhalf.trans (by norm_num)))
        (RandomBoard.randomHostGoodEvent
          (2 * queryBudget q ell)
          (edgeBudget q 8 (queryBudget q ell))
          (degeneracyBudget q 4
            (edgeBudget q 8 (queryBudget q ell))) 90
          (HostGoodProbability.scaledPairBound q 12
            (queryBudget q ell))
          (HostGoodProbability.scaledTripleBound q (560 / ell)
            (queryBudget q ell)))ᶜ).toReal ≤
      64 * ell ^ 6 * q ^ 10 := by
  let N := queryBudget q ell
  have hN := queryBudget_cast_le_target hq hell0.le
  have hbase : ((2 * N : ℕ) : ℝ) ≤ 2 * ell / q ^ 10 := by
    calc
      ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
      _ ≤ 2 * (ell / q ^ 10) := by gcongr
      _ = 2 * ell / q ^ 10 := by ring
  have hcount : (((2 * N) ^ 6 : ℕ) : ℝ) ≤
      (2 * ell / q ^ 10) ^ 6 := by
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
      (pow_le_pow_left₀ (Nat.cast_nonneg (2 * N)) hbase 6)
  have hprob :=
    HostGoodProbability.measure_scaledRandomHostGoodEvent_smallEll_compl_toReal_le_q70
      hq hqhalf hell0 hell1 hscale hpairScale hdense
  change (((2 * N) ^ 6 : ℕ) : ℝ) * _ ≤ _
  calc
    (((2 * N) ^ 6 : ℕ) : ℝ) *
        (RandomBoard.bitBoardMeasure
          (Sym2 (Fin (2 * N)))
          (HostGoodProbability.cubeProbability q hq.le
            (hqhalf.trans (by norm_num)))
          (RandomBoard.randomHostGoodEvent
            (2 * N) (edgeBudget q 8 N)
            (degeneracyBudget q 4 (edgeBudget q 8 N)) 90
            (HostGoodProbability.scaledPairBound q 12 N)
            (HostGoodProbability.scaledTripleBound q (560 / ell) N))ᶜ).toReal ≤
        (2 * ell / q ^ 10) ^ 6 * q ^ 70 := by
      exact mul_le_mul hcount hprob ENNReal.toReal_nonneg (by positivity)
    _ = 64 * ell ^ 6 * q ^ 10 := by
      field_simp [ne_of_gt hq]
      ring

/-- `ENNReal` form of the preceding crude-host estimate. -/
theorem measure_scaledRandomHostGoodEvent_smallEll_crudeSixVertex_le
    {q ell : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * q ≤ (4 : ℝ) * √(8 * ell / 2)) :
    (((2 * queryBudget q ell) ^ 6 : ℕ) : ℝ≥0∞) *
      RandomBoard.bitBoardMeasure
        (Sym2 (Fin (2 * queryBudget q ell)))
        (HostGoodProbability.cubeProbability q hq.le
          (hqhalf.trans (by norm_num)))
        (RandomBoard.randomHostGoodEvent
          (2 * queryBudget q ell)
          (edgeBudget q 8 (queryBudget q ell))
          (degeneracyBudget q 4
            (edgeBudget q 8 (queryBudget q ell))) 90
          (HostGoodProbability.scaledPairBound q 12
            (queryBudget q ell))
          (HostGoodProbability.scaledTripleBound q (560 / ell)
            (queryBudget q ell)))ᶜ ≤
      ENNReal.ofReal (64 * ell ^ 6 * q ^ 10) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by finiteness))
      ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 64 * ell ^ 6 * q ^ 10)]
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
    measure_scaledRandomHostGoodEvent_smallEll_crudeSixVertex_toReal_le
      hq hqhalf hell0 hell1 hscale hpairScale hdense

/-- Strategy-uniform simultaneous host/transcript failure after the crude
six-vertex count.  The second summand is the same explicit tail used by the
ordinary recurrence. -/
theorem scaledSmallEllHostEdgeGood_crudeSixVertex_le
    {q ell : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * q ≤ (4 : ℝ) * √(8 * ell / 2))
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy) (H : K6FinitePattern) :
    let N := queryBudget q ell
    let pUI := HostGoodProbability.cubeProbability q hq.le
      (hqhalf.trans (by norm_num))
    let M := edgeBudget q 8 N
    let D := degeneracyBudget q 4 M
    let c₂ := HostGoodProbability.scaledPairBound q 12 N
    let c₃ := HostGoodProbability.scaledTripleBound q (560 / ell) N
    (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
      finiteBoardMass
        (bernoulliWeight (unitInterval.toNNReal pUI : ℝ≥0∞))
        (RandomBoard.randomHostGoodEvent (2 * N) M D 90 c₂ c₃ ∩
          transcriptEdgeGoodEvent strategy M)ᶜ ≤
      ENNReal.ofReal (64 * ell ^ 6 * q ^ 10) +
        (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞) := by
  dsimp only
  have hmain := scaledHostEdgeGood_crudeSixVertex_le
    (ell := ell) (A := 4) (B₂ := 12) (B₃ := 560 / ell)
    (L := 90) hq (hqhalf.trans (by norm_num)) strategy hfresh H
  have hhost :=
    measure_scaledRandomHostGoodEvent_smallEll_crudeSixVertex_le
      hq hqhalf hell0 hell1 hscale hpairScale hdense
  exact hmain.trans (add_le_add_right hhost _)

end
end SmallEllBadMass
end OnlineRamsey
