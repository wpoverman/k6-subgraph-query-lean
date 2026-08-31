import OnlineRamsey.ExceptionalHistoryCount
import OnlineRamsey.B4SharpScale
import OnlineRamsey.SmallEllBadMass

/-!
# Cubic-scale history bounds for the `H₃` and `K₅-e` branches

This module specializes the two nine-edge exceptional-prefix estimates to
`N = floor (ell / q^10)`.  It keeps the exact good/bad truncation term and
bounds the deterministic main terms by their paper-scale monomials.
-/

open scoped ENNReal NNReal

namespace OnlineRamsey
namespace ExceptionalHistoryScale

open AsymptoticScale HostGoodProbability QueryComplexity
open PrefixSoundness RecurrenceInstantiation B4SharpScale
open StoppingHistory StoppingCoverage StoppingPrefixCount
open AdaptiveHostTruncation

noncomputable section

/-- The deterministic good-board main term in the `H₃` estimate. -/
noncomputable def h3Main (q : ℝ) (N : ℕ) : ℕ :=
  let c₂ := scaledPairBound q 12 N
  let M := edgeBudget q 8 N
  2 * ((6 * c₂ * (2 * 90) * M) * M)

/-- The deterministic good-board main term in the `(K₅-e) ⊔ K₁`
estimate. -/
noncomputable def k5IsolatedMain (q ell : ℝ) (N : ℕ) : ℕ :=
  let c₃ := scaledTripleBound q (560 / ell) N
  let M := edgeBudget q 8 N
  ((24 * c₃ * (2 * 90 * 90)) * M) * (2 * N)

/-- Rounded-scale real bound for the `H₃` main term. -/
theorem h3Main_cast_le {q : ℝ} {N : ℕ} (hq : 0 ≤ q)
    (hpairOne : 1 ≤ 12 * q ^ 6 * (N : ℝ))
    (hedgeOne : 1 ≤ 8 * q ^ 3 * (N : ℝ)) :
    (h3Main q N : ℝ) ≤
      13271040 * (q ^ 3) ^ 4 * (N : ℝ) ^ 3 := by
  have hc₂ := scaledPairBound_cast_le_two_mul hq
    (by norm_num : (0 : ℝ) ≤ 12) hpairOne
  have hM := edgeBudget_cast_le_two_mul hq
    (by norm_num : (0 : ℝ) ≤ 8) hedgeOne
  dsimp [h3Main]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    2 * ((6 * (scaledPairBound q 12 N : ℝ) * 180 *
          edgeBudget q 8 N) * edgeBudget q 8 N) ≤
        2 * ((6 * (2 * (12 * q ^ 6 * (N : ℝ))) * 180 *
          (2 * (8 * q ^ 3 * (N : ℝ)))) *
            (2 * (8 * q ^ 3 * (N : ℝ)))) := by
      gcongr
    _ = 13271040 * (q ^ 3) ^ 4 * (N : ℝ) ^ 3 := by ring

/-- Rounded-scale real bound for the isolated-`K₅-e` main term. -/
theorem k5IsolatedMain_cast_le {q ell : ℝ} {N : ℕ}
    (hq : 0 ≤ q) (hell : 0 < ell)
    (htripleOne : 1 ≤ (560 / ell) * q ^ 9 * (N : ℝ))
    (hedgeOne : 1 ≤ 8 * q ^ 3 * (N : ℝ)) :
    (k5IsolatedMain q ell N : ℝ) ≤
      (13934592000 / ell) * (q ^ 3) ^ 4 * (N : ℝ) ^ 3 := by
  have hc₃ : (scaledTripleBound q (560 / ell) N : ℝ) ≤
      2 * ((560 / ell) * q ^ 9 * (N : ℝ)) := by
    unfold scaledTripleBound
    exact natCeil_cast_le_two_mul
      (mul_nonneg
        (mul_nonneg (div_nonneg (by norm_num) hell.le) (pow_nonneg hq _))
        (Nat.cast_nonneg _)) htripleOne
  have hM := edgeBudget_cast_le_two_mul hq
    (by norm_num : (0 : ℝ) ≤ 8) hedgeOne
  dsimp [k5IsolatedMain]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    ((24 * (scaledTripleBound q (560 / ell) N : ℝ) *
          16200) * edgeBudget q 8 N) * (2 * N) ≤
        ((24 * (2 * ((560 / ell) * q ^ 9 * (N : ℝ))) *
          16200) * (2 * (8 * q ^ 3 * (N : ℝ)))) *
            (2 * (N : ℝ)) := by
      gcongr
    _ = (13934592000 / ell) * (q ^ 3) ^ 4 * (N : ℝ) ^ 3 := by
      field_simp [ne_of_gt hell]
      ring

/-- `ENNReal` form of the `H₃` scale estimate. -/
theorem h3Main_coe_le {q : ℝ} {N : ℕ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hpairOne : 1 ≤ 12 * q ^ 6 * (N : ℝ))
    (hedgeOne : 1 ≤ 8 * q ^ 3 * (N : ℝ)) :
    ((h3Main q N : ℕ) : ℝ≥0∞) ≤
      13271040 *
        (unitInterval.toNNReal (cubeProbability q hq hq1) : ℝ≥0∞) ^ 4 *
          (N : ℝ≥0∞) ^ 3 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  exact h3Main_cast_le hq hpairOne hedgeOne

/-- `ENNReal` form of the isolated-`K₅-e` scale estimate. -/
theorem k5IsolatedMain_coe_le {q ell : ℝ} {N : ℕ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (htripleOne : 1 ≤ (560 / ell) * q ^ 9 * (N : ℝ))
    (hedgeOne : 1 ≤ 8 * q ^ 3 * (N : ℝ)) :
    ((k5IsolatedMain q ell N : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (13934592000 / ell) *
        (unitInterval.toNNReal (cubeProbability q hq hq1) : ℝ≥0∞) ^ 4 *
          (N : ℝ≥0∞) ^ 3 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) hell.le)]
  exact k5IsolatedMain_cast_le hq hell htripleOne hedgeOne

/-- For `N=floor(ell/q^10)`, the triple-codegree target used by the
isolated-`K₅-e` branch is at least one. -/
theorem queryBudget_triple_target_ge_one
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell) :
    1 ≤ (560 / ell) * q ^ 9 * (queryBudget q ell : ℝ) := by
  have hN := (normalized_queryBudget_bounds_half hq hell.le hfloor).1
  have hmul : (560 / ell) * (ell / 2) <
      (560 / ell) * (q ^ 10 * (queryBudget q ell : ℝ)) :=
    mul_lt_mul_of_pos_left hN (div_pos (by norm_num) hell)
  have hdiv := div_lt_div_of_pos_right hmul hq
  have hq280 : q ≤ 280 := hq1.trans (by norm_num)
  exact (calc
    1 ≤ 280 / q := (le_div_iff₀ hq).2 (by simpa using hq280)
    _ = (560 / ell) * (ell / 2) / q := by
      field_simp [ne_of_gt hell, ne_of_gt hq]
      ring
    _ < (560 / ell) * (q ^ 10 * (queryBudget q ell : ℝ)) / q := hdiv
    _ = (560 / ell) * q ^ 9 * (queryBudget q ell : ℝ) := by
      field_simp [ne_of_gt hq]).le

/-- After the six remaining completion edges, the `H₃` main term is at
most its constant times `ell³`. -/
theorem completedH3Main_queryBudget_le_ell_cubed
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell) :
    (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^ 6 *
        (13271040 *
          (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^ 4 *
          (queryBudget q ell : ℝ≥0∞) ^ 3) ≤
      ENNReal.ofReal (13271040 * ell ^ 3) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  norm_num only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (by norm_num) (pow_nonneg hell _))]
  have hscale := queryBudget_cubic_threshold hq hell
  change (q ^ 3) ^ 6 * (13271040 * (q ^ 3) ^ 4 *
    (queryBudget q ell : ℝ) ^ 3) ≤ 13271040 * ell ^ 3
  calc
    (q ^ 3) ^ 6 * (13271040 * (q ^ 3) ^ 4 *
        (queryBudget q ell : ℝ) ^ 3) =
      13271040 * (q ^ 30 * (queryBudget q ell : ℝ) ^ 3) := by ring
    _ ≤ 13271040 * ell ^ 3 := by gcongr

/-- After the six remaining completion edges, the isolated-`K₅-e` main
term is at most its constant times `ell²`. -/
theorem completedK5IsolatedMain_queryBudget_le_ell_squared
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell) :
    (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^ 6 *
        (ENNReal.ofReal (13934592000 / ell) *
          (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^ 4 *
          (queryBudget q ell : ℝ≥0∞) ^ 3) ≤
      ENNReal.ofReal (13934592000 * ell ^ 2) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  norm_num only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  rw [
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) hell.le),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (pow_nonneg hell.le _))]
  have hscale := queryBudget_cubic_threshold hq hell.le
  change (q ^ 3) ^ 6 * ((13934592000 / ell) * (q ^ 3) ^ 4 *
    (queryBudget q ell : ℝ) ^ 3) ≤ 13934592000 * ell ^ 2
  calc
    (q ^ 3) ^ 6 * ((13934592000 / ell) * (q ^ 3) ^ 4 *
        (queryBudget q ell : ℝ) ^ 3) =
      (13934592000 / ell) *
        (q ^ 30 * (queryBudget q ell : ℝ) ^ 3) := by ring
    _ ≤ (13934592000 / ell) * ell ^ 3 := by
      gcongr
    _ = 13934592000 * ell ^ 2 := by
      field_simp [ne_of_gt hell]

/-- Full per-order `H₃` prefix estimate at arbitrary fixed `ell`. -/
theorem h3_orderNinePrefixHistoryMass_cubicScale_le
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy) (π : K6EdgeOrder)
    (hH3 : K6Prefix.h3Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    orderPrefixHistoryMass
        (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞)
        strategy π ninePrefixLength ≤
      13271040 *
          (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^ 4 *
          (queryBudget q ell : ℝ≥0∞) ^ 3 +
        (((2 * queryBudget q ell) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass
            (unitInterval.toNNReal (cubeProbability q hq.le hq1)) strategy
            (edgeBudget q 8 (queryBudget q ell))
            (degeneracyBudget q 4
              (edgeBudget q 8 (queryBudget q ell))) 90
            (scaledPairBound q 12 (queryBudget q ell))
            (scaledTripleBound q (560 / ell) (queryBudget q ell)) := by
  let N := queryBudget q ell
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := scaledPairBound q 12 N
  let c₃ := scaledTripleBound q (560 / ell) N
  let p : unitInterval := cubeProbability q hq.le hq1
  have htargets := queryBudget_pair_edge_targets_ge_one hq hell
    (by norm_num : (0 : ℝ) < 12) (by norm_num : (0 : ℝ) < 8)
      hfloor hpairSmall hedgeSmall
  have hN : 0 < N := by
    have hq10 : 0 < q ^ 10 := pow_pos hq _
    have hq10le : q ^ 10 ≤ ell := by linarith [hfloor]
    have htarget : 1 ≤ ell / q ^ 10 :=
      (le_div_iff₀ hq10).2 (by simpa using hq10le)
    dsimp [N, queryBudget]
    exact Nat.floor_pos.mpr htarget
  have hM : 0 < M := by
    have htarget : 8 * q ^ 3 * (N : ℝ) ≤ (M : ℝ) := by
      simpa [M] using edgeBudget_target_le q 8 N
    have hone : (1 : ℝ) ≤ (M : ℝ) := htargets.2.trans htarget
    exact_mod_cast (show (0 : ℝ) < (M : ℝ) from
      lt_of_lt_of_le (by norm_num) hone)
  have hD : 0 < D := by
    dsimp [D, degeneracyBudget]
    apply Nat.ceil_pos.mpr
    exact mul_pos (by norm_num)
      (Real.sqrt_pos.2 (mul_pos (pow_pos hq _) (by exact_mod_cast hM)))
  have hraw := h3_orderNinePrefixHistoryMass_le
    (unitInterval.toNNReal p) (RandomBoard.toNNReal_le_one p) hN
      strategy hfresh π (M := M) (D := D) (L := 90) (c₂ := c₂) (c₃ := c₃)
      hD hH3
  have hmain := h3Main_coe_le hq.le hq1 htargets.1 htargets.2
  change orderPrefixHistoryMass (unitInterval.toNNReal p : ℝ≥0∞)
      strategy π ninePrefixLength ≤ _
  calc
    orderPrefixHistoryMass (unitInterval.toNNReal p : ℝ≥0∞)
        strategy π ninePrefixLength ≤
      ((h3Main q N : ℕ) : ℝ≥0∞) +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal p) strategy
            M D 90 c₂ c₃ := by
      simpa [h3Main, N, M, D, c₂, c₃, p] using hraw
    _ ≤ 13271040 * (unitInterval.toNNReal p : ℝ≥0∞) ^ 4 *
          (N : ℝ≥0∞) ^ 3 +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal p) strategy
            M D 90 c₂ c₃ := add_le_add_right hmain _
    _ = _ := by rfl

/-- Full per-order isolated-`K₅-e` prefix estimate at arbitrary fixed
`ell`. -/
theorem k5_orderNinePrefixHistoryMass_cubicScale_le
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy) (π : K6EdgeOrder)
    (hK5 : K6Prefix.k5MinusEdgePlusIsolateOrbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    orderPrefixHistoryMass
        (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞)
        strategy π ninePrefixLength ≤
      ENNReal.ofReal (13934592000 / ell) *
          (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^ 4 *
          (queryBudget q ell : ℝ≥0∞) ^ 3 +
        (((2 * queryBudget q ell) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass
            (unitInterval.toNNReal (cubeProbability q hq.le hq1)) strategy
            (edgeBudget q 8 (queryBudget q ell))
            (degeneracyBudget q 4
              (edgeBudget q 8 (queryBudget q ell))) 90
            (scaledPairBound q 12 (queryBudget q ell))
            (scaledTripleBound q (560 / ell) (queryBudget q ell)) := by
  let N := queryBudget q ell
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := scaledPairBound q 12 N
  let c₃ := scaledTripleBound q (560 / ell) N
  let p : unitInterval := cubeProbability q hq.le hq1
  have htargets := queryBudget_pair_edge_targets_ge_one hq hell
    (by norm_num : (0 : ℝ) < 12) (by norm_num : (0 : ℝ) < 8)
      hfloor hpairSmall hedgeSmall
  have htriple := queryBudget_triple_target_ge_one hq hq1 hell hfloor
  have hN : 0 < N := by
    have hq10 : 0 < q ^ 10 := pow_pos hq _
    have hq10le : q ^ 10 ≤ ell := by linarith [hfloor]
    have htarget : 1 ≤ ell / q ^ 10 :=
      (le_div_iff₀ hq10).2 (by simpa using hq10le)
    dsimp [N, queryBudget]
    exact Nat.floor_pos.mpr htarget
  have hM : 0 < M := by
    have htarget : 8 * q ^ 3 * (N : ℝ) ≤ (M : ℝ) := by
      simpa [M] using edgeBudget_target_le q 8 N
    have hone : (1 : ℝ) ≤ (M : ℝ) := htargets.2.trans htarget
    exact_mod_cast (show (0 : ℝ) < (M : ℝ) from
      lt_of_lt_of_le (by norm_num) hone)
  have hD : 0 < D := by
    dsimp [D, degeneracyBudget]
    apply Nat.ceil_pos.mpr
    exact mul_pos (by norm_num)
      (Real.sqrt_pos.2 (mul_pos (pow_pos hq _) (by exact_mod_cast hM)))
  have hraw := k5_orderNinePrefixHistoryMass_le
    (unitInterval.toNNReal p) (RandomBoard.toNNReal_le_one p) hN
      strategy hfresh π (M := M) (D := D) (L := 90) (c₂ := c₂) (c₃ := c₃)
      hD hK5
  have hmain := k5IsolatedMain_coe_le hq.le hq1 hell htriple htargets.2
  change orderPrefixHistoryMass (unitInterval.toNNReal p : ℝ≥0∞)
      strategy π ninePrefixLength ≤ _
  calc
    orderPrefixHistoryMass (unitInterval.toNNReal p : ℝ≥0∞)
        strategy π ninePrefixLength ≤
      ((k5IsolatedMain q ell N : ℕ) : ℝ≥0∞) +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal p) strategy
            M D 90 c₂ c₃ := by
      simpa [k5IsolatedMain, N, M, D, c₂, c₃, p] using hraw
    _ ≤ ENNReal.ofReal (13934592000 / ell) *
          (unitInterval.toNNReal p : ℝ≥0∞) ^ 4 *
          (N : ℝ≥0∞) ^ 3 +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal p) strategy
            M D 90 c₂ c₃ := add_le_add_right hmain _
    _ = _ := by rfl

/-- The `H₃` estimate with the exceptional error split into the sampled-host
failure and the common adaptive pair tail. -/
theorem h3_orderNinePrefixHistoryMass_explicitError_le
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy) (π : K6EdgeOrder)
    (hH3 : K6Prefix.h3Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    let N := queryBudget q ell
    let pUI := cubeProbability q hq.le hq1
    let M := edgeBudget q 8 N
    let D := degeneracyBudget q 4 M
    let c₂ := scaledPairBound q 12 N
    let c₃ := scaledTripleBound q (560 / ell) N
    let H := finitePatternOfMasks fullVertexMask
      (orderPrefixMask π ninePrefixLength)
    orderPrefixHistoryMass (unitInterval.toNNReal pUI : ℝ≥0∞)
        strategy π ninePrefixLength ≤
      13271040 * (unitInterval.toNNReal pUI : ℝ≥0∞) ^ 4 *
          (N : ℝ≥0∞) ^ 3 +
        ((((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
            RandomBoard.bitBoardMeasure (Query N) pUI
              (RandomBoard.randomHostGoodEvent
                (2 * N) M D 90 c₂ c₃)ᶜ +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞)) := by
  dsimp only
  let N := queryBudget q ell
  let pUI := cubeProbability q hq.le hq1
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := scaledPairBound q 12 N
  let c₃ := scaledTripleBound q (560 / ell) N
  let H := finitePatternOfMasks fullVertexMask
    (orderPrefixMask π ninePrefixLength)
  have hbase := h3_orderNinePrefixHistoryMass_cubicScale_le
    hq hq1 hell hfloor hpairSmall hedgeSmall strategy hfresh π hH3
  have hsplit := scaledHostEdgeGood_crudeSixVertex_le
    (ell := ell) (A := 4) (B₂ := 12) (B₃ := 560 / ell) (L := 90)
      hq hq1 strategy hfresh H
  have hsplit' :
      (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal pUI) strategy
            M D 90 c₂ c₃ ≤
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
            RandomBoard.bitBoardMeasure (Query N) pUI
              (RandomBoard.randomHostGoodEvent
                (2 * N) M D 90 c₂ c₃)ᶜ +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞) := by
    simpa [exceptionalBadMass, exceptionalGoodEvent, N, pUI, M, D, c₂, c₃, H]
      using hsplit
  dsimp only [N, pUI, M, D, c₂, c₃, H] at hbase hsplit' ⊢
  exact hbase.trans (add_le_add_left hsplit' _)

/-- The isolated-`K₅-e` estimate with the exceptional error split into the
sampled-host failure and the common adaptive pair tail. -/
theorem k5_orderNinePrefixHistoryMass_explicitError_le
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy) (π : K6EdgeOrder)
    (hK5 : K6Prefix.k5MinusEdgePlusIsolateOrbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    let N := queryBudget q ell
    let pUI := cubeProbability q hq.le hq1
    let M := edgeBudget q 8 N
    let D := degeneracyBudget q 4 M
    let c₂ := scaledPairBound q 12 N
    let c₃ := scaledTripleBound q (560 / ell) N
    let H := finitePatternOfMasks fullVertexMask
      (orderPrefixMask π ninePrefixLength)
    orderPrefixHistoryMass (unitInterval.toNNReal pUI : ℝ≥0∞)
        strategy π ninePrefixLength ≤
      ENNReal.ofReal (13934592000 / ell) *
          (unitInterval.toNNReal pUI : ℝ≥0∞) ^ 4 *
          (N : ℝ≥0∞) ^ 3 +
        ((((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
            RandomBoard.bitBoardMeasure (Query N) pUI
              (RandomBoard.randomHostGoodEvent
                (2 * N) M D 90 c₂ c₃)ᶜ +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞)) := by
  dsimp only
  let N := queryBudget q ell
  let pUI := cubeProbability q hq.le hq1
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := scaledPairBound q 12 N
  let c₃ := scaledTripleBound q (560 / ell) N
  let H := finitePatternOfMasks fullVertexMask
    (orderPrefixMask π ninePrefixLength)
  have hbase := k5_orderNinePrefixHistoryMass_cubicScale_le
    hq hq1 hell hfloor hpairSmall hedgeSmall strategy hfresh π hK5
  have hsplit := scaledHostEdgeGood_crudeSixVertex_le
    (ell := ell) (A := 4) (B₂ := 12) (B₃ := 560 / ell) (L := 90)
      hq hq1 strategy hfresh H
  have hsplit' :
      (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal pUI) strategy
            M D 90 c₂ c₃ ≤
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
            RandomBoard.bitBoardMeasure (Query N) pUI
              (RandomBoard.randomHostGoodEvent
                (2 * N) M D 90 c₂ c₃)ᶜ +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞) := by
    simpa [exceptionalBadMass, exceptionalGoodEvent, N, pUI, M, D, c₂, c₃, H]
      using hsplit
  dsimp only [N, pUI, M, D, c₂, c₃, H] at hbase hsplit' ⊢
  exact hbase.trans (add_le_add_left hsplit' _)

end
end ExceptionalHistoryScale
end OnlineRamsey
