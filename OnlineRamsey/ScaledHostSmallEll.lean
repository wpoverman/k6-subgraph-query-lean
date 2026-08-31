import OnlineRamsey.HostGoodProbability

/-!
# A polynomially good random host at an arbitrary small query scale

The lower bound must use `N = floor (ell / q^10)` with a *small* positive
constant `ell`; the earlier fully numeric host theorem was specialized to
`ell = 1`.  Here the pair- and triple-codegree constants are enlarged by
`1 / ell`.  This keeps all deterministic prefix counts at a positive power
of `ell`, while retaining the `q^70` exceptional probability needed after a
crude six-vertex count.
-/

open scoped ENNReal

namespace OnlineRamsey
namespace HostGoodProbability

noncomputable section

set_option maxRecDepth 10000

/-- The small-set error coefficient is monotone enough on `0 ≤ ell ≤ 1` to
be dominated by the already checked `ell = 1` numerical estimate. -/
theorem actualSmallSetErrorPowerBound_c8_L90_le_one_scale
    {q ell : ℝ} (hq : 0 ≤ q) (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1) :
    actualSmallSetErrorPowerBound q ell 8 4 90 ≤
      actualSmallSetErrorPowerBound q 1 8 4 90 := by
  have hsqrt_nonneg : 0 ≤ √(8 * ell + 1) := Real.sqrt_nonneg _
  have harg : 8 * ell + 1 ≤ (9 : ℝ) := by linarith
  have hsqrt : √(8 * ell + 1) ≤ 3 := by
    have harg0 : 0 ≤ 8 * ell + 1 := by linarith
    nlinarith [Real.sq_sqrt harg0]
  have hK0 : 0 ≤ 4 * √(8 * ell + 1) + 1 := by positivity
  have hK : 4 * √(8 * ell + 1) + 1 ≤ 13 := by linarith
  have hKpow : (4 * √(8 * ell + 1) + 1) ^ 89 ≤ (13 : ℝ) ^ 89 :=
    pow_le_pow_left₀ hK0 hK 89
  have hfactor :
      0 ≤ 2 * Real.exp 1 * (Real.exp 1 / (2 * (90 : ℝ))) ^ 90 := by
    positivity
  have hsqrt9 : √(9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  let K : ℝ := 4 * √(8 * ell + 1) + 1
  let F : ℝ := 2 * Real.exp 1 * (Real.exp 1 / (2 * (90 : ℝ))) ^ 90
  have hK' : K ≤ 13 := by simpa [K] using hK
  have hK0' : 0 ≤ K := by simpa [K] using hK0
  have hKpow' : K ^ 89 ≤ (13 : ℝ) ^ 89 := by simpa [K] using hKpow
  change (K + 1) * F * ell * K ^ 89 * q ^ 80 ≤
    ((4 * √((8 : ℝ) * 1 + 1) + 1) + 1) * F * 1 *
      (4 * √((8 : ℝ) * 1 + 1) + 1) ^ 89 * q ^ 80
  rw [show (8 : ℝ) * 1 + 1 = 9 by norm_num, hsqrt9]
  norm_num only [mul_one]
  have hKplus : K + 1 ≤ 14 := by linarith
  have hKplus0 : 0 ≤ K + 1 := by linarith
  have hqpow0 : 0 ≤ q ^ 80 := pow_nonneg hq _
  have h₁ : (K + 1) * F ≤ 14 * F :=
    mul_le_mul_of_nonneg_right hKplus (by simpa [F] using hfactor)
  have h₂ : (K + 1) * F * ell ≤ 14 * F * 1 :=
    mul_le_mul h₁ hell1 hell0 (mul_nonneg (by norm_num)
      (by simpa [F] using hfactor))
  have h₃ : (K + 1) * F * ell * K ^ 89 ≤
      14 * F * 1 * (13 : ℝ) ^ 89 :=
    mul_le_mul h₂ hKpow' (pow_nonneg hK0' _)
      (mul_nonneg (mul_nonneg (by norm_num)
        (by simpa [F] using hfactor)) (by norm_num))
  have h₃' : (K + 1) * F * ell * K ^ 89 ≤
      14 * F * (13 : ℝ) ^ 89 := by simpa using h₃
  norm_num only [pow_succ, pow_zero, mul_one] at h₃'
  exact mul_le_mul_of_nonneg_right h₃' hqpow0

/-- Uniform `q^80` bound for the complete small-set contribution at every
fixed scale `0 ≤ ell ≤ 1`. -/
theorem actualSmallSetErrorPowerBound_c8_L90_le_q80
    {q ell : ℝ} (hq : 0 ≤ q) (hell0 : 0 ≤ ell) (hell1 : ell ≤ 1) :
    actualSmallSetErrorPowerBound q ell 8 4 90 ≤ q ^ 80 :=
  (actualSmallSetErrorPowerBound_c8_L90_le_one_scale hq hell0 hell1).trans
    numeric_smallSetErrorPowerBound_c8_L90

/-- High-probability `HostGood` estimate at `N=floor(ell/q^10)`.  The
displayed elementary hypotheses are exactly the smallness conditions later
discharged by choosing a positive cutoff `q₀(ell)`. -/
theorem measure_scaledRandomHostGoodEvent_smallEll_compl_toReal_le_q70
    {q ell : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * q ≤ (4 : ℝ) * √(8 * ell / 2)) :
    (RandomBoard.bitBoardMeasure
      (Sym2 (Fin (2 * AsymptoticScale.queryBudget q ell)))
      (cubeProbability q hq.le (hqhalf.trans (by norm_num)))
      (RandomBoard.randomHostGoodEvent
        (2 * AsymptoticScale.queryBudget q ell)
        (AsymptoticScale.edgeBudget q 8
          (AsymptoticScale.queryBudget q ell))
        (AsymptoticScale.degeneracyBudget q 4
          (AsymptoticScale.edgeBudget q 8
            (AsymptoticScale.queryBudget q ell))) 90
        (scaledPairBound q 12
          (AsymptoticScale.queryBudget q ell))
        (scaledTripleBound q (560 / ell)
          (AsymptoticScale.queryBudget q ell)))ᶜ).toReal ≤ q ^ 70 := by
  have hq1 : q ≤ 1 := hqhalf.trans (by norm_num)
  have hell : 0 ≤ ell := hell0.le
  have he3 : Real.exp 1 ≤ 3 :=
    (lt_trans Real.exp_one_lt_d9 (by norm_num)).le
  have hB₂ : 4 * Real.exp 1 ≤ (12 : ℝ) := by nlinarith
  have hB₃ : 4 * Real.exp 1 ≤ 560 / ell := by
    apply (le_div_iff₀ hell0).2
    have : ell * 12 ≤ 560 := by nlinarith
    nlinarith
  have hAlarge : 4 * Real.exp 1 ≤ (4 : ℝ) ^ 2 := by nlinarith
  have hentropy : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1 := by
    have hq10 : q ^ 10 ≤ (1 / 2 : ℝ) ^ 10 := by gcongr
    calc
      2 * Real.exp 1 * ell * q ^ 10 ≤
          2 * 3 * 1 * (1 / 2 : ℝ) ^ 10 := by gcongr
      _ ≤ 1 := by norm_num
  have hlocal : Real.exp 1 *
      ((4 : ℝ) * √((8 : ℝ) * ell + 1) + 1) * q ≤ 2 * (90 : ℝ) := by
    have harg : (8 : ℝ) * ell + 1 ≤ 9 := by linarith
    have hsqrt : √((8 : ℝ) * ell + 1) ≤ 3 := by
      have harg0 : 0 ≤ (8 : ℝ) * ell + 1 := by linarith
      nlinarith [Real.sq_sqrt harg0]
    have hK0 : 0 ≤ (4 : ℝ) * √((8 : ℝ) * ell + 1) + 1 := by positivity
    calc
      Real.exp 1 * ((4 : ℝ) * √((8 : ℝ) * ell + 1) + 1) * q ≤
          3 * 13 * (1 / 2 : ℝ) := by
            gcongr
            · nlinarith
      _ ≤ 2 * (90 : ℝ) := by norm_num
  have hedge : (8 : ℝ) * q ^ 3 ≤ 1 := by
    calc
      (8 : ℝ) * q ^ 3 ≤ 8 * (1 / 2 : ℝ) ^ 3 := by gcongr
      _ = 1 := by norm_num
  have hremain : ell / 2 ≤ ell - q ^ 10 := by linarith
  have hpair : 2 * entropyIndex q + 4 * entropyIndex q ≤
      scaledPairBound q 12
        (AsymptoticScale.queryBudget q ell) + 1 := by
    let N := AsymptoticScale.queryBudget q ell
    let s := entropyIndex q
    have hs : (s : ℝ) ≤ 40 / q := by
      simpa [s] using entropyIndex_cast_le hq hq1
    have hleft : ((6 * s : ℕ) : ℝ) ≤ 240 / q := by
      calc
        ((6 * s : ℕ) : ℝ) = 6 * (s : ℝ) := by norm_num
        _ ≤ 6 * (40 / q) := by gcongr
        _ = 240 / q := by ring
    have hq4 : 0 < q ^ 4 := pow_pos hq _
    have hpairCut : 240 * q ^ 3 ≤ 12 * (ell - q ^ 10) := by
      have hq10half : q ^ 10 ≤ ell / 2 := by linarith
      calc
        240 * q ^ 3 = 6 * (40 * q ^ 3) := by ring
        _ ≤ 6 * ell := by gcongr
        _ ≤ 12 * (ell - q ^ 10) := by nlinarith
    have hcut : 240 / q ≤ 12 * (ell - q ^ 10) / q ^ 4 := by
      have hq4pos : 0 < q ^ 4 := pow_pos hq _
      calc
        240 / q = (240 * q ^ 3) / q ^ 4 := by
          field_simp [ne_of_gt hq, ne_of_gt hq4pos]
        _ ≤ 12 * (ell - q ^ 10) / q ^ 4 :=
          div_le_div_of_nonneg_right hpairCut hq4pos.le
    have hNlower : ell - q ^ 10 < q ^ 10 * (N : ℝ) := by
      simpa [N] using (AsymptoticScale.normalized_queryBudget_bounds hq hell).1
    have hscale' : 12 * (ell - q ^ 10) / q ^ 4 <
        12 * q ^ 6 * (N : ℝ) := by
      calc
        12 * (ell - q ^ 10) / q ^ 4 <
            12 * (q ^ 10 * (N : ℝ)) / q ^ 4 := by gcongr
        _ = 12 * q ^ 6 * (N : ℝ) := by
          field_simp [ne_of_gt hq, ne_of_gt hq4]
    have hreal : ((6 * s : ℕ) : ℝ) <
        12 * q ^ 6 * (N : ℝ) :=
      hleft.trans_lt (hcut.trans_lt hscale')
    have hceil : 12 * q ^ 6 * (N : ℝ) ≤
        (scaledPairBound q 12 N : ℝ) := Nat.le_ceil _
    have hnat : 6 * s < scaledPairBound q 12 N := by
      exact_mod_cast hreal.trans_le hceil
    simpa [s, N] using
      (show 2 * s + 4 * s ≤ scaledPairBound q 12 N + 1 by omega)
  have htriple : 3 * entropyIndex q + 4 * entropyIndex q ≤
      scaledTripleBound q (560 / ell)
        (AsymptoticScale.queryBudget q ell) + 1 := by
    let N := AsymptoticScale.queryBudget q ell
    let s := entropyIndex q
    have hs : (s : ℝ) ≤ 40 / q := by
      simpa [s] using entropyIndex_cast_le hq hq1
    have hleft : ((7 * s : ℕ) : ℝ) ≤ 280 / q := by
      calc
        ((7 * s : ℕ) : ℝ) = 7 * (s : ℝ) := by norm_num
        _ ≤ 7 * (40 / q) := by gcongr
        _ = 280 / q := by ring
    have hcut : 280 / q ≤ (560 / ell) * (ell - q ^ 10) / q := by
      apply div_le_div_of_nonneg_right _ hq.le
      calc
        (280 : ℝ) = (560 / ell) * (ell / 2) := by
          field_simp [ne_of_gt hell0]
          ring
        _ ≤ (560 / ell) * (ell - q ^ 10) := by gcongr
    have hNlower : ell - q ^ 10 < q ^ 10 * (N : ℝ) := by
      simpa [N] using (AsymptoticScale.normalized_queryBudget_bounds hq hell).1
    have hscale' : (560 / ell) * (ell - q ^ 10) / q <
        (560 / ell) * q ^ 9 * (N : ℝ) := by
      calc
        (560 / ell) * (ell - q ^ 10) / q <
            (560 / ell) * (q ^ 10 * (N : ℝ)) / q := by gcongr
        _ = (560 / ell) * q ^ 9 * (N : ℝ) := by
          field_simp [ne_of_gt hq]
    have hreal : ((7 * s : ℕ) : ℝ) <
        (560 / ell) * q ^ 9 * (N : ℝ) :=
      hleft.trans_lt (hcut.trans_lt hscale')
    have hceil : (560 / ell) * q ^ 9 * (N : ℝ) ≤
        (scaledTripleBound q (560 / ell) N : ℝ) := Nat.le_ceil _
    have hnat : 7 * s < scaledTripleBound q (560 / ell) N := by
      exact_mod_cast hreal.trans_le hceil
    simpa [s, N] using
      (show 3 * s + 4 * s ≤ scaledTripleBound q (560 / ell) N + 1 by omega)
  have hsmall :
      ((AsymptoticScale.degeneracyBudget q 4
          (AsymptoticScale.edgeBudget q 8
            (AsymptoticScale.queryBudget q ell)) + 1 : ℕ) : ℝ) *
        actualSmallSetPowerBound q ell 8 4 90 ≤ q ^ 80 :=
    (actual_smallSetErrorPowerBound hq hq1 hell (by norm_num)
      (by norm_num) hscale (by norm_num : 10 ≤ 90)).trans
        (actualSmallSetErrorPowerBound_c8_L90_le_q80 hq.le hell hell1)
  have hmeasure := measure_scaledRandomHostGoodEvent_compl_toReal_le_explicit
    (q := q) (ell := ell) (C := 8) (A := 4)
    (B₂ := 12) (B₃ := 560 / ell) (L := 90)
    hq hq1 hell (by norm_num) (by norm_num) hB₂ hB₃ hAlarge hscale
      hentropy hdense (by norm_num) hlocal (by
        have hpow0 : 0 ≤ actualSmallSetPowerBound q ell 8 4 90 := by
          unfold actualSmallSetPowerBound
          positivity
        calc
          actualSmallSetPowerBound q ell 8 4 90 ≤
              ((AsymptoticScale.degeneracyBudget q 4
                (AsymptoticScale.edgeBudget q 8
                  (AsymptoticScale.queryBudget q ell)) + 1 : ℕ) : ℝ) *
                actualSmallSetPowerBound q ell 8 4 90 :=
            le_mul_of_one_le_left hpow0 (by norm_num)
          _ ≤ q ^ 80 := hsmall
          _ ≤ 1 := pow_le_one₀ hq.le hq1)
  have hfailure : scaledHostFailureBoundReal q ell 8 4
      12 (560 / ell) 90 ≤ 4 * q ^ 80 :=
    scaledHostFailureBoundReal_le_four_mul_q_pow_eighty_of_strong_bounds
      hq hq1 hell (by norm_num) (by norm_num) hscale hentropy hdense hedge
        hpair htriple hsmall
  exact hmeasure.trans
    (hfailure.trans (four_mul_q_pow_eighty_le_q_pow_seventy hq.le hqhalf))

/-- After the crude six-label factor, sixty of the seventy powers are spent;
the bound remains `64 q^10`, uniformly for `ell ≤ 1`. -/
theorem measure_scaledRandomHostGoodEvent_smallEll_crudeSixVertex_le
    {q ell : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * q ≤ (4 : ℝ) * √(8 * ell / 2)) :
    ((2 * AsymptoticScale.queryBudget q ell : ℕ) : ℝ) ^ 6 *
      (RandomBoard.bitBoardMeasure
        (Sym2 (Fin (2 * AsymptoticScale.queryBudget q ell)))
        (cubeProbability q hq.le (hqhalf.trans (by norm_num)))
        (RandomBoard.randomHostGoodEvent
          (2 * AsymptoticScale.queryBudget q ell)
          (AsymptoticScale.edgeBudget q 8
            (AsymptoticScale.queryBudget q ell))
          (AsymptoticScale.degeneracyBudget q 4
            (AsymptoticScale.edgeBudget q 8
              (AsymptoticScale.queryBudget q ell))) 90
          (scaledPairBound q 12
            (AsymptoticScale.queryBudget q ell))
          (scaledTripleBound q (560 / ell)
            (AsymptoticScale.queryBudget q ell)))ᶜ).toReal ≤
      64 * q ^ 10 := by
  let N := AsymptoticScale.queryBudget q ell
  have hN := AsymptoticScale.queryBudget_cast_le_target hq hell0.le
  have htarget : ell / q ^ 10 ≤ 1 / q ^ 10 := by
    exact div_le_div_of_nonneg_right hell1 (pow_nonneg hq.le _)
  have hcount : ((2 * N : ℕ) : ℝ) ^ 6 ≤ (2 / q ^ 10) ^ 6 := by
    have hbase : ((2 * N : ℕ) : ℝ) ≤ 2 / q ^ 10 := by
      calc
        ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
        _ ≤ 2 * (ell / q ^ 10) := by gcongr
        _ ≤ 2 * (1 / q ^ 10) := by gcongr
        _ = 2 / q ^ 10 := by ring
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbase 6
  have hprob :=
    measure_scaledRandomHostGoodEvent_smallEll_compl_toReal_le_q70
      hq hqhalf hell0 hell1 hscale hpairScale hdense
  change ((2 * N : ℕ) : ℝ) ^ 6 * _ ≤ _
  calc
    ((2 * N : ℕ) : ℝ) ^ 6 * _ ≤ (2 / q ^ 10) ^ 6 * q ^ 70 := by
      exact mul_le_mul hcount hprob ENNReal.toReal_nonneg (by positivity)
    _ = 64 * q ^ 10 := by
      field_simp [ne_of_gt hq]
      ring

/-- `ENNReal` form consumed directly by the adaptive exceptional-history
truncation theorem. -/
theorem measure_scaledRandomHostGoodEvent_smallEll_crudeSixVertex_le_ofReal
    {q ell : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * q ≤ (4 : ℝ) * √(8 * ell / 2)) :
    ((((2 * AsymptoticScale.queryBudget q ell) ^ 6 : ℕ) : ℝ≥0∞) *
      RandomBoard.bitBoardMeasure
        (Sym2 (Fin (2 * AsymptoticScale.queryBudget q ell)))
        (cubeProbability q hq.le (hqhalf.trans (by norm_num)))
        (RandomBoard.randomHostGoodEvent
          (2 * AsymptoticScale.queryBudget q ell)
          (AsymptoticScale.edgeBudget q 8
            (AsymptoticScale.queryBudget q ell))
          (AsymptoticScale.degeneracyBudget q 4
            (AsymptoticScale.edgeBudget q 8
              (AsymptoticScale.queryBudget q ell))) 90
          (scaledPairBound q 12
            (AsymptoticScale.queryBudget q ell))
          (scaledTripleBound q (560 / ell)
            (AsymptoticScale.queryBudget q ell)))ᶜ) ≤
      ENNReal.ofReal (64 * q ^ 10) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by finiteness))
      ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 64 * q ^ 10)]
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
    measure_scaledRandomHostGoodEvent_smallEll_crudeSixVertex_le
      hq hqhalf hell0 hell1 hscale hpairScale hdense

end
end HostGoodProbability
end OnlineRamsey
