import OnlineRamsey.AsymptoticScale
import OnlineRamsey.HostGoodProbability

/-!
# Cubic-scale arithmetic for the shifted `B₄` branch

For `p=q³`, the sharp deterministic count is

`c₂² · (24 · 2L²) · M`,

where `c₂ = ceil(B₂ q⁶ N)` and `M = ceil(C q³ N)`.  Once both
unrounded targets are at least one, each ceiling costs at most a factor two,
so this expression is at most a fixed constant times `q¹⁵ N³`.  This is
exactly the prefix exponent required before the five remaining positive
completion edges are exposed.
-/

open scoped ENNReal NNReal

namespace OnlineRamsey
namespace B4SharpScale

open AsymptoticScale HostGoodProbability

/-- The natural main term in the sharp `Q` prefix estimate. -/
noncomputable def sharpQMain (q B₂ C : ℝ) (L N : ℕ) : ℕ :=
  let c₂ := scaledPairBound q B₂ N
  let M := edgeBudget q C N
  (c₂ * c₂ * (24 * (2 * L * L))) * M

/-- A nonnegative ceiling is at most twice its target once the target is at
least one. -/
theorem natCeil_cast_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : 1 ≤ x) :
    ((⌈x⌉₊ : ℕ) : ℝ) ≤ 2 * x := by
  have hceil : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  linarith

theorem scaledPairBound_cast_le_two_mul
    {q B₂ : ℝ} {N : ℕ} (hq : 0 ≤ q) (hB₂ : 0 ≤ B₂)
    (hone : 1 ≤ B₂ * q ^ 6 * (N : ℝ)) :
    (scaledPairBound q B₂ N : ℝ) ≤
      2 * (B₂ * q ^ 6 * (N : ℝ)) := by
  unfold scaledPairBound
  exact natCeil_cast_le_two_mul
    (mul_nonneg (mul_nonneg hB₂ (pow_nonneg hq _)) (Nat.cast_nonneg _)) hone

theorem edgeBudget_cast_le_two_mul
    {q C : ℝ} {N : ℕ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hone : 1 ≤ C * q ^ 3 * (N : ℝ)) :
    (edgeBudget q C N : ℝ) ≤
      2 * (C * q ^ 3 * (N : ℝ)) := by
  unfold edgeBudget
  exact natCeil_cast_le_two_mul
    (mul_nonneg (mul_nonneg hC (pow_nonneg hq _)) (Nat.cast_nonneg _)) hone

/-- General real-valued cubic-scale bound for the sharp `Q` coefficient. -/
theorem sharpQMain_cast_le
    {q B₂ C : ℝ} {L N : ℕ}
    (hq : 0 ≤ q) (hB₂ : 0 ≤ B₂) (hC : 0 ≤ C)
    (hpairOne : 1 ≤ B₂ * q ^ 6 * (N : ℝ))
    (hedgeOne : 1 ≤ C * q ^ 3 * (N : ℝ)) :
    (sharpQMain q B₂ C L N : ℝ) ≤
      (8 * (24 * (2 * (L : ℝ) * L)) * B₂ ^ 2 * C) *
        (q ^ 3) ^ 5 * (N : ℝ) ^ 3 := by
  have hc₂ := scaledPairBound_cast_le_two_mul hq hB₂ hpairOne
  have hM := edgeBudget_cast_le_two_mul hq hC hedgeOne
  dsimp [sharpQMain]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (scaledPairBound q B₂ N : ℝ) * scaledPairBound q B₂ N *
          (24 * (2 * (L : ℝ) * L)) * edgeBudget q C N ≤
        (2 * (B₂ * q ^ 6 * (N : ℝ))) *
          (2 * (B₂ * q ^ 6 * (N : ℝ))) *
          (24 * (2 * (L : ℝ) * L)) *
          (2 * (C * q ^ 3 * (N : ℝ))) := by
      gcongr
    _ = (8 * (24 * (2 * (L : ℝ) * L)) * B₂ ^ 2 * C) *
          (q ^ 3) ^ 5 * (N : ℝ) ^ 3 := by ring

/-- Numeric form used by the `C=8`, `B₂=12`, `L=90` host. -/
theorem sharpQMain_c8_L90_cast_le
    {q : ℝ} {N : ℕ} (hq : 0 ≤ q)
    (hpairOne : 1 ≤ 12 * q ^ 6 * (N : ℝ))
    (hedgeOne : 1 ≤ 8 * q ^ 3 * (N : ℝ)) :
    (sharpQMain q 12 8 90 N : ℝ) ≤
      3583180800 * (q ^ 3) ^ 5 * (N : ℝ) ^ 3 := by
  convert sharpQMain_cast_le (L := 90) hq
    (by norm_num : (0 : ℝ) ≤ 12) (by norm_num : (0 : ℝ) ≤ 8)
      hpairOne hedgeOne using 1 <;> norm_num

/-- `ENNReal` form matching the concrete stopping-history estimate. -/
theorem sharpQMain_c8_L90_coe_le
    {q : ℝ} {N : ℕ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hpairOne : 1 ≤ 12 * q ^ 6 * (N : ℝ))
    (hedgeOne : 1 ≤ 8 * q ^ 3 * (N : ℝ)) :
    ((sharpQMain q 12 8 90 N : ℕ) : ℝ≥0∞) ≤
      3583180800 *
        (unitInterval.toNNReal (cubeProbability q hq hq1) : ℝ≥0∞) ^ 5 *
          (N : ℝ≥0∞) ^ 3 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  exact sharpQMain_c8_L90_cast_le hq hpairOne hedgeOne

/-! ## Arbitrary fixed `ell` -/

/-- At `N=floor(ell/q¹⁰)`, explicit smallness conditions force both
rounded targets to be at least one.  No specialization to `ell=1` occurs. -/
theorem queryBudget_pair_edge_targets_ge_one
    {q ell B₂ C : ℝ}
    (hq : 0 < q) (hell : 0 < ell) (hB₂ : 0 < B₂) (hC : 0 < C)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ B₂ * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ C * ell) :
    1 ≤ B₂ * q ^ 6 * (queryBudget q ell : ℝ) ∧
      1 ≤ C * q ^ 3 * (queryBudget q ell : ℝ) := by
  have hN := (normalized_queryBudget_bounds_half hq hell.le hfloor).1
  have hq4 : 0 < q ^ 4 := pow_pos hq _
  have hq7 : 0 < q ^ 7 := pow_pos hq _
  constructor
  · have hnorm : 1 ≤ B₂ * ell / (2 * q ^ 4) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hq4)]
      linarith
    exact (calc
      1 ≤ B₂ * ell / (2 * q ^ 4) := hnorm
      _ < B₂ * q ^ 6 * (queryBudget q ell : ℝ) := by
        have hmul := mul_lt_mul_of_pos_left hN hB₂
        calc
          B₂ * ell / (2 * q ^ 4) = B₂ * (ell / 2) / q ^ 4 := by ring
          _ < B₂ * (q ^ 10 * (queryBudget q ell : ℝ)) / q ^ 4 :=
            (div_lt_div_iff_of_pos_right hq4).2 hmul
          _ = B₂ * q ^ 6 * (queryBudget q ell : ℝ) := by
            field_simp [ne_of_gt hq]) |>.le
  · have hnorm : 1 ≤ C * ell / (2 * q ^ 7) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hq7)]
      linarith
    exact (calc
      1 ≤ C * ell / (2 * q ^ 7) := hnorm
      _ < C * q ^ 3 * (queryBudget q ell : ℝ) := by
        have hmul := mul_lt_mul_of_pos_left hN hC
        calc
          C * ell / (2 * q ^ 7) = C * (ell / 2) / q ^ 7 := by ring
          _ < C * (q ^ 10 * (queryBudget q ell : ℝ)) / q ^ 7 :=
            (div_lt_div_iff_of_pos_right hq7).2 hmul
          _ = C * q ^ 3 * (queryBudget q ell : ℝ) := by
            field_simp [ne_of_gt hq]) |>.le

/-- The sharp shifted-`B₄` main term has a uniform `q¹⁵N³` bound at
the floor scale for every fixed positive `ell`. -/
theorem sharpQMain_queryBudget_cast_le
    {q ell B₂ C : ℝ} {L : ℕ}
    (hq : 0 < q) (hell : 0 < ell) (hB₂ : 0 < B₂) (hC : 0 < C)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ B₂ * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ C * ell) :
    (sharpQMain q B₂ C L (queryBudget q ell) : ℝ) ≤
      (8 * (24 * (2 * (L : ℝ) * L)) * B₂ ^ 2 * C) *
        (q ^ 3) ^ 5 * (queryBudget q ell : ℝ) ^ 3 := by
  rcases queryBudget_pair_edge_targets_ge_one hq hell hB₂ hC hfloor
      hpairSmall hedgeSmall with ⟨hpairOne, hedgeOne⟩
  exact sharpQMain_cast_le hq.le hB₂.le hC.le hpairOne hedgeOne

/-- General arbitrary-`ell` form after the five remaining completion edges.
The constant is independent of `ell`; all `ell`-dependence is the desired
cubic factor. -/
theorem completedSharpQMain_queryBudget_le_ell_cubed
    {q ell B₂ C : ℝ} {L : ℕ}
    (hq : 0 < q) (hell : 0 < ell) (hB₂ : 0 < B₂) (hC : 0 < C)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ B₂ * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ C * ell) :
    (q ^ 3) ^ 5 *
        (sharpQMain q B₂ C L (queryBudget q ell) : ℝ) ≤
      (8 * (24 * (2 * (L : ℝ) * L)) * B₂ ^ 2 * C) * ell ^ 3 := by
  have hmain := sharpQMain_queryBudget_cast_le
    (L := L) hq hell hB₂ hC hfloor hpairSmall hedgeSmall
  have hthreshold := queryBudget_cubic_threshold hq hell.le
  calc
    (q ^ 3) ^ 5 *
        (sharpQMain q B₂ C L (queryBudget q ell) : ℝ) ≤
      (q ^ 3) ^ 5 *
        ((8 * (24 * (2 * (L : ℝ) * L)) * B₂ ^ 2 * C) *
          (q ^ 3) ^ 5 * (queryBudget q ell : ℝ) ^ 3) := by
        gcongr
    _ = (8 * (24 * (2 * (L : ℝ) * L)) * B₂ ^ 2 * C) *
        (q ^ 30 * (queryBudget q ell : ℝ) ^ 3) := by ring
    _ ≤ (8 * (24 * (2 * (L : ℝ) * L)) * B₂ ^ 2 * C) * ell ^ 3 := by
      gcongr

/-- After the five completion edges, the numeric main contribution of one
shifted-`B₄` order is at most `3583180800 * ell³`. -/
theorem completedSharpQMain_c8_L90_queryBudget_le_ell_cubed
    {q ell : ℝ}
    (hq : 0 < q) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell) :
    (q ^ 3) ^ 5 *
        (sharpQMain q 12 8 90 (queryBudget q ell) : ℝ) ≤
      3583180800 * ell ^ 3 := by
  convert completedSharpQMain_queryBudget_le_ell_cubed
    (L := 90) hq hell (by norm_num : (0 : ℝ) < 12)
      (by norm_num : (0 : ℝ) < 8) hfloor hpairSmall hedgeSmall using 1 <;>
    norm_num

end B4SharpScale
end OnlineRamsey
