import OnlineRamsey.K4Moments
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Sqrt

/-!
# Explicit scale bounds for the four-clique moments

This file begins the analytic bridge from the exact finite-board formulas in
`K4Moments.lean` to the constants used by `UpperBound.lean`.  The density is
`a⁻³` and the filled vertex set has cardinality `a⁴`.
-/

namespace OnlineRamsey
namespace K4MomentBounds

open K4Moments

/-- Edge density on the integral `a`-scale. -/
noncomputable def density (a : ℕ) : ℝ := 1 / (a : ℝ) ^ 3

/-- Exact real first-moment expression furnished by
`graphK4Count_firstMoment` after casting out of `ENNReal`. -/
noncomputable def firstMomentExpression (a : ℕ) : ℝ :=
  (Nat.choose (a ^ 4) 4 : ℝ) * density a ^ 6

/-- Exact real five-overlap expression furnished by
`graphK4Count_secondMoment` after casting out of `ENNReal`. -/
noncomputable def secondMomentExpression (a : ℕ) : ℝ :=
  ∑ k ∈ Finset.range 5,
    (Nat.choose (a ^ 4) 4 * Nat.choose 4 k *
      Nat.choose (a ^ 4 - 4) (4 - k) : ℝ) *
      density a ^ (12 - Nat.choose k 2)

/-- Closed polynomial formula for the number of four-subsets. -/
theorem cast_choose_four (n : ℕ) : (n.choose 4 : ℝ) =
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) *
      ((n : ℝ) - 3) / 24 := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  norm_num [descPochhammer, Nat.factorial]
  ring

/-- The exact first moment has the lower constant used by the paper's
branch-and-fill calculation. -/
theorem firstMomentExpression_lower (a : ℕ) (ha : 2 ≤ a) :
    1 / (192 * (a : ℝ) ^ 2) ≤ firstMomentExpression a := by
  let x : ℝ := a
  let n : ℝ := x ^ 4
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast ha
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hn : 16 ≤ n := by
    dsimp [n]
    nlinarith [sq_nonneg (x ^ 2 - 4)]
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have h1 : n / 2 ≤ n - 1 := by linarith
  have h2 : n / 2 ≤ n - 2 := by linarith
  have h3 : n / 2 ≤ n - 3 := by linarith
  have hhalf : 0 ≤ n / 2 := by positivity
  have hn1 : 0 ≤ n - 1 := by linarith
  have hn2 : 0 ≤ n - 2 := by linarith
  have hprod : n ^ 4 / 8 ≤ n * (n - 1) * (n - 2) * (n - 3) := by
    calc
      n ^ 4 / 8 = n * (n / 2) * (n / 2) * (n / 2) := by ring
      _ ≤ n * (n - 1) * (n - 2) * (n - 3) := by gcongr
  have hchoose : n ^ 4 / 192 ≤ (Nat.choose (a ^ 4) 4 : ℝ) := by
    rw [cast_choose_four]
    have hncast : ((a ^ 4 : ℕ) : ℝ) = n := by simp [n, x]
    rw [hncast]
    linarith
  unfold firstMomentExpression density
  have hscale :
      1 / (192 * x ^ 2) = (n ^ 4 / 192) * (1 / x ^ 3) ^ 6 := by
    dsimp [n]
    field_simp [ne_of_gt hx0]
  change 1 / (192 * x ^ 2) ≤
    (Nat.choose (a ^ 4) 4 : ℝ) * (1 / x ^ 3) ^ 6
  rw [hscale]
  exact mul_le_mul_of_nonneg_right hchoose (by positivity)

/-- The five overlap classes written out explicitly. -/
theorem secondMomentExpression_expand (a : ℕ) (ha : 2 ≤ a) : secondMomentExpression a =
    (Nat.choose (a ^ 4) 4 : ℝ) * Nat.choose (a ^ 4 - 4) 4 * density a ^ 12 +
    (Nat.choose (a ^ 4) 4 : ℝ) * 4 * Nat.choose (a ^ 4 - 4) 3 * density a ^ 12 +
    (Nat.choose (a ^ 4) 4 : ℝ) * 6 * Nat.choose (a ^ 4 - 4) 2 * density a ^ 11 +
    (Nat.choose (a ^ 4) 4 : ℝ) * 4 * (a ^ 4 - 4) * density a ^ 9 +
    (Nat.choose (a ^ 4) 4 : ℝ) * density a ^ 6 := by
  have hfour : 4 ≤ a ^ 4 := by
    have hpow : 2 ^ 4 ≤ a ^ 4 := Nat.pow_le_pow_left ha 4
    norm_num at hpow ⊢
    omega
  simp [secondMomentExpression, Finset.sum_range_succ,
    show Nat.choose 4 2 = 6 by decide, Nat.cast_sub hfour]

/-- A term-by-term factorial bound for the exact overlap expansion. -/
theorem secondMomentExpression_upper_explicit (a : ℕ) (ha : 2 ≤ a) :
    secondMomentExpression a ≤
      1 / (576 * (a : ℝ) ^ 4) + 1 / (36 * (a : ℝ) ^ 8) +
      1 / (8 * (a : ℝ) ^ 9) + 1 / (6 * (a : ℝ) ^ 7) +
      1 / (24 * (a : ℝ) ^ 2) := by
  let x : ℝ := a
  let N : ℕ := a ^ 4
  let n : ℝ := N
  let M : ℕ := N - 4
  let m : ℝ := M
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast ha
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hncast : n = x ^ 4 := by simp [n, N, x]
  have hmle : m ≤ n := by
    dsimp [m, M, n]
    exact_mod_cast Nat.sub_le N 4
  have hn0 : 0 ≤ n := by positivity
  have hm0 : 0 ≤ m := by positivity
  have hc4 : (Nat.choose N 4 : ℝ) ≤ n ^ 4 / 24 := by
    simpa [n, Nat.factorial] using
      (Nat.choose_le_pow_div (α := ℝ) 4 N)
  have hm4 : (Nat.choose M 4 : ℝ) ≤ n ^ 4 / 24 := by
    calc
      (Nat.choose M 4 : ℝ) ≤ m ^ 4 / 24 := by
        simpa [m, Nat.factorial] using
          (Nat.choose_le_pow_div (α := ℝ) 4 M)
      _ ≤ n ^ 4 / 24 := by gcongr
  have hm3 : (Nat.choose M 3 : ℝ) ≤ n ^ 3 / 6 := by
    calc
      (Nat.choose M 3 : ℝ) ≤ m ^ 3 / 6 := by
        simpa [m, Nat.factorial] using
          (Nat.choose_le_pow_div (α := ℝ) 3 M)
      _ ≤ n ^ 3 / 6 := by gcongr
  have hm2 : (Nat.choose M 2 : ℝ) ≤ n ^ 2 / 2 := by
    calc
      (Nat.choose M 2 : ℝ) ≤ m ^ 2 / 2 := by
        simpa [m, Nat.factorial] using
          (Nat.choose_le_pow_div (α := ℝ) 2 M)
      _ ≤ n ^ 2 / 2 := by gcongr
  have hM : (M : ℝ) ≤ n := by simpa [m] using hmle
  rw [secondMomentExpression_expand a ha]
  have hfour : 4 ≤ a ^ 4 := by
    have hpow : 2 ^ 4 ≤ a ^ 4 := Nat.pow_le_pow_left ha 4
    norm_num at hpow ⊢
    omega
  have hM' : ((a ^ 4 : ℕ) : ℝ) - 4 ≤ n := by
    simpa [M, N, Nat.cast_sub hfour] using hM
  have hM0' : 0 ≤ ((a ^ 4 : ℕ) : ℝ) - 4 := by
    apply sub_nonneg.mpr
    exact_mod_cast hfour
  have hd0 : 0 ≤ density a := by
    unfold density
    positivity
  simp only [N, M] at hc4 hm4 hm3 hm2
  calc
    _ ≤ (n ^ 4 / 24) * (n ^ 4 / 24) * density a ^ 12 +
        (n ^ 4 / 24) * 4 * (n ^ 3 / 6) * density a ^ 12 +
        (n ^ 4 / 24) * 6 * (n ^ 2 / 2) * density a ^ 11 +
        (n ^ 4 / 24) * 4 * n * density a ^ 9 +
        (n ^ 4 / 24) * density a ^ 6 := by
          gcongr
          · simpa using hM0'
          · simpa using hM'
    _ = 1 / (576 * x ^ 4) + 1 / (36 * x ^ 8) +
        1 / (8 * x ^ 9) + 1 / (6 * x ^ 7) + 1 / (24 * x ^ 2) := by
          rw [hncast]
          unfold density
          field_simp [ne_of_gt hx0]
          ring
    _ = _ := by rfl

/-- The exact second moment has the loose upper constant used by the paper. -/
theorem secondMomentExpression_upper (a : ℕ) (ha : 2 ≤ a) :
    secondMomentExpression a ≤ 5 / (a : ℝ) ^ 2 := by
  let x : ℝ := a
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast ha
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hpow (k : ℕ) (hk : 2 ≤ k) : x ^ 2 ≤ x ^ k :=
    pow_le_pow_right₀ hx1 hk
  have hden (k c : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ c) :
      x ^ 2 ≤ (c : ℝ) * x ^ k := by
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
    calc
      x ^ 2 ≤ x ^ k := hpow k hk
      _ ≤ (c : ℝ) * x ^ k := by
        nlinarith [show 0 ≤ x ^ k by positivity]
  calc
    secondMomentExpression a ≤
        1 / (576 * (a : ℝ) ^ 4) + 1 / (36 * (a : ℝ) ^ 8) +
        1 / (8 * (a : ℝ) ^ 9) + 1 / (6 * (a : ℝ) ^ 7) +
        1 / (24 * (a : ℝ) ^ 2) := secondMomentExpression_upper_explicit a ha
    _ ≤ 1 / x ^ 2 + 1 / x ^ 2 + 1 / x ^ 2 + 1 / x ^ 2 + 1 / x ^ 2 := by
      dsimp [x]
      gcongr
      · simpa [x] using hden 4 576 (by omega) (by omega)
      · simpa [x] using hden 8 36 (by omega) (by omega)
      · simpa [x] using hden 9 8 (by omega) (by omega)
      · simpa [x] using hden 7 6 (by omega) (by omega)
      · simpa [x] using hden 2 24 (by omega) (by omega)
    _ = 5 / (a : ℝ) ^ 2 := by
      dsimp [x]
      ring

/-! ## Finite second-moment inequality -/

/-- Weighted finite Cauchy--Schwarz in the exact form needed after restricting
the sample space to boards on which the count is positive. -/
theorem finite_weighted_cauchy {Ω : Type*} [DecidableEq Ω]
    (s : Finset Ω) (weight X : Ω → ℝ)
    (hweight : ∀ ω ∈ s, 0 ≤ weight ω) :
    (∑ ω ∈ s, weight ω * X ω) ^ 2 ≤
      (∑ ω ∈ s, weight ω) * ∑ ω ∈ s, weight ω * X ω ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun ω => √(weight ω)) (fun ω => √(weight ω) * X ω)
  have hleft : (∑ ω ∈ s, √(weight ω) * (√(weight ω) * X ω)) =
      ∑ ω ∈ s, weight ω * X ω := by
    apply Finset.sum_congr rfl
    intro ω hω
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hweight ω hω)]
  have hfirst : (∑ ω ∈ s, √(weight ω) ^ 2) = ∑ ω ∈ s, weight ω := by
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Real.sq_sqrt (hweight ω hω)]
  have hsecond : (∑ ω ∈ s, (√(weight ω) * X ω) ^ 2) =
      ∑ ω ∈ s, weight ω * X ω ^ 2 := by
    apply Finset.sum_congr rfl
    intro ω hω
    rw [mul_pow, Real.sq_sqrt (hweight ω hω)]
  rwa [hleft, hfirst, hsecond] at hcs

/-- Exact finite-board Paley--Zygmund bookkeeping.  The first moment may be
restricted to the positive support because a nonnegative random variable
vanishes off that support. -/
theorem finite_secondMoment_success {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (weight X : Ω → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω) (hX : ∀ ω, 0 ≤ X ω) :
    (∑ ω, weight ω * X ω) ^ 2 ≤
      (∑ ω ∈ (Finset.univ.filter fun ω => 0 < X ω), weight ω) *
        ∑ ω, weight ω * X ω ^ 2 := by
  let support : Finset Ω := Finset.univ.filter fun ω => 0 < X ω
  have hfirst : (∑ ω ∈ support, weight ω * X ω) =
      ∑ ω, weight ω * X ω := by
    symm
    calc
      (∑ ω, weight ω * X ω) =
          ∑ ω, if 0 < X ω then weight ω * X ω else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hpos : 0 < X ω
        · simp [hpos]
        · have hz : X ω = 0 := le_antisymm (le_of_not_gt hpos) (hX ω)
          simp [hpos, hz]
      _ = ∑ ω ∈ support, weight ω * X ω := by
        simpa [support] using
          (Finset.sum_filter (s := (Finset.univ : Finset Ω))
            (fun ω => 0 < X ω) (fun ω => weight ω * X ω)).symm
  have hsecond : (∑ ω ∈ support, weight ω * X ω ^ 2) =
      ∑ ω, weight ω * X ω ^ 2 := by
    symm
    calc
      (∑ ω, weight ω * X ω ^ 2) =
          ∑ ω, if 0 < X ω then weight ω * X ω ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hpos : 0 < X ω
        · simp [hpos]
        · have hz : X ω = 0 := le_antisymm (le_of_not_gt hpos) (hX ω)
          simp [hpos, hz]
      _ = ∑ ω ∈ support, weight ω * X ω ^ 2 := by
        simpa [support] using
          (Finset.sum_filter (s := (Finset.univ : Finset Ω))
            (fun ω => 0 < X ω) (fun ω => weight ω * X ω ^ 2)).symm
  have hcs := finite_weighted_cauchy support weight X
    (fun ω _ => hweight ω)
  rw [hfirst, hsecond] at hcs
  simpa [support] using hcs

/-- Quotient form of the finite second-moment lower bound. -/
theorem finite_success_ge_first_sq_div_second
    (mu second success : ℝ) (hsecond : 0 < second)
    (hcs : mu ^ 2 ≤ success * second) :
    mu ^ 2 / second ≤ success := by
  exact (div_le_iff₀ hsecond).2 (by simpa [mul_comm] using hcs)

end K4MomentBounds
end OnlineRamsey
