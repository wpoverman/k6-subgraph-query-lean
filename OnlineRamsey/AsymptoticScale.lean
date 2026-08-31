import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite `q`-scale inequalities for the `K₆` lower bound

Writing `p = q³` turns every scale in the subgraph-query argument into an
integral power of `q`.  This module uses the actual natural floor and ceiling
scales

* `N = floor (ell / q¹⁰)`;
* `M = ceil (C q³ N)`;
* `D = ceil (A sqrt (q³ M))`.

The results are finite inequalities, with all rounding errors displayed.
They are deliberately stronger and easier to instantiate than filter-level
`IsTheta` statements.
-/

namespace OnlineRamsey
namespace AsymptoticScale

/-- Natural query budget at the `q⁻¹⁰` scale. -/
noncomputable def queryBudget (q ell : ℝ) : ℕ :=
  ⌊ell / q ^ 10⌋₊

/-- Natural upper scale for the number of positive queried edges. -/
noncomputable def edgeBudget (q C : ℝ) (N : ℕ) : ℕ :=
  ⌈C * q ^ 3 * (N : ℝ)⌉₊

/-- Natural degeneracy scale used by the uniform-host argument. -/
noncomputable def degeneracyBudget (q A : ℝ) (M : ℕ) : ℕ :=
  ⌈A * √(q ^ 3 * (M : ℝ))⌉₊

section QueryBudget

theorem queryBudget_cast_le_target {q ell : ℝ} (hq : 0 < q) (hell : 0 ≤ ell) :
    (queryBudget q ell : ℝ) ≤ ell / q ^ 10 := by
  unfold queryBudget
  exact Nat.floor_le (div_nonneg hell (pow_nonneg hq.le _))

theorem queryBudget_target_lt_cast_add_one (q ell : ℝ) :
    ell / q ^ 10 < (queryBudget q ell : ℝ) + 1 := by
  simpa [queryBudget] using Nat.lt_floor_add_one (ell / q ^ 10)

/-- The exact additive-error sandwich for the floored query budget. -/
theorem queryBudget_additive_sandwich {q ell : ℝ} (hq : 0 < q) (hell : 0 ≤ ell) :
    ell / q ^ 10 - 1 < (queryBudget q ell : ℝ) ∧
      (queryBudget q ell : ℝ) ≤ ell / q ^ 10 := by
  constructor
  · have h := queryBudget_target_lt_cast_add_one q ell
    linarith
  · exact queryBudget_cast_le_target hq hell

/-- Multiplying out the floor sandwich avoids all negative exponents. -/
theorem normalized_queryBudget_bounds {q ell : ℝ} (hq : 0 < q) (hell : 0 ≤ ell) :
    ell - q ^ 10 < q ^ 10 * (queryBudget q ell : ℝ) ∧
      q ^ 10 * (queryBudget q ell : ℝ) ≤ ell := by
  rcases queryBudget_additive_sandwich hq hell with ⟨hlower, hupper⟩
  have hq10 : 0 < q ^ 10 := pow_pos hq _
  constructor
  · calc
      ell - q ^ 10 = q ^ 10 * (ell / q ^ 10 - 1) := by
        field_simp [ne_of_gt hq]
      _ < q ^ 10 * (queryBudget q ell : ℝ) :=
        mul_lt_mul_of_pos_left hlower hq10
  · calc
      q ^ 10 * (queryBudget q ell : ℝ) ≤
          q ^ 10 * (ell / q ^ 10) :=
        mul_le_mul_of_nonneg_left hupper hq10.le
      _ = ell := by field_simp [ne_of_gt hq]

/-- Once the floor target is at least two, its normalized value lies between
`ell/2` and `ell`. -/
theorem normalized_queryBudget_bounds_half {q ell : ℝ}
    (hq : 0 < q) (hell : 0 ≤ ell) (hsmall : 2 * q ^ 10 ≤ ell) :
    ell / 2 < q ^ 10 * (queryBudget q ell : ℝ) ∧
      q ^ 10 * (queryBudget q ell : ℝ) ≤ ell := by
  have h := normalized_queryBudget_bounds hq hell
  constructor
  · linarith
  · exact h.2

/-- With `p=q³`, this is the exact finite form of `pN = Θ(q⁻⁷)`. -/
theorem density_mul_queryBudget_bounds {q ell : ℝ} (hq : 0 < q) (hell : 0 ≤ ell) :
    ell / q ^ 7 - q ^ 3 < q ^ 3 * (queryBudget q ell : ℝ) ∧
      q ^ 3 * (queryBudget q ell : ℝ) ≤ ell / q ^ 7 := by
  rcases queryBudget_additive_sandwich hq hell with ⟨hlower, hupper⟩
  have hq3 : 0 < q ^ 3 := pow_pos hq _
  constructor
  · calc
      ell / q ^ 7 - q ^ 3 = q ^ 3 * (ell / q ^ 10 - 1) := by
        field_simp [ne_of_gt hq]
      _ < q ^ 3 * (queryBudget q ell : ℝ) :=
        mul_lt_mul_of_pos_left hlower hq3
  · calc
      q ^ 3 * (queryBudget q ell : ℝ) ≤ q ^ 3 * (ell / q ^ 10) :=
        mul_le_mul_of_nonneg_left hupper hq3.le
      _ = ell / q ^ 7 := by
        field_simp [ne_of_gt hq]

/-- With `p=q³`, this is the exact finite form of `p²N = Θ(q⁻⁴)`. -/
theorem density_sq_mul_queryBudget_bounds {q ell : ℝ}
    (hq : 0 < q) (hell : 0 ≤ ell) :
    ell / q ^ 4 - q ^ 6 < q ^ 6 * (queryBudget q ell : ℝ) ∧
      q ^ 6 * (queryBudget q ell : ℝ) ≤ ell / q ^ 4 := by
  rcases queryBudget_additive_sandwich hq hell with ⟨hlower, hupper⟩
  have hq6 : 0 < q ^ 6 := pow_pos hq _
  constructor
  · calc
      ell / q ^ 4 - q ^ 6 = q ^ 6 * (ell / q ^ 10 - 1) := by
        field_simp [ne_of_gt hq]
      _ < q ^ 6 * (queryBudget q ell : ℝ) :=
        mul_lt_mul_of_pos_left hlower hq6
  · calc
      q ^ 6 * (queryBudget q ell : ℝ) ≤ q ^ 6 * (ell / q ^ 10) :=
        mul_le_mul_of_nonneg_left hupper hq6.le
      _ = ell / q ^ 4 := by
        field_simp [ne_of_gt hq]

/-- With `p=q³`, this is the exact finite form of `p³N = Θ(q⁻¹)`. -/
theorem density_cube_mul_queryBudget_bounds {q ell : ℝ}
    (hq : 0 < q) (hell : 0 ≤ ell) :
    ell / q - q ^ 9 < q ^ 9 * (queryBudget q ell : ℝ) ∧
      q ^ 9 * (queryBudget q ell : ℝ) ≤ ell / q := by
  rcases queryBudget_additive_sandwich hq hell with ⟨hlower, hupper⟩
  have hq9 : 0 < q ^ 9 := pow_pos hq _
  constructor
  · calc
      ell / q - q ^ 9 = q ^ 9 * (ell / q ^ 10 - 1) := by
        field_simp [ne_of_gt hq]
      _ < q ^ 9 * (queryBudget q ell : ℝ) :=
        mul_lt_mul_of_pos_left hlower hq9
  · calc
      q ^ 9 * (queryBudget q ell : ℝ) ≤ q ^ 9 * (ell / q ^ 10) :=
        mul_le_mul_of_nonneg_left hupper hq9.le
      _ = ell / q := by
        field_simp [ne_of_gt hq]

/-- The threshold monomial already used abstractly in `Assembly.lean`, now
specialized to the actual floored natural query budget. -/
theorem queryBudget_cubic_threshold {q ell : ℝ} (hq : 0 < q) (hell : 0 ≤ ell) :
    q ^ 30 * (queryBudget q ell : ℝ) ^ 3 ≤ ell ^ 3 := by
  have hscale := (normalized_queryBudget_bounds hq hell).2
  have hnonneg : 0 ≤ q ^ 10 * (queryBudget q ell : ℝ) := by positivity
  calc
    q ^ 30 * (queryBudget q ell : ℝ) ^ 3 =
        (q ^ 10 * (queryBudget q ell : ℝ)) ^ 3 := by ring
    _ ≤ ell ^ 3 := pow_le_pow_left₀ hnonneg hscale 3

end QueryBudget

section CeilingScales

theorem edgeBudget_target_le (q C : ℝ) (N : ℕ) :
    C * q ^ 3 * (N : ℝ) ≤ (edgeBudget q C N : ℝ) := by
  exact Nat.le_ceil _

theorem edgeBudget_lt_target_add_one {q C : ℝ} (N : ℕ)
    (hq : 0 ≤ q) (hC : 0 ≤ C) :
    (edgeBudget q C N : ℝ) < C * q ^ 3 * (N : ℝ) + 1 := by
  unfold edgeBudget
  exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hC (pow_nonneg hq _)) (Nat.cast_nonneg _))

/-- Optimal additive-error normalization of the edge ceiling. -/
theorem normalized_edgeBudget_additive_bounds {q ell C : ℝ}
    (hq : 0 < q) (hell : 0 ≤ ell) (hC : 0 < C) :
    C * (ell - q ^ 10) <
        q ^ 7 * (edgeBudget q C (queryBudget q ell) : ℝ) ∧
      q ^ 7 * (edgeBudget q C (queryBudget q ell) : ℝ) <
        C * ell + q ^ 7 := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  have hN := normalized_queryBudget_bounds hq hell
  have hMlower : C * q ^ 3 * (N : ℝ) ≤ (M : ℝ) :=
    edgeBudget_target_le q C N
  have hMupper : (M : ℝ) < C * q ^ 3 * (N : ℝ) + 1 :=
    edgeBudget_lt_target_add_one N hq.le hC.le
  have hq7 : 0 < q ^ 7 := pow_pos hq _
  constructor
  · calc
      C * (ell - q ^ 10) < C * (q ^ 10 * (N : ℝ)) :=
        mul_lt_mul_of_pos_left hN.1 hC
      _ = q ^ 7 * (C * q ^ 3 * (N : ℝ)) := by ring
      _ ≤ q ^ 7 * (M : ℝ) := mul_le_mul_of_nonneg_left hMlower hq7.le
  · calc
      q ^ 7 * (M : ℝ) < q ^ 7 * (C * q ^ 3 * (N : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hMupper hq7
      _ = C * (q ^ 10 * (N : ℝ)) + q ^ 7 := by ring
      _ ≤ C * ell + q ^ 7 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hN.2 hC.le) _

/-- The edge ceiling satisfies `q⁷M = Θ(1)` with explicit finite constants. -/
theorem normalized_edgeBudget_bounds {q ell C : ℝ}
    (hq : 0 < q) (hell : 0 ≤ ell) (hC : 0 < C)
    (hsmall : 2 * q ^ 10 ≤ ell) :
    C * ell / 2 <
        q ^ 7 * (edgeBudget q C (queryBudget q ell) : ℝ) ∧
      q ^ 7 * (edgeBudget q C (queryBudget q ell) : ℝ) <
        C * ell + q ^ 7 := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  have hN := normalized_queryBudget_bounds_half hq hell hsmall
  have hMlower : C * q ^ 3 * (N : ℝ) ≤ (M : ℝ) :=
    edgeBudget_target_le q C N
  have hMupper : (M : ℝ) < C * q ^ 3 * (N : ℝ) + 1 :=
    edgeBudget_lt_target_add_one N hq.le hC.le
  have hq7 : 0 < q ^ 7 := pow_pos hq _
  constructor
  · calc
      C * ell / 2 = C * (ell / 2) := by ring
      _ < C * (q ^ 10 * (N : ℝ)) := mul_lt_mul_of_pos_left hN.1 hC
      _ = q ^ 7 * (C * q ^ 3 * (N : ℝ)) := by ring
      _ ≤ q ^ 7 * (M : ℝ) := mul_le_mul_of_nonneg_left hMlower hq7.le
  · calc
      q ^ 7 * (M : ℝ) < q ^ 7 * (C * q ^ 3 * (N : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hMupper hq7
      _ = C * (q ^ 10 * (N : ℝ)) + q ^ 7 := by ring
      _ ≤ C * ell + q ^ 7 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hN.2 hC.le) _

theorem degeneracyBudget_target_le (q A : ℝ) (M : ℕ) :
    A * √(q ^ 3 * (M : ℝ)) ≤ (degeneracyBudget q A M : ℝ) := by
  exact Nat.le_ceil _

theorem degeneracyBudget_lt_target_add_one {q A : ℝ} (M : ℕ)
    (hA : 0 ≤ A) :
    (degeneracyBudget q A M : ℝ) < A * √(q ^ 3 * (M : ℝ)) + 1 := by
  unfold degeneracyBudget
  exact Nat.ceil_lt_add_one (mul_nonneg hA (Real.sqrt_nonneg _))

/-- Normalizing the square-root scale introduces exactly two powers of `q`. -/
theorem q_sq_mul_sqrt_density (q m : ℝ) (hq : 0 ≤ q) :
    q ^ 2 * √(q ^ 3 * m) = √(q ^ 7 * m) := by
  have hq4 : √(q ^ 4) = q ^ 2 := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg q)]
  rw [← hq4, ← Real.sqrt_mul (pow_nonneg hq 4)]
  congr 1
  ring

/-- Optimal additive-error normalization of the degeneracy ceiling. -/
theorem normalized_degeneracyBudget_additive_bounds {q ell C A : ℝ}
    (hq : 0 < q) (hell : 0 ≤ ell) (hC : 0 < C) (hA : 0 ≤ A) :
    A * √(C * (ell - q ^ 10)) ≤
        q ^ 2 *
          (degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) : ℝ) ∧
      q ^ 2 *
          (degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) : ℝ) <
        A * √(C * ell + q ^ 7) + q ^ 2 := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  let D := degeneracyBudget q A M
  have hM := normalized_edgeBudget_additive_bounds hq hell hC
  have hsqrtLower : √(C * (ell - q ^ 10)) ≤ √(q ^ 7 * (M : ℝ)) :=
    Real.sqrt_le_sqrt hM.1.le
  have hsqrtUpper : √(q ^ 7 * (M : ℝ)) ≤ √(C * ell + q ^ 7) :=
    Real.sqrt_le_sqrt hM.2.le
  have hDlower : A * √(q ^ 3 * (M : ℝ)) ≤ (D : ℝ) :=
    degeneracyBudget_target_le q A M
  have hDupper : (D : ℝ) < A * √(q ^ 3 * (M : ℝ)) + 1 :=
    degeneracyBudget_lt_target_add_one M hA
  constructor
  · calc
      A * √(C * (ell - q ^ 10)) ≤ A * √(q ^ 7 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtLower hA
      _ = q ^ 2 * (A * √(q ^ 3 * (M : ℝ))) := by
        rw [← q_sq_mul_sqrt_density q (M : ℝ) hq.le]
        ring
      _ ≤ q ^ 2 * (D : ℝ) :=
        mul_le_mul_of_nonneg_left hDlower (pow_nonneg hq.le _)
  · calc
      q ^ 2 * (D : ℝ) < q ^ 2 * (A * √(q ^ 3 * (M : ℝ)) + 1) :=
        mul_lt_mul_of_pos_left hDupper (pow_pos hq _)
      _ = A * √(q ^ 7 * (M : ℝ)) + q ^ 2 := by
        rw [← q_sq_mul_sqrt_density q (M : ℝ) hq.le]
        ring
      _ ≤ A * √(C * ell + q ^ 7) + q ^ 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsqrtUpper hA) _

/-- The actual ceiling `D` satisfies `q²D = Θ(1)`, including both floor and
ceiling errors. -/
theorem normalized_degeneracyBudget_bounds {q ell C A : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 ≤ A) (hsmall : 2 * q ^ 10 ≤ ell) :
    A * √(C * ell / 2) ≤
        q ^ 2 *
          (degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) : ℝ) ∧
      q ^ 2 *
          (degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) : ℝ) <
        A * √(C * ell + 1) + 1 := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  let D := degeneracyBudget q A M
  have hM := normalized_edgeBudget_bounds hq hell hC hsmall
  have hq7one : q ^ 7 ≤ 1 := pow_le_one₀ hq.le hq1
  have hq2one : q ^ 2 ≤ 1 := pow_le_one₀ hq.le hq1
  have hMupper : q ^ 7 * (M : ℝ) ≤ C * ell + 1 := by
    exact hM.2.le.trans (add_le_add_left hq7one (C * ell))
  have hsqrtLower : √(C * ell / 2) ≤ √(q ^ 7 * (M : ℝ)) :=
    Real.sqrt_le_sqrt hM.1.le
  have hsqrtUpper : √(q ^ 7 * (M : ℝ)) ≤ √(C * ell + 1) :=
    Real.sqrt_le_sqrt hMupper
  have hDlower : A * √(q ^ 3 * (M : ℝ)) ≤ (D : ℝ) :=
    degeneracyBudget_target_le q A M
  have hDupper : (D : ℝ) < A * √(q ^ 3 * (M : ℝ)) + 1 :=
    degeneracyBudget_lt_target_add_one M hA
  constructor
  · calc
      A * √(C * ell / 2) ≤ A * √(q ^ 7 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtLower hA
      _ = q ^ 2 * (A * √(q ^ 3 * (M : ℝ))) := by
        rw [← q_sq_mul_sqrt_density q (M : ℝ) hq.le]
        ring
      _ ≤ q ^ 2 * (D : ℝ) :=
        mul_le_mul_of_nonneg_left hDlower (pow_nonneg hq.le _)
  · calc
      q ^ 2 * (D : ℝ) < q ^ 2 * (A * √(q ^ 3 * (M : ℝ)) + 1) :=
        mul_lt_mul_of_pos_left hDupper (pow_pos hq _)
      _ = A * √(q ^ 7 * (M : ℝ)) + q ^ 2 := by
        rw [← q_sq_mul_sqrt_density q (M : ℝ) hq.le]
        ring
      _ ≤ A * √(C * ell + 1) + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hsqrtUpper hA) hq2one

/-- The defining ceiling for `D` gives the deterministic ratio used at the
end of the dense-set estimate. -/
theorem degeneracyBudget_ratio_bound {q A : ℝ} {M : ℕ}
    (hq : 0 < q) (hA : 0 < A) (hM : 0 < M) :
    2 * q ^ 3 * (M : ℝ) /
        (degeneracyBudget q A M : ℝ) ^ 2 ≤ 2 / A ^ 2 := by
  let x : ℝ := q ^ 3 * (M : ℝ)
  let D : ℝ := degeneracyBudget q A M
  have hx : 0 < x := mul_pos (pow_pos hq _) (Nat.cast_pos.mpr hM)
  have hD : A * √x ≤ D := by
    simpa [x, D] using degeneracyBudget_target_le q A M
  have hDpos : 0 < D := (mul_pos hA (Real.sqrt_pos.2 hx)).trans_le hD
  have hsq : A ^ 2 * x ≤ D ^ 2 := by
    calc
      A ^ 2 * x = (A * √x) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hx.le]
      _ ≤ D ^ 2 := pow_le_pow_left₀ (mul_nonneg hA.le (Real.sqrt_nonneg _)) hD 2
  apply (div_le_div_iff₀ (sq_pos_of_pos hDpos) (sq_pos_of_pos hA)).2
  dsimp [x, D] at hsq ⊢
  nlinarith

end CeilingScales

section WitnessMonomials

/-- Integral-exponent form of the small-set scale calculation
`N p^L D^(L-1) = O(q^(L-8))`, under normalized finite bounds for `N` and
`D`.  Since `p=q³`, the left side contains `q^(3L)`. -/
theorem smallSet_witness_monomial_bound
    {q n d ell K : ℝ} {L : ℕ}
    (hq : 0 ≤ q) (hn : 0 ≤ n) (hd : 0 ≤ d)
    (hK : 0 ≤ K) (hL : 8 ≤ L)
    (hNscale : q ^ 10 * n ≤ ell) (hDscale : q ^ 2 * d ≤ K) :
    n * q ^ (3 * L) * d ^ (L - 1) ≤
      ell * K ^ (L - 1) * q ^ (L - 8) := by
  have hDpow : (q ^ 2 * d) ^ (L - 1) ≤ K ^ (L - 1) :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hq _) hd) hDscale _
  have hprod :
      (q ^ 10 * n) * (q ^ 2 * d) ^ (L - 1) ≤
        ell * K ^ (L - 1) := by
    calc
      (q ^ 10 * n) * (q ^ 2 * d) ^ (L - 1) ≤
          (q ^ 10 * n) * K ^ (L - 1) :=
        mul_le_mul_of_nonneg_left hDpow (mul_nonneg (pow_nonneg hq _) hn)
      _ ≤ ell * K ^ (L - 1) :=
        mul_le_mul_of_nonneg_right hNscale (pow_nonneg hK _)
  have hcore := mul_le_mul_of_nonneg_right hprod (pow_nonneg hq (L - 8))
  have hexponent : 10 + 2 * (L - 1) + (L - 8) = 3 * L := by omega
  calc
    n * q ^ (3 * L) * d ^ (L - 1) =
        (q ^ 10 * n) * (q ^ 2 * d) ^ (L - 1) * q ^ (L - 8) := by
      rw [mul_pow, ← pow_mul]
      calc
        n * q ^ (3 * L) * d ^ (L - 1) =
            n * d ^ (L - 1) * q ^ (3 * L) := by ring
        _ = n * d ^ (L - 1) * q ^
              (10 + 2 * (L - 1) + (L - 8)) := by rw [hexponent]
        _ = (q ^ 10 * n) * (q ^ (2 * (L - 1)) * d ^ (L - 1)) *
              q ^ (L - 8) := by
                rw [pow_add, pow_add]
                ring
    _ ≤ ell * K ^ (L - 1) * q ^ (L - 8) := hcore

/-- The small-set witness monomial bound instantiated with the actual floor
and ceiling scales from this module. -/
theorem actual_smallSet_witness_monomial_bound
    {q ell C A : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 ≤ A) (hsmall : 2 * q ^ 10 ≤ ell)
    (hL : 8 ≤ L) :
    (queryBudget q ell : ℝ) * q ^ (3 * L) *
        (degeneracyBudget q A
          (edgeBudget q C (queryBudget q ell)) : ℝ) ^ (L - 1) ≤
      ell * (A * √(C * ell + 1) + 1) ^ (L - 1) * q ^ (L - 8) := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  let D := degeneracyBudget q A M
  let K := A * √(C * ell + 1) + 1
  have hNscale : q ^ 10 * (N : ℝ) ≤ ell :=
    (normalized_queryBudget_bounds hq hell).2
  have hDscale : q ^ 2 * (D : ℝ) ≤ K :=
    (normalized_degeneracyBudget_bounds hq hq1 hell hC hA hsmall).2.le
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  simpa [N, M, D, K] using
    smallSet_witness_monomial_bound
      (q := q) (n := (N : ℝ)) (d := (D : ℝ))
      (ell := ell) (K := K) (L := L)
      hq.le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hK hL hNscale hDscale

end WitnessMonomials

end AsymptoticScale
end OnlineRamsey
