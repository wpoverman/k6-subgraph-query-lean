import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import OnlineRamsey.AsymptoticScale
import OnlineRamsey.RandomBoard

/-!
# A finite probability certificate for a good random host

`RandomBoard.lean` constructs the individual codegree and spanned-edge
witnesses used in the random-host argument.  This file assembles those
witnesses into the actual four-part `HostGood` predicate.  In particular, it
checks all strict/non-strict and floor/ceiling boundaries rather than hiding
them in asymptotic notation.

The main theorem `measure_scaledRandomHostGoodEvent_compl_le` is an explicit,
finite statement at the paper's rounded scales

* `N = floor (ell / q^10)`,
* ambient host order `n = 2N`,
* `M = ceil (C q^3 N)`, and
* `D = ceil (A sqrt (q^3 M))`.

Its right-hand side is the exact finite witness sum.  Thus any desired
numerical failure target follows by proving a finite inequality for that
displayed expression; see `scaledRandomHostGood_of_witnessBound`.

The asymptotic arithmetic is also discharged with conservative concrete
constants.  In the shared recurrence-compatible form,
`exists_q0_numeric_scaledHostGood_c8` proves that for every
`0 < q < 1/10000` there is an actual graph satisfying `HostGood` at
`ell=1`, `C=8`, `A=4`, `B₂=12`, `B₃=256`, and `L=12`.

For the adaptive good/bad decomposition, the stronger theorem
`measure_numericRandomHostGoodEvent_c8_compl_toReal_le_q70` uses
`B₃=512` and `L=90` and bounds the bad-host probability by `q^70`.
After the crude labelled six-vertex factor, ten powers still remain; see
`measure_numericRandomHostGoodEvent_c8_crudeSixVertex_le`.
-/

open scoped ENNReal NNReal

open MeasureTheory Set

namespace OnlineRamsey
namespace HostGoodProbability

open RandomBoard AsymptoticScale

/-! ## Elementary binomial-coefficient estimates -/

/-- A convenient all-finite form of the standard estimate
`choose(n,k) ≤ (e*n/k)^k`.  Keeping `exp 1` rather than replacing it by a
decimal constant avoids any numerical approximation in the proof. -/
theorem choose_cast_le_exp_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (Nat.choose n k : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    calc
      (1 : ℝ) ^ 2 ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * (k : ℝ) := by
        gcongr
        exact Real.pi_gt_three.le
  have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
    calc
      ((k : ℝ) / Real.exp 1) ^ k ≤
          Real.sqrt (2 * Real.pi * (k : ℝ)) *
            ((k : ℝ) / Real.exp 1) ^ k := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ (k.factorial : ℝ) := Stirling.le_factorial_stirling k
  have hchoose := Nat.choose_le_pow_div (α := ℝ) k n
  have hfacpos : 0 < (k.factorial : ℝ) := by positivity
  have hbase : 0 ≤ (n : ℝ) ^ k := by positivity
  calc
    (Nat.choose n k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := hchoose
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / Real.exp 1) ^ k) := by
      exact div_le_div_of_nonneg_left hbase (by positivity) hfac
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
      rw [div_pow, div_pow]
      field_simp [ne_of_gt hkR, ne_of_gt (Real.exp_pos 1)]
      <;> ring

/-- The real-valued codegree witness term. -/
noncomputable def codegreeWitnessTermReal
    (x : ℝ) (n j R : ℕ) : ℝ :=
  (Nat.choose n j : ℝ) * (Nat.choose (n - j) R : ℝ) * x ^ (j * R)

/-- Applying `choose(n,k) ≤ (e n/k)^k` to the large choice in a
codegree witness gives the usual factorial-moment base. -/
theorem codegreeWitnessTermReal_le
    {x : ℝ} (hx : 0 ≤ x) (n j R : ℕ) (hR : 0 < R) :
    codegreeWitnessTermReal x n j R ≤
      (n : ℝ) ^ j *
        (Real.exp 1 * (n : ℝ) * x ^ j / (R : ℝ)) ^ R := by
  have hchooseRootNat : Nat.choose n j ≤ n ^ j := Nat.choose_le_pow n j
  have hchooseRoot : (Nat.choose n j : ℝ) ≤ (n : ℝ) ^ j := by
    exact_mod_cast hchooseRootNat
  have hchooseTips := choose_cast_le_exp_mul_div_pow (n - j) R hR
  have hnsub : ((n - j : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n j
  have hRreal : 0 < (R : ℝ) := Nat.cast_pos.mpr hR
  have hbase :
      Real.exp 1 * ((n - j : ℕ) : ℝ) / (R : ℝ) ≤
        Real.exp 1 * (n : ℝ) / (R : ℝ) := by
    gcongr
  have hchooseTips' : (Nat.choose (n - j) R : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (R : ℝ)) ^ R :=
    hchooseTips.trans (pow_le_pow_left₀ (by positivity) hbase R)
  calc
    codegreeWitnessTermReal x n j R ≤
        (n : ℝ) ^ j *
          (Real.exp 1 * (n : ℝ) / (R : ℝ)) ^ R * x ^ (j * R) := by
      unfold codegreeWitnessTermReal
      gcongr
    _ = (n : ℝ) ^ j *
        (Real.exp 1 * (n : ℝ) * x ^ j / (R : ℝ)) ^ R := by
      rw [show x ^ (j * R) = (x ^ j) ^ R by rw [pow_mul]]
      calc
        (n : ℝ) ^ j * (Real.exp 1 * (n : ℝ) / (R : ℝ)) ^ R *
            (x ^ j) ^ R =
            (n : ℝ) ^ j *
              ((Real.exp 1 * (n : ℝ) / (R : ℝ)) ^ R *
                (x ^ j) ^ R) := by ring
        _ = (n : ℝ) ^ j *
            ((Real.exp 1 * (n : ℝ) / (R : ℝ)) * x ^ j) ^ R := by
          rw [mul_pow]
        _ = (n : ℝ) ^ j *
            (Real.exp 1 * (n : ℝ) * x ^ j / (R : ℝ)) ^ R := by
          congr 2
          ring

/-- The real-valued fixed-size spanned-edge witness term. -/
noncomputable def spannedWitnessTermReal
    (x : ℝ) (n k r : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) *
    (Nat.choose (Nat.choose k 2) r : ℝ) * x ^ r

/-- The exact analytic reduction behind both dense-set and small-set union
bounds.  This is the formal version of the two standard binomial estimates
before any scale-specific simplification of the bases. -/
theorem spannedWitnessTermReal_le
    {x : ℝ} (hx : 0 ≤ x) (n k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    spannedWitnessTermReal x n k r ≤
      (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
        (Real.exp 1 * (Nat.choose k 2 : ℝ) * x / (r : ℝ)) ^ r := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have hvertices := choose_cast_le_exp_mul_div_pow n k hk
  have hedges := choose_cast_le_exp_mul_div_pow (Nat.choose k 2) r hr
  calc
    spannedWitnessTermReal x n k r ≤
        (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
          (Real.exp 1 * (Nat.choose k 2 : ℝ) / (r : ℝ)) ^ r * x ^ r := by
      unfold spannedWitnessTermReal
      gcongr
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
        (Real.exp 1 * (Nat.choose k 2 : ℝ) * x / (r : ℝ)) ^ r := by
      calc
        (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
            (Real.exp 1 * (Nat.choose k 2 : ℝ) / (r : ℝ)) ^ r * x ^ r =
            (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
              ((Real.exp 1 * (Nat.choose k 2 : ℝ) / (r : ℝ)) ^ r *
                x ^ r) := by ring
        _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
            ((Real.exp 1 * (Nat.choose k 2 : ℝ) / (r : ℝ)) * x) ^ r := by
          rw [mul_pow]
        _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
            (Real.exp 1 * (Nat.choose k 2 : ℝ) * x / (r : ℝ)) ^ r := by
          congr 2
          ring

/-- Coercing a finite `ENNReal` codegree witness term back to `ℝ` loses no
information. -/
theorem codegreeWitnessTerm_toReal (p : unitInterval) (n j R : ℕ) :
    ((Nat.choose n j * Nat.choose (n - j) R : ℝ≥0∞) *
        (unitInterval.toNNReal p : ℝ≥0∞) ^ (j * R)).toReal =
      codegreeWitnessTermReal (p : ℝ) n j R := by
  simp [codegreeWitnessTermReal]

/-- The analogous exact coercion bridge for a spanned-edge witness term. -/
theorem spannedWitnessTerm_toReal (p : unitInterval) (n k r : ℕ) :
    ((Nat.choose n k * Nat.choose (Nat.choose k 2) r : ℝ≥0∞) *
        (unitInterval.toNNReal p : ℝ≥0∞) ^ r).toReal =
      spannedWitnessTermReal (p : ℝ) n k r := by
  simp [spannedWitnessTermReal]

theorem natCast_mul_nnreal_pow_ne_top (a r : ℕ) (p : ℝ≥0) :
    (a : ℝ≥0∞) * (p : ℝ≥0∞) ^ r ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.natCast_ne_top a)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- For the dense-set threshold `r=ceil(Dk/2)`, the second binomial base is
at most `e*k*x/D`.  This includes the rounding in `ceil(Dk/2)` exactly. -/
theorem denseSpanned_factorialBase_le
    {x : ℝ} (hx : 0 ≤ x) {D k : ℕ} (hD : 0 < D) (hk : 0 < k) :
    Real.exp 1 * (Nat.choose k 2 : ℝ) * x /
        ((D * k ⌈/⌉ 2 : ℕ) : ℝ) ≤
      Real.exp 1 * (k : ℝ) * x / (D : ℝ) := by
  let r := D * k ⌈/⌉ 2
  have hDrNat : D * k ≤ 2 * r := by
    simpa [r, nsmul_eq_mul] using
      (le_smul_ceilDiv (b := D * k) (by decide : 0 < (2 : ℕ)))
  have hr : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hr0] at hDrNat
    have hprod : 0 < D * k := Nat.mul_pos hD hk
    omega
  have hDr : (D : ℝ) * (k : ℝ) / 2 ≤ (r : ℝ) := by
    have hDrCast : (D : ℝ) * (k : ℝ) ≤ 2 * (r : ℝ) := by
      exact_mod_cast hDrNat
    linarith
  have hchoose : (Nat.choose k 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    simpa [Nat.factorial] using (Nat.choose_le_pow_div (α := ℝ) 2 k)
  have hCD : (Nat.choose k 2 : ℝ) * (D : ℝ) ≤
      (k : ℝ) * (r : ℝ) := by
    calc
      (Nat.choose k 2 : ℝ) * (D : ℝ) ≤
          ((k : ℝ) ^ 2 / 2) * (D : ℝ) := by gcongr
      _ = (k : ℝ) * ((D : ℝ) * (k : ℝ) / 2) := by ring
      _ ≤ (k : ℝ) * (r : ℝ) := by gcongr
  have hrR : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  have hDR : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  change Real.exp 1 * (Nat.choose k 2 : ℝ) * x / (r : ℝ) ≤ _
  rw [div_le_div_iff₀ hrR hDR]
  have hmul := mul_le_mul_of_nonneg_left hCD
    (mul_nonneg (Real.exp_pos 1).le hx)
  nlinarith

/-- A vertex-set size in the permitted dense range converts `e*k*x/D` to
the normalized ratio `e*(2*x*M/D²)`. -/
theorem denseSpanned_rangeBase_le
    {x : ℝ} (hx : 0 ≤ x) {M D k : ℕ} (hD : 0 < D)
    (hk : k ≤ 2 * M / D) :
    Real.exp 1 * (k : ℝ) * x / (D : ℝ) ≤
      Real.exp 1 * (2 * x * (M : ℝ) / (D : ℝ) ^ 2) := by
  have hkNat : k * D ≤ 2 * M := Nat.mul_le_of_le_div D k (2 * M) hk
  have hkReal : (k : ℝ) * (D : ℝ) ≤ 2 * (M : ℝ) := by
    exact_mod_cast hkNat
  have hDR : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hratio : (k : ℝ) / (D : ℝ) ≤
      2 * (M : ℝ) / (D : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hDR (sq_pos_of_pos hDR)]
    have hmul := mul_le_mul_of_nonneg_right hkReal hDR.le
    nlinarith
  calc
    Real.exp 1 * (k : ℝ) * x / (D : ℝ) =
        (Real.exp 1 * x) * ((k : ℝ) / (D : ℝ)) := by ring
    _ ≤ (Real.exp 1 * x) *
        (2 * (M : ℝ) / (D : ℝ) ^ 2) := by gcongr
    _ = Real.exp 1 * (2 * x * (M : ℝ) / (D : ℝ) ^ 2) := by ring

/-- At the actual degeneracy ceiling, every dense-range factorial base is
at most `1/2` once `A² ≥ 4e`. -/
theorem actualDense_factorialBase_le_half
    {q A : ℝ} {M k : ℕ} (hq : 0 < q) (hA : 0 < A) (hM : 0 < M)
    (hkpos : 0 < k)
    (hk : k ≤ 2 * M / degeneracyBudget q A M)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2) :
    Real.exp 1 * (Nat.choose k 2 : ℝ) * q ^ 3 /
        ((degeneracyBudget q A M * k ⌈/⌉ 2 : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) := by
  let D := degeneracyBudget q A M
  have hx : 0 ≤ q ^ 3 := by positivity
  have htarget : 0 < A * √(q ^ 3 * (M : ℝ)) := by positivity
  have hDcast : A * √(q ^ 3 * (M : ℝ)) ≤ (D : ℝ) := by
    simpa [D] using degeneracyBudget_target_le q A M
  have hD : 0 < D := by
    exact_mod_cast htarget.trans_le hDcast
  have hfirst := denseSpanned_factorialBase_le hx hD hkpos
  have hrange := denseSpanned_rangeBase_le hx hD (by simpa [D] using hk)
  have hscale := degeneracyBudget_ratio_bound hq hA hM
  have hexpScale :
      Real.exp 1 *
          (2 * q ^ 3 * (M : ℝ) / (D : ℝ) ^ 2) ≤
        Real.exp 1 * (2 / A ^ 2) := by
    exact mul_le_mul_of_nonneg_left (by simpa [D] using hscale) (Real.exp_pos 1).le
  have hhalf : Real.exp 1 * (2 / A ^ 2) ≤ (1 / 2 : ℝ) := by
    have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
    calc
      Real.exp 1 * (2 / A ^ 2) = (2 * Real.exp 1) / A ^ 2 := by ring
      _ ≤ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ hA2]
        linarith
  exact hfirst.trans (hrange.trans (hexpScale.trans hhalf))

/-- Consequently every fixed-size dense witness has the paper's entropy
factor times an exact power of `1/2`. -/
theorem actualDenseWitnessTermReal_le
    {q A : ℝ} {n M k : ℕ} (hq : 0 < q) (hA : 0 < A) (hM : 0 < M)
    (hkpos : 0 < k)
    (hk : k ≤ 2 * M / degeneracyBudget q A M)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2) :
    spannedWitnessTermReal (q ^ 3) n k
        (degeneracyBudget q A M * k ⌈/⌉ 2) ≤
      (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
        (1 / 2 : ℝ) ^ (degeneracyBudget q A M * k ⌈/⌉ 2) := by
  let D := degeneracyBudget q A M
  let r := D * k ⌈/⌉ 2
  have htarget : 0 < A * √(q ^ 3 * (M : ℝ)) := by positivity
  have hDcast : A * √(q ^ 3 * (M : ℝ)) ≤ (D : ℝ) := by
    simpa [D] using degeneracyBudget_target_le q A M
  have hD : 0 < D := by exact_mod_cast htarget.trans_le hDcast
  have hDrNat : D * k ≤ 2 * r := by
    simpa [r, nsmul_eq_mul] using
      (le_smul_ceilDiv (b := D * k) (by decide : 0 < (2 : ℕ)))
  have hr : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hr0] at hDrNat
    have hprod : 0 < D * k := Nat.mul_pos hD hkpos
    omega
  have hbase :
      Real.exp 1 * (Nat.choose k 2 : ℝ) * q ^ 3 / (r : ℝ) ≤
        (1 / 2 : ℝ) := by
    simpa [D, r] using
      actualDense_factorialBase_le_half hq hA hM hkpos hk hAlarge
  refine (spannedWitnessTermReal_le (by positivity) n k r hkpos hr).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)

/-- A completely finite entropy-domination form.  If `2^s` dominates the
ambient entropy base and `D ≥ 4s`, then the fixed-size dense witness is at
most the geometric term `2^(-sk)`.  These two elementary inequalities are
the exact finite residue of the paper's assertion `D ≫ log n`. -/
theorem actualDenseWitnessTermReal_le_geometric
    {q A : ℝ} {n M k s : ℕ} (hq : 0 < q) (hA : 0 < A) (hM : 0 < M)
    (hkpos : 0 < k)
    (hk : k ≤ 2 * M / degeneracyBudget q A M)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hentropy : Real.exp 1 * (n : ℝ) ≤ (2 : ℝ) ^ s)
    (hlog : 4 * s ≤ degeneracyBudget q A M) :
    spannedWitnessTermReal (q ^ 3) n k
        (degeneracyBudget q A M * k ⌈/⌉ 2) ≤
      (1 / 2 : ℝ) ^ (s * k) := by
  let D := degeneracyBudget q A M
  let r := D * k ⌈/⌉ 2
  have hraw := actualDenseWitnessTermReal_le (n := n) hq hA hM hkpos hk hAlarge
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hentropyBase : Real.exp 1 * (n : ℝ) / (k : ℝ) ≤
      (2 : ℝ) ^ s :=
    (div_le_self (by positivity) hkone).trans hentropy
  have hfirst : (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k ≤
      (2 : ℝ) ^ (s * k) := by
    calc
      (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k ≤
          ((2 : ℝ) ^ s) ^ k := pow_le_pow_left₀ (by positivity) hentropyBase _
      _ = (2 : ℝ) ^ (s * k) := by rw [pow_mul]
  have hDrNat : D * k ≤ 2 * r := by
    simpa [r, nsmul_eq_mul] using
      (le_smul_ceilDiv (b := D * k) (by decide : 0 < (2 : ℕ)))
  have h4mul : 4 * s * k ≤ D * k := by
    exact Nat.mul_le_mul_right k (by simpa [D] using hlog)
  have h4mul' : 4 * (s * k) ≤ D * k := by
    simpa [Nat.mul_assoc] using h4mul
  have hexponent : 2 * (s * k) ≤ r := by omega
  have hsecond : (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ (2 * (s * k)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexponent
  calc
    spannedWitnessTermReal (q ^ 3) n k r ≤
        (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
          (1 / 2 : ℝ) ^ r := by simpa [D, r] using hraw
    _ ≤ (2 : ℝ) ^ (s * k) * (1 / 2 : ℝ) ^ (2 * (s * k)) :=
      mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = (1 / 2 : ℝ) ^ (s * k) := by
      let t := s * k
      change (2 : ℝ) ^ t * (1 / 2 : ℝ) ^ (2 * t) = (1 / 2 : ℝ) ^ t
      rw [show (1 / 2 : ℝ) ^ (2 * t) = ((1 / 2 : ℝ) ^ 2) ^ t by
        exact pow_mul (1 / 2 : ℝ) 2 t]
      rw [← mul_pow]
      norm_num

/-- Summing the preceding estimate over the entire dense range costs only
the number of possible cardinalities.  This is an explicit finite substitute
for the phrase "summing over `k`" in the paper. -/
theorem actualDenseWitnessSumReal_le
    {q A : ℝ} {n M s : ℕ} (hq : 0 < q) (hA : 0 < A) (hM : 0 < M)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hentropy : Real.exp 1 * (n : ℝ) ≤ (2 : ℝ) ^ s)
    (hlog : 4 * s ≤ degeneracyBudget q A M) :
    (∑ k ∈ Finset.Icc (degeneracyBudget q A M)
          (2 * M / degeneracyBudget q A M),
        spannedWitnessTermReal (q ^ 3) n k
          (degeneracyBudget q A M * k ⌈/⌉ 2)) ≤
      ((2 * M / degeneracyBudget q A M + 1 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ (s * degeneracyBudget q A M) := by
  let D := degeneracyBudget q A M
  let U := 2 * M / D
  have htarget : 0 < A * √(q ^ 3 * (M : ℝ)) := by positivity
  have hDcast : A * √(q ^ 3 * (M : ℝ)) ≤ (D : ℝ) := by
    simpa [D] using degeneracyBudget_target_le q A M
  have hD : 0 < D := by exact_mod_cast htarget.trans_le hDcast
  have hterm : ∀ k ∈ Finset.Icc D U,
      spannedWitnessTermReal (q ^ 3) n k (D * k ⌈/⌉ 2) ≤
        (1 / 2 : ℝ) ^ (s * D) := by
    intro k hk
    have hki := Finset.mem_Icc.mp hk
    have hkpos : 0 < k := hD.trans_le hki.1
    have hone := actualDenseWitnessTermReal_le_geometric
      (n := n) (s := s) hq hA hM hkpos
      (by simpa [D, U] using hki.2) hAlarge hentropy (by simpa [D] using hlog)
    have hexp : s * D ≤ s * k := Nat.mul_le_mul_left s hki.1
    exact hone.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp)
  calc
    (∑ k ∈ Finset.Icc D U,
        spannedWitnessTermReal (q ^ 3) n k (D * k ⌈/⌉ 2)) ≤
        ∑ _k ∈ Finset.Icc D U, (1 / 2 : ℝ) ^ (s * D) := by
      exact Finset.sum_le_sum fun k hk ↦ hterm k hk
    _ = ((Finset.Icc D U).card : ℝ) * (1 / 2 : ℝ) ^ (s * D) := by
      simp
    _ ≤ ((U + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (s * D) := by
      gcongr
      exact_mod_cast (by
        rw [Nat.card_Icc]
        exact Nat.sub_le (U + 1) D : (Finset.Icc D U).card ≤ U + 1)
    _ = ((2 * M / degeneracyBudget q A M + 1 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ (s * degeneracyBudget q A M) := by
      rfl

/-- For the small-set threshold `Lk+1`, the second binomial base is bounded
by `e*k*x/(2L)`, again with the integer rounding retained. -/
theorem smallSpanned_factorialBase_le
    {x : ℝ} (hx : 0 ≤ x) {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    Real.exp 1 * (Nat.choose k 2 : ℝ) * x / ((L * k + 1 : ℕ) : ℝ) ≤
      Real.exp 1 * (k : ℝ) * x / (2 * (L : ℝ)) := by
  have hchoose : (Nat.choose k 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    simpa [Nat.factorial] using (Nat.choose_le_pow_div (α := ℝ) 2 k)
  have hthreshold : (L : ℝ) * (k : ℝ) ≤ ((L * k + 1 : ℕ) : ℝ) := by
    norm_num
  have hcross : (Nat.choose k 2 : ℝ) * (2 * (L : ℝ)) ≤
      (k : ℝ) * ((L * k + 1 : ℕ) : ℝ) := by
    calc
      (Nat.choose k 2 : ℝ) * (2 * (L : ℝ)) ≤
          ((k : ℝ) ^ 2 / 2) * (2 * (L : ℝ)) := by gcongr
      _ = (k : ℝ) * ((L : ℝ) * (k : ℝ)) := by ring
      _ ≤ (k : ℝ) * ((L * k + 1 : ℕ) : ℝ) := by gcongr
  have hden1 : 0 < ((L * k + 1 : ℕ) : ℝ) := by positivity
  have hden2 : 0 < 2 * (L : ℝ) := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  have hmul := mul_le_mul_of_nonneg_left hcross
    (mul_nonneg (Real.exp_pos 1).le hx)
  nlinarith

/-- The corresponding fixed-size small-set witness estimate. -/
theorem smallWitnessTermReal_le
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) {L k : ℕ}
    (hL : 0 < L) (hk : 0 < k) :
    spannedWitnessTermReal x n k (L * k + 1) ≤
      (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k *
        (Real.exp 1 * (k : ℝ) * x / (2 * (L : ℝ))) ^ (L * k + 1) := by
  refine (spannedWitnessTermReal_le hx n k (L * k + 1) hk (by omega)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity)
      (smallSpanned_factorialBase_le hx hL hk) _) (by positivity)

/-- The geometric base controlling the whole small-set range.  Its `D^(L-1)`
factor is the sharp cancellation responsible for the exponent `L-8` in the
paper. -/
noncomputable def smallSetGeometricBase
    (x : ℝ) (n D L : ℕ) : ℝ :=
  Real.exp 1 * (n : ℝ) *
    (Real.exp 1 * x / (2 * (L : ℝ))) ^ L * (D : ℝ) ^ (L - 1)

/-- Every positive cardinality in the small-set range is bounded by the
corresponding power of `smallSetGeometricBase`, provided the elementary local
base is at most one. -/
theorem smallWitnessTermReal_le_geometricBase
    {x : ℝ} (hx : 0 ≤ x) (n D : ℕ) {L k : ℕ}
    (hL : 0 < L) (hk : 0 < k) (hkD : k ≤ D)
    (hlocal : Real.exp 1 * (D : ℝ) * x / (2 * (L : ℝ)) ≤ 1) :
    spannedWitnessTermReal x n k (L * k + 1) ≤
      (smallSetGeometricBase x n D L) ^ k := by
  let a := Real.exp 1 * (n : ℝ) / (k : ℝ)
  let b := Real.exp 1 * (k : ℝ) * x / (2 * (L : ℝ))
  have hraw := smallWitnessTermReal_le hx n hL hk
  have hkDreal : (k : ℝ) ≤ (D : ℝ) := by exact_mod_cast hkD
  have hbnonneg : 0 ≤ b := by dsimp [b]; positivity
  have hbunit : b ≤ 1 := by
    exact (show b ≤ Real.exp 1 * (D : ℝ) * x / (2 * (L : ℝ)) by
      dsimp [b]
      gcongr).trans hlocal
  have hdrop : b ^ (L * k + 1) ≤ b ^ (L * k) :=
    pow_le_pow_of_le_one hbnonneg hbunit (Nat.le_succ _)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hkpow : (k : ℝ) ^ (L - 1) ≤ (D : ℝ) ^ (L - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hkDreal _
  have hbaseIdentity :
      a * b ^ L = Real.exp 1 * (n : ℝ) *
        (Real.exp 1 * x / (2 * (L : ℝ))) ^ L * (k : ℝ) ^ (L - 1) := by
    dsimp [a, b]
    rw [show Real.exp 1 * (k : ℝ) * x / (2 * (L : ℝ)) =
        (Real.exp 1 * x / (2 * (L : ℝ))) * (k : ℝ) by ring]
    rw [mul_pow, ← mul_pow_sub_one hL.ne' (k : ℝ)]
    field_simp [ne_of_gt hkR]
  have hbase : a * b ^ L ≤ smallSetGeometricBase x n D L := by
    rw [hbaseIdentity]
    unfold smallSetGeometricBase
    gcongr
  calc
    spannedWitnessTermReal x n k (L * k + 1) ≤
        a ^ k * b ^ (L * k + 1) := by simpa [a, b] using hraw
    _ ≤ a ^ k * b ^ (L * k) := mul_le_mul_of_nonneg_left hdrop (by positivity)
    _ = (a * b ^ L) ^ k := by
      rw [show b ^ (L * k) = (b ^ L) ^ k by exact pow_mul b L k]
      rw [mul_pow]
    _ ≤ (smallSetGeometricBase x n D L) ^ k :=
      pow_le_pow_left₀ (mul_nonneg (by positivity) (pow_nonneg hbnonneg _)) hbase _

/-- Finite summed small-set estimate.  Once the displayed geometric base is
at most `ρ≤1`, all `D+1` possible cardinalities together cost at most
`(D+1)ρ`.  The `k=0` term is checked to vanish exactly. -/
theorem smallWitnessSumReal_le
    {x ρ : ℝ} (hx : 0 ≤ x) (n D : ℕ) {L : ℕ}
    (hL : 0 < L) (hlocal : Real.exp 1 * (D : ℝ) * x /
      (2 * (L : ℝ)) ≤ 1)
    (hgeom : smallSetGeometricBase x n D L ≤ ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∑ k ∈ Finset.Icc 0 D,
        spannedWitnessTermReal x n k (L * k + 1)) ≤
      ((D + 1 : ℕ) : ℝ) * ρ := by
  have hterm : ∀ k ∈ Finset.Icc 0 D,
      spannedWitnessTermReal x n k (L * k + 1) ≤ ρ := by
    intro k hkIcc
    obtain rfl | hkpos := k.eq_zero_or_pos
    · simpa [spannedWitnessTermReal] using hρ0
    · have hkD := (Finset.mem_Icc.mp hkIcc).2
      have hpow := smallWitnessTermReal_le_geometricBase
        hx n D hL hkpos hkD hlocal
      have hpow' : (smallSetGeometricBase x n D L) ^ k ≤ ρ ^ k :=
        pow_le_pow_left₀ (by
          unfold smallSetGeometricBase
          positivity) hgeom _
      exact hpow.trans (hpow'.trans
        (by simpa using pow_le_pow_of_le_one hρ0 hρ1 (Nat.one_le_iff_ne_zero.mpr hkpos.ne')))
  calc
    (∑ k ∈ Finset.Icc 0 D,
        spannedWitnessTermReal x n k (L * k + 1)) ≤
        ∑ _k ∈ Finset.Icc 0 D, ρ :=
      Finset.sum_le_sum fun k hk ↦ hterm k hk
    _ = ((D + 1 : ℕ) : ℝ) * ρ := by
      simp [Nat.card_Icc]

/-- The explicit power-law majorant for the small-set geometric base at the
paper's rounded scales. -/
noncomputable def actualSmallSetPowerBound
    (q ell C A : ℝ) (L : ℕ) : ℝ :=
  (2 * Real.exp 1 * (Real.exp 1 / (2 * (L : ℝ))) ^ L) *
    (ell * (A * √(C * ell + 1) + 1) ^ (L - 1) * q ^ (L - 8))

/-- At the paper's rounded scales, the small-set geometric base is bounded
by an explicit constant times `q^(L-8)`.  This is the finite, rounded version
of the scale calculation responsible for the restriction `L>8`. -/
theorem actual_smallSetGeometricBase_bound
    {q ell C A : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 ≤ A) (hsmall : 2 * q ^ 10 ≤ ell)
    (hL : 8 ≤ L) :
    smallSetGeometricBase (q ^ 3) (2 * queryBudget q ell)
        (degeneracyBudget q A (edgeBudget q C (queryBudget q ell))) L ≤
      actualSmallSetPowerBound q ell C A L := by
  let N := queryBudget q ell
  let D := degeneracyBudget q A (edgeBudget q C N)
  have hmono := actual_smallSet_witness_monomial_bound
    (q := q) (ell := ell) (C := C) (A := A) (L := L)
    hq hq1 hell hC hA hsmall hL
  have hfactor :
      0 ≤ 2 * Real.exp 1 * (Real.exp 1 / (2 * (L : ℝ))) ^ L := by
    positivity
  have hid :
      smallSetGeometricBase (q ^ 3) (2 * N) D L =
        (2 * Real.exp 1 * (Real.exp 1 / (2 * (L : ℝ))) ^ L) *
          ((N : ℝ) * q ^ (3 * L) * (D : ℝ) ^ (L - 1)) := by
    unfold smallSetGeometricBase
    push_cast
    simp only [div_pow, mul_pow, ← pow_mul]
    ring
  change smallSetGeometricBase (q ^ 3) (2 * N) D L ≤ _
  unfold actualSmallSetPowerBound
  rw [hid]
  exact mul_le_mul_of_nonneg_left (by simpa [N, D] using hmono) hfactor

/-- The local small-set factorial base is at most one once the displayed
linear cutoff in `q` holds.  The ceiling error in `D` is included in the
constant `A*sqrt(C*ell+1)+1`. -/
theorem actual_smallSetLocalBase_le
    {q ell C A : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 ≤ A) (hsmall : 2 * q ^ 10 ≤ ell)
    (hL : 0 < L)
    (hcut : Real.exp 1 * (A * √(C * ell + 1) + 1) * q ≤
      2 * (L : ℝ)) :
    Real.exp 1 *
        (degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) : ℝ) *
        q ^ 3 / (2 * (L : ℝ)) ≤ 1 := by
  let D := degeneracyBudget q A (edgeBudget q C (queryBudget q ell))
  let K := A * √(C * ell + 1) + 1
  have hDscale : q ^ 2 * (D : ℝ) ≤ K :=
    (normalized_degeneracyBudget_bounds hq hq1 hell hC hA hsmall).2.le
  have hmul := mul_le_mul_of_nonneg_left hDscale
    (mul_nonneg (Real.exp_pos 1).le hq.le)
  have hnum : Real.exp 1 * (D : ℝ) * q ^ 3 ≤ 2 * (L : ℝ) := by
    calc
      Real.exp 1 * (D : ℝ) * q ^ 3 =
          (Real.exp 1 * q) * (q ^ 2 * (D : ℝ)) := by ring
      _ ≤ (Real.exp 1 * q) * K := hmul
      _ = Real.exp 1 * K * q := by ring
      _ ≤ 2 * (L : ℝ) := by simpa [K] using hcut
  apply (div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))).2
  simpa [D] using hnum

/-- After multiplying by the number of permitted small-set sizes, the
rounded small-set error has an explicit `q^(L-10)` majorant. -/
noncomputable def actualSmallSetErrorPowerBound
    (q ell C A : ℝ) (L : ℕ) : ℝ :=
  let K := A * √(C * ell + 1) + 1
  (K + 1) * (2 * Real.exp 1 * (Real.exp 1 / (2 * (L : ℝ))) ^ L) *
    ell * K ^ (L - 1) * q ^ (L - 10)

/-- The complete small-set contribution is bounded by
`actualSmallSetErrorPowerBound`; hence it tends polynomially to zero as soon
as `L>10`. -/
theorem actual_smallSetErrorPowerBound
    {q ell C A : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 ≤ A) (hscale : 2 * q ^ 10 ≤ ell)
    (hL : 10 ≤ L) :
    ((degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) + 1 : ℕ) : ℝ) *
        actualSmallSetPowerBound q ell C A L ≤
      actualSmallSetErrorPowerBound q ell C A L := by
  let D := degeneracyBudget q A (edgeBudget q C (queryBudget q ell))
  let K := A * √(C * ell + 1) + 1
  let F := 2 * Real.exp 1 * (Real.exp 1 / (2 * (L : ℝ))) ^ L
  have hq2 : 0 < q ^ 2 := pow_pos hq _
  have hq2one : q ^ 2 ≤ 1 := pow_le_one₀ hq.le hq1
  have hDscale : q ^ 2 * (D : ℝ) ≤ K := by
    simpa [D, K] using
      (normalized_degeneracyBudget_bounds hq hq1 hell hC hA hscale).2.le
  have hscaled : q ^ 2 * ((D + 1 : ℕ) : ℝ) ≤ K + 1 := by
    calc
      q ^ 2 * ((D + 1 : ℕ) : ℝ) = q ^ 2 * (D : ℝ) + q ^ 2 := by
        push_cast
        ring
      _ ≤ K + 1 := add_le_add hDscale hq2one
  have hDplus : ((D + 1 : ℕ) : ℝ) ≤ (K + 1) / q ^ 2 := by
    exact (le_div_iff₀ hq2).2 (by simpa [mul_comm] using hscaled)
  have hpower0 : 0 ≤ actualSmallSetPowerBound q ell C A L := by
    unfold actualSmallSetPowerBound
    positivity
  calc
    ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L ≤
        ((K + 1) / q ^ 2) * actualSmallSetPowerBound q ell C A L := by
      exact mul_le_mul_of_nonneg_right hDplus hpower0
    _ = actualSmallSetErrorPowerBound q ell C A L := by
      unfold actualSmallSetPowerBound actualSmallSetErrorPowerBound
      dsimp [K, F]
      rw [show L - 8 = (L - 10) + 2 by omega, pow_add]
      field_simp [ne_of_gt hq2]

/-- A concrete entropy exponent.  Taking twenty times `ceil(1/q)` is a
deliberately generous elementary substitute for choosing a logarithm of the
ambient vertex count. -/
noncomputable def entropyIndex (q : ℝ) : ℕ :=
  ⌈1 / q⌉₊ * 20

/-- The concrete entropy exponent is at most `40/q` for `0<q≤1`. -/
theorem entropyIndex_cast_le
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (entropyIndex q : ℝ) ≤ 40 / q := by
  let m : ℕ := ⌈1 / q⌉₊
  have hm_lt : (m : ℝ) < 1 / q + 1 := by
    simpa [m] using Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / q)
  have hrecip : 1 / q + 1 ≤ 2 / q := by
    rw [le_div_iff₀ hq]
    field_simp [ne_of_gt hq]
    linarith
  calc
    (entropyIndex q : ℝ) = 20 * (m : ℝ) := by
      simp [entropyIndex, m]
      ring
    _ ≤ 20 * (2 / q) := by gcongr; exact hm_lt.le.trans hrecip
    _ = 40 / q := by ring

/-- The entropy factor in the dense-set union bound is absorbed by
`2^entropyIndex(q)` under a single polynomial smallness inequality. -/
theorem actual_entropyCondition
    {q ell : ℝ} (hq : 0 < q) (hell : 0 ≤ ell)
    (hsmall : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1) :
    Real.exp 1 * ((2 * queryBudget q ell : ℕ) : ℝ) ≤
      (2 : ℝ) ^ entropyIndex q := by
  let m : ℕ := ⌈1 / q⌉₊
  have hq10 : 0 < q ^ 10 := pow_pos hq _
  have hq20 : 0 < q ^ 20 := pow_pos hq _
  have hN := queryBudget_cast_le_target hq hell
  have hfirst :
      Real.exp 1 * ((2 * queryBudget q ell : ℕ) : ℝ) ≤
        1 / q ^ 20 := by
    calc
      Real.exp 1 * ((2 * queryBudget q ell : ℕ) : ℝ) =
          2 * Real.exp 1 * (queryBudget q ell : ℝ) := by
            push_cast
            ring
      _ ≤ 2 * Real.exp 1 * (ell / q ^ 10) := by gcongr
      _ = (2 * Real.exp 1 * ell * q ^ 10) / q ^ 20 := by
        field_simp [ne_of_gt hq10, ne_of_gt hq20]
      _ ≤ 1 / q ^ 20 := by
        exact div_le_div_of_nonneg_right hsmall hq20.le
  have hm : 1 / q ≤ (m : ℝ) := by
    simpa [m] using (Nat.le_ceil (1 / q))
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hpowm : 1 / q ^ 20 ≤ (m : ℝ) ^ 20 := by
    rw [← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hm 20
  have hmtwoNat : m ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
  have hmtwo : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast hmtwoNat
  have hpowtwo : (m : ℝ) ^ 20 ≤ (2 : ℝ) ^ (m * 20) := by
    calc
      (m : ℝ) ^ 20 ≤ ((2 : ℝ) ^ m) ^ 20 :=
        pow_le_pow_left₀ hm0 hmtwo 20
      _ = (2 : ℝ) ^ (m * 20) := by rw [pow_mul]
  simpa [entropyIndex, m] using hfirst.trans (hpowm.trans hpowtwo)

/-- The same concrete entropy exponent fits below `D/4` under a linear
smallness condition.  Thus the dense-set sum no longer needs a logarithmic
side condition. -/
theorem actual_entropyIndex_le_degeneracyBudget
    {q ell C A : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hell : 0 ≤ ell) (hC : 0 < C) (hA : 0 ≤ A)
    (hsmall : 2 * q ^ 10 ≤ ell)
    (hcut : 160 * q ≤ A * √(C * ell / 2)) :
    4 * entropyIndex q ≤
      degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) := by
  let m : ℕ := ⌈1 / q⌉₊
  let D := degeneracyBudget q A (edgeBudget q C (queryBudget q ell))
  have hm_lt : (m : ℝ) < 1 / q + 1 := by
    simpa [m] using Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / q)
  have hrecip : 1 / q + 1 ≤ 2 / q := by
    rw [le_div_iff₀ hq]
    field_simp [ne_of_gt hq]
    linarith
  have hm : (m : ℝ) ≤ 2 / q := hm_lt.le.trans hrecip
  have hDlower : A * √(C * ell / 2) ≤ q ^ 2 * (D : ℝ) := by
    simpa [D] using
      (normalized_degeneracyBudget_bounds hq hq1 hell hC hA hsmall).1
  have hscale : 160 / q ≤ (D : ℝ) := by
    have hqd : 160 * q ≤ q ^ 2 * (D : ℝ) := hcut.trans hDlower
    rw [div_le_iff₀ hq]
    have hcancel := (mul_le_mul_iff_right₀ hq).mp
      (show q * (160 : ℝ) ≤ q * (q * (D : ℝ)) by
        simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hqd)
    simpa [mul_comm] using hcancel
  have hs : ((4 * entropyIndex q : ℕ) : ℝ) ≤ (D : ℝ) := by
    calc
      ((4 * entropyIndex q : ℕ) : ℝ) = 80 * (m : ℝ) := by
        simp [entropyIndex, m]
        ring
      _ ≤ 80 * (2 / q) := by gcongr
      _ = 160 / q := by ring
      _ ≤ (D : ℝ) := hscale
  exact_mod_cast hs

/-! ## The four bad witness events -/

/-- A failure of the dense-set certificate, written as a finite union over
the exact permitted cardinality range. -/
def denseSetFailureEvent (n M D : ℕ) : Set (Sym2 (Fin n) → Bool) :=
  spannedEdgeAtLeastInSizesEvent n
    (Finset.Icc D (2 * M / D)) (fun k ↦ D * k ⌈/⌉ 2)

/-- A failure of the small-set certificate.  The threshold is `L*k+1`
because `SmallSetCertificate` itself has the non-strict bound `e(U) ≤ L|U|`.
-/
def smallSetFailureEvent (n D L : ℕ) : Set (Sym2 (Fin n) → Bool) :=
  spannedEdgeAtLeastInSizesEvent n
    (Finset.Icc 0 D) (fun k ↦ L * k + 1)

/-- The union of all four witness families which can obstruct `HostGood`.
For codegrees, failure of an upper bound `B` starts at `B+1`.-/
def hostWitnessFailureEvent
    (n M D L pairBound tripleBound : ℕ) : Set (Sym2 (Fin n) → Bool) :=
  codegreeAtLeastEvent n 2 (pairBound + 1) ∪
  codegreeAtLeastEvent n 3 (tripleBound + 1) ∪
  denseSetFailureEvent n M D ∪
  smallSetFailureEvent n D L

/-- The exact finite union-bound expression associated with
`hostWitnessFailureEvent`. -/
noncomputable def hostWitnessBound (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ) : ℝ≥0∞ :=
  (Nat.choose n 2 * Nat.choose (n - 2) (pairBound + 1) : ℝ≥0∞) *
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (2 * (pairBound + 1)) +
  (Nat.choose n 3 * Nat.choose (n - 3) (tripleBound + 1) : ℝ≥0∞) *
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (3 * (tripleBound + 1)) +
  ∑ k ∈ Finset.Icc D (2 * M / D),
    (Nat.choose n k * Nat.choose (Nat.choose k 2) (D * k ⌈/⌉ 2) : ℝ≥0∞) *
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (D * k ⌈/⌉ 2) +
  ∑ k ∈ Finset.Icc 0 D,
    (Nat.choose n k * Nat.choose (Nat.choose k 2) (L * k + 1) : ℝ≥0∞) *
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (L * k + 1)

/-- The exact real form of `hostWitnessBound`.  All summands are finite, so
`ENNReal.toReal` distributes through the four components without loss. -/
theorem hostWitnessBound_toReal (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ) :
    (hostWitnessBound p n M D L pairBound tripleBound).toReal =
      codegreeWitnessTermReal (p : ℝ) n 2 (pairBound + 1) +
      codegreeWitnessTermReal (p : ℝ) n 3 (tripleBound + 1) +
      ∑ k ∈ Finset.Icc D (2 * M / D),
        spannedWitnessTermReal (p : ℝ) n k (D * k ⌈/⌉ 2) +
      ∑ k ∈ Finset.Icc 0 D,
        spannedWitnessTermReal (p : ℝ) n k (L * k + 1) := by
  let pNN := unitInterval.toNNReal p
  have hterm : ∀ a b r : ℕ,
      (a : ℝ≥0∞) * (b : ℝ≥0∞) * (pNN : ℝ≥0∞) ^ r ≠ ⊤ :=
    fun a b r ↦ ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top a) (ENNReal.natCast_ne_top b))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hDterms : ∀ k ∈ Finset.Icc D (2 * M / D),
      (Nat.choose n k * Nat.choose (Nat.choose k 2) (D * k ⌈/⌉ 2) : ℝ≥0∞) *
        (pNN : ℝ≥0∞) ^ (D * k ⌈/⌉ 2) ≠ ⊤ :=
    fun k _ ↦ hterm _ _ _
  have hSterms : ∀ k ∈ Finset.Icc 0 D,
      (Nat.choose n k * Nat.choose (Nat.choose k 2) (L * k + 1) : ℝ≥0∞) *
        (pNN : ℝ≥0∞) ^ (L * k + 1) ≠ ⊤ :=
    fun k _ ↦ hterm _ _ _
  have hDsum : (∑ k ∈ Finset.Icc D (2 * M / D),
      (Nat.choose n k * Nat.choose (Nat.choose k 2) (D * k ⌈/⌉ 2) : ℝ≥0∞) *
        (pNN : ℝ≥0∞) ^ (D * k ⌈/⌉ 2)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hDterms
  have hSsum : (∑ k ∈ Finset.Icc 0 D,
      (Nat.choose n k * Nat.choose (Nat.choose k 2) (L * k + 1) : ℝ≥0∞) *
        (pNN : ℝ≥0∞) ^ (L * k + 1)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hSterms
  unfold hostWitnessBound
  rw [ENNReal.toReal_add (by
      exact ENNReal.add_ne_top.mpr ⟨
        ENNReal.add_ne_top.mpr ⟨hterm _ _ _, hterm _ _ _⟩, hDsum⟩) hSsum]
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hterm _ _ _, hterm _ _ _⟩) hDsum]
  rw [ENNReal.toReal_add (hterm _ _ _) (hterm _ _ _)]
  rw [ENNReal.toReal_sum hDterms, ENNReal.toReal_sum hSterms]
  simp [pNN, codegreeWitnessTermReal, spannedWitnessTermReal]

theorem hostWitnessBound_ne_top (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ) :
    hostWitnessBound p n M D L pairBound tripleBound ≠ ⊤ := by
  let pNN := unitInterval.toNNReal p
  have ht : ∀ a b r : ℕ,
      (a : ℝ≥0∞) * (b : ℝ≥0∞) * (pNN : ℝ≥0∞) ^ r ≠ ⊤ :=
    fun a b r ↦ ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top a) (ENNReal.natCast_ne_top b))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hD : (∑ k ∈ Finset.Icc D (2 * M / D),
      (Nat.choose n k * Nat.choose (Nat.choose k 2) (D * k ⌈/⌉ 2) : ℝ≥0∞) *
        (pNN : ℝ≥0∞) ^ (D * k ⌈/⌉ 2)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ ↦ ht _ _ _
  have hS : (∑ k ∈ Finset.Icc 0 D,
      (Nat.choose n k * Nat.choose (Nat.choose k 2) (L * k + 1) : ℝ≥0∞) *
        (pNN : ℝ≥0∞) ^ (L * k + 1)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ ↦ ht _ _ _
  unfold hostWitnessBound
  exact ENNReal.add_ne_top.mpr ⟨
    ENNReal.add_ne_top.mpr ⟨
      ENNReal.add_ne_top.mpr ⟨ht _ _ _, ht _ _ _⟩, hD⟩, hS⟩

/-! ## Deterministic soundness of the witness certificate -/

/-- If none of the four finite witness events occurs, the extracted graph
satisfies the four components of `HostGood` with exactly the stated bounds.
-/
theorem hostGood_of_not_mem_hostWitnessFailureEvent
    {n M D L pairBound tripleBound : ℕ} {w : Sym2 (Fin n) → Bool}
    (hw : w ∉ hostWitnessFailureEvent n M D L pairBound tripleBound) :
    HostGood (randomHost n w) M D L pairBound tripleBound := by
  have hpair : w ∉ codegreeAtLeastEvent n 2 (pairBound + 1) := by
    intro h
    exact hw (by simp [hostWitnessFailureEvent, h])
  have htriple : w ∉ codegreeAtLeastEvent n 3 (tripleBound + 1) := by
    intro h
    exact hw (by simp [hostWitnessFailureEvent, h])
  have hdense : w ∉ denseSetFailureEvent n M D := by
    intro h
    exact hw (by simp [hostWitnessFailureEvent, h])
  have hsmall : w ∉ smallSetFailureEvent n D L := by
    intro h
    exact hw (by simp [hostWitnessFailureEvent, h])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hScard
    by_contra hbad
    apply hpair
    refine ⟨S, hScard, ?_⟩
    omega
  · intro S hScard
    by_contra hbad
    apply htriple
    refine ⟨S, hScard, ?_⟩
    omega
  · intro U hlo hhi
    by_contra hbad
    apply hdense
    change w ∈ ⋃ k ∈ Finset.Icc D (2 * M / D),
      spannedEdgeAtLeastEvent n k (D * k ⌈/⌉ 2)
    refine Set.mem_iUnion.mpr ⟨U.card, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, ?_⟩
    refine ⟨U, rfl, ?_⟩
    rw [ceilDiv_le_iff_le_mul (by decide : 0 < (2 : ℕ))]
    exact Nat.le_of_not_gt hbad
  · intro U hU
    by_contra hbad
    apply hsmall
    change w ∈ ⋃ k ∈ Finset.Icc 0 D,
      spannedEdgeAtLeastEvent n k (L * k + 1)
    refine Set.mem_iUnion.mpr ⟨U.card, ?_⟩
    refine Set.mem_iUnion.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hU⟩, ?_⟩
    refine ⟨U, rfl, ?_⟩
    omega

/-- Equivalently, every board outside `HostGood` belongs to one of the
explicit witness families. -/
theorem randomHostGoodEvent_compl_subset_hostWitnessFailureEvent
    (n M D L pairBound tripleBound : ℕ) :
    (randomHostGoodEvent n M D L pairBound tripleBound)ᶜ ⊆
      hostWitnessFailureEvent n M D L pairBound tripleBound := by
  intro w hw
  by_contra hnot
  exact hw (hostGood_of_not_mem_hostWitnessFailureEvent hnot)

/-! ## Exact finite probability bound -/

theorem measure_denseSetFailureEvent_le (n M D : ℕ) (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p (denseSetFailureEvent n M D) ≤
      ∑ k ∈ Finset.Icc D (2 * M / D),
        (Nat.choose n k * Nat.choose (Nat.choose k 2) (D * k ⌈/⌉ 2) : ℝ≥0∞) *
          (unitInterval.toNNReal p : ℝ≥0∞) ^ (D * k ⌈/⌉ 2) := by
  exact measure_spannedEdgeAtLeastInSizesEvent_le n
    (Finset.Icc D (2 * M / D)) (fun k ↦ D * k ⌈/⌉ 2) p

theorem measure_smallSetFailureEvent_le (n D L : ℕ) (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p (smallSetFailureEvent n D L) ≤
      ∑ k ∈ Finset.Icc 0 D,
        (Nat.choose n k * Nat.choose (Nat.choose k 2) (L * k + 1) : ℝ≥0∞) *
          (unitInterval.toNNReal p : ℝ≥0∞) ^ (L * k + 1) := by
  exact measure_spannedEdgeAtLeastInSizesEvent_le n
    (Finset.Icc 0 D) (fun k ↦ L * k + 1) p

/-- The mass of the four-way witness union is bounded by the exact finite
witness sum. -/
theorem measure_hostWitnessFailureEvent_le (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (hostWitnessFailureEvent n M D L pairBound tripleBound) ≤
      hostWitnessBound p n M D L pairBound tripleBound := by
  let μ := bitBoardMeasure (Sym2 (Fin n)) p
  let E2 := codegreeAtLeastEvent n 2 (pairBound + 1)
  let E3 := codegreeAtLeastEvent n 3 (tripleBound + 1)
  let ED := denseSetFailureEvent n M D
  let ES := smallSetFailureEvent n D L
  have h2 := measure_codegreeAtLeastEvent_le n 2 (pairBound + 1) p
  have h3 := measure_codegreeAtLeastEvent_le n 3 (tripleBound + 1) p
  have hD := measure_denseSetFailureEvent_le n M D p
  have hS := measure_smallSetFailureEvent_le n D L p
  calc
    μ (hostWitnessFailureEvent n M D L pairBound tripleBound) =
        μ ((E2 ∪ E3) ∪ ED ∪ ES) := by rfl
    _ ≤ (μ E2 + μ E3) + μ ED + μ ES := by
      calc
        μ ((E2 ∪ E3) ∪ ED ∪ ES) ≤
            μ ((E2 ∪ E3) ∪ ED) + μ ES := measure_union_le _ _
        _ ≤ (μ (E2 ∪ E3) + μ ED) + μ ES :=
          add_le_add_right (measure_union_le _ _) _
        _ ≤ (μ E2 + μ E3) + μ ED + μ ES :=
          add_le_add_right (add_le_add_right (measure_union_le _ _) _) _
    _ ≤ hostWitnessBound p n M D L pairBound tripleBound := by
      dsimp [μ, E2, E3, ED, ES, hostWitnessBound] at *
      exact add_le_add (add_le_add (add_le_add h2 h3) hD) hS

/-- A finite, non-asymptotic high-probability version of the uniform-host
event: its complement has mass at most the displayed witness sum. -/
theorem measure_randomHostGoodEvent_compl_le (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (randomHostGoodEvent n M D L pairBound tripleBound)ᶜ ≤
      hostWitnessBound p n M D L pairBound tripleBound := by
  exact (measure_mono
    (randomHostGoodEvent_compl_subset_hostWitnessFailureEvent
      n M D L pairBound tripleBound)).trans
    (measure_hostWitnessFailureEvent_le p n M D L pairBound tripleBound)

/-- Real-valued form of `measure_randomHostGoodEvent_compl_le`.  The
right-hand side is finite because it is a finite sum of finite witness
weights, so applying `ENNReal.toReal` loses no information. -/
theorem measure_randomHostGoodEvent_compl_toReal_le (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ) :
    (bitBoardMeasure (Sym2 (Fin n)) p
        (randomHostGoodEvent n M D L pairBound tripleBound)ᶜ).toReal ≤
      (hostWitnessBound p n M D L pairBound tripleBound).toReal := by
  exact ENNReal.toReal_mono
    (hostWitnessBound_ne_top p n M D L pairBound tripleBound)
    (measure_randomHostGoodEvent_compl_le
      p n M D L pairBound tripleBound)

/-- A complement of real mass strictly below one leaves at least one board
whose extracted graph satisfies `HostGood`. -/
theorem exists_hostGood_of_compl_toReal_lt_one (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ)
    (hfail : (bitBoardMeasure (Sym2 (Fin n)) p
      (randomHostGoodEvent n M D L pairBound tripleBound)ᶜ).toReal < 1) :
    ∃ w : Sym2 (Fin n) → Bool,
      HostGood (randomHost n w) M D L pairBound tripleBound := by
  by_contra hnone
  push_neg at hnone
  have hevent : randomHostGoodEvent n M D L pairBound tripleBound = ∅ := by
    ext w
    simp only [randomHostGoodEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    exact hnone w
  have hmass : bitBoardMeasure (Sym2 (Fin n)) p
      (randomHostGoodEvent n M D L pairBound tripleBound)ᶜ = 1 := by
    rw [hevent]
    simp
  rw [hmass] at hfail
  norm_num at hfail

/-- If the explicit finite witness expression is below a target `δ`, the
actual random host is good except on a set of mass at most `δ`.  This is a
pure finite-arithmetic interface: it assumes no asymptotic or probability
postulate. -/
theorem randomHostGood_of_witnessBound (p : unitInterval)
    (n M D L pairBound tripleBound : ℕ) (δ : ℝ≥0∞)
    (hbound : hostWitnessBound p n M D L pairBound tripleBound ≤ δ) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (randomHostGoodEvent n M D L pairBound tripleBound)ᶜ ≤ δ :=
  (measure_randomHostGoodEvent_compl_le p n M D L pairBound tripleBound).trans hbound

/-! ## Instantiation at the paper's rounded `q`-scales -/

/-- The probability `p=q³`, as an element of the unit interval. -/
def cubeProbability (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : unitInterval :=
  ⟨q ^ 3, pow_nonneg hq0 3, pow_le_one₀ hq0 hq1⟩

@[simp]
theorem cubeProbability_coe (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((cubeProbability q hq0 hq1 : unitInterval) : ℝ) = q ^ 3 :=
  rfl

/-- The natural pair-codegree cutoff `ceil(B₂ q⁶N)`. -/
noncomputable def scaledPairBound (q B₂ : ℝ) (N : ℕ) : ℕ :=
  ⌈B₂ * q ^ 6 * (N : ℝ)⌉₊

/-- The natural triple-codegree cutoff `ceil(B₃ q⁹N)`. -/
noncomputable def scaledTripleBound (q B₃ : ℝ) (N : ℕ) : ℕ :=
  ⌈B₃ * q ^ 9 * (N : ℝ)⌉₊

/-- A polynomial sufficient condition for the rounded pair-codegree cutoff
to clear twice the entropy exponent by four bits. -/
theorem actual_pairExponent_condition
    {q ell B₂ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hell : 0 ≤ ell) (hB₂ : 0 < B₂)
    (hcut : 80 * q ^ 3 + 3 * q ^ 4 ≤ B₂ * (ell - q ^ 10)) :
    2 * entropyIndex q + 4 ≤
      scaledPairBound q B₂ (queryBudget q ell) + 1 := by
  let N := queryBudget q ell
  let s := entropyIndex q
  have hs : (s : ℝ) ≤ 40 / q := by
    simpa [s] using entropyIndex_cast_le hq hq1
  have hq4 : 0 < q ^ 4 := pow_pos hq _
  have hleft : ((2 * s + 3 : ℕ) : ℝ) ≤
      (80 * q ^ 3 + 3 * q ^ 4) / q ^ 4 := by
    calc
      ((2 * s + 3 : ℕ) : ℝ) = 2 * (s : ℝ) + 3 := by norm_num
      _ ≤ 2 * (40 / q) + 3 := by gcongr
      _ = (80 * q ^ 3 + 3 * q ^ 4) / q ^ 4 := by
        field_simp [ne_of_gt hq, ne_of_gt hq4]
        ring
  have hcut' : (80 * q ^ 3 + 3 * q ^ 4) / q ^ 4 ≤
      B₂ * (ell - q ^ 10) / q ^ 4 :=
    div_le_div_of_nonneg_right hcut hq4.le
  have hNlower : ell - q ^ 10 < q ^ 10 * (N : ℝ) := by
    simpa [N] using (normalized_queryBudget_bounds hq hell).1
  have hscale : B₂ * (ell - q ^ 10) / q ^ 4 <
      B₂ * q ^ 6 * (N : ℝ) := by
    calc
      B₂ * (ell - q ^ 10) / q ^ 4 <
          B₂ * (q ^ 10 * (N : ℝ)) / q ^ 4 := by gcongr
      _ = B₂ * q ^ 6 * (N : ℝ) := by
        field_simp [ne_of_gt hq, ne_of_gt hq4]
  have hreal : ((2 * s + 3 : ℕ) : ℝ) <
      B₂ * q ^ 6 * (N : ℝ) := hleft.trans_lt (hcut'.trans_lt hscale)
  have hceil : B₂ * q ^ 6 * (N : ℝ) ≤
      (scaledPairBound q B₂ N : ℝ) := Nat.le_ceil _
  have hnat : 2 * s + 3 < scaledPairBound q B₂ N := by
    exact_mod_cast hreal.trans_le hceil
  simpa [s, N] using
    (show 2 * s + 4 ≤ scaledPairBound q B₂ N + 1 by omega)

/-- A constant-scale sufficient condition for the rounded triple-codegree
cutoff to clear three times the entropy exponent by four bits. -/
theorem actual_tripleExponent_condition
    {q ell B₃ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hell : 0 ≤ ell) (hB₃ : 0 < B₃)
    (hcut : 120 + 3 * q ≤ B₃ * (ell - q ^ 10)) :
    3 * entropyIndex q + 4 ≤
      scaledTripleBound q B₃ (queryBudget q ell) + 1 := by
  let N := queryBudget q ell
  let s := entropyIndex q
  have hs : (s : ℝ) ≤ 40 / q := by
    simpa [s] using entropyIndex_cast_le hq hq1
  have hleft : ((3 * s + 3 : ℕ) : ℝ) ≤
      (120 + 3 * q) / q := by
    calc
      ((3 * s + 3 : ℕ) : ℝ) = 3 * (s : ℝ) + 3 := by norm_num
      _ ≤ 3 * (40 / q) + 3 := by gcongr
      _ = (120 + 3 * q) / q := by
        field_simp [ne_of_gt hq]
        ring
  have hcut' : (120 + 3 * q) / q ≤
      B₃ * (ell - q ^ 10) / q :=
    div_le_div_of_nonneg_right hcut hq.le
  have hNlower : ell - q ^ 10 < q ^ 10 * (N : ℝ) := by
    simpa [N] using (normalized_queryBudget_bounds hq hell).1
  have hscale : B₃ * (ell - q ^ 10) / q <
      B₃ * q ^ 9 * (N : ℝ) := by
    calc
      B₃ * (ell - q ^ 10) / q <
          B₃ * (q ^ 10 * (N : ℝ)) / q := by gcongr
      _ = B₃ * q ^ 9 * (N : ℝ) := by
        field_simp [ne_of_gt hq]
  have hreal : ((3 * s + 3 : ℕ) : ℝ) <
      B₃ * q ^ 9 * (N : ℝ) := hleft.trans_lt (hcut'.trans_lt hscale)
  have hceil : B₃ * q ^ 9 * (N : ℝ) ≤
      (scaledTripleBound q B₃ N : ℝ) := Nat.le_ceil _
  have hnat : 3 * s + 3 < scaledTripleBound q B₃ N := by
    exact_mod_cast hreal.trans_le hceil
  simpa [s, N] using
    (show 3 * s + 4 ≤ scaledTripleBound q B₃ N + 1 by omega)

/-- At the pair-codegree scale, the factorial-moment base is at most
`2e/B₂`.  The `2` is the ambient-host factor `n=2N`; the extra `+1` is
the exact failure threshold for an upper bound. -/
theorem scaledPair_factorialBase_le
    {q B₂ : ℝ} {N : ℕ} (hB₂ : 0 < B₂) :
    Real.exp 1 * (2 * N : ℕ) * (q ^ 3) ^ 2 /
        ((scaledPairBound q B₂ N + 1 : ℕ) : ℝ) ≤
      2 * Real.exp 1 / B₂ := by
  have htarget : B₂ * q ^ 6 * (N : ℝ) ≤
      (scaledPairBound q B₂ N : ℝ) := by
    exact Nat.le_ceil _
  have htarget' : B₂ * q ^ 6 * (N : ℝ) ≤
      ((scaledPairBound q B₂ N + 1 : ℕ) : ℝ) := by
    exact htarget.trans (by norm_num)
  have hden : 0 < ((scaledPairBound q B₂ N + 1 : ℕ) : ℝ) := by
    positivity
  rw [div_le_div_iff₀ hden hB₂]
  have hmul := mul_le_mul_of_nonneg_left htarget' (by positivity : 0 ≤ 2 * Real.exp 1)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (Real.exp 1 * (2 * (N : ℝ)) * (q ^ 3) ^ 2) * B₂ =
        (2 * Real.exp 1) * (B₂ * q ^ 6 * (N : ℝ)) := by ring
    _ ≤ (2 * Real.exp 1) *
        ((scaledPairBound q B₂ N + 1 : ℕ) : ℝ) := hmul

/-- Triple-codegrees have the same normalized factorial-moment base. -/
theorem scaledTriple_factorialBase_le
    {q B₃ : ℝ} {N : ℕ} (hB₃ : 0 < B₃) :
    Real.exp 1 * (2 * N : ℕ) * (q ^ 3) ^ 3 /
        ((scaledTripleBound q B₃ N + 1 : ℕ) : ℝ) ≤
      2 * Real.exp 1 / B₃ := by
  have htarget : B₃ * q ^ 9 * (N : ℝ) ≤
      (scaledTripleBound q B₃ N : ℝ) := by
    exact Nat.le_ceil _
  have htarget' : B₃ * q ^ 9 * (N : ℝ) ≤
      ((scaledTripleBound q B₃ N + 1 : ℕ) : ℝ) := by
    exact htarget.trans (by norm_num)
  have hden : 0 < ((scaledTripleBound q B₃ N + 1 : ℕ) : ℝ) := by
    positivity
  rw [div_le_div_iff₀ hden hB₃]
  have hmul := mul_le_mul_of_nonneg_left htarget' (by positivity : 0 ≤ 2 * Real.exp 1)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    (Real.exp 1 * (2 * (N : ℝ)) * (q ^ 3) ^ 3) * B₃ =
        (2 * Real.exp 1) * (B₃ * q ^ 9 * (N : ℝ)) := by ring
    _ ≤ (2 * Real.exp 1) *
        ((scaledTripleBound q B₃ N + 1 : ℕ) : ℝ) := hmul

/-- With `B₂ ≥ 4e`, the complete pair-codegree witness term is a
polynomial prefactor times a power of `1/2`. -/
theorem scaledPairWitnessTermReal_le_halfPow
    {q B₂ : ℝ} {N : ℕ} (hq : 0 < q)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) :
    codegreeWitnessTermReal (q ^ 3) (2 * N) 2
        (scaledPairBound q B₂ N + 1) ≤
      ((2 * N : ℕ) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) := by
  have hBpos : 0 < B₂ := (mul_pos (by norm_num) (Real.exp_pos 1)).trans_le hB₂
  have hbase := scaledPair_factorialBase_le (q := q) (N := N) hBpos
  have hhalf : 2 * Real.exp 1 / B₂ ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hBpos]
    linarith
  refine (codegreeWitnessTermReal_le (by positivity) (2 * N) 2
    (scaledPairBound q B₂ N + 1) (by omega)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (hbase.trans hhalf) _) (by positivity)

/-- The preceding real estimate applied directly to the exact `ENNReal`
pair-codegree summand in `hostWitnessBound`. -/
theorem scaledPairWitnessTerm_toReal_le_halfPow
    {q B₂ : ℝ} {N : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) :
    ((Nat.choose (2 * N) 2 *
          Nat.choose (2 * N - 2) (scaledPairBound q B₂ N + 1) : ℝ≥0∞) *
        (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^
          (2 * (scaledPairBound q B₂ N + 1))).toReal ≤
      ((2 * N : ℕ) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) := by
  rw [codegreeWitnessTerm_toReal]
  exact scaledPairWitnessTermReal_le_halfPow hq hB₂

/-- With `B₃ ≥ 4e`, the triple-codegree witness term has the analogous
power-of-two bound. -/
theorem scaledTripleWitnessTermReal_le_halfPow
    {q B₃ : ℝ} {N : ℕ} (hq : 0 < q)
    (hB₃ : 4 * Real.exp 1 ≤ B₃) :
    codegreeWitnessTermReal (q ^ 3) (2 * N) 3
        (scaledTripleBound q B₃ N + 1) ≤
      ((2 * N : ℕ) : ℝ) ^ 3 *
        (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1) := by
  have hBpos : 0 < B₃ := (mul_pos (by norm_num) (Real.exp_pos 1)).trans_le hB₃
  have hbase := scaledTriple_factorialBase_le (q := q) (N := N) hBpos
  have hhalf : 2 * Real.exp 1 / B₃ ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hBpos]
    linarith
  refine (codegreeWitnessTermReal_le (by positivity) (2 * N) 3
    (scaledTripleBound q B₃ N + 1) (by omega)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (hbase.trans hhalf) _) (by positivity)

/-- The exact `ENNReal` triple-codegree summand obeys the same estimate after
coercion to the reals. -/
theorem scaledTripleWitnessTerm_toReal_le_halfPow
    {q B₃ : ℝ} {N : ℕ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hB₃ : 4 * Real.exp 1 ≤ B₃) :
    ((Nat.choose (2 * N) 3 *
          Nat.choose (2 * N - 3) (scaledTripleBound q B₃ N + 1) : ℝ≥0∞) *
        (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^
          (3 * (scaledTripleBound q B₃ N + 1))).toReal ≤
      ((2 * N : ℕ) : ℝ) ^ 3 *
        (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1) := by
  rw [codegreeWitnessTerm_toReal]
  exact scaledTripleWitnessTermReal_le_halfPow hq hB₃

/-- Absorb a polynomial prefactor bounded by `2^s` into a negative
power of two.  This elementary lemma controls the pair, triple, and dense
errors uniformly. -/
theorem mul_halfPow_le_halfPow
    {x : ℝ} {j r s K : ℕ} (hx0 : 0 ≤ x)
    (hx : x ≤ (2 : ℝ) ^ s) (hr : j * s + K ≤ r) :
    x ^ j * (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ K := by
  have hxpow : x ^ j ≤ ((2 : ℝ) ^ s) ^ j :=
    pow_le_pow_left₀ hx0 hx j
  have hrpow : (1 / 2 : ℝ) ^ r ≤
      (1 / 2 : ℝ) ^ (j * s + K) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
  calc
    x ^ j * (1 / 2 : ℝ) ^ r ≤
        ((2 : ℝ) ^ s) ^ j * (1 / 2 : ℝ) ^ (j * s + K) :=
      mul_le_mul hxpow hrpow (by positivity) (by positivity)
    _ = (1 / 2 : ℝ) ^ K := by
      rw [pow_add]
      have heq : ((2 : ℝ) ^ s) ^ j = (2 : ℝ) ^ (j * s) := by
        rw [← pow_mul]
        congr 1
        exact Nat.mul_comm s j
      rw [heq]
      calc
        (2 : ℝ) ^ (j * s) *
            ((1 / 2 : ℝ) ^ (j * s) * (1 / 2 : ℝ) ^ K) =
            ((2 : ℝ) ^ (j * s) * (1 / 2 : ℝ) ^ (j * s)) *
              (1 / 2 : ℝ) ^ K := by ring
        _ = ((2 : ℝ) * (1 / 2 : ℝ)) ^ (j * s) *
              (1 / 2 : ℝ) ^ K := by rw [mul_pow]
        _ = (1 / 2 : ℝ) ^ K := by norm_num

/-- The completely explicit real failure bound obtained after choosing the
elementary dense entropy exponent `entropyIndex q` and the power-law
small-set majorant. -/
noncomputable def scaledHostFailureBoundReal
    (q ell C A B₂ B₃ : ℝ) (L : ℕ) : ℝ :=
  let N := queryBudget q ell
  let M := edgeBudget q C N
  let D := degeneracyBudget q A M
  (((2 * N : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) +
    ((2 * N : ℕ) : ℝ) ^ 3 *
      (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1)) +
  ((2 * M / D + 1 : ℕ) : ℝ) *
    (1 / 2 : ℝ) ^ (entropyIndex q * D) +
  ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L

/-- A convenient finite criterion making the explicit four-error bound
strictly smaller than one.  The pair and triple hypotheses ask their rounded
cutoffs to clear the entropy exponent by four bits; the final hypothesis is
the sole remaining small-set arithmetic estimate. -/
theorem scaledHostFailureBoundReal_lt_one_of_simple_bounds
    {q ell C A B₂ B₃ : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 ≤ A)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hentropySmall : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1)
    (hdenseSmall : 160 * q ≤ A * √(C * ell / 2))
    (hedgeSmall : C * q ^ 3 ≤ 1)
    (hpairExponent : 2 * entropyIndex q + 4 ≤
      scaledPairBound q B₂ (queryBudget q ell) + 1)
    (htripleExponent : 3 * entropyIndex q + 4 ≤
      scaledTripleBound q B₃ (queryBudget q ell) + 1)
    (hsmallError :
      ((degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) + 1 : ℕ) : ℝ) *
        actualSmallSetPowerBound q ell C A L ≤ 1 / 16) :
    scaledHostFailureBoundReal q ell C A B₂ B₃ L < 1 := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  let D := degeneracyBudget q A M
  let s := entropyIndex q
  have hentropy : Real.exp 1 * ((2 * N : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by
    simpa [N, s] using actual_entropyCondition hq hell hentropySmall
  have hn : ((2 * N : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by
    calc
      ((2 * N : ℕ) : ℝ) ≤
          Real.exp 1 * ((2 * N : ℕ) : ℝ) := by
        exact le_mul_of_one_le_left (Nat.cast_nonneg _)
          (Real.one_le_exp (by norm_num))
      _ ≤ (2 : ℝ) ^ s := hentropy
  have hpair : ((2 * N : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) ≤
        (1 / 2 : ℝ) ^ 4 := by
    simpa [s] using (mul_halfPow_le_halfPow
      (x := ((2 * N : ℕ) : ℝ)) (j := 2)
      (r := scaledPairBound q B₂ N + 1) (s := s) (K := 4)
      (Nat.cast_nonneg _) hn (by simpa [N, s] using hpairExponent))
  have htriple : ((2 * N : ℕ) : ℝ) ^ 3 *
      (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1) ≤
        (1 / 2 : ℝ) ^ 4 := by
    simpa [s] using (mul_halfPow_le_halfPow
      (x := ((2 * N : ℕ) : ℝ)) (j := 3)
      (r := scaledTripleBound q B₃ N + 1) (s := s) (K := 4)
      (Nat.cast_nonneg _) hn (by simpa [N, s] using htripleExponent))
  have hq10 : 0 < q ^ 10 := pow_pos hq _
  have hq10le : q ^ 10 ≤ ell := by
    have : 0 ≤ q ^ 10 := hq10.le
    linarith
  have hNtarget : 1 ≤ ell / q ^ 10 :=
    (le_div_iff₀ hq10).2 (by simpa using hq10le)
  have hN : 0 < N := by
    dsimp [N, queryBudget]
    exact Nat.floor_pos.mpr hNtarget
  have hMN : M ≤ N := by
    apply (Nat.ceil_le).2
    change C * q ^ 3 * (N : ℝ) ≤ (N : ℝ)
    calc
      C * q ^ 3 * (N : ℝ) ≤ 1 * (N : ℝ) := by gcongr
      _ = (N : ℝ) := one_mul _
  have hspos : 0 < s := by
    dsimp [s, entropyIndex]
    exact Nat.mul_pos (Nat.ceil_pos.mpr (by positivity)) (by norm_num)
  have hs20 : 20 ≤ s := by
    dsimp [s, entropyIndex]
    have hm : 1 ≤ ⌈1 / q⌉₊ := Nat.ceil_pos.mpr (by positivity)
    omega
  have hlog : 4 * s ≤ D := by
    simpa [s, D, M, N] using actual_entropyIndex_le_degeneracyBudget
      hq hq1 hell hC hA hscale hdenseSmall
  have hDfour : 4 ≤ D := by omega
  have hdiv : 2 * M / D ≤ M := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right M (by omega : 2 ≤ D)
  have hcountNat : 2 * M / D + 1 ≤ 2 * N := by omega
  have hcount : ((2 * M / D + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by
    exact (by exact_mod_cast hcountNat :
      ((2 * M / D + 1 : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ)).trans hn
  have hdenseExponent : 1 * s + 4 ≤ s * D := by
    calc
      1 * s + 4 ≤ s * 4 := by omega
      _ ≤ s * D := Nat.mul_le_mul_left s hDfour
  have hdense : ((2 * M / D + 1 : ℕ) : ℝ) *
      (1 / 2 : ℝ) ^ (s * D) ≤ (1 / 2 : ℝ) ^ 4 := by
    simpa using (mul_halfPow_le_halfPow
      (x := ((2 * M / D + 1 : ℕ) : ℝ)) (j := 1)
      (r := s * D) (s := s) (K := 4)
      (Nat.cast_nonneg _) hcount hdenseExponent)
  change
    (((2 * N : ℕ) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) +
      ((2 * N : ℕ) : ℝ) ^ 3 *
        (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1)) +
    ((2 * M / D + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (s * D) +
    ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L < 1
  have hsmall : ((D + 1 : ℕ) : ℝ) *
      actualSmallSetPowerBound q ell C A L ≤ 1 / 16 := by
    simpa [D, M, N] using hsmallError
  calc
    (((2 * N : ℕ) : ℝ) ^ 2 *
          (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) +
        ((2 * N : ℕ) : ℝ) ^ 3 *
          (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1)) +
      ((2 * M / D + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (s * D) +
      ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L ≤
        ((1 / 2 : ℝ) ^ 4 + (1 / 2 : ℝ) ^ 4) +
          (1 / 2 : ℝ) ^ 4 + 1 / 16 := by
      exact add_le_add (add_le_add (add_le_add hpair htriple) hdense) hsmall
    _ < 1 := by norm_num

/-- A single finite bound for all four random-host errors.  Every side
condition is an explicit arithmetic inequality: the two codegree constants,
the dense entropy comparison, and the two small-set bases.  In particular,
there is no asymptotic or probabilistic hypothesis hidden in this theorem. -/
theorem actualHostWitnessBound_toReal_le
    {q A B₂ B₃ ρ : ℝ} {N M L s : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hA : 0 < A) (hM : 0 < M)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) (hB₃ : 4 * Real.exp 1 ≤ B₃)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hentropy : Real.exp 1 * ((2 * N : ℕ) : ℝ) ≤ (2 : ℝ) ^ s)
    (hlog : 4 * s ≤ degeneracyBudget q A M)
    (hL : 0 < L)
    (hlocal : Real.exp 1 * (degeneracyBudget q A M : ℝ) * q ^ 3 /
      (2 * (L : ℝ)) ≤ 1)
    (hgeom : smallSetGeometricBase (q ^ 3) (2 * N)
      (degeneracyBudget q A M) L ≤ ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (hostWitnessBound (cubeProbability q hq.le hq1) (2 * N) M
      (degeneracyBudget q A M) L
      (scaledPairBound q B₂ N) (scaledTripleBound q B₃ N)).toReal ≤
      (((2 * N : ℕ) : ℝ) ^ 2 *
          (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) +
        ((2 * N : ℕ) : ℝ) ^ 3 *
          (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1)) +
      ((2 * M / degeneracyBudget q A M + 1 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ (s * degeneracyBudget q A M) +
      ((degeneracyBudget q A M + 1 : ℕ) : ℝ) * ρ := by
  let D := degeneracyBudget q A M
  have hpair := scaledPairWitnessTermReal_le_halfPow
    (N := N) hq hB₂
  have htriple := scaledTripleWitnessTermReal_le_halfPow
    (N := N) hq hB₃
  have hdense := actualDenseWitnessSumReal_le
    (n := 2 * N) (s := s) hq hA hM hAlarge hentropy
      (by simpa [D] using hlog)
  have hsmall := smallWitnessSumReal_le (x := q ^ 3) (ρ := ρ)
    (by positivity) (2 * N) D hL (by simpa [D] using hlocal)
    (by simpa [D] using hgeom) hρ0 hρ1
  rw [hostWitnessBound_toReal]
  change codegreeWitnessTermReal (q ^ 3) (2 * N) 2
      (scaledPairBound q B₂ N + 1) +
    codegreeWitnessTermReal (q ^ 3) (2 * N) 3
      (scaledTripleBound q B₃ N + 1) +
    (∑ k ∈ Finset.Icc D (2 * M / D),
      spannedWitnessTermReal (q ^ 3) (2 * N) k (D * k ⌈/⌉ 2)) +
    (∑ k ∈ Finset.Icc 0 D,
      spannedWitnessTermReal (q ^ 3) (2 * N) k (L * k + 1)) ≤ _
  simpa [D] using add_le_add (add_le_add (add_le_add hpair htriple) hdense) hsmall

/-- The finite four-error estimate applied to the actual random-host event.
This is a high-probability theorem with only explicit arithmetic side
conditions: its left side is the probability that one of the four
`HostGood` clauses fails. -/
theorem measure_actualRandomHostGoodEvent_compl_toReal_le
    {q A B₂ B₃ ρ : ℝ} {N M L s : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hA : 0 < A) (hM : 0 < M)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) (hB₃ : 4 * Real.exp 1 ≤ B₃)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hentropy : Real.exp 1 * ((2 * N : ℕ) : ℝ) ≤ (2 : ℝ) ^ s)
    (hlog : 4 * s ≤ degeneracyBudget q A M)
    (hL : 0 < L)
    (hlocal : Real.exp 1 * (degeneracyBudget q A M : ℝ) * q ^ 3 /
      (2 * (L : ℝ)) ≤ 1)
    (hgeom : smallSetGeometricBase (q ^ 3) (2 * N)
      (degeneracyBudget q A M) L ≤ ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (bitBoardMeasure (Sym2 (Fin (2 * N)))
      (cubeProbability q hq.le hq1)
      (randomHostGoodEvent (2 * N) M (degeneracyBudget q A M) L
        (scaledPairBound q B₂ N) (scaledTripleBound q B₃ N))ᶜ).toReal ≤
      (((2 * N : ℕ) : ℝ) ^ 2 *
          (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) +
        ((2 * N : ℕ) : ℝ) ^ 3 *
          (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1)) +
      ((2 * M / degeneracyBudget q A M + 1 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ (s * degeneracyBudget q A M) +
      ((degeneracyBudget q A M + 1 : ℕ) : ℝ) * ρ := by
  exact (measure_randomHostGoodEvent_compl_toReal_le
    (cubeProbability q hq.le hq1) (2 * N) M (degeneracyBudget q A M) L
      (scaledPairBound q B₂ N) (scaledTripleBound q B₃ N)).trans
    (actualHostWitnessBound_toReal_le hq hq1 hA hM hB₂ hB₃ hAlarge
      hentropy hlog hL hlocal hgeom hρ0 hρ1)

/-- Paper-scale high-probability estimate with the logarithmic and geometric
side conditions discharged.  Its hypotheses are elementary inequalities in
`q` and the fixed constants; the remaining right-hand side is the explicit
sum whose being less than one guarantees a deterministic good host. -/
theorem measure_scaledRandomHostGoodEvent_compl_toReal_le_explicit
    {q ell C A B₂ B₃ : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 < A)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) (hB₃ : 4 * Real.exp 1 ≤ B₃)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hentropySmall : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1)
    (hdenseSmall : 160 * q ≤ A * √(C * ell / 2))
    (hL : 8 ≤ L)
    (hlocalSmall : Real.exp 1 * (A * √(C * ell + 1) + 1) * q ≤
      2 * (L : ℝ))
    (hsmallPower : actualSmallSetPowerBound q ell C A L ≤ 1) :
    (bitBoardMeasure (Sym2 (Fin (2 * queryBudget q ell)))
      (cubeProbability q hq.le hq1)
      (randomHostGoodEvent (2 * queryBudget q ell)
        (edgeBudget q C (queryBudget q ell))
        (degeneracyBudget q A (edgeBudget q C (queryBudget q ell))) L
        (scaledPairBound q B₂ (queryBudget q ell))
        (scaledTripleBound q B₃ (queryBudget q ell)))ᶜ).toReal ≤
      scaledHostFailureBoundReal q ell C A B₂ B₃ L := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  have hq10 : 0 < q ^ 10 := pow_pos hq _
  have hq10le : q ^ 10 ≤ ell := by
    have hq10nonneg : 0 ≤ q ^ 10 := hq10.le
    linarith
  have hNtarget : 1 ≤ ell / q ^ 10 := by
    exact (le_div_iff₀ hq10).2 (by simpa using hq10le)
  have hN : 0 < N := by
    dsimp [N, queryBudget]
    exact Nat.floor_pos.mpr hNtarget
  have hM : 0 < M := by
    dsimp [M, edgeBudget]
    exact Nat.ceil_pos.mpr (by positivity)
  have hentropy := actual_entropyCondition hq hell hentropySmall
  have hlog := actual_entropyIndex_le_degeneracyBudget
    hq hq1 hell hC hA.le hscale hdenseSmall
  have hLpos : 0 < L := by omega
  have hlocal := actual_smallSetLocalBase_le
    hq hq1 hell hC hA.le hscale hLpos hlocalSmall
  have hgeom := actual_smallSetGeometricBase_bound
    hq hq1 hell hC hA.le hscale hL
  have hpower0 : 0 ≤ actualSmallSetPowerBound q ell C A L := by
    unfold actualSmallSetPowerBound
    positivity
  have hmain := measure_actualRandomHostGoodEvent_compl_toReal_le
    (N := N) (M := M) (L := L) (s := entropyIndex q)
    (q := q) (A := A) (B₂ := B₂) (B₃ := B₃)
    (ρ := actualSmallSetPowerBound q ell C A L)
    hq hq1 hA hM hB₂ hB₃ hAlarge hentropy hlog hLpos hlocal
      hgeom hpower0 hsmallPower
  simpa [N, M, scaledHostFailureBoundReal] using hmain

/-- The precise finite residue of the random-host argument: once the
explicit four-error expression is below one, a deterministic host with all
four required properties exists. -/
theorem exists_scaledHostGood_of_failureBound_lt_one
    {q ell C A B₂ B₃ : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 < A)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) (hB₃ : 4 * Real.exp 1 ≤ B₃)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hentropySmall : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1)
    (hdenseSmall : 160 * q ≤ A * √(C * ell / 2))
    (hL : 8 ≤ L)
    (hlocalSmall : Real.exp 1 * (A * √(C * ell + 1) + 1) * q ≤
      2 * (L : ℝ))
    (hsmallPower : actualSmallSetPowerBound q ell C A L ≤ 1)
    (hfailure : scaledHostFailureBoundReal q ell C A B₂ B₃ L < 1) :
    ∃ w : Sym2 (Fin (2 * queryBudget q ell)) → Bool,
      HostGood (randomHost (2 * queryBudget q ell) w)
        (edgeBudget q C (queryBudget q ell))
        (degeneracyBudget q A (edgeBudget q C (queryBudget q ell))) L
        (scaledPairBound q B₂ (queryBudget q ell))
        (scaledTripleBound q B₃ (queryBudget q ell)) := by
  have hmeasure := measure_scaledRandomHostGoodEvent_compl_toReal_le_explicit
    hq hq1 hell hC hA hB₂ hB₃ hAlarge hscale hentropySmall
      hdenseSmall hL hlocalSmall hsmallPower
  exact exists_hostGood_of_compl_toReal_lt_one
    (cubeProbability q hq.le hq1) (2 * queryBudget q ell)
    (edgeBudget q C (queryBudget q ell))
    (degeneracyBudget q A (edgeBudget q C (queryBudget q ell))) L
    (scaledPairBound q B₂ (queryBudget q ell))
    (scaledTripleBound q B₃ (queryBudget q ell))
    (hmeasure.trans_lt hfailure)

/-- A version of `exists_scaledHostGood_of_failureBound_lt_one` whose final
failure-bound hypothesis has been split into three transparent checks: the
pair cutoff, the triple cutoff, and a `1/16` small-set error.  The dense error
is then absorbed automatically. -/
theorem exists_scaledHostGood_of_simple_bounds
    {q ell C A B₂ B₃ : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 < A)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) (hB₃ : 4 * Real.exp 1 ≤ B₃)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hentropySmall : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1)
    (hdenseSmall : 160 * q ≤ A * √(C * ell / 2))
    (hL : 8 ≤ L)
    (hlocalSmall : Real.exp 1 * (A * √(C * ell + 1) + 1) * q ≤
      2 * (L : ℝ))
    (hedgeSmall : C * q ^ 3 ≤ 1)
    (hpairExponent : 2 * entropyIndex q + 4 ≤
      scaledPairBound q B₂ (queryBudget q ell) + 1)
    (htripleExponent : 3 * entropyIndex q + 4 ≤
      scaledTripleBound q B₃ (queryBudget q ell) + 1)
    (hsmallError :
      ((degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) + 1 : ℕ) : ℝ) *
        actualSmallSetPowerBound q ell C A L ≤ 1 / 16) :
    ∃ w : Sym2 (Fin (2 * queryBudget q ell)) → Bool,
      HostGood (randomHost (2 * queryBudget q ell) w)
        (edgeBudget q C (queryBudget q ell))
        (degeneracyBudget q A (edgeBudget q C (queryBudget q ell))) L
        (scaledPairBound q B₂ (queryBudget q ell))
        (scaledTripleBound q B₃ (queryBudget q ell)) := by
  let D := degeneracyBudget q A (edgeBudget q C (queryBudget q ell))
  have hpower0 : 0 ≤ actualSmallSetPowerBound q ell C A L := by
    unfold actualSmallSetPowerBound
    positivity
  have hpower_le_product : actualSmallSetPowerBound q ell C A L ≤
      ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L := by
    exact le_mul_of_one_le_left hpower0 (by norm_num)
  have hpower1 : actualSmallSetPowerBound q ell C A L ≤ 1 := by
    calc
      actualSmallSetPowerBound q ell C A L ≤
          ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L :=
        hpower_le_product
      _ ≤ 1 / 16 := by simpa [D] using hsmallError
      _ ≤ 1 := by norm_num
  have hfailure := scaledHostFailureBoundReal_lt_one_of_simple_bounds
    hq hq1 hell hC hA.le hscale hentropySmall hdenseSmall hedgeSmall
      hpairExponent htripleExponent hsmallError
  exact exists_scaledHostGood_of_failureBound_lt_one
    hq hq1 hell hC hA hB₂ hB₃ hAlarge hscale hentropySmall
      hdenseSmall hL hlocalSmall hpower1 hfailure

/-- Fully polynomial form of the finite random-host existence criterion.
For fixed positive constants with `B₃*ell > 120` and `L>10`, every displayed
side condition holds for all sufficiently small positive `q`; proving that
last elementary eventual statement is now independent of probability and
graph theory. -/
theorem exists_scaledHostGood_of_power_bounds
    {q ell C A B₂ B₃ : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 < A)
    (hB₂ : 4 * Real.exp 1 ≤ B₂) (hB₃ : 4 * Real.exp 1 ≤ B₃)
    (hAlarge : 4 * Real.exp 1 ≤ A ^ 2)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hentropySmall : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1)
    (hdenseSmall : 160 * q ≤ A * √(C * ell / 2))
    (hL : 11 ≤ L)
    (hlocalSmall : Real.exp 1 * (A * √(C * ell + 1) + 1) * q ≤
      2 * (L : ℝ))
    (hedgeSmall : C * q ^ 3 ≤ 1)
    (hpairPower : 80 * q ^ 3 + 3 * q ^ 4 ≤ B₂ * (ell - q ^ 10))
    (htriplePower : 120 + 3 * q ≤ B₃ * (ell - q ^ 10))
    (hsmallPower : actualSmallSetErrorPowerBound q ell C A L ≤ 1 / 16) :
    ∃ w : Sym2 (Fin (2 * queryBudget q ell)) → Bool,
      HostGood (randomHost (2 * queryBudget q ell) w)
        (edgeBudget q C (queryBudget q ell))
        (degeneracyBudget q A (edgeBudget q C (queryBudget q ell))) L
        (scaledPairBound q B₂ (queryBudget q ell))
        (scaledTripleBound q B₃ (queryBudget q ell)) := by
  have hB₂pos : 0 < B₂ :=
    (mul_pos (by norm_num) (Real.exp_pos 1)).trans_le hB₂
  have hB₃pos : 0 < B₃ :=
    (mul_pos (by norm_num) (Real.exp_pos 1)).trans_le hB₃
  have hpair := actual_pairExponent_condition
    hq hq1 hell hB₂pos hpairPower
  have htriple := actual_tripleExponent_condition
    hq hq1 hell hB₃pos htriplePower
  have hsmall := (actual_smallSetErrorPowerBound
    hq hq1 hell hC hA.le hscale (by omega : 10 ≤ L)).trans hsmallPower
  exact exists_scaledHostGood_of_simple_bounds
    hq hq1 hell hC hA hB₂ hB₃ hAlarge hscale hentropySmall
      hdenseSmall (by omega) hlocalSmall hedgeSmall hpair htriple hsmall

/-- A completely numeric paper-scale host.  The constants are intentionally
conservative; their purpose is to close the random-host argument without any
remaining asymptotic hypothesis. -/
theorem numeric_scaledHostGood
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 1000) :
    ∃ w : Sym2 (Fin (2 * queryBudget q 1)) → Bool,
      HostGood (randomHost (2 * queryBudget q 1) w)
        (edgeBudget q 1 (queryBudget q 1))
        (degeneracyBudget q 4 (edgeBudget q 1 (queryBudget q 1))) 12
        (scaledPairBound q 12 (queryBudget q 1))
        (scaledTripleBound q 256 (queryBudget q 1)) := by
  have hq1 : q ≤ 1 := hqsmall.le.trans (by norm_num)
  have hq1000 : q ≤ 1 / 1000 := hqsmall.le
  have hqpow : ∀ n : ℕ, 0 < n → q ^ n ≤ q := by
    intro n hn
    simpa using pow_le_pow_of_le_one hq.le hq1
      (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have he3 : Real.exp 1 ≤ 3 :=
    (lt_trans Real.exp_one_lt_d9 (by norm_num)).le
  have hsqrt2nonneg : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
  have hsqrt2sq : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2 : √(2 : ℝ) ≤ 3 / 2 := by nlinarith
  have hK0 : 0 ≤ 4 * √(2 : ℝ) + 1 := by positivity
  have hK7 : 4 * √(2 : ℝ) + 1 ≤ 7 := by nlinarith
  have hsqrtHalfNonneg : 0 ≤ √(1 / 2 : ℝ) := Real.sqrt_nonneg _
  have hsqrtHalfSq : √(1 / 2 : ℝ) ^ 2 = 1 / 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtHalf : (1 / 2 : ℝ) ≤ √(1 / 2 : ℝ) := by nlinarith
  have hB₂ : 4 * Real.exp 1 ≤ (12 : ℝ) := by nlinarith
  have hB₃ : 4 * Real.exp 1 ≤ (256 : ℝ) := by nlinarith
  have hAlarge : 4 * Real.exp 1 ≤ (4 : ℝ) ^ 2 := by nlinarith
  have hscale : 2 * q ^ 10 ≤ (1 : ℝ) := by
    calc
      2 * q ^ 10 ≤ 2 * (1 / 1000 : ℝ) := by
        gcongr
        exact (hqpow 10 (by omega)).trans hq1000
      _ ≤ 1 := by norm_num
  have hentropy : 2 * Real.exp 1 * (1 : ℝ) * q ^ 10 ≤ 1 := by
    calc
      2 * Real.exp 1 * (1 : ℝ) * q ^ 10 ≤
          2 * 3 * 1 * (1 / 1000 : ℝ) := by
        gcongr
        exact (hqpow 10 (by omega)).trans hq1000
      _ ≤ 1 := by norm_num
  have hdense : 160 * q ≤ (4 : ℝ) * √((1 : ℝ) * 1 / 2) := by
    calc
      160 * q ≤ 160 * (1 / 1000 : ℝ) := by gcongr
      _ ≤ 4 * √(1 / 2 : ℝ) := by nlinarith
      _ = (4 : ℝ) * √((1 : ℝ) * 1 / 2) := by norm_num
  have hlocal : Real.exp 1 * ((4 : ℝ) * √((1 : ℝ) * 1 + 1) + 1) * q ≤
      2 * (12 : ℝ) := by
    have hprod : Real.exp 1 * (4 * √(2 : ℝ) + 1) ≤ 21 := by
      have hp := mul_le_mul he3 hK7 hK0 (by norm_num : (0 : ℝ) ≤ 3)
      norm_num at hp ⊢
      exact hp
    calc
      Real.exp 1 * ((4 : ℝ) * √((1 : ℝ) * 1 + 1) + 1) * q ≤
          3 * 7 * q := by
        norm_num only [one_mul, one_add_one_eq_two]
        exact mul_le_mul_of_nonneg_right hprod hq.le
      _ ≤ 3 * 7 * (1 / 1000 : ℝ) := by gcongr
      _ ≤ 2 * (12 : ℝ) := by norm_num
  have hedge : (1 : ℝ) * q ^ 3 ≤ 1 := by
    simpa using (hqpow 3 (by omega)).trans hq1
  have hpair : 80 * q ^ 3 + 3 * q ^ 4 ≤
      (12 : ℝ) * ((1 : ℝ) - q ^ 10) := by
    have hq3 := (hqpow 3 (by omega)).trans hq1000
    have hq4 := (hqpow 4 (by omega)).trans hq1000
    have hq10 := (hqpow 10 (by omega)).trans hq1000
    nlinarith
  have htriple : 120 + 3 * q ≤
      (256 : ℝ) * ((1 : ℝ) - q ^ 10) := by
    have hq10 := (hqpow 10 (by omega)).trans hq1000
    nlinarith
  have hbase : Real.exp 1 / (2 * (12 : ℝ)) ≤ 1 / 8 := by
    norm_num only
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).2 (by nlinarith)
  have hsmall : actualSmallSetErrorPowerBound q 1 1 4 12 ≤ 1 / 16 := by
    have hKplus : 4 * √(2 : ℝ) + 1 + 1 ≤ 8 := by nlinarith
    have hKpow : (4 * √(2 : ℝ) + 1) ^ 11 ≤ (7 : ℝ) ^ 11 :=
      pow_le_pow_left₀ hK0 hK7 11
    have hbase0 : 0 ≤ Real.exp 1 / 24 := by positivity
    have hbasePow : (Real.exp 1 / 24) ^ 12 ≤ (1 / 8 : ℝ) ^ 12 :=
      pow_le_pow_left₀ hbase0 (by
        have hb := hbase
        norm_num at hb ⊢
        exact hb) 12
    have hinner : Real.exp 1 * (Real.exp 1 / 24) ^ 12 ≤
        3 * (1 / 8 : ℝ) ^ 12 :=
      mul_le_mul he3 hbasePow (by positivity) (by norm_num)
    have hF : 2 * Real.exp 1 * (Real.exp 1 / 24) ^ 12 ≤
        2 * 3 * (1 / 8 : ℝ) ^ 12 := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 2)
    have hq2 : q ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hq.le hq1000 2
    unfold actualSmallSetErrorPowerBound
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, one_mul, mul_one,
      one_add_one_eq_two]
    calc
      (4 * √(2 : ℝ) + 1 + 1) *
          (2 * Real.exp 1 * (Real.exp 1 / 24) ^ 12) *
          (4 * √(2 : ℝ) + 1) ^ 11 * q ^ 2 ≤
        8 * (2 * 3 * (1 / 8 : ℝ) ^ 12) * 7 ^ 11 *
          (1 / 1000 : ℝ) ^ 2 := by
        gcongr
      _ ≤ 1 / 16 := by norm_num
  exact exists_scaledHostGood_of_power_bounds
    hq hq1 (by norm_num) (by norm_num) (by norm_num)
    hB₂ hB₃ hAlarge hscale hentropy hdense (by norm_num) hlocal
      hedge hpair htriple hsmall

/-- Unconditional finite random-host theorem with an explicit threshold and
an actual graph witness (rather than a probability statement). -/
theorem exists_q0_numeric_scaledHostGood :
    ∃ q₀ : ℝ, 0 < q₀ ∧ ∀ q : ℝ, 0 < q → q < q₀ →
      ∃ G : SimpleGraph (Fin (2 * queryBudget q 1)),
        HostGood G
          (edgeBudget q 1 (queryBudget q 1))
          (degeneracyBudget q 4 (edgeBudget q 1 (queryBudget q 1))) 12
          (scaledPairBound q 12 (queryBudget q 1))
          (scaledTripleBound q 256 (queryBudget q 1)) := by
  refine ⟨1 / 1000, by norm_num, ?_⟩
  intro q hq hqsmall
  obtain ⟨w, hw⟩ := numeric_scaledHostGood hq hqsmall
  exact ⟨randomHost (2 * queryBudget q 1) w, hw⟩

/-- Numeric host specialized to the edge-budget multiplier `C=8` used by
the adaptive-tail/recurrence layer. -/
theorem numeric_scaledHostGood_c8
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 10000) :
    ∃ w : Sym2 (Fin (2 * queryBudget q 1)) → Bool,
      HostGood (randomHost (2 * queryBudget q 1) w)
        (edgeBudget q 8 (queryBudget q 1))
        (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 12
        (scaledPairBound q 12 (queryBudget q 1))
        (scaledTripleBound q 256 (queryBudget q 1)) := by
  have hq1 : q ≤ 1 := hqsmall.le.trans (by norm_num)
  have hqsmall' : q ≤ 1 / 10000 := hqsmall.le
  have hqpow : ∀ n : ℕ, 0 < n → q ^ n ≤ q := by
    intro n hn
    simpa using pow_le_pow_of_le_one hq.le hq1
      (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have he3 : Real.exp 1 ≤ 3 :=
    (lt_trans Real.exp_one_lt_d9 (by norm_num)).le
  have hsqrt4 : √(4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt9 : √(9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hB₂ : 4 * Real.exp 1 ≤ (12 : ℝ) := by nlinarith
  have hB₃ : 4 * Real.exp 1 ≤ (256 : ℝ) := by nlinarith
  have hAlarge : 4 * Real.exp 1 ≤ (4 : ℝ) ^ 2 := by nlinarith
  have hscale : 2 * q ^ 10 ≤ (1 : ℝ) := by
    calc
      2 * q ^ 10 ≤ 2 * (1 / 10000 : ℝ) := by
        gcongr
        exact (hqpow 10 (by omega)).trans hqsmall'
      _ ≤ 1 := by norm_num
  have hentropy : 2 * Real.exp 1 * (1 : ℝ) * q ^ 10 ≤ 1 := by
    calc
      2 * Real.exp 1 * (1 : ℝ) * q ^ 10 ≤
          2 * 3 * 1 * (1 / 10000 : ℝ) := by
        gcongr
        exact (hqpow 10 (by omega)).trans hqsmall'
      _ ≤ 1 := by norm_num
  have hdense : 160 * q ≤ (4 : ℝ) * √((8 : ℝ) * 1 / 2) := by
    rw [show (8 : ℝ) * 1 / 2 = 4 by norm_num, hsqrt4]
    nlinarith
  have hlocal : Real.exp 1 * ((4 : ℝ) * √((8 : ℝ) * 1 + 1) + 1) * q ≤
      2 * (12 : ℝ) := by
    rw [show (8 : ℝ) * 1 + 1 = 9 by norm_num, hsqrt9]
    calc
      Real.exp 1 * (4 * 3 + 1) * q ≤ 3 * 13 * (1 / 10000 : ℝ) := by
        gcongr
        norm_num
      _ ≤ 2 * (12 : ℝ) := by norm_num
  have hedge : (8 : ℝ) * q ^ 3 ≤ 1 := by
    calc
      (8 : ℝ) * q ^ 3 ≤ 8 * (1 / 10000 : ℝ) := by
        gcongr
        exact (hqpow 3 (by omega)).trans hqsmall'
      _ ≤ 1 := by norm_num
  have hpair : 80 * q ^ 3 + 3 * q ^ 4 ≤
      (12 : ℝ) * ((1 : ℝ) - q ^ 10) := by
    have hq3 := (hqpow 3 (by omega)).trans hqsmall'
    have hq4 := (hqpow 4 (by omega)).trans hqsmall'
    have hq10 := (hqpow 10 (by omega)).trans hqsmall'
    nlinarith
  have htriple : 120 + 3 * q ≤
      (256 : ℝ) * ((1 : ℝ) - q ^ 10) := by
    have hq10 := (hqpow 10 (by omega)).trans hqsmall'
    nlinarith
  have hbase : Real.exp 1 / (2 * (12 : ℝ)) ≤ 1 / 8 := by
    norm_num only
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).2 (by nlinarith)
  have hsmall : actualSmallSetErrorPowerBound q 1 8 4 12 ≤ 1 / 16 := by
    have hbase0 : 0 ≤ Real.exp 1 / 24 := by positivity
    have hbasePow : (Real.exp 1 / 24) ^ 12 ≤ (1 / 8 : ℝ) ^ 12 :=
      pow_le_pow_left₀ hbase0 (by
        have hb := hbase
        norm_num at hb ⊢
        exact hb) 12
    have hinner : Real.exp 1 * (Real.exp 1 / 24) ^ 12 ≤
        3 * (1 / 8 : ℝ) ^ 12 :=
      mul_le_mul he3 hbasePow (by positivity) (by norm_num)
    have hF : 2 * Real.exp 1 * (Real.exp 1 / 24) ^ 12 ≤
        2 * 3 * (1 / 8 : ℝ) ^ 12 := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hinner (by norm_num : (0 : ℝ) ≤ 2)
    have hq2 : q ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hq.le hqsmall' 2
    unfold actualSmallSetErrorPowerBound
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, one_mul, mul_one,
      one_add_one_eq_two]
    rw [hsqrt9]
    norm_num only
    calc
      14 * (2 * Real.exp 1 * (Real.exp 1 / 24) ^ 12) *
          1792160394037 * q ^ 2 ≤
        14 * (2 * 3 * (1 / 8 : ℝ) ^ 12) * 1792160394037 *
          (1 / 10000 : ℝ) ^ 2 := by
        gcongr
      _ ≤ 1 / 16 := by norm_num
  exact exists_scaledHostGood_of_power_bounds
    hq hq1 (by norm_num) (by norm_num) (by norm_num)
    hB₂ hB₃ hAlarge hscale hentropy hdense (by norm_num) hlocal
      hedge hpair htriple hsmall

/-- The unconditional graph-witness theorem at the shared recurrence
constant `C=8`. -/
theorem exists_q0_numeric_scaledHostGood_c8 :
    ∃ q₀ : ℝ, 0 < q₀ ∧ ∀ q : ℝ, 0 < q → q < q₀ →
      ∃ G : SimpleGraph (Fin (2 * queryBudget q 1)),
        HostGood G
          (edgeBudget q 8 (queryBudget q 1))
          (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 12
          (scaledPairBound q 12 (queryBudget q 1))
          (scaledTripleBound q 256 (queryBudget q 1)) := by
  refine ⟨1 / 10000, by norm_num, ?_⟩
  intro q hq hqsmall
  obtain ⟨w, hw⟩ := numeric_scaledHostGood_c8 hq hqsmall
  exact ⟨randomHost (2 * queryBudget q 1) w, hw⟩

/-- The exact finite witness expression after substituting all rounded
parameters from the paper. -/
noncomputable def scaledHostWitnessBound
    (q ell C A B₂ B₃ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (L : ℕ) : ℝ≥0∞ :=
  let N := queryBudget q ell
  let n := 2 * N
  let M := edgeBudget q C N
  let D := degeneracyBudget q A M
  hostWitnessBound (cubeProbability q hq0 hq1) n M D L
    (scaledPairBound q B₂ N) (scaledTripleBound q B₃ N)

/-- Fully instantiated finite random-host estimate at
`N=floor(ell/q^10)`, `M=ceil(C q^3 N)`, and
`D=ceil(A sqrt(q^3 M))`. -/
theorem measure_scaledRandomHostGoodEvent_compl_le
    (q ell C A B₂ B₃ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (L : ℕ) :
    let N := queryBudget q ell
    let n := 2 * N
    let M := edgeBudget q C N
    let D := degeneracyBudget q A M
    bitBoardMeasure (Sym2 (Fin n)) (cubeProbability q hq0 hq1)
        (randomHostGoodEvent n M D L
          (scaledPairBound q B₂ N) (scaledTripleBound q B₃ N))ᶜ ≤
      scaledHostWitnessBound q ell C A B₂ B₃ hq0 hq1 L := by
  dsimp [scaledHostWitnessBound]
  exact measure_randomHostGoodEvent_compl_le _ _ _ _ _ _ _

/-- Any concrete estimate of the explicit scaled witness expression
immediately yields the corresponding high-probability `HostGood` theorem. -/
theorem scaledRandomHostGood_of_witnessBound
    (q ell C A B₂ B₃ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (L : ℕ)
    (δ : ℝ≥0∞)
    (hbound : scaledHostWitnessBound q ell C A B₂ B₃ hq0 hq1 L ≤ δ) :
    let N := queryBudget q ell
    let n := 2 * N
    let M := edgeBudget q C N
    let D := degeneracyBudget q A M
    bitBoardMeasure (Sym2 (Fin n)) (cubeProbability q hq0 hq1)
        (randomHostGoodEvent n M D L
          (scaledPairBound q B₂ N) (scaledTripleBound q B₃ N))ᶜ ≤ δ := by
  exact (measure_scaledRandomHostGoodEvent_compl_le
    q ell C A B₂ B₃ hq0 hq1 L).trans hbound

/-! ## A polynomially small failure bound

For use inside an adaptive good/bad decomposition, mere positive probability
of a good host is not enough: the exceptional host mass is multiplied by a
crude six-vertex count.  The following estimates retain enough decay to
absorb that factor.  The constants are still deliberately conservative.
-/

/-- The negative power of two supplied by `entropyIndex` is already at most
`q^20`.  This elementary proof uses only `ceil(1/q) ≤ 2^ceil(1/q)` and does
not appeal to logarithms or an asymptotic library. -/
theorem entropy_halfPow_le_q_pow_twenty
    {q : ℝ} (hq : 0 < q) :
    (1 / 2 : ℝ) ^ entropyIndex q ≤ q ^ 20 := by
  let m : ℕ := ⌈1 / q⌉₊
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.ceil_pos.mpr (by positivity)
  have hm : 1 / q ≤ (m : ℝ) := by
    simpa [m] using Nat.le_ceil (1 / q)
  have hmtwoNat : m ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
  have hmtwo : (m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hmtwoNat
  have hhalf : (1 / 2 : ℝ) ^ m ≤ q := by
    have hinv_m : 1 / (m : ℝ) ≤ q := by
      rw [div_le_iff₀ (Nat.cast_pos.mpr hmpos)]
      have hqmul : q * (m : ℝ) ≥ 1 := by
        have ht := mul_le_mul_of_nonneg_left hm hq.le
        field_simp [ne_of_gt hq] at ht
        simpa [mul_comm] using ht
      simpa [mul_comm] using hqmul
    calc
      (1 / 2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := by rw [one_div_pow]
      _ ≤ 1 / (m : ℝ) :=
        one_div_le_one_div_of_le (Nat.cast_pos.mpr hmpos) hmtwo
      _ ≤ q := hinv_m
  calc
    (1 / 2 : ℝ) ^ entropyIndex q = ((1 / 2 : ℝ) ^ m) ^ 20 := by
      rw [← pow_mul]
      simp [entropyIndex, m]
    _ ≤ q ^ 20 := pow_le_pow_left₀ (by positivity) hhalf 20

/-- Four entropy blocks give eighty powers of `q`. -/
theorem entropy_four_halfPow_le_q_pow_eighty
    {q : ℝ} (hq : 0 < q) :
    (1 / 2 : ℝ) ^ (4 * entropyIndex q) ≤ q ^ 80 := by
  have h := entropy_halfPow_le_q_pow_twenty hq
  calc
    (1 / 2 : ℝ) ^ (4 * entropyIndex q) =
        ((1 / 2 : ℝ) ^ entropyIndex q) ^ 4 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ (q ^ 20) ^ 4 := pow_le_pow_left₀ (by positivity) h 4
    _ = q ^ 80 := by rw [← pow_mul]

/-- If the codegree cutoffs leave four full entropy blocks after absorbing
their polynomial prefactors, then the four host-failure contributions total
at most `4*q^80`. -/
theorem scaledHostFailureBoundReal_le_four_mul_q_pow_eighty_of_strong_bounds
    {q ell C A B₂ B₃ : ℝ} {L : ℕ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 ≤ ell)
    (hC : 0 < C) (hA : 0 ≤ A)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hentropySmall : 2 * Real.exp 1 * ell * q ^ 10 ≤ 1)
    (hdenseSmall : 160 * q ≤ A * √(C * ell / 2))
    (hedgeSmall : C * q ^ 3 ≤ 1)
    (hpairExponent : 2 * entropyIndex q + 4 * entropyIndex q ≤
      scaledPairBound q B₂ (queryBudget q ell) + 1)
    (htripleExponent : 3 * entropyIndex q + 4 * entropyIndex q ≤
      scaledTripleBound q B₃ (queryBudget q ell) + 1)
    (hsmallError :
      ((degeneracyBudget q A (edgeBudget q C (queryBudget q ell)) + 1 : ℕ) : ℝ) *
        actualSmallSetPowerBound q ell C A L ≤ q ^ 80) :
    scaledHostFailureBoundReal q ell C A B₂ B₃ L ≤ 4 * q ^ 80 := by
  let N := queryBudget q ell
  let M := edgeBudget q C N
  let D := degeneracyBudget q A M
  let s := entropyIndex q
  have hentropy : Real.exp 1 * ((2 * N : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by
    simpa [N, s] using actual_entropyCondition hq hell hentropySmall
  have hn : ((2 * N : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by
    calc
      ((2 * N : ℕ) : ℝ) ≤ Real.exp 1 * ((2 * N : ℕ) : ℝ) := by
        exact le_mul_of_one_le_left (Nat.cast_nonneg _)
          (Real.one_le_exp (by norm_num))
      _ ≤ (2 : ℝ) ^ s := hentropy
  have hq80 : (1 / 2 : ℝ) ^ (4 * s) ≤ q ^ 80 := by
    simpa [s] using entropy_four_halfPow_le_q_pow_eighty hq
  have hpair : ((2 * N : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) ≤ q ^ 80 := by
    refine (mul_halfPow_le_halfPow
      (x := ((2 * N : ℕ) : ℝ)) (j := 2)
      (r := scaledPairBound q B₂ N + 1) (s := s) (K := 4 * s)
      (Nat.cast_nonneg _) hn ?_).trans hq80
    simpa [N, s] using hpairExponent
  have htriple : ((2 * N : ℕ) : ℝ) ^ 3 *
      (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1) ≤ q ^ 80 := by
    refine (mul_halfPow_le_halfPow
      (x := ((2 * N : ℕ) : ℝ)) (j := 3)
      (r := scaledTripleBound q B₃ N + 1) (s := s) (K := 4 * s)
      (Nat.cast_nonneg _) hn ?_).trans hq80
    simpa [N, s] using htripleExponent
  have hq10 : 0 < q ^ 10 := pow_pos hq _
  have hq10le : q ^ 10 ≤ ell := by
    have : 0 ≤ q ^ 10 := hq10.le
    linarith
  have hNtarget : 1 ≤ ell / q ^ 10 :=
    (le_div_iff₀ hq10).2 (by simpa using hq10le)
  have hN : 0 < N := by
    dsimp [N, queryBudget]
    exact Nat.floor_pos.mpr hNtarget
  have hMN : M ≤ N := by
    apply (Nat.ceil_le).2
    change C * q ^ 3 * (N : ℝ) ≤ (N : ℝ)
    calc
      C * q ^ 3 * (N : ℝ) ≤ 1 * (N : ℝ) := by gcongr
      _ = (N : ℝ) := one_mul _
  have hspos : 0 < s := by
    dsimp [s, entropyIndex]
    exact Nat.mul_pos (Nat.ceil_pos.mpr (by positivity)) (by norm_num)
  have hs20 : 20 ≤ s := by
    dsimp [s, entropyIndex]
    have hm : 1 ≤ ⌈1 / q⌉₊ := Nat.ceil_pos.mpr (by positivity)
    omega
  have hlog : 4 * s ≤ D := by
    simpa [s, D, M, N] using actual_entropyIndex_le_degeneracyBudget
      hq hq1 hell hC hA hscale hdenseSmall
  have hDfive : 5 ≤ D := by omega
  have hdiv : 2 * M / D ≤ M := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right M (by omega : 2 ≤ D)
  have hcountNat : 2 * M / D + 1 ≤ 2 * N := by omega
  have hcount : ((2 * M / D + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by
    exact (by exact_mod_cast hcountNat :
      ((2 * M / D + 1 : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ)).trans hn
  have hdenseExponent : 1 * s + 4 * s ≤ s * D := by
    calc
      1 * s + 4 * s = s * 5 := by omega
      _ ≤ s * D := Nat.mul_le_mul_left s hDfive
  have hdense : ((2 * M / D + 1 : ℕ) : ℝ) *
      (1 / 2 : ℝ) ^ (s * D) ≤ q ^ 80 := by
    simpa using (mul_halfPow_le_halfPow
      (x := ((2 * M / D + 1 : ℕ) : ℝ)) (j := 1)
      (r := s * D) (s := s) (K := 4 * s)
      (Nat.cast_nonneg _) hcount hdenseExponent).trans hq80
  change
    (((2 * N : ℕ) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) +
      ((2 * N : ℕ) : ℝ) ^ 3 *
        (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1)) +
    ((2 * M / D + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (s * D) +
    ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L ≤ _
  calc
    (((2 * N : ℕ) : ℝ) ^ 2 *
          (1 / 2 : ℝ) ^ (scaledPairBound q B₂ N + 1) +
        ((2 * N : ℕ) : ℝ) ^ 3 *
          (1 / 2 : ℝ) ^ (scaledTripleBound q B₃ N + 1)) +
      ((2 * M / D + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (s * D) +
      ((D + 1 : ℕ) : ℝ) * actualSmallSetPowerBound q ell C A L ≤
        (q ^ 80 + q ^ 80) + q ^ 80 + q ^ 80 := by
      exact add_le_add (add_le_add (add_le_add hpair htriple) hdense)
        (by simpa [D, M, N] using hsmallError)
    _ = 4 * q ^ 80 := by ring

/-- At `q≤1/2`, the ten spare powers absorb the factor four. -/
theorem four_mul_q_pow_eighty_le_q_pow_seventy
    {q : ℝ} (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    4 * q ^ 80 ≤ q ^ 70 := by
  have hq10 : 4 * q ^ 10 ≤ 1 := by
    calc
      4 * q ^ 10 ≤ 4 * (1 / 2 : ℝ) ^ 10 := by gcongr
      _ ≤ 1 := by norm_num
  calc
    4 * q ^ 80 = (4 * q ^ 10) * q ^ 70 := by ring
    _ ≤ 1 * q ^ 70 := by gcongr
    _ = q ^ 70 := one_mul _

/-- A strong pair-codegree exponent estimate at the numeric scale. -/
theorem numeric_pairExponent_strong
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hcut : 240 * q ^ 3 ≤ 12 * (1 - q ^ 10)) :
    2 * entropyIndex q + 4 * entropyIndex q ≤
      scaledPairBound q 12 (queryBudget q 1) + 1 := by
  let N := queryBudget q 1
  let s := entropyIndex q
  have hs : (s : ℝ) ≤ 40 / q := by
    simpa [s] using entropyIndex_cast_le hq hq1
  have hleft : ((6 * s : ℕ) : ℝ) ≤ 240 / q := by
    calc
      ((6 * s : ℕ) : ℝ) = 6 * (s : ℝ) := by norm_num
      _ ≤ 6 * (40 / q) := by gcongr
      _ = 240 / q := by ring
  have hq4 : 0 < q ^ 4 := pow_pos hq _
  have hcut' : 240 / q ≤ 12 * (1 - q ^ 10) / q ^ 4 := by
    calc
      240 / q = (240 * q ^ 3) / q ^ 4 := by
        field_simp [ne_of_gt hq, ne_of_gt hq4]
      _ ≤ 12 * (1 - q ^ 10) / q ^ 4 :=
        div_le_div_of_nonneg_right hcut hq4.le
  have hNlower : 1 - q ^ 10 < q ^ 10 * (N : ℝ) := by
    simpa [N] using
      (normalized_queryBudget_bounds hq (by norm_num : (0 : ℝ) ≤ 1)).1
  have hscale : 12 * (1 - q ^ 10) / q ^ 4 <
      12 * q ^ 6 * (N : ℝ) := by
    calc
      12 * (1 - q ^ 10) / q ^ 4 <
          12 * (q ^ 10 * (N : ℝ)) / q ^ 4 := by gcongr
      _ = 12 * q ^ 6 * (N : ℝ) := by
        field_simp [ne_of_gt hq, ne_of_gt hq4]
  have hreal : ((6 * s : ℕ) : ℝ) < 12 * q ^ 6 * (N : ℝ) :=
    hleft.trans_lt (hcut'.trans_lt hscale)
  have hceil : 12 * q ^ 6 * (N : ℝ) ≤
      (scaledPairBound q 12 N : ℝ) := Nat.le_ceil _
  have hnat : 6 * s < scaledPairBound q 12 N := by
    exact_mod_cast hreal.trans_le hceil
  simpa [s, N] using
    (show 2 * s + 4 * s ≤ scaledPairBound q 12 N + 1 by omega)

/-- A strong triple-codegree exponent estimate at the numeric scale. -/
theorem numeric_tripleExponent_strong
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hcut : 280 ≤ 512 * (1 - q ^ 10)) :
    3 * entropyIndex q + 4 * entropyIndex q ≤
      scaledTripleBound q 512 (queryBudget q 1) + 1 := by
  let N := queryBudget q 1
  let s := entropyIndex q
  have hs : (s : ℝ) ≤ 40 / q := by
    simpa [s] using entropyIndex_cast_le hq hq1
  have hleft : ((7 * s : ℕ) : ℝ) ≤ 280 / q := by
    calc
      ((7 * s : ℕ) : ℝ) = 7 * (s : ℝ) := by norm_num
      _ ≤ 7 * (40 / q) := by gcongr
      _ = 280 / q := by ring
  have hcut' : 280 / q ≤ 512 * (1 - q ^ 10) / q :=
    div_le_div_of_nonneg_right hcut hq.le
  have hNlower : 1 - q ^ 10 < q ^ 10 * (N : ℝ) := by
    simpa [N] using
      (normalized_queryBudget_bounds hq (by norm_num : (0 : ℝ) ≤ 1)).1
  have hscale : 512 * (1 - q ^ 10) / q <
      512 * q ^ 9 * (N : ℝ) := by
    calc
      512 * (1 - q ^ 10) / q <
          512 * (q ^ 10 * (N : ℝ)) / q := by gcongr
      _ = 512 * q ^ 9 * (N : ℝ) := by
        field_simp [ne_of_gt hq]
  have hreal : ((7 * s : ℕ) : ℝ) < 512 * q ^ 9 * (N : ℝ) :=
    hleft.trans_lt (hcut'.trans_lt hscale)
  have hceil : 512 * q ^ 9 * (N : ℝ) ≤
      (scaledTripleBound q 512 N : ℝ) := Nat.le_ceil _
  have hnat : 7 * s < scaledTripleBound q 512 N := by
    exact_mod_cast hreal.trans_le hceil
  simpa [s, N] using
    (show 3 * s + 4 * s ≤ scaledTripleBound q 512 N + 1 by omega)

/- The complete small-set contribution at `C=8,A=4,L=90` is at most
`q^80`. -/
set_option maxRecDepth 10000 in
theorem numeric_smallSetErrorPowerBound_c8_L90 {q : ℝ} :
    actualSmallSetErrorPowerBound q 1 8 4 90 ≤ q ^ 80 := by
  have he3 : Real.exp 1 ≤ 3 :=
    (lt_trans Real.exp_one_lt_d9 (by norm_num)).le
  have hsqrt9 : √(9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hbase : Real.exp 1 / 180 ≤ 1 / 60 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 180)).2
    nlinarith
  have hbasePow : (Real.exp 1 / 180) ^ 90 ≤ (1 / 60 : ℝ) ^ 90 :=
    pow_le_pow_left₀ (by positivity) hbase 90
  have hcoef :
      14 * (2 * Real.exp 1 * (Real.exp 1 / 180) ^ 90) * 13 ^ 89 ≤
        (1 : ℝ) := by
    calc
      14 * (2 * Real.exp 1 * (Real.exp 1 / 180) ^ 90) * 13 ^ 89 ≤
          14 * (2 * 3 * (1 / 60 : ℝ) ^ 90) * 13 ^ 89 := by
        gcongr
      _ ≤ 1 := by norm_num
  unfold actualSmallSetErrorPowerBound
  simp only [Nat.cast_ofNat, Nat.reduceSub, mul_one]
  rw [show (8 : ℝ) + 1 = 9 by norm_num, hsqrt9,
    show (2 : ℝ) * 90 = 180 by norm_num]
  norm_num only [mul_one, one_mul, add_comm, add_left_comm, add_assoc,
    OfNat.ofNat, Nat.cast_ofNat]
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ q ^ 80 by positivity)
  norm_num only [one_mul] at hmul
  exact hmul

/-- Fully numeric high-probability host estimate.  Unlike the earlier
existence theorem, this retains a `q^70` exceptional-mass bound, sufficient
to absorb a crude `(2N)^6` count when `N≤q⁻¹⁰`. -/
theorem measure_numericRandomHostGoodEvent_c8_compl_toReal_le_q70
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 10000) :
    (bitBoardMeasure (Sym2 (Fin (2 * queryBudget q 1)))
      (cubeProbability q hq.le (hqsmall.le.trans (by norm_num)))
      (randomHostGoodEvent (2 * queryBudget q 1)
        (edgeBudget q 8 (queryBudget q 1))
        (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 90
        (scaledPairBound q 12 (queryBudget q 1))
        (scaledTripleBound q 512 (queryBudget q 1)))ᶜ).toReal ≤ q ^ 70 := by
  have hq1 : q ≤ 1 := hqsmall.le.trans (by norm_num)
  have hqsmall' : q ≤ 1 / 10000 := hqsmall.le
  have hqhalf : q ≤ 1 / 2 := hqsmall'.trans (by norm_num)
  have hqpow : ∀ n : ℕ, 0 < n → q ^ n ≤ q := by
    intro n hn
    simpa using pow_le_pow_of_le_one hq.le hq1
      (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have he3 : Real.exp 1 ≤ 3 :=
    (lt_trans Real.exp_one_lt_d9 (by norm_num)).le
  have hsqrt4 : √(4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hsqrt9 : √(9 : ℝ) = 3 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hB₂ : 4 * Real.exp 1 ≤ (12 : ℝ) := by nlinarith
  have hB₃ : 4 * Real.exp 1 ≤ (512 : ℝ) := by nlinarith
  have hAlarge : 4 * Real.exp 1 ≤ (4 : ℝ) ^ 2 := by nlinarith
  have hscale : 2 * q ^ 10 ≤ (1 : ℝ) := by
    calc
      2 * q ^ 10 ≤ 2 * (1 / 10000 : ℝ) := by
        gcongr
        exact (hqpow 10 (by omega)).trans hqsmall'
      _ ≤ 1 := by norm_num
  have hentropy : 2 * Real.exp 1 * (1 : ℝ) * q ^ 10 ≤ 1 := by
    calc
      2 * Real.exp 1 * (1 : ℝ) * q ^ 10 ≤
          2 * 3 * 1 * (1 / 10000 : ℝ) := by
        gcongr
        exact (hqpow 10 (by omega)).trans hqsmall'
      _ ≤ 1 := by norm_num
  have hdense : 160 * q ≤ (4 : ℝ) * √((8 : ℝ) * 1 / 2) := by
    rw [show (8 : ℝ) * 1 / 2 = 4 by norm_num, hsqrt4]
    nlinarith
  have hlocal : Real.exp 1 * ((4 : ℝ) * √((8 : ℝ) * 1 + 1) + 1) * q ≤
      2 * (90 : ℝ) := by
    rw [show (8 : ℝ) * 1 + 1 = 9 by norm_num, hsqrt9]
    calc
      Real.exp 1 * (4 * 3 + 1) * q ≤ 3 * 13 * (1 / 10000 : ℝ) := by
        gcongr
        norm_num
      _ ≤ 2 * (90 : ℝ) := by norm_num
  have hedge : (8 : ℝ) * q ^ 3 ≤ 1 := by
    calc
      (8 : ℝ) * q ^ 3 ≤ 8 * (1 / 10000 : ℝ) := by
        gcongr
        exact (hqpow 3 (by omega)).trans hqsmall'
      _ ≤ 1 := by norm_num
  have hpairCut : 240 * q ^ 3 ≤ 12 * (1 - q ^ 10) := by
    have hq3 := (hqpow 3 (by omega)).trans hqsmall'
    have hq10 := (hqpow 10 (by omega)).trans hqsmall'
    nlinarith
  have htripleCut : 280 ≤ 512 * (1 - q ^ 10) := by
    have hq10 := (hqpow 10 (by omega)).trans hqsmall'
    nlinarith
  have hpair := numeric_pairExponent_strong hq hq1 hpairCut
  have htriple := numeric_tripleExponent_strong hq hq1 htripleCut
  have hsmallError :
      ((degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1)) + 1 : ℕ) : ℝ) *
        actualSmallSetPowerBound q 1 8 4 90 ≤ q ^ 80 :=
    (actual_smallSetErrorPowerBound hq hq1 (by norm_num) (by norm_num)
      (by norm_num) hscale (by norm_num : 10 ≤ 90)).trans
        numeric_smallSetErrorPowerBound_c8_L90
  have hpower0 : 0 ≤ actualSmallSetPowerBound q 1 8 4 90 := by
    unfold actualSmallSetPowerBound
    positivity
  have hpower_le_product : actualSmallSetPowerBound q 1 8 4 90 ≤
      ((degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1)) + 1 : ℕ) : ℝ) *
        actualSmallSetPowerBound q 1 8 4 90 := by
    exact le_mul_of_one_le_left hpower0 (by norm_num)
  have hpower1 : actualSmallSetPowerBound q 1 8 4 90 ≤ 1 := by
    calc
      actualSmallSetPowerBound q 1 8 4 90 ≤
          ((degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1)) + 1 : ℕ) : ℝ) *
            actualSmallSetPowerBound q 1 8 4 90 := hpower_le_product
      _ ≤ q ^ 80 := hsmallError
      _ ≤ 1 := pow_le_one₀ hq.le hq1
  have hmeasure := measure_scaledRandomHostGoodEvent_compl_toReal_le_explicit
    (q := q) (ell := 1) (C := 8) (A := 4) (B₂ := 12) (B₃ := 512) (L := 90)
    hq hq1 (by norm_num) (by norm_num) (by norm_num) hB₂ hB₃ hAlarge
      hscale hentropy hdense (by norm_num) hlocal hpower1
  have hfailure : scaledHostFailureBoundReal q 1 8 4 12 512 90 ≤
      4 * q ^ 80 :=
    scaledHostFailureBoundReal_le_four_mul_q_pow_eighty_of_strong_bounds
      hq hq1 (by norm_num) (by norm_num) (by norm_num) hscale hentropy
        hdense hedge hpair htriple hsmallError
  exact hmeasure.trans
    (hfailure.trans (four_mul_q_pow_eighty_le_q_pow_seventy hq.le hqhalf))

/-- `ENNReal` form of the numeric `q^70` bad-host estimate. -/
theorem measure_numericRandomHostGoodEvent_c8_compl_le_ofReal_q70
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 10000) :
    bitBoardMeasure (Sym2 (Fin (2 * queryBudget q 1)))
      (cubeProbability q hq.le (hqsmall.le.trans (by norm_num)))
      (randomHostGoodEvent (2 * queryBudget q 1)
        (edgeBudget q 8 (queryBudget q 1))
        (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 90
        (scaledPairBound q 12 (queryBudget q 1))
        (scaledTripleBound q 512 (queryBudget q 1)))ᶜ ≤
      ENNReal.ofReal (q ^ 70) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ q ^ 70)]
  exact measure_numericRandomHostGoodEvent_c8_compl_toReal_le_q70 hq hqsmall

/-- The preceding `q^70` estimate after multiplication by the crude number
of labelled six-vertex maps.  Since `N=floor(q⁻¹⁰)`, sixty powers are spent
and ten powers remain.  This is the form used directly by the adaptive
good/bad decomposition. -/
theorem measure_numericRandomHostGoodEvent_c8_crudeSixVertex_le
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 10000) :
    ((2 * queryBudget q 1 : ℕ) : ℝ) ^ 6 *
      (bitBoardMeasure (Sym2 (Fin (2 * queryBudget q 1)))
        (cubeProbability q hq.le (hqsmall.le.trans (by norm_num)))
        (randomHostGoodEvent (2 * queryBudget q 1)
          (edgeBudget q 8 (queryBudget q 1))
          (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 90
          (scaledPairBound q 12 (queryBudget q 1))
          (scaledTripleBound q 512 (queryBudget q 1)))ᶜ).toReal ≤
        64 * q ^ 10 := by
  have hN := queryBudget_cast_le_target hq (by norm_num : (0 : ℝ) ≤ 1)
  have hcount : ((2 * queryBudget q 1 : ℕ) : ℝ) ^ 6 ≤
      (2 / q ^ 10) ^ 6 := by
    have hbase : ((2 * queryBudget q 1 : ℕ) : ℝ) ≤ 2 / q ^ 10 := by
      calc
        ((2 * queryBudget q 1 : ℕ) : ℝ) =
            2 * (queryBudget q 1 : ℝ) := by push_cast; ring
        _ ≤ 2 * (1 / q ^ 10) := by gcongr
        _ = 2 / q ^ 10 := by ring
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbase 6
  have hprob := measure_numericRandomHostGoodEvent_c8_compl_toReal_le_q70
    hq hqsmall
  calc
    ((2 * queryBudget q 1 : ℕ) : ℝ) ^ 6 *
        (bitBoardMeasure (Sym2 (Fin (2 * queryBudget q 1)))
          (cubeProbability q hq.le (hqsmall.le.trans (by norm_num)))
          (randomHostGoodEvent (2 * queryBudget q 1)
            (edgeBudget q 8 (queryBudget q 1))
            (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 90
            (scaledPairBound q 12 (queryBudget q 1))
            (scaledTripleBound q 512 (queryBudget q 1)))ᶜ).toReal ≤
        (2 / q ^ 10) ^ 6 * q ^ 70 := by
      exact mul_le_mul hcount hprob ENNReal.toReal_nonneg (by positivity)
    _ = 64 * q ^ 10 := by
      field_simp [ne_of_gt hq]
      ring

/-- `ENNReal` form of the host-bad-mass estimate after the crude labelled
six-vertex factor has already been applied. -/
theorem measure_numericRandomHostGoodEvent_c8_crudeSixVertex_le_ofReal
    {q : ℝ} (hq : 0 < q) (hqsmall : q < 1 / 10000) :
    (((2 * queryBudget q 1 : ℕ) ^ 6 : ℕ) : ℝ≥0∞) *
      bitBoardMeasure (Sym2 (Fin (2 * queryBudget q 1)))
        (cubeProbability q hq.le (hqsmall.le.trans (by norm_num)))
        (randomHostGoodEvent (2 * queryBudget q 1)
          (edgeBudget q 8 (queryBudget q 1))
          (degeneracyBudget q 4 (edgeBudget q 8 (queryBudget q 1))) 90
          (scaledPairBound q 12 (queryBudget q 1))
          (scaledTripleBound q 512 (queryBudget q 1)))ᶜ ≤
      ENNReal.ofReal (64 * q ^ 10) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by finiteness))
      ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 64 * q ^ 10)]
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
    measure_numericRandomHostGoodEvent_c8_crudeSixVertex_le hq hqsmall

end HostGoodProbability
end OnlineRamsey
