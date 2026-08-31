import OnlineRamsey.AllCasesHistoryCount

/-!
# Choosing the fixed small query-scale constant

The uniform four-case coefficient contains one term proportional to
`ell⁻¹`, coming from the isolated vertex in the `K₅-e` branch.  After
the cubic query-scale factor is applied, this contributes only `ell²`; all
other main terms contribute `ell³`.  Consequently one fixed positive `ell`
makes the complete deterministic all-orders contribution arbitrarily small.
-/

open scoped ENNReal NNReal
open Filter Topology

namespace OnlineRamsey
namespace SmallEllMainCoefficient

open AllCasesHistoryCount OrdinaryAllOrders

noncomputable section

/-- The four-case coefficient before coercion to `ENNReal`. -/
def allCasesCoefficientNN (ell : ℝ≥0) : ℝ≥0 :=
  ordinaryUniformCoefficient + 13271040 + 13934592000 / ell + 3583180800

theorem ofReal_k5Coefficient_eq_coe (ell : ℝ≥0) :
    ENNReal.ofReal (13934592000 / (ell : ℝ)) =
      ((13934592000 / ell : ℝ≥0) : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1

theorem allCasesCoefficient_eq_coe (ell : ℝ≥0) :
    allCasesCoefficient ell = (allCasesCoefficientNN ell : ℝ≥0∞) := by
  simp only [allCasesCoefficient, allCasesCoefficientNN, NNReal.coe_add,
    ENNReal.coe_add, ofReal_k5Coefficient_eq_coe]
  norm_num

/-- The exact polynomial form after multiplying by `ell³`, valid on the
punctured positive neighborhood used in the lower-bound choice. -/
theorem coefficient_mul_cube_eq_polynomial {ell : ℝ≥0} (hell : 0 < ell) :
    allCasesCoefficientNN ell * ell ^ 3 =
      (ordinaryUniformCoefficient + 13271040 + 3583180800) * ell ^ 3 +
        13934592000 * ell ^ 2 := by
  unfold allCasesCoefficientNN
  field_simp [ne_of_gt hell]
  ring

/-- The deterministic all-orders main term tends to zero as the fixed scale
constant tends to zero from above. -/
theorem factorial_mul_allCasesCoefficient_mul_cube_tendsto_zero :
    Tendsto (fun ell : ℝ≥0 ↦
      (Nat.factorial 15 : ℝ≥0∞) * allCasesCoefficient ell *
        (ell : ℝ≥0∞) ^ 3) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun ell : ℝ≥0 ↦ ell) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hpolyNN : Tendsto (fun ell : ℝ≥0 ↦
      (Nat.factorial 15 : ℝ≥0) *
        ((ordinaryUniformCoefficient + 13271040 + 3583180800) * ell ^ 3 +
          13934592000 * ell ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have hthree := (hid.pow 3).const_mul
      (ordinaryUniformCoefficient + 13271040 + 3583180800)
    have htwo := (hid.pow 2).const_mul (13934592000 : ℝ≥0)
    simpa using (hthree.add htwo).const_mul (Nat.factorial 15 : ℝ≥0)
  have heqNN : (∀ᶠ ell in 𝓝[>] (0 : ℝ≥0),
      (Nat.factorial 15 : ℝ≥0) * allCasesCoefficientNN ell * ell ^ 3 =
        (Nat.factorial 15 : ℝ≥0) *
          ((ordinaryUniformCoefficient + 13271040 + 3583180800) * ell ^ 3 +
            13934592000 * ell ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with ell hell
    rw [mul_assoc, coefficient_mul_cube_eq_polynomial hell]
  have hmainNN : Tendsto (fun ell : ℝ≥0 ↦
      (Nat.factorial 15 : ℝ≥0) * allCasesCoefficientNN ell * ell ^ 3)
      (𝓝[>] 0) (𝓝 0) :=
    hpolyNN.congr' (heqNN.mono fun _ h ↦ h.symm)
  have hcoe := ENNReal.tendsto_coe.mpr hmainNN
  simpa only [allCasesCoefficient_eq_coe, NNReal.coe_mul, NNReal.coe_pow,
    ENNReal.coe_mul, ENNReal.coe_pow, Nat.cast_ofNat] using hcoe

/-- A fixed positive `ell ≤ 1` for which the deterministic main term of
all `15!` relative orders is below one quarter. -/
theorem exists_smallEll_main_lt_quarter :
    ∃ ell : ℝ≥0, 0 < ell ∧ ell ≤ 1 ∧
      (Nat.factorial 15 : ℝ≥0∞) * allCasesCoefficient ell *
          (ell : ℝ≥0∞) ^ 3 < (4 : ℝ≥0∞)⁻¹ := by
  let f : ℝ≥0 → ℝ≥0∞ := fun ell ↦
    (Nat.factorial 15 : ℝ≥0∞) * allCasesCoefficient ell *
      (ell : ℝ≥0∞) ^ 3
  have ht : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    simpa [f] using factorial_mul_allCasesCoefficient_mul_cube_tendsto_zero
  have hsmall : ∀ᶠ ell in 𝓝[>] (0 : ℝ≥0), f ell < (4 : ℝ≥0∞)⁻¹ :=
    (tendsto_order.mp ht).2 _ (by norm_num)
  have hid : Tendsto (fun ell : ℝ≥0 ↦ ell) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hone : ∀ᶠ ell in 𝓝[>] (0 : ℝ≥0), ell < 1 :=
    (tendsto_order.mp hid).2 1 (by norm_num)
  rcases (hsmall.and (hone.and self_mem_nhdsWithin)).exists with
    ⟨ell, hmain, hellOne, hellPos⟩
  exact ⟨ell, hellPos, hellOne.le, by simpa [f] using hmain⟩

end
end SmallEllMainCoefficient
end OnlineRamsey
