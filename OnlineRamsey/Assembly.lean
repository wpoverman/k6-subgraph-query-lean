import Mathlib.GroupTheory.Perm.Fin
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite expectation and final-assembly lemmas

This file contains the measure-theoretic bookkeeping used after the graph and
random-board estimates have been proved.  The statements are deliberately
finite and non-asymptotic: they apply to any finite family of ordered-copy
counts and to any measurable good event.  In particular, no independence is
assumed between the good host event and the adaptively selected transcript.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace OnlineRamsey

universe u v

section OrderedDecomposition

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]

/-- Integrating a finite ordered decomposition and bounding each summand. -/
theorem lintegral_finset_sum_le (μ : Measure Ω) (s : Finset ι)
    (X : ι → Ω → ℝ≥0∞) (B : ι → ℝ≥0∞)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hB : ∀ i ∈ s, (∫⁻ ω, X i ω ∂μ) ≤ B i) :
    (∫⁻ ω, ∑ i ∈ s, X i ω ∂μ) ≤ ∑ i ∈ s, B i := by
  rw [lintegral_finset_sum' s hX]
  exact Finset.sum_le_sum fun i hi ↦ hB i hi

/-- A pointwise partition may be substituted before applying the sum bound. -/
theorem lintegral_partition_le (μ : Measure Ω) (s : Finset ι)
    (total : Ω → ℝ≥0∞) (part : ι → Ω → ℝ≥0∞) (B : ι → ℝ≥0∞)
    (hpartition : ∀ ω, total ω = ∑ i ∈ s, part i ω)
    (hpart : ∀ i ∈ s, AEMeasurable (part i) μ)
    (hB : ∀ i ∈ s, (∫⁻ ω, part i ω ∂μ) ≤ B i) :
    (∫⁻ ω, total ω ∂μ) ≤ ∑ i ∈ s, B i := by
  have hfun : total = fun ω ↦ ∑ i ∈ s, part i ω := funext hpartition
  rw [hfun]
  exact lintegral_finset_sum_le μ s part B hpart hB

/-- Relative query orders of the fifteen edges of a labeled `K₆`. -/
abbrev K6EdgeOrder := Equiv.Perm (Fin 15)

theorem card_k6EdgeOrder : Fintype.card K6EdgeOrder = Nat.factorial 15 := by
  simp [K6EdgeOrder, Fintype.card_perm]

/--
Summing a uniform bound over a finite type containing exactly `15!` orders.
Together with `card_k6EdgeOrder`, this applies to relative orders of `K₆`.
The index type is left abstract here to keep the theorem kernel-light: unfolding
the standard `Fintype` enumeration of all permutations of fifteen elements
constructs a list of length `15!` during compilation.
-/
theorem sum_over_k6_orders_le {Order : Type v} [Fintype Order]
    (hcard : Fintype.card Order = Nat.factorial 15)
    (x : Order → ℝ≥0∞) (B : ℝ≥0∞) (hx : ∀ π, x π ≤ B) :
    (∑ π, x π) ≤ (Nat.factorial 15 : ℕ) * B := by
  calc
    (∑ π, x π) ≤ ∑ _π : Order, B :=
      Finset.sum_le_sum fun i _hi ↦ hx i
    _ = (Fintype.card Order : ℕ) * B := by simp
    _ = (Nat.factorial 15 : ℕ) * B := by rw [hcard]

end OrderedDecomposition

section GoodBad

variable {Ω : Type u} [MeasurableSpace Ω]

/--
Pointwise good/bad truncation.  This is the precise form needed for the
adaptive exceptional-copy bounds: the good event may depend arbitrarily on
the same random host which drives the strategy.
-/
theorem lintegral_le_good_bad (μ : Measure Ω) (X : Ω → ℝ≥0∞)
    (good : Set Ω) (B U : ℝ≥0∞) (hgoodMeas : MeasurableSet good)
    (hgood : ∀ ω ∈ good, X ω ≤ B) (hall : ∀ ω, X ω ≤ U) :
    (∫⁻ ω, X ω ∂μ) ≤ B * μ good + U * μ goodᶜ := by
  have hpoint : ∀ ω,
      X ω ≤ good.indicator (fun _ ↦ B) ω + goodᶜ.indicator (fun _ ↦ U) ω := by
    intro ω
    by_cases hω : ω ∈ good
    · simpa [hω] using hgood ω hω
    · simpa [hω] using hall ω
  calc
    (∫⁻ ω, X ω ∂μ) ≤
        ∫⁻ ω, good.indicator (fun _ ↦ B) ω +
          goodᶜ.indicator (fun _ ↦ U) ω ∂μ := lintegral_mono hpoint
    _ = (∫⁻ ω, good.indicator (fun _ ↦ B) ω ∂μ) +
          ∫⁻ ω, goodᶜ.indicator (fun _ ↦ U) ω ∂μ := by
            rw [lintegral_add_left]
            exact measurable_const.indicator hgoodMeas
    _ = B * μ good + U * μ goodᶜ := by
      rw [lintegral_indicator_const hgoodMeas,
        lintegral_indicator_const hgoodMeas.compl]

/-- The common probability-measure corollary `E X ≤ B + U P[bad]`. -/
theorem lintegral_le_bound_add_bad (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ≥0∞) (good : Set Ω) (B U : ℝ≥0∞)
    (hgoodMeas : MeasurableSet good)
    (hgood : ∀ ω ∈ good, X ω ≤ B) (hall : ∀ ω, X ω ≤ U) :
    (∫⁻ ω, X ω ∂μ) ≤ B + U * μ goodᶜ := by
  refine (lintegral_le_good_bad μ X good B U hgoodMeas hgood hall).trans ?_
  have hgood_le : μ good ≤ 1 := by
    calc
      μ good ≤ μ Set.univ := measure_mono (Set.subset_univ good)
      _ = 1 := measure_univ
  calc
    B * μ good + U * μ goodᶜ ≤ B * 1 + U * μ goodᶜ := by gcongr
    _ = B + U * μ goodᶜ := by simp

end GoodBad

section Markov

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Markov's inequality at the threshold one, in the exact form used here. -/
theorem success_measure_le_expectation (μ : Measure Ω) (X : Ω → ℝ≥0∞)
    (hX : AEMeasurable X μ) :
    μ {ω | 1 ≤ X ω} ≤ ∫⁻ ω, X ω ∂μ := by
  exact meas_le_lintegral₀ hX fun _ω hω ↦ hω

/-- Expected copy count below `1/2` implies success probability below `1/2`. -/
theorem success_measure_lt_half (μ : Measure Ω) (X : Ω → ℝ≥0∞)
    (hX : AEMeasurable X μ)
    (hmean : (∫⁻ ω, X ω ∂μ) < (1 / 2 : ℝ≥0∞)) :
    μ {ω | 1 ≤ X ω} < (1 / 2 : ℝ≥0∞) :=
  (success_measure_le_expectation μ X hX).trans_lt hmean

/-- For a natural copy count, positivity is exactly the Markov event at one. -/
theorem natCast_one_le_iff_pos (n : ℕ) :
    (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) ↔ 0 < n := by
  norm_cast

end Markov

section ThresholdAlgebra

/--
Writing `p = q^3` removes fractional exponents.  The threshold inequality
`q^10 * N ≤ λ` immediately gives `p^10 * N^3 ≤ λ^3`.
-/
theorem threshold_monomial_bound {q n ell : ℝ} (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hscale : q ^ 10 * n ≤ ell) :
    q ^ 30 * n ^ 3 ≤ ell ^ 3 := by
  have hnonneg : 0 ≤ q ^ 10 * n := mul_nonneg (pow_nonneg hq _) hn
  calc
    q ^ 30 * n ^ 3 = (q ^ 10 * n) ^ 3 := by ring
    _ ≤ ell ^ 3 := pow_le_pow_left₀ hnonneg hscale 3

/-- A vanishing error smaller than the remaining gap preserves `< 1/2`. -/
theorem absorb_error_below_half {main error : ℝ}
    (hmain : main < 1 / 2) (herror : error < 1 / 2 - main) :
    main + error < 1 / 2 := by
  have _hgap : 0 < 1 / 2 - main := sub_pos.mpr hmain
  linarith

end ThresholdAlgebra

end OnlineRamsey
