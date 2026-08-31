import OnlineRamsey.K4OneTrial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact finite amplification of independent trials

This file proves the product calculation used to amplify a one-trial success
probability.  The probability space is completely explicit: a point is a
function assigning one finite outcome to each trial, and its mass is the
product of the one-trial point masses.

The generic calculation is then instantiated with the finite Bernoulli graph
board from `K4OneTrial.lean`.  With `184320 * a^2` independent copies, the
probability that every copy fails is at most `exp (-1)`.

The construction of those independent copies inside the adaptive
branch-and-fill strategy is intentionally outside this file.
-/

namespace OnlineRamsey
namespace Amplification

open scoped ENNReal

universe u

section FiniteProduct

variable {Ω : Type u} [Fintype Ω]

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Product point mass of a vector of `t` independent finite outcomes. -/
noncomputable def outcomeVectorWeight (weight : Ω → ℝ≥0∞) {t : ℕ}
    (outcomes : Fin t → Ω) : ℝ≥0∞ :=
  ∏ i, weight (outcomes i)

/-- Mass of an event in the explicit `t`-fold finite product. -/
noncomputable def finiteOutcomeProductMass (weight : Ω → ℝ≥0∞) (t : ℕ)
    (event : Set (Fin t → Ω)) : ℝ≥0∞ :=
  ∑ outcomes : Fin t → Ω,
    if outcomes ∈ event then outcomeVectorWeight weight outcomes else 0

/-- The event that none of the `t` outcomes satisfies `success`. -/
def allTrialsFailEvent (success : Ω → Prop) (t : ℕ) : Set (Fin t → Ω) :=
  {outcomes | ∀ i, ¬ success (outcomes i)}

/-- One-trial success mass, as an explicit finite sum. -/
noncomputable def oneTrialSuccessMass (weight : Ω → ℝ≥0∞)
    (success : Ω → Prop) : ℝ≥0∞ :=
  ∑ outcome : Ω, if success outcome then weight outcome else 0

/-- One-trial failure mass, as an explicit finite sum. -/
noncomputable def oneTrialFailureMass (weight : Ω → ℝ≥0∞)
    (success : Ω → Prop) : ℝ≥0∞ :=
  ∑ outcome : Ω, if success outcome then 0 else weight outcome

/-- Success and failure partition the total one-trial mass. -/
theorem oneTrialSuccessMass_add_failureMass (weight : Ω → ℝ≥0∞)
    (success : Ω → Prop) :
    oneTrialSuccessMass weight success + oneTrialFailureMass weight success =
      ∑ outcome : Ω, weight outcome := by
  classical
  unfold oneTrialSuccessMass oneTrialFailureMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro outcome _houtcome
  by_cases h : success outcome <;> simp [h]

/-- Under a normalized one-trial mass, failure has mass `1 - success`. -/
theorem oneTrialFailureMass_eq_one_sub (weight : Ω → ℝ≥0∞)
    (success : Ω → Prop) (hnormalized : (∑ outcome : Ω, weight outcome) = 1) :
    oneTrialFailureMass weight success = 1 - oneTrialSuccessMass weight success := by
  have hpartition := oneTrialSuccessMass_add_failureMass weight success
  rw [hnormalized] at hpartition
  apply ENNReal.eq_sub_of_add_eq
  · have hle : oneTrialSuccessMass weight success ≤ 1 := by
      rw [← hpartition]
      exact le_add_of_nonneg_right bot_le
    exact (lt_top_iff_ne_top.mp (hle.trans_lt ENNReal.one_lt_top))
  · simpa [add_comm] using hpartition

/-- Exact independent-trial identity: all `t` trials fail with the `t`-th
power of the one-trial failure mass. -/
theorem finiteOutcomeProductMass_allTrialsFail (weight : Ω → ℝ≥0∞)
    (success : Ω → Prop) (t : ℕ) :
    finiteOutcomeProductMass weight t (allTrialsFailEvent success t) =
      oneTrialFailureMass weight success ^ t := by
  classical
  unfold finiteOutcomeProductMass outcomeVectorWeight allTrialsFailEvent
  calc
    _ =
        ∑ outcomes : Fin t → Ω,
          ∏ i, if success (outcomes i) then 0 else weight (outcomes i) := by
      apply Finset.sum_congr rfl
      intro outcomes _houtcomes
      by_cases hfail : ∀ i, ¬ success (outcomes i)
      · rw [if_pos (show outcomes ∈ {outcomes | ∀ i, ¬ success (outcomes i)} from hfail)]
        apply Finset.prod_congr rfl
        intro i _hi
        simp [hfail i]
      · rw [if_neg (show outcomes ∉ {outcomes | ∀ i, ¬ success (outcomes i)} from hfail)]
        push_neg at hfail
        obtain ⟨i, hi⟩ := hfail
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
    _ = ∏ _i : Fin t,
        ∑ outcome : Ω, if success outcome then 0 else weight outcome := by
      simpa using
        (Fintype.prod_sum
          (fun _i : Fin t => fun outcome : Ω =>
            if success outcome then 0 else weight outcome)).symm
    _ = oneTrialFailureMass weight success ^ t := by
      simp [oneTrialFailureMass]

/-- Normalized form of the exact product identity. -/
theorem finiteOutcomeProductMass_allTrialsFail_eq_one_sub_pow
    (weight : Ω → ℝ≥0∞) (success : Ω → Prop) (t : ℕ)
    (hnormalized : (∑ outcome : Ω, weight outcome) = 1) :
    finiteOutcomeProductMass weight t (allTrialsFailEvent success t) =
      (1 - oneTrialSuccessMass weight success) ^ t := by
  rw [finiteOutcomeProductMass_allTrialsFail,
    oneTrialFailureMass_eq_one_sub weight success hnormalized]

end FiniteProduct

section ExponentialBound

/-- The elementary exponential amplification inequality. -/
theorem one_sub_pow_le_exp_neg_mul {s : ℝ} (hs1 : s ≤ 1)
    (t : ℕ) :
    (1 - s) ^ t ≤ Real.exp (-s * (t : ℝ)) := by
  have hbase0 : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hbase : 1 - s ≤ Real.exp (-s) := by
    have h := Real.add_one_le_exp (-s)
    linarith
  calc
    (1 - s) ^ t ≤ Real.exp (-s) ^ t :=
      pow_le_pow_left₀ hbase0 hbase t
    _ = Real.exp ((t : ℝ) * (-s)) := (Real.exp_nat_mul (-s) t).symm
    _ = Real.exp (-s * (t : ℝ)) := by
      congr 1
      ring

/-- A rational consequence sufficient for the standard success threshold:
`e⁻¹ ≤ 1/2`. -/
theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg]
  have hinv : (Real.exp (1 : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).2 hexp
  norm_num at hinv ⊢
  exact hinv

end ExponentialBound

section K4Instantiation

open K4OneTrial

/-- The `ENNReal` point mass of a one-trial graph board. -/
noncomputable def k4TrialBoardWeight (a : ℕ)
    (board : Board (Sym2 (TrialVertex a))) : ℝ≥0∞ :=
  boardWeight (bernoulliWeight (densityENN a)) board

/-- Predicate that the one-trial graph board contains a four-clique. -/
noncomputable def k4TrialSucceeds (a : ℕ)
    (board : Board (Sym2 (TrialVertex a))) : Prop :=
  0 < trialK4Count a board

/-- Exact product-space mass of the event that all `t` one-trial graph boards
fail.  A sample contains the full edge board of every trial, rather than only
a vector of abstract success bits. -/
noncomputable def repeatedK4FailureMass (a t : ℕ) : ℝ≥0∞ :=
  finiteOutcomeProductMass (k4TrialBoardWeight a) t
    (allTrialsFailEvent (k4TrialSucceeds a) t)

theorem sum_k4TrialBoardWeight (a : ℕ) (ha : 2 ≤ a) :
    (∑ board : Board (Sym2 (TrialVertex a)), k4TrialBoardWeight a board) = 1 := by
  unfold k4TrialBoardWeight
  exact sum_boardWeight (bernoulliWeight (densityENN a))
    (sum_bernoulliWeight (densityENN a) (densityENN_le_one a ha))

/-- The generic one-trial success mass is the event mass already used to
define `trialSuccess`. -/
theorem oneTrialSuccessMass_k4_eq (a : ℕ) :
    oneTrialSuccessMass (k4TrialBoardWeight a) (k4TrialSucceeds a) =
      finiteBoardMass (bernoulliWeight (densityENN a))
        {board | 0 < trialK4Count a board} := by
  classical
  unfold oneTrialSuccessMass k4TrialBoardWeight k4TrialSucceeds finiteBoardMass
  rfl

/-- Exact full-board amplification identity. -/
theorem repeatedK4FailureMass_eq (a t : ℕ) (ha : 2 ≤ a) :
    repeatedK4FailureMass a t =
      (1 - finiteBoardMass (bernoulliWeight (densityENN a))
        {board | 0 < trialK4Count a board}) ^ t := by
  unfold repeatedK4FailureMass
  rw [finiteOutcomeProductMass_allTrialsFail_eq_one_sub_pow
    (k4TrialBoardWeight a) (k4TrialSucceeds a) t
    (sum_k4TrialBoardWeight a ha)]
  rw [oneTrialSuccessMass_k4_eq]

/-- The one-trial real success probability lies in `[0,1]`. -/
theorem trialSuccess_le_one (a : ℕ) (ha : 2 ≤ a) : trialSuccess a ≤ 1 := by
  have hpartition := oneTrialSuccessMass_add_failureMass
    (k4TrialBoardWeight a) (k4TrialSucceeds a)
  rw [sum_k4TrialBoardWeight a ha] at hpartition
  have hle : oneTrialSuccessMass (k4TrialBoardWeight a) (k4TrialSucceeds a) ≤ 1 := by
    rw [← hpartition]
    exact le_add_of_nonneg_right bot_le
  rw [trialSuccess_eq_mass, ← oneTrialSuccessMass_k4_eq]
  exact ENNReal.toReal_mono (by simp) hle

/-- Real-valued exact product identity. -/
theorem repeatedK4FailureMass_toReal (a t : ℕ) (ha : 2 ≤ a) :
    (repeatedK4FailureMass a t).toReal = (1 - trialSuccess a) ^ t := by
  rw [repeatedK4FailureMass_eq a t ha, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le]
  · rw [ENNReal.toReal_one, ← trialSuccess_eq_mass]
  · have hpartition := oneTrialSuccessMass_add_failureMass
      (k4TrialBoardWeight a) (k4TrialSucceeds a)
    rw [sum_k4TrialBoardWeight a ha] at hpartition
    rw [← oneTrialSuccessMass_k4_eq]
    rw [← hpartition]
    exact le_add_of_nonneg_right bot_le
  · simp

/-- The chosen number of trials cancels the explicit one-trial lower bound. -/
theorem oneTrialSuccessLower_mul_trialCount (a : ℕ) (ha : 0 < a) :
    K6Upper.oneTrialSuccessLower a *
      ((K6Upper.momentAmplification * a ^ 2 : ℕ) : ℝ) = 1 := by
  have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
  unfold K6Upper.oneTrialSuccessLower K6Upper.momentAmplification
  norm_num
  field_simp [ne_of_gt haR]

/-- Concrete amplification bound for the K4 trial model: after
`184320 * a^2` independent full-board trials, simultaneous failure has
probability at most `e⁻¹`. -/
theorem repeatedK4FailureMass_toReal_le_exp_neg_one (a : ℕ) (ha : 2 ≤ a) :
    (repeatedK4FailureMass a
      (K6Upper.momentAmplification * a ^ 2)).toReal ≤ Real.exp (-1) := by
  let t : ℕ := K6Upper.momentAmplification * a ^ 2
  have ha0 : 0 < a := lt_of_lt_of_le (by omega) ha
  have hs1 : trialSuccess a ≤ 1 := trialSuccess_le_one a ha
  have hlower := oneTrialSuccess_lower a ha
  have hcount : K6Upper.oneTrialSuccessLower a * (t : ℝ) = 1 := by
    simpa [t] using oneTrialSuccessLower_mul_trialCount a ha0
  have hproduct : 1 ≤ trialSuccess a * (t : ℝ) := by
    rw [← hcount]
    exact mul_le_mul_of_nonneg_right hlower (Nat.cast_nonneg t)
  calc
    (repeatedK4FailureMass a
        (K6Upper.momentAmplification * a ^ 2)).toReal =
        (1 - trialSuccess a) ^ t := by
          simpa [t] using repeatedK4FailureMass_toReal a t ha
    _ ≤ Real.exp (-trialSuccess a * (t : ℝ)) :=
      one_sub_pow_le_exp_neg_mul hs1 t
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)

/-- In particular, the explicit amplification reaches the conventional
one-half failure threshold. -/
theorem repeatedK4FailureMass_toReal_le_half (a : ℕ) (ha : 2 ≤ a) :
    (repeatedK4FailureMass a
      (K6Upper.momentAmplification * a ^ 2)).toReal ≤ (1 : ℝ) / 2 :=
  (repeatedK4FailureMass_toReal_le_exp_neg_one a ha).trans exp_neg_one_le_half

end K4Instantiation

end Amplification
end OnlineRamsey
