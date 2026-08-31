import OnlineRamsey.K4MomentBounds
import Mathlib.Data.ENNReal.BigOperators

/-!
# One-trial success bound for the finite Bernoulli board

This file connects the exact `ENNReal` moments of `K4Moments.lean` to the real
scale inequalities and finite Paley--Zygmund calculation in
`K4MomentBounds.lean`.
-/

namespace OnlineRamsey
namespace K4OneTrial

open K4Moments K4MomentBounds

open scoped ENNReal

universe u

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Bernoulli board point masses never take the value infinity. -/
theorem boardWeight_ne_top (p : ℝ≥0∞) (hp : p ≠ ∞) (board : Board Q) :
    boardWeight (bernoulliWeight p) board ≠ ∞ := by
  unfold boardWeight
  apply ENNReal.prod_ne_top
  intro q _
  cases h : board q
  · simp [bernoulliWeight]
  · simpa [bernoulliWeight] using hp

/-- The finite clique count never takes the value infinity. -/
theorem k4Count_ne_top {V : Type*} [DecidableEq V]
    (U : Finset V) (edgeFamily : Finset V → Finset Q) (board : Board Q) :
    k4Count U edgeFamily board ≠ ∞ := by
  unfold k4Count
  rw [ENNReal.sum_ne_top]
  intro A _
  unfold allTrueIndicator
  split <;> simp

/-- `toReal` commutes with the explicit finite expectation whenever the
Bernoulli parameter is finite and the random variable is finite-valued. -/
theorem expectation_toReal (p : ℝ≥0∞) (hp : p ≠ ∞) (X : Board Q → ℝ≥0∞)
    (hX : ∀ board, X board ≠ ∞) :
    (expectation p X).toReal =
      ∑ board : Board Q,
        (boardWeight (bernoulliWeight p) board).toReal * (X board).toReal := by
  unfold expectation
  rw [ENNReal.toReal_sum]
  · simp
  · intro board _
    exact ENNReal.mul_ne_top (boardWeight_ne_top p hp board) (hX board)

/-- The finite board used for one branch-and-fill trial. -/
abbrev TrialVertex (a : ℕ) := Fin (a ^ 4)

/-- `a⁻³`, embedded into `ENNReal`. -/
noncomputable def densityENN (a : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (density a)

/-- Real point mass of a board in the one-trial model. -/
noncomputable def trialWeight (a : ℕ)
    (board : Board (Sym2 (TrialVertex a))) : ℝ :=
  (boardWeight (bernoulliWeight (densityENN a)) board).toReal

/-- Real-valued number of four-cliques on a trial board. -/
noncomputable def trialK4Count (a : ℕ)
    (board : Board (Sym2 (TrialVertex a))) : ℝ :=
  (k4Count (Finset.univ : Finset (TrialVertex a)) cliqueEdges board).toReal

/-- Probability of finding at least one four-clique, written as a finite sum
of board point masses. -/
noncomputable def trialSuccess (a : ℕ) : ℝ :=
  ∑ board ∈ (Finset.univ.filter fun board : Board (Sym2 (TrialVertex a)) =>
      0 < trialK4Count a board), trialWeight a board

theorem density_nonneg (a : ℕ) : 0 ≤ density a := by
  unfold density
  positivity

theorem density_le_one (a : ℕ) (ha : 2 ≤ a) : density a ≤ 1 := by
  unfold density
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hpow : (1 : ℝ) ≤ (a : ℝ) ^ 3 := by nlinarith [sq_nonneg ((a : ℝ) - 1)]
  exact (div_le_one (by positivity)).2 hpow

theorem densityENN_le_one (a : ℕ) (ha : 2 ≤ a) : densityENN a ≤ 1 := by
  rw [densityENN, ENNReal.ofReal_le_one]
  exact density_le_one a ha

theorem densityENN_ne_top (a : ℕ) : densityENN a ≠ ∞ := by
  simp [densityENN]

/-- `trialSuccess` is literally the real value of the corresponding event
under the explicit finite Bernoulli board mass. -/
theorem trialSuccess_eq_mass (a : ℕ) :
    trialSuccess a =
      (finiteBoardMass (bernoulliWeight (densityENN a))
        {board | 0 < trialK4Count a board}).toReal := by
  unfold trialSuccess finiteBoardMass
  rw [ENNReal.toReal_sum]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro board _
    by_cases h : 0 < trialK4Count a board <;> simp [trialWeight, h]
  · intro board _
    split
    · exact boardWeight_ne_top (densityENN a) (densityENN_ne_top a) board
    · simp

@[simp] theorem densityENN_toReal (a : ℕ) : (densityENN a).toReal = density a := by
  simp [densityENN, density_nonneg]

/-- Cast of the exact finite first-moment formula. -/
theorem trial_firstMoment (a : ℕ) (ha : 2 ≤ a) :
    (∑ board, trialWeight a board * trialK4Count a board) =
      firstMomentExpression a := by
  let U : Finset (TrialVertex a) := Finset.univ
  have hexact := graphK4Count_firstMoment (densityENN a)
    (densityENN_le_one a ha) U
  have hcast := congrArg ENNReal.toReal hexact
  rw [expectation_toReal (densityENN a) (densityENN_ne_top a)
    (k4Count U cliqueEdges) (fun board => k4Count_ne_top U cliqueEdges board)] at hcast
  simpa [trialWeight, trialK4Count, firstMomentExpression, U] using hcast

/-- Cast of the exact five-overlap second-moment formula. -/
theorem trial_secondMoment (a : ℕ) (ha : 2 ≤ a) :
    (∑ board, trialWeight a board * trialK4Count a board ^ 2) =
      secondMomentExpression a := by
  let U : Finset (TrialVertex a) := Finset.univ
  have hexact := graphK4Count_secondMoment (densityENN a)
    (densityENN_le_one a ha) U
  have hcast := congrArg ENNReal.toReal hexact
  rw [expectation_toReal (densityENN a) (densityENN_ne_top a)
    (fun board => k4Count U cliqueEdges board ^ 2)
    (fun board => ENNReal.pow_ne_top (k4Count_ne_top U cliqueEdges board))] at hcast
  have hterms : ∀ k ∈ Finset.range 5,
      ((Nat.choose U.card 4 * Nat.choose 4 k *
        Nat.choose (U.card - 4) (4 - k) : ℝ≥0∞) *
        densityENN a ^ (12 - Nat.choose k 2)) ≠ ∞ := by
    intro k _
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top <;> simp
      · simp
    · exact ENNReal.pow_ne_top (by simp [densityENN])
  rw [ENNReal.toReal_sum hterms] at hcast
  simpa [trialWeight, trialK4Count, secondMomentExpression, U] using hcast

theorem trialWeight_nonneg (a : ℕ) (board : Board (Sym2 (TrialVertex a))) :
    0 ≤ trialWeight a board := ENNReal.toReal_nonneg

theorem trialK4Count_nonneg (a : ℕ) (board : Board (Sym2 (TrialVertex a))) :
    0 ≤ trialK4Count a board := ENNReal.toReal_nonneg

/-- The finite-board second-moment inequality, now with all quantities in the
same real model. -/
theorem trial_secondMoment_success (a : ℕ) (ha : 2 ≤ a) :
    firstMomentExpression a ^ 2 ≤ trialSuccess a * secondMomentExpression a := by
  have hcs := finite_secondMoment_success (trialWeight a) (trialK4Count a)
    (trialWeight_nonneg a) (trialK4Count_nonneg a)
  rw [trial_firstMoment a ha, trial_secondMoment a ha] at hcs
  exact hcs

/-- Fully instantiated one-trial success probability lower bound. -/
theorem oneTrialSuccess_lower (a : ℕ) (ha : 2 ≤ a) :
    K6Upper.oneTrialSuccessLower a ≤ trialSuccess a := by
  apply K6Upper.oneTrial_success_of_moment_bounds a (by omega)
    (firstMomentExpression a) (secondMomentExpression a) (trialSuccess a)
  · unfold trialSuccess
    exact Finset.sum_nonneg fun board _ => trialWeight_nonneg a board
  · simpa [K6Upper.k4FirstMomentLower] using firstMomentExpression_lower a ha
  · simpa [K6Upper.k4SecondMomentUpper] using secondMomentExpression_upper a ha
  · exact trial_secondMoment_success a ha

end K4OneTrial
end OnlineRamsey
