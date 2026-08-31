import OnlineRamsey.AdaptiveQuery

/-!
# Monotonicity for decreasing events on finite Bernoulli boards

This file gives an explicit finite coupling, so no measure-theoretic
stochastic-order result is hidden in the upper-bound argument.  If `p₀ ≤ p`,
the coupling samples a low-density board below a high-density board
coordinatewise.  Consequently every decreasing event has smaller mass at
`p` than at `p₀`.
-/

namespace OnlineRamsey
namespace BernoulliMonotonicity

open scoped ENNReal

universe u

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- One-coordinate monotone coupling of Bernoulli(`p₀`) and Bernoulli(`p`). -/
def couplingBitWeight (p₀ p : ℝ≥0∞) : Bool × Bool → ℝ≥0∞
  | (false, false) => 1 - p
  | (false, true) => p - p₀
  | (true, false) => 0
  | (true, true) => p₀

/-- The second marginal of the coupling is Bernoulli(`p`). -/
theorem sum_couplingBitWeight_low (p₀ p : ℝ≥0∞) (hp₀p : p₀ ≤ p)
    (high : Bool) :
    (∑ low : Bool, couplingBitWeight p₀ p (low, high)) =
      bernoulliWeight p high := by
  cases high with
  | false =>
      rw [Fintype.sum_bool]
      simp [couplingBitWeight, bernoulliWeight]
  | true =>
      rw [Fintype.sum_bool]
      simp only [couplingBitWeight, bernoulliWeight]
      rw [add_comm, tsub_add_cancel_of_le hp₀p]

/-- The first marginal of the coupling is Bernoulli(`p₀`). -/
theorem sum_couplingBitWeight_high (p₀ p : ℝ≥0∞)
    (hp₀p : p₀ ≤ p) (hp : p ≤ 1) (low : Bool) :
    (∑ high : Bool, couplingBitWeight p₀ p (low, high)) =
      bernoulliWeight p₀ low := by
  cases low with
  | false =>
      rw [Fintype.sum_bool]
      simp only [couplingBitWeight, bernoulliWeight]
      rw [add_comm, tsub_add_tsub_cancel hp hp₀p]
  | true =>
      rw [Fintype.sum_bool]
      simp [couplingBitWeight, bernoulliWeight]

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Product weight of the coordinatewise monotone coupling. -/
def coupledBoardWeight (p₀ p : ℝ≥0∞)
    (boards : Board Q × Board Q) : ℝ≥0∞ :=
  ∏ q : Q, couplingBitWeight p₀ p (boards.1 q, boards.2 q)

theorem sum_low_coupledBoardWeight (p₀ p : ℝ≥0∞)
    (hp₀p : p₀ ≤ p) (high : Board Q) :
    (∑ low : Board Q, coupledBoardWeight p₀ p (low, high)) =
      boardWeight (bernoulliWeight p) high := by
  unfold coupledBoardWeight boardWeight
  rw [show
      (∑ low : Board Q,
        ∏ q : Q, couplingBitWeight p₀ p (low q, high q)) =
        ∏ q : Q, ∑ bit : Bool,
          couplingBitWeight p₀ p (bit, high q) by
    simpa using (Fintype.prod_sum
      (fun q : Q => fun bit : Bool =>
        couplingBitWeight p₀ p (bit, high q))).symm]
  apply Finset.prod_congr rfl
  intro q _hq
  exact sum_couplingBitWeight_low p₀ p hp₀p (high q)

theorem sum_high_coupledBoardWeight (p₀ p : ℝ≥0∞)
    (hp₀p : p₀ ≤ p) (hp : p ≤ 1) (low : Board Q) :
    (∑ high : Board Q, coupledBoardWeight p₀ p (low, high)) =
      boardWeight (bernoulliWeight p₀) low := by
  unfold coupledBoardWeight boardWeight
  rw [show
      (∑ high : Board Q,
        ∏ q : Q, couplingBitWeight p₀ p (low q, high q)) =
        ∏ q : Q, ∑ bit : Bool,
          couplingBitWeight p₀ p (low q, bit) by
    simpa using (Fintype.prod_sum
      (fun q : Q => fun bit : Bool =>
        couplingBitWeight p₀ p (low q, bit))).symm]
  apply Finset.prod_congr rfl
  intro q _hq
  exact sum_couplingBitWeight_high p₀ p hp₀p hp (low q)

/-- The high-board projection of the coupling has the `p`-board law. -/
theorem coupled_high_event_mass_eq (p₀ p : ℝ≥0∞) (hp₀p : p₀ ≤ p)
    (event : Set (Board Q)) :
    (∑ boards : Board Q × Board Q,
      if boards.2 ∈ event then coupledBoardWeight p₀ p boards else 0) =
      finiteBoardMass (bernoulliWeight p) event := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  unfold finiteBoardMass
  apply Finset.sum_congr rfl
  intro high _hhigh
  by_cases hevent : high ∈ event
  · simp only [hevent, if_true]
    exact sum_low_coupledBoardWeight p₀ p hp₀p high
  · simp [hevent]

/-- The low-board projection of the coupling has the `p₀`-board law. -/
theorem coupled_low_event_mass_eq (p₀ p : ℝ≥0∞)
    (hp₀p : p₀ ≤ p) (hp : p ≤ 1) (event : Set (Board Q)) :
    (∑ boards : Board Q × Board Q,
      if boards.1 ∈ event then coupledBoardWeight p₀ p boards else 0) =
      finiteBoardMass (bernoulliWeight p₀) event := by
  rw [Fintype.sum_prod_type]
  unfold finiteBoardMass
  apply Finset.sum_congr rfl
  intro low _hlow
  by_cases hevent : low ∈ event
  · simp only [hevent, if_true]
    exact sum_high_coupledBoardWeight p₀ p hp₀p hp low
  · simp [hevent]

/-- A nonzero coupled pair is ordered coordinatewise. -/
theorem low_le_high_of_coupledBoardWeight_ne_zero
    (p₀ p : ℝ≥0∞) {low high : Board Q}
    (hweight : coupledBoardWeight p₀ p (low, high) ≠ 0) :
    ∀ q, low q ≤ high q := by
  intro q
  rw [Bool.le_iff_imp]
  intro hlow
  by_contra hhigh
  have hhighFalse : high q = false := Bool.eq_false_of_not_eq_true hhigh
  apply hweight
  unfold coupledBoardWeight
  apply Finset.prod_eq_zero (Finset.mem_univ q)
  simp [couplingBitWeight, hlow, hhighFalse]

/-- A board event is decreasing when deleting positive coordinates preserves
membership. -/
def DownClosed (event : Set (Board Q)) : Prop :=
  ∀ low high, (∀ q, low q ≤ high q) → high ∈ event → low ∈ event

/-- Finite Bernoulli monotonicity for decreasing board events. -/
theorem finiteBoardMass_antitone_of_downClosed
    {p₀ p : ℝ≥0∞} (hp₀p : p₀ ≤ p) (hp : p ≤ 1)
    {event : Set (Board Q)} (hdown : DownClosed event) :
    finiteBoardMass (bernoulliWeight p) event ≤
      finiteBoardMass (bernoulliWeight p₀) event := by
  rw [← coupled_high_event_mass_eq p₀ p hp₀p event,
    ← coupled_low_event_mass_eq p₀ p hp₀p hp event]
  apply Finset.sum_le_sum
  intro boards _hboards
  by_cases hhigh : boards.2 ∈ event
  · by_cases hweight : coupledBoardWeight p₀ p boards = 0
    · simp [hhigh, hweight]
    · have hlow : boards.1 ∈ event :=
        hdown boards.1 boards.2
          (low_le_high_of_coupledBoardWeight_ne_zero p₀ p hweight) hhigh
      simp [hhigh, hlow]
  · simp [hhigh]

end
end BernoulliMonotonicity
end OnlineRamsey
