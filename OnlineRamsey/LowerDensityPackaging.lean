import OnlineRamsey.RecurrenceInstantiation

/-!
# Extending a small-density lower bound to every density

The hard lower-bound argument naturally applies only below a fixed positive
density cutoff.  This file closes the elementary complementary range.  A
successful transcript contains all fifteen distinct edges of a `K₆`, hence
no query budget below fifteen is achievable.  Combining this fact with
monotonicity of `q ^ 10` turns any positive small-`q` lower constant into one
valid for every `0 < q ≤ 1`.
-/

namespace OnlineRamsey
namespace LowerDensityPackaging

open scoped ENNReal
open QueryComplexity

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- A transcript containing a labelled `K₆` has at least fifteen positive
edges. -/
theorem fifteen_le_positiveEdgeCount {N : ℕ} {h : Transcript (Query N)}
    (hs : TranscriptSucceeds h) :
    15 ≤ (positiveGraph h).edgeFinset.card := by
  classical
  obtain ⟨copy⟩ := hs
  have hcard : Fintype.card K6.edgeSet ≤
      Fintype.card (positiveGraph h).edgeSet :=
    Fintype.card_le_of_embedding copy.mapEdgeSet
  rw [← K6.edgeFinset_card, ← (positiveGraph h).edgeFinset_card] at hcard
  simpa [K6, SimpleGraph.card_edgeFinset_top_eq_card_choose_two] using hcard

/-- A successful transcript has length at least fifteen.  Repeated positive
entries cannot help because the positive graph records distinct unordered
coordinates. -/
theorem fifteen_le_transcript_length {N : ℕ} {h : Transcript (Query N)}
    (hs : TranscriptSucceeds h) : 15 ≤ h.length := by
  calc
    15 ≤ (positiveGraph h).edgeFinset.card := fifteen_le_positiveEdgeCount hs
    _ ≤ (answers h).count true :=
      RecurrenceInstantiation.positiveGraph_edgeCount_le_trueCount h
    _ ≤ (answers h).length := List.count_le_length
    _ = h.length := length_answers h

/-- With fewer than fifteen queries the success event is empty, for every
strategy (even an inadmissible one). -/
theorem successEvent_eq_empty_of_budget_lt_fifteen {N : ℕ}
    (hN : N < 15) (strategy : K6Strategy N) :
    successEvent N strategy = ∅ := by
  ext board
  constructor
  · intro hs
    have h15 : 15 ≤ N := by
      simpa using fifteen_le_transcript_length hs
    exact (Nat.not_le_of_gt hN) h15
  · simp

/-- No budget below fifteen is sufficient at any density. -/
theorem not_achievable_of_budget_lt_fifteen {p : ℝ≥0∞} {N : ℕ}
    (hN : N < 15) : ¬Achievable p N := by
  rintro ⟨_hp, strategy, _hadmissible, hsuccess⟩
  have hevent := successEvent_eq_empty_of_budget_lt_fifteen hN strategy
  have hzero : successProbability p N strategy = 0 := by
    rw [successProbability, hevent]
    simp [finiteBoardMass]
  rw [hzero] at hsuccess
  simpa [threshold] using hsuccess

/-- Every achievable budget is at least fifteen. -/
theorem fifteen_le_of_achievable {p : ℝ≥0∞} {N : ℕ}
    (hN : Achievable p N) : 15 ≤ N := by
  by_contra h
  exact not_achievable_of_budget_lt_fifteen (Nat.lt_of_not_ge h) hN

/-- A lower estimate below `q₀` extends to all cubic densities.  Above the
cutoff, the universal fifteen-query obstruction supplies the lower bound
`15 * q₀ ^ 10`; taking the minimum preserves the small-density estimate. -/
theorem global_lower_of_small_density
    (q₀ c₀ : ℝ≥0∞) (hq₀1 : q₀ ≤ 1)
    (hsmall : ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 → q < q₀ →
      ∀ N, Achievable (q ^ 3) N → c₀ ≤ (N : ℝ≥0∞) * q ^ 10) :
    ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∀ N, Achievable (q ^ 3) N →
        min c₀ (15 * q₀ ^ 10) ≤ (N : ℝ≥0∞) * q ^ 10 := by
  intro q hq hq1 N hN
  by_cases hqq₀ : q < q₀
  · exact (min_le_left _ _).trans (hsmall q hq hq1 hqq₀ N hN)
  · have hq₀q : q₀ ≤ q := le_of_not_gt hqq₀
    have h15' : (15 : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
      exact_mod_cast fifteen_le_of_achievable hN
    refine (min_le_right _ _).trans ?_
    exact mul_le_mul' h15' (pow_le_pow_left' hq₀q 10)

/-- The globally extended constant is strictly positive whenever the input
constant and cutoff are strictly positive. -/
theorem global_lower_constant_pos {q₀ c₀ : ℝ≥0∞}
    (hq₀ : 0 < q₀) (hc₀ : 0 < c₀) :
    0 < min c₀ (15 * q₀ ^ 10) := by
  simp only [lt_min_iff]
  exact ⟨hc₀, ENNReal.mul_pos (by norm_num) (pow_ne_zero _ hq₀.ne')⟩

end
end LowerDensityPackaging
end OnlineRamsey
