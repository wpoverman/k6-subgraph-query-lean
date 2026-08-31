import OnlineRamsey.UpperFillMonotonicity

/-!
# Final finite probability assembly for the upper strategy

The only input not proved in this file is deterministic: raw reservoir and
branch supply, together with one successful fill board, must yield the
concrete allocator certificate.  All Bernoulli mass bookkeeping and the
strict numerical margin above `1/2` are discharged here.
-/

namespace OnlineRamsey
namespace UpperProbabilityAssembly

open scoped ENNReal
open Amplification K4OneTrial QueryComplexity UpperStrategy
open UpperFillMonotonicity

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The fully explicit event retained by the probability calculation. -/
def SlackFullSupplySuccess (a : ℕ)
    (bits : List.Vector Bool (slackQueryBudget a)) : Prop :=
  SlackBaseSupplyGood a (slackBranchAnswerVector a bits) ∧
    ∃ i, offDiagTrialSucceeds a (slackFillBoards a bits i)

/-- Marginalizing the fill segment leaves exactly the raw pre-fill supply
failure mass. -/
theorem slackFull_not_baseSupplyGood_weight_eq
    (a : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1) :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if ¬SlackBaseSupplyGood a (slackBranchAnswerVector a bits) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      ∑ base : List.Vector Bool (slackFillStart a),
        if ¬SlackBaseSupplyGood a base then
          (base.toList.map (bernoulliWeight p)).prod else 0 := by
  have hsplit := slackAnswerSplit_event_weight_eq p a
    (fun _fill : List.Vector Bool (slackFillQueryCount a) => True)
    (fun base : List.Vector Bool (slackFillStart a) =>
      ¬SlackBaseSupplyGood a base)
  simpa [sum_boolVector_weight p hp] using hsplit

/-- With no restriction on the prefix, complete fill failure has exactly the
arbitrary-density amplified failure mass. -/
theorem slackFull_fillFailure_weight_eq
    (a : ℕ) (p : ℝ≥0∞) (hp : p ≤ 1) :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if slackFillAnswerEquiv a (slackFillAnswerVector a bits) ∈
          allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      repeatedOffDiagK4FailureMassAt p a (slackTrialCount a) := by
  have hsplit := slackFullFailure_with_prefix_weight_eq_at p a
    (fun _base : List.Vector Bool (slackFillStart a) => True)
  simpa [sum_boolVector_weight p hp] using hsplit

/-- Failure of the explicit full good event is contained in the union of
pre-fill supply failure and complete fill failure. -/
theorem slackFull_not_supplySuccess_weight_le
    (a : ℕ) (p : ℝ≥0∞) :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if ¬SlackFullSupplySuccess a bits then
        (bits.toList.map (bernoulliWeight p)).prod else 0) ≤
      (∑ bits : List.Vector Bool (slackQueryBudget a),
        if ¬SlackBaseSupplyGood a (slackBranchAnswerVector a bits) then
          (bits.toList.map (bernoulliWeight p)).prod else 0) +
      (∑ bits : List.Vector Bool (slackQueryBudget a),
        if slackFillAnswerEquiv a (slackFillAnswerVector a bits) ∈
            allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a) then
          (bits.toList.map (bernoulliWeight p)).prod else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro bits _hbits
  let baseGood := SlackBaseSupplyGood a (slackBranchAnswerVector a bits)
  let fillFails := slackFillAnswerEquiv a (slackFillAnswerVector a bits) ∈
    allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a)
  by_cases hb : baseGood
  · by_cases hf : fillFails
    · have hf' : ∀ i : Fin (slackTrialCount a),
          ¬offDiagTrialSucceeds a
            (slackFillAnswerEquiv a (slackFillAnswerVector a bits) i) := by
        simpa [fillFails, allTrialsFailEvent] using hf
      have hnotgood : ¬SlackFullSupplySuccess a bits := by
        rintro ⟨_hbase, i, hi⟩
        exact hf' i (by
          simpa [slackFillBoards_eq_slackFillAnswerEquiv] using hi)
      simp only [hnotgood]
      rw [if_neg (not_not_intro hb), if_pos hf]
      simp
    · have hexists : ∃ i, offDiagTrialSucceeds a (slackFillBoards a bits i) := by
        simpa [fillFails, allTrialsFailEvent,
          slackFillBoards_eq_slackFillAnswerEquiv] using hf
      have hgood : SlackFullSupplySuccess a bits := ⟨hb, hexists⟩
      simp [hgood, baseGood, fillFails, hb, hf]
  · simp [SlackFullSupplySuccess, baseGood, hb]

/-- The complete raw supply-and-fill event has probability at least one half
throughout the density bucket. -/
theorem threshold_le_slackFullSupplySuccess_weight
    (a : ℕ) (ha : 2 ≤ a) (p : ℝ≥0∞)
    (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    threshold ≤
      ∑ bits : List.Vector Bool (slackQueryBudget a),
        if SlackFullSupplySuccess a bits then
          (bits.toList.map (bernoulliWeight p)).prod else 0 := by
  have hbase := slackBase_not_supplyGood_weight_le a ha p hp hdensity
  have hfill := repeatedOffDiagK4FailureMassAt_lt_three_eighths
    a ha p hp hdensity
  have hunion := slackFull_not_supplySuccess_weight_le a p
  rw [slackFull_not_baseSupplyGood_weight_eq a p hp,
    slackFull_fillFailure_weight_eq a p hp] at hunion
  have hbad :
      (∑ bits : List.Vector Bool (slackQueryBudget a),
        if ¬SlackFullSupplySuccess a bits then
          (bits.toList.map (bernoulliWeight p)).prod else 0) ≤ threshold := by
    have hnumeric :
        ((2 : ℝ≥0∞)⁻¹) ^ 63 +
              (2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 63 +
            (3 : ℝ≥0∞) / 8 ≤ threshold := by
      have hpow : ((2 : ℝ≥0∞)⁻¹) ^ 63 ≤
          ((2 : ℝ≥0∞)⁻¹) ^ 5 :=
        pow_le_pow_of_le_one (by simp) (by norm_num) (by norm_num)
      calc
        ((2 : ℝ≥0∞)⁻¹) ^ 63 +
              2 * ((2 : ℝ≥0∞)⁻¹) ^ 63 + 3 / 8 ≤
            ((2 : ℝ≥0∞)⁻¹) ^ 5 +
              2 * ((2 : ℝ≥0∞)⁻¹) ^ 5 + 3 / 8 := by
          gcongr
        _ ≤ threshold := by
          apply (ENNReal.toReal_le_toReal (by finiteness)
            (by simp [threshold])).mp
          rw [ENNReal.toReal_add (by finiteness) (by finiteness),
            ENNReal.toReal_add (by finiteness) (by finiteness)]
          norm_num [threshold]
    exact hunion.trans
      ((add_le_add hbase hfill.le).trans hnumeric)
  exact threshold_le_vectorEventWeight_of_complement_le p hp
    (slackQueryBudget a) (SlackFullSupplySuccess a) hbad

/-- Any deterministic proof that the raw event constructs the concrete path
certificate immediately yields achievability of the implemented strategy. -/
theorem achievable_slack_of_supplySuccess_implies_concrete
    (a : ℕ) (ha : 2 ≤ a) (p : ℝ≥0∞)
    (hp : p ≤ 1) (hdensity : densityENN a ≤ p)
    (hdet : ∀ bits : List.Vector Bool (slackQueryBudget a),
      SlackFullSupplySuccess a bits →
        ConcreteSlackCoupledPath a (by omega) bits) :
    Achievable p (slackQueryBudget a) := by
  apply achievable_slack_of_concretePath_mass a (by omega) p hp
  have hraw := threshold_le_slackFullSupplySuccess_weight
    a ha p hp hdensity
  apply hraw.trans
  apply Finset.sum_le_sum
  intro bits _hbits
  by_cases hgood : SlackFullSupplySuccess a bits
  · have hconcrete := hdet bits hgood
    simp [hgood, hconcrete]
  · simp [hgood]

end
end UpperProbabilityAssembly
end OnlineRamsey
