import OnlineRamsey.AmplificationSharp
import OnlineRamsey.BernoulliMonotonicity
import OnlineRamsey.UpperStrategy

/-!
# Density robustness of the concrete amplified fill phase

The one-trial moment estimate is proved at the bucket density `a⁻³`.  This
file transports it to every larger density by the explicit monotone coupling
from `BernoulliMonotonicity.lean`.  It also gives the arbitrary-density
answer-vector factorization needed by the concrete upper strategy.
-/

namespace OnlineRamsey
namespace UpperFillMonotonicity

open scoped ENNReal
open Amplification K4OneTrial QueryComplexity UpperStrategy

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Turning additional off-diagonal edges on cannot destroy a successful
four-clique trial. -/
theorem offDiagTrialSucceeds_mono (a : ℕ)
    {low high : Board (OffDiagTrialQuery a)}
    (hle : ∀ q, low q ≤ high q)
    (hsuccess : offDiagTrialSucceeds a low) :
    offDiagTrialSucceeds a high := by
  unfold offDiagTrialSucceeds at hsuccess ⊢
  rw [k4TrialSucceeds_iff_exists_fourSet] at hsuccess ⊢
  obtain ⟨A, hA, hall⟩ := hsuccess
  refine ⟨A, hA, ?_⟩
  intro q hq
  induction q using Sym2.ind with
  | _ x y =>
      have hxy : x ≠ y := (K4Moments.mem_cliqueEdges.mp hq).2.2
      have hnonloop : ¬s(x, y).IsDiag := by simpa using hxy
      have hlow : low ⟨s(x, y), hnonloop⟩ = true := by
        simpa [extendOffDiagTrialBoard, hnonloop] using hall s(x, y) hq
      have hhigh : high ⟨s(x, y), hnonloop⟩ = true :=
        (Bool.le_iff_imp.mp (hle ⟨s(x, y), hnonloop⟩)) hlow
      simpa [extendOffDiagTrialBoard, hnonloop] using hhigh

/-- One-trial failure is a decreasing event. -/
theorem offDiagTrialFailure_downClosed (a : ℕ) :
    BernoulliMonotonicity.DownClosed
      {board : Board (OffDiagTrialQuery a) | ¬offDiagTrialSucceeds a board} := by
  intro low high hle hhigh hlow
  exact hhigh (offDiagTrialSucceeds_mono a hle hlow)

/-- Failure mass of one off-diagonal trial at an arbitrary density. -/
noncomputable def offDiagK4FailureMassAt (p : ℝ≥0∞) (a : ℕ) : ℝ≥0∞ :=
  finiteBoardMass (bernoulliWeight p)
    {board : Board (OffDiagTrialQuery a) | ¬offDiagTrialSucceeds a board}

/-- One-trial failure mass is antitone in the Bernoulli density. -/
theorem offDiagK4FailureMassAt_antitone
    (a : ℕ) {p₀ p : ℝ≥0∞} (hp₀p : p₀ ≤ p) (hp : p ≤ 1) :
    offDiagK4FailureMassAt p a ≤ offDiagK4FailureMassAt p₀ a := by
  exact BernoulliMonotonicity.finiteBoardMass_antitone_of_downClosed
    hp₀p hp (offDiagTrialFailure_downClosed a)

/-- Repeated off-diagonal failure mass at an arbitrary density. -/
noncomputable def repeatedOffDiagK4FailureMassAt
    (p : ℝ≥0∞) (a t : ℕ) : ℝ≥0∞ :=
  finiteOutcomeProductMass
    (fun board : Board (OffDiagTrialQuery a) =>
      boardWeight (bernoulliWeight p) board) t
    (allTrialsFailEvent (offDiagTrialSucceeds a) t)

/-- The repeated failure mass is exactly the power of the one-trial failure
mass, without any normalization assumption. -/
theorem repeatedOffDiagK4FailureMassAt_eq_pow
    (p : ℝ≥0∞) (a t : ℕ) :
    repeatedOffDiagK4FailureMassAt p a t =
      offDiagK4FailureMassAt p a ^ t := by
  rw [repeatedOffDiagK4FailureMassAt,
    finiteOutcomeProductMass_allTrialsFail]
  congr 1
  classical
  unfold oneTrialFailureMass offDiagK4FailureMassAt finiteBoardMass
  apply Finset.sum_congr rfl
  intro board _hboard
  by_cases hs : offDiagTrialSucceeds a board <;> simp [hs]

/-- Repeated failure remains antitone in the density. -/
theorem repeatedOffDiagK4FailureMassAt_antitone
    (a t : ℕ) {p₀ p : ℝ≥0∞} (hp₀p : p₀ ≤ p) (hp : p ≤ 1) :
    repeatedOffDiagK4FailureMassAt p a t ≤
      repeatedOffDiagK4FailureMassAt p₀ a t := by
  rw [repeatedOffDiagK4FailureMassAt_eq_pow,
    repeatedOffDiagK4FailureMassAt_eq_pow]
  exact pow_le_pow_left' (offDiagK4FailureMassAt_antitone a hp₀p hp) t

/-- At the bucket density, the arbitrary-density definition reduces to the
amplification mass already bounded in `Amplification.lean`. -/
theorem repeatedOffDiagK4FailureMassAt_density_eq
    (a t : ℕ) :
    repeatedOffDiagK4FailureMassAt (densityENN a) a t =
      repeatedOffDiagK4FailureMass a t := rfl

/-- The sharp amplified failure estimate is robust throughout the entire
density bucket. -/
theorem repeatedOffDiagK4FailureMassAt_toReal_lt_three_eighths
    (a : ℕ) (ha : 2 ≤ a) (p : ℝ≥0∞)
    (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    (repeatedOffDiagK4FailureMassAt p a
      (K6Upper.momentAmplification * a ^ 2)).toReal < (3 : ℝ) / 8 := by
  let t := K6Upper.momentAmplification * a ^ 2
  have hmass := repeatedOffDiagK4FailureMassAt_antitone
    a t hdensity hp
  have hfinite : repeatedOffDiagK4FailureMassAt (densityENN a) a t ≠ ∞ := by
    rw [repeatedOffDiagK4FailureMassAt_density_eq,
      repeatedOffDiagK4FailureMass_eq a t ha,
      Amplification.repeatedK4FailureMass_eq a t ha]
    exact ENNReal.pow_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  calc
    (repeatedOffDiagK4FailureMassAt p a t).toReal ≤
        (repeatedOffDiagK4FailureMassAt (densityENN a) a t).toReal :=
      ENNReal.toReal_mono hfinite hmass
    _ = (repeatedK4FailureMass a t).toReal := by
      rw [repeatedOffDiagK4FailureMassAt_density_eq,
        repeatedOffDiagK4FailureMass_eq a t ha]
    _ < (3 : ℝ) / 8 := by
      exact repeatedK4FailureMass_toReal_lt_three_eighths a ha

/-- `ENNReal` form of the bucket-robust sharp failure estimate. -/
theorem repeatedOffDiagK4FailureMassAt_lt_three_eighths
    (a : ℕ) (ha : 2 ≤ a) (p : ℝ≥0∞)
    (hp : p ≤ 1) (hdensity : densityENN a ≤ p) :
    repeatedOffDiagK4FailureMassAt p a
        (K6Upper.momentAmplification * a ^ 2) <
      (3 : ℝ≥0∞) / 8 := by
  let t := K6Upper.momentAmplification * a ^ 2
  have hmass := repeatedOffDiagK4FailureMassAt_antitone
    a t hdensity hp
  have hfinite₀ : repeatedOffDiagK4FailureMassAt (densityENN a) a t ≠ ∞ := by
    rw [repeatedOffDiagK4FailureMassAt_density_eq,
      repeatedOffDiagK4FailureMass_eq a t ha,
      Amplification.repeatedK4FailureMass_eq a t ha]
    exact ENNReal.pow_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  have hfinite : repeatedOffDiagK4FailureMassAt p a t ≠ ∞ :=
    ne_top_of_le_ne_top hfinite₀ hmass
  apply (ENNReal.toReal_lt_toReal hfinite
    (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  simpa [t] using
    repeatedOffDiagK4FailureMassAt_toReal_lt_three_eighths
      a ha p hp hdensity

/-- Exact failure mass of the implemented fill answer segment at arbitrary
density. -/
theorem slackFill_allFailure_weight_eq_at (p : ℝ≥0∞) (a : ℕ) :
    (∑ bits : List.Vector Bool (slackFillQueryCount a),
      if slackFillAnswerEquiv a bits ∈
          allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      repeatedOffDiagK4FailureMassAt p a (slackTrialCount a) := by
  unfold repeatedOffDiagK4FailureMassAt finiteOutcomeProductMass
  apply Fintype.sum_equiv (slackFillAnswerEquiv a)
  intro bits
  by_cases hfail : slackFillAnswerEquiv a bits ∈
      allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a)
  · simp [hfail, slackFillAnswerEquiv_weight]
  · simp [hfail]

/-- Conditioned on any pre-fill answer event, the arbitrary-density fill
failure mass factors from the prefix mass. -/
theorem slackFullFailure_with_prefix_weight_eq_at
    (p : ℝ≥0∞) (a : ℕ)
    (Pbase : List.Vector Bool (slackFillStart a) → Prop)
    [DecidablePred Pbase] :
    (∑ bits : List.Vector Bool (slackQueryBudget a),
      if slackFillAnswerEquiv a (slackFillAnswerVector a bits) ∈
            allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a) ∧
          Pbase (slackBranchAnswerVector a bits) then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      repeatedOffDiagK4FailureMassAt p a (slackTrialCount a) *
        (∑ base : List.Vector Bool (slackFillStart a),
          if Pbase base then
            (base.toList.map (bernoulliWeight p)).prod else 0) := by
  have hsplit := slackAnswerSplit_event_weight_eq p a
    (fun fill => slackFillAnswerEquiv a fill ∈
      allTrialsFailEvent (offDiagTrialSucceeds a) (slackTrialCount a)) Pbase
  rw [slackFill_allFailure_weight_eq_at] at hsplit
  exact hsplit

end
end UpperFillMonotonicity
end OnlineRamsey
