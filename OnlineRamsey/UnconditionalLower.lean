import OnlineRamsey.UnifiedAllCasesHCount
import OnlineRamsey.SmallEllMainCoefficient
import OnlineRamsey.LowerBudgetTransfer

/-!
# Unconditional lower bound for the `K₆` subgraph-query game

This file chooses the fixed normalized query scale, gathers the finitely many
small-density side conditions, obtains a forbidden canonical floor budget,
and packages that obstruction as a positive global lower constant.
-/

open scoped BigOperators ENNReal NNReal
open Filter Topology

namespace OnlineRamsey
namespace UnconditionalLower

open QueryComplexity RecurrenceInstantiation AllCasesHistoryCount
open SmallEllError SmallEllMainCoefficient UnifiedAllCasesHCount
open LowerBudgetTransfer

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 1000000

/-- A convenient positive fallback density satisfying the three global
hypotheses required by the error-limit theorem. -/
theorem half_ell_is_admissible
    {ell : ℝ≥0} (hell0 : 0 < ell) (hell1 : ell ≤ 1) :
    0 < ell / 2 ∧ ell / 2 ≤ 1 ∧ 2 * (ell / 2) ^ 10 ≤ ell := by
  have hr0 : 0 < ell / 2 := div_pos hell0 (by norm_num)
  have hr1 : ell / 2 ≤ 1 := by
    calc
      ell / 2 ≤ ell := div_le_self (zero_le ell) (by norm_num)
      _ ≤ 1 := hell1
  have hrpow : (ell / 2) ^ 9 ≤ 1 :=
    pow_le_one₀ (zero_le (ell / 2)) hr1
  refine ⟨hr0, hr1, ?_⟩
  calc
    2 * (ell / 2) ^ 10 = (2 * (ell / 2)) * (ell / 2) ^ 9 := by ring
    _ = ell * (ell / 2) ^ 9 := by
      congr 1
      field_simp
    _ ≤ ell * 1 := mul_le_mul_left' hrpow ell
    _ = ell := mul_one _

/-- Although the existing tail limit is stated for families satisfying the
positivity and floor hypotheses at every index, it yields the expected local
statement for the identity density on a punctured neighborhood of zero. -/
theorem eventually_factorial_combinedError_lt_quarter
    (ell : ℝ≥0) (hell0 : 0 < ell) (hell1 : ell ≤ 1) :
    ∀ᶠ q in nhdsWithin (0 : ℝ≥0) (Set.Ioi 0),
      ∀ (hq : 0 < q) (hq1 : q ≤ 1) (hfloor : 2 * q ^ 10 ≤ ell),
        (Nat.factorial 15 : ℝ≥0∞) *
          (smallEllCombinedError q ell hq1
            (nnrealQueryBudget_pos hq hfloor) : ℝ≥0∞) <
          (4 : ℝ≥0∞)⁻¹ := by
  let r : ℝ≥0 := ell / 2
  let admissible : ℝ≥0 → Prop := fun q ↦
    0 < q ∧ q ≤ 1 ∧ 2 * q ^ 10 ≤ ell
  let safeQ : ℝ≥0 → ℝ≥0 := fun q ↦ if admissible q then q else r
  have hr := half_ell_is_admissible hell0 hell1
  have hsafe_pos : ∀ q, 0 < safeQ q := by
    intro q
    by_cases hq : admissible q
    · simpa [safeQ, hq] using hq.1
    · simpa [safeQ, hq, r] using hr.1
  have hsafe_one : ∀ q, safeQ q ≤ 1 := by
    intro q
    by_cases hq : admissible q
    · simpa [safeQ, hq] using hq.2.1
    · simpa [safeQ, hq, r] using hr.2.1
  have hsafe_floor : ∀ q, 2 * safeQ q ^ 10 ≤ ell := by
    intro q
    by_cases hq : admissible q
    · simpa [safeQ, hq] using hq.2.2
    · simpa [safeQ, hq, r] using hr.2.2
  let l : Filter ℝ≥0 := nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)
  have hid : Tendsto (fun q : ℝ≥0 ↦ q) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hone : ∀ᶠ q in l, q ≤ 1 :=
    ((tendsto_order.mp hid).2 1 (by norm_num)).mono fun _ h ↦ h.le
  have hscaleTendsto : Tendsto (fun q : ℝ≥0 ↦ 2 * q ^ 10) l (nhds 0) := by
    simpa using (hid.pow 10).const_mul (2 : ℝ≥0)
  have hfloorEventually : ∀ᶠ q in l, 2 * q ^ 10 ≤ ell :=
    ((tendsto_order.mp hscaleTendsto).2 ell hell0).mono fun _ h ↦ h.le
  have hpositive : ∀ᶠ q in l, 0 < q := self_mem_nhdsWithin
  have hsafe_eq : safeQ =ᶠ[l] (fun q : ℝ≥0 ↦ q) := by
    filter_upwards [hpositive, hone, hfloorEventually] with q hq hq1 hfloor
    simp [safeQ, admissible, hq, hq1, hfloor]
  have hsafe_tendsto : Tendsto safeQ l
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hid.congr' hsafe_eq.symm, ?_⟩
    exact Filter.Eventually.of_forall hsafe_pos
  have herrorSafe := eventually_factorial_mul_smallEllCombinedError_lt
    safeQ ell hell0 hsafe_tendsto hsafe_pos hsafe_one hsafe_floor
      ((4 : ℝ≥0∞)⁻¹) (by norm_num)
  filter_upwards [herrorSafe, hsafe_eq] with q herror hsafe
  intro hq hq1 hfloor
  simpa [hsafe] using herror

/-- Extract a positive interval cutoff from an eventual statement on the
punctured right neighborhood of zero. -/
theorem exists_cutoff_of_eventually_right
    {P : ℝ≥0 → Prop}
    (hP : ∀ᶠ q in nhdsWithin (0 : ℝ≥0) (Set.Ioi 0), P q) :
    ∃ q₀ : ℝ≥0, 0 < q₀ ∧ q₀ ≤ 1 ∧
      ∀ q : ℝ≥0, 0 < q → q < q₀ → P q := by
  change {q : ℝ≥0 | P q} ∈
    nhdsWithin (0 : ℝ≥0) (Set.Ioi 0) at hP
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hP
  rcases hP with ⟨U, hU, hsub⟩
  rcases NNReal.nhds_zero_basis.mem_iff.mp hU with ⟨a, ha, haU⟩
  let q₀ : ℝ≥0 := min a 1
  have hq₀ : 0 < q₀ := by simp [q₀, ha]
  refine ⟨q₀, hq₀, min_le_right _ _, ?_⟩
  intro q hq hqq₀
  apply hsub
  exact ⟨haU (hqq₀.trans_le (min_le_left _ _)), hq⟩

/-- All elementary scale hypotheses needed by the host-counting estimate hold
simultaneously for sufficiently small positive density. -/
theorem eventually_small_density_sideConditions
    (ell : ℝ≥0) (hell0 : 0 < ell) :
    ∀ᶠ q in nhdsWithin (0 : ℝ≥0) (Set.Ioi 0),
      q ≤ 1 / 2 ∧
      2 * q ^ 10 ≤ ell ∧
      2 * q ^ 4 ≤ 12 * ell ∧
      2 * q ^ 7 ≤ 8 * ell ∧
      40 * q ^ 3 ≤ ell ∧
      160 * (q : ℝ) ≤ (4 : ℝ) * √(8 * (ell : ℝ) / 2) := by
  let l : Filter ℝ≥0 := nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)
  have hid : Tendsto (fun q : ℝ≥0 ↦ q) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hhalf : ∀ᶠ q in l, q ≤ 1 / 2 :=
    ((tendsto_order.mp hid).2 (1 / 2) (by norm_num)).mono fun _ h ↦ h.le
  have hpow10 : Tendsto (fun q : ℝ≥0 ↦ 2 * q ^ 10) l (nhds 0) := by
    simpa using (hid.pow 10).const_mul (2 : ℝ≥0)
  have hfloor : ∀ᶠ q in l, 2 * q ^ 10 ≤ ell :=
    ((tendsto_order.mp hpow10).2 ell hell0).mono fun _ h ↦ h.le
  have hpow4 : Tendsto (fun q : ℝ≥0 ↦ 2 * q ^ 4) l (nhds 0) := by
    simpa using (hid.pow 4).const_mul (2 : ℝ≥0)
  have hpair : ∀ᶠ q in l, 2 * q ^ 4 ≤ 12 * ell :=
    ((tendsto_order.mp hpow4).2 (12 * ell)
      (mul_pos (by norm_num) hell0)).mono fun _ h ↦ h.le
  have hpow7 : Tendsto (fun q : ℝ≥0 ↦ 2 * q ^ 7) l (nhds 0) := by
    simpa using (hid.pow 7).const_mul (2 : ℝ≥0)
  have hedge : ∀ᶠ q in l, 2 * q ^ 7 ≤ 8 * ell :=
    ((tendsto_order.mp hpow7).2 (8 * ell)
      (mul_pos (by norm_num) hell0)).mono fun _ h ↦ h.le
  have hpow3 : Tendsto (fun q : ℝ≥0 ↦ 40 * q ^ 3) l (nhds 0) := by
    simpa using (hid.pow 3).const_mul (40 : ℝ≥0)
  have hpairScale : ∀ᶠ q in l, 40 * q ^ 3 ≤ ell :=
    ((tendsto_order.mp hpow3).2 ell hell0).mono fun _ h ↦ h.le
  have hcoe : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ)) l (nhds 0) :=
    NNReal.tendsto_coe.mpr hid
  have hlinear : Tendsto (fun q : ℝ≥0 ↦ 160 * (q : ℝ)) l
      (nhds 0) := by
    simpa using hcoe.const_mul (160 : ℝ)
  have hrhs : 0 < (4 : ℝ) * √(8 * (ell : ℝ) / 2) := by
    have hellReal : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell0
    positivity
  have hdense : ∀ᶠ q : ℝ≥0 in l,
      160 * (q : ℝ) ≤ (4 : ℝ) * √(8 * (ell : ℝ) / 2) :=
    ((tendsto_order.mp hlinear).2 _ hrhs).mono fun _ h ↦ h.le
  filter_upwards [hhalf, hfloor, hpair, hedge, hpairScale, hdense] with
    q hqhalf hqfloor hqpair hqedge hqpairScale hqdense
  exact ⟨hqhalf, hqfloor, hqpair, hqedge, hqpairScale, hqdense⟩

/-- The floored cubic query scale contributes at most `ell³` to the target
monomial. -/
theorem nnrealQueryBudget_targetMonomial_le
    {q ell : ℝ≥0} (hq : 0 < q) (hfloor : 2 * q ^ 10 ≤ ell) :
    (((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10) *
        (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3 ≤
      (ell : ℝ≥0∞) ^ 3 := by
  have hscaleNN := (nnreal_normalized_queryBudget_bounds_half hq hfloor).2
  have hcubicNN :
      (q ^ 10 * (nnrealQueryBudget q ell : ℝ≥0)) ^ 3 ≤ ell ^ 3 :=
    pow_le_pow_left₀ (zero_le _) hscaleNN 3
  have hcubicENN :
      (((q ^ 10 * (nnrealQueryBudget q ell : ℝ≥0)) ^ 3 : ℝ≥0) :
          ℝ≥0∞) ≤ ((ell ^ 3 : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hcubicNN
  have hcubicENN' :
      (((q : ℝ≥0∞) ^ 10) *
        (nnrealQueryBudget q ell : ℝ≥0∞)) ^ 3 ≤
          (ell : ℝ≥0∞) ^ 3 := by
    simpa only [ENNReal.coe_mul, ENNReal.coe_pow, Nat.cast_ofNat]
      using hcubicENN
  calc
    (((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10) *
        (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3 =
      (((q : ℝ≥0∞) ^ 10) *
        (nnrealQueryBudget q ell : ℝ≥0∞)) ^ 3 := by
          norm_num only [ENNReal.coe_pow]
          ring
    _ ≤ (ell : ℝ≥0∞) ^ 3 := hcubicENN'

/-- There are fixed positive constants `q₀` and `ell` such that every
canonical floor budget below `q₀` is forbidden. -/
theorem exists_small_density_queryBudget_obstruction :
    ∃ q₀ ell : ℝ≥0,
      0 < q₀ ∧ q₀ ≤ 1 ∧ 0 < ell ∧
      ∀ q : ℝ≥0, 0 < q → q ≤ 1 → q < q₀ →
        ¬ Achievable ((q ^ 3 : ℝ≥0) : ℝ≥0∞)
          (nnrealQueryBudget q ell) := by
  rcases exists_smallEll_main_lt_quarter with
    ⟨ell, hell0, hell1, hmain⟩
  have hside := eventually_small_density_sideConditions ell hell0
  have herror := eventually_factorial_combinedError_lt_quarter ell hell0 hell1
  have hall : ∀ᶠ q in nhdsWithin (0 : ℝ≥0) (Set.Ioi 0),
      (q ≤ 1 / 2 ∧
        2 * q ^ 10 ≤ ell ∧
        2 * q ^ 4 ≤ 12 * ell ∧
        2 * q ^ 7 ≤ 8 * ell ∧
        40 * q ^ 3 ≤ ell ∧
        160 * (q : ℝ) ≤ (4 : ℝ) * √(8 * (ell : ℝ) / 2)) ∧
      (∀ (hq : 0 < q) (hq1 : q ≤ 1) (hfloor : 2 * q ^ 10 ≤ ell),
        (Nat.factorial 15 : ℝ≥0∞) *
          (smallEllCombinedError q ell hq1
            (nnrealQueryBudget_pos hq hfloor) : ℝ≥0∞) <
          (4 : ℝ≥0∞)⁻¹) := hside.and herror
  rcases exists_cutoff_of_eventually_right hall with
    ⟨q₀, hq₀0, hq₀1, hq₀⟩
  refine ⟨q₀, ell, hq₀0, hq₀1, hell0, ?_⟩
  intro q hq hq1 hqq₀
  rcases hq₀ q hq hqq₀ with
    ⟨⟨hqhalf, hfloor, hpairSmall, hedgeSmall, hpairScale, hdense⟩,
      herrorAt⟩
  have hq1' : q ≤ 1 := hqhalf.trans (by norm_num)
  have herrorQuarter := herrorAt hq hq1' hfloor
  have hmonomial := nnrealQueryBudget_targetMonomial_le hq hfloor
  have hmainQuarter :
      (Nat.factorial 15 : ℝ≥0∞) *
          (allCasesCoefficient ell *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10 *
            (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3) <
        (4 : ℝ≥0∞)⁻¹ := by
    calc
      (Nat.factorial 15 : ℝ≥0∞) *
          (allCasesCoefficient ell *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10 *
            (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3) =
          (Nat.factorial 15 : ℝ≥0∞) * allCasesCoefficient ell *
            ((((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10) *
              (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3) := by
        ac_rfl
      _ ≤ (Nat.factorial 15 : ℝ≥0∞) * allCasesCoefficient ell *
          (ell : ℝ≥0∞) ^ 3 := mul_le_mul_left' hmonomial _
      _ < (4 : ℝ≥0∞)⁻¹ := hmain
  have hsmall :
      (Nat.factorial 15 : ℝ≥0∞) *
          (allCasesCoefficient ell *
            ((q ^ 3 : ℝ≥0) : ℝ≥0∞) ^ 10 *
            (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3) +
        (Nat.factorial 15 : ℝ≥0∞) *
          (smallEllCombinedError q ell hq1'
            (nnrealQueryBudget_pos hq hfloor) : ℝ≥0∞) < threshold := by
    have hadd := ENNReal.add_lt_add hmainQuarter herrorQuarter
    have hquarters :
        (4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹ =
          (2 : ℝ≥0∞)⁻¹ := by
      change (((4 : ℝ≥0) : ℝ≥0∞))⁻¹ +
          (((4 : ℝ≥0) : ℝ≥0∞))⁻¹ =
        (((2 : ℝ≥0) : ℝ≥0∞))⁻¹
      rw [← ENNReal.coe_inv (r := (4 : ℝ≥0)) (by norm_num),
        ← ENNReal.coe_inv (r := (2 : ℝ≥0)) (by norm_num),
        ← ENNReal.coe_add]
      norm_num
    exact hadd.trans_eq (by simpa [threshold] using hquarters)
  exact not_achievable_of_combinedError_lt_threshold q ell hq hqhalf
    hell0 hell1 hfloor hpairSmall hedgeSmall hpairScale hdense hsmall

/-- Unconditional global lower bound: every achievable `K₆` query budget
has normalized size bounded below by one fixed positive constant. -/
theorem exists_global_queryBudget_lower_constant :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
        ∀ N : ℕ, Achievable (q ^ 3) N →
          c ≤ (N : ℝ≥0∞) * q ^ 10 := by
  rcases exists_small_density_queryBudget_obstruction with
    ⟨q₀, ell, hq₀0, hq₀1, hell0, hforbidden⟩
  let c : ℝ≥0∞ := min (ell : ℝ≥0∞)
    (15 * (q₀ : ℝ≥0∞) ^ 10)
  refine ⟨c, ?_, ?_⟩
  · exact global_queryBudget_lower_constant_pos hq₀0 hell0
  · exact global_lower_of_queryBudget_obstruction q₀ ell hq₀1 hforbidden

end
end UnconditionalLower
end OnlineRamsey
