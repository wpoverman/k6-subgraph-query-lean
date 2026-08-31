import OnlineRamsey.ExceptionalHistoryCount
import OnlineRamsey.B4SharpScale
import OnlineRamsey.SmallEllBadMass
import OnlineRamsey.ConcreteLowerAssembly

/-!
# The complete shifted-`B₄` prefix estimate at cubic scale

This file combines the canonical tenth-edge stopping theorem with the sharp
`Q` count and the rounded-scale arithmetic.  The result has precisely the
`p⁵N³` prefix main term expected by the four-case lower assembly; the only
remaining summand is the explicit good/bad truncation error.
-/

open scoped BigOperators ENNReal NNReal
open Filter Topology

namespace OnlineRamsey
namespace B4SharpScale

open AsymptoticScale HostGoodProbability QueryComplexity
open StoppingHistory StoppingCoverage StoppingPrefixCount
open PrefixSoundness RecurrenceInstantiation
open AdaptiveHostTruncation
open ConcreteLowerAssembly LowerAssembly

noncomputable section

/-- The full per-order shifted-`B₄` prefix estimate, at
`N=floor(ell/q¹⁰)`, for arbitrary fixed positive `ell`. -/
theorem b4_orderTenPrefixHistoryMass_cubicScale_le
    {q ell B₃ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder)
    (hB4 : K6Prefix.b4Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    orderPrefixHistoryMass
        (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞)
        strategy π tenPrefixLength ≤
      3583180800 *
          (unitInterval.toNNReal (cubeProbability q hq.le hq1) : ℝ≥0∞) ^ 5 *
          (queryBudget q ell : ℝ≥0∞) ^ 3 +
        (((2 * queryBudget q ell) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass
            (unitInterval.toNNReal (cubeProbability q hq.le hq1)) strategy
            (edgeBudget q 8 (queryBudget q ell))
            (degeneracyBudget q 4
              (edgeBudget q 8 (queryBudget q ell))) 90
            (scaledPairBound q 12 (queryBudget q ell))
            (scaledTripleBound q B₃ (queryBudget q ell)) := by
  let N := queryBudget q ell
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := scaledPairBound q 12 N
  let c₃ := scaledTripleBound q B₃ N
  let p : unitInterval := cubeProbability q hq.le hq1
  have htargets := queryBudget_pair_edge_targets_ge_one hq hell
    (by norm_num : (0 : ℝ) < 12) (by norm_num : (0 : ℝ) < 8)
      hfloor hpairSmall hedgeSmall
  have hN : 0 < N := by
    have hq10 : 0 < q ^ 10 := pow_pos hq _
    have hq10le : q ^ 10 ≤ ell := by linarith [hfloor]
    have htarget : 1 ≤ ell / q ^ 10 :=
      (le_div_iff₀ hq10).2 (by simpa using hq10le)
    dsimp [N, queryBudget]
    exact Nat.floor_pos.mpr htarget
  have hM : 0 < M := by
    have htarget : 8 * q ^ 3 * (N : ℝ) ≤ (M : ℝ) := by
      simpa [M] using edgeBudget_target_le q 8 N
    have hone : (1 : ℝ) ≤ (M : ℝ) := htargets.2.trans htarget
    exact_mod_cast (show (0 : ℝ) < (M : ℝ) from lt_of_lt_of_le (by norm_num) hone)
  have hD : 0 < D := by
    dsimp [D, degeneracyBudget]
    apply Nat.ceil_pos.mpr
    have hinside : 0 < q ^ 3 * (M : ℝ) :=
      mul_pos (pow_pos hq _) (by exact_mod_cast hM)
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 hinside)
  have hraw := b4_orderTenPrefixHistoryMass_le
    (unitInterval.toNNReal p) (RandomBoard.toNNReal_le_one p) hN
      strategy hfresh π (M := M) (D := D) (L := 90) (c₂ := c₂) (c₃ := c₃)
      hD hB4
  have hmain : ((sharpQMain q 12 8 90 N : ℕ) : ℝ≥0∞) ≤
      3583180800 * (unitInterval.toNNReal p : ℝ≥0∞) ^ 5 *
        (N : ℝ≥0∞) ^ 3 := by
    exact sharpQMain_c8_L90_coe_le hq.le hq1 htargets.1 htargets.2
  change orderPrefixHistoryMass (unitInterval.toNNReal p : ℝ≥0∞)
      strategy π tenPrefixLength ≤ _
  calc
    orderPrefixHistoryMass (unitInterval.toNNReal p : ℝ≥0∞)
        strategy π tenPrefixLength ≤
      ((sharpQMain q 12 8 90 N : ℕ) : ℝ≥0∞) +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal p) strategy
            M D 90 c₂ c₃ := by
      simpa [sharpQMain, N, M, D, c₂, c₃, p] using hraw
    _ ≤ 3583180800 * (unitInterval.toNNReal p : ℝ≥0∞) ^ 5 *
          (N : ℝ≥0∞) ^ 3 +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal p) strategy
            M D 90 c₂ c₃ := add_le_add_right hmain _
    _ = _ := by rfl

/-- The same bound with the truncation error split into the actual random-host
failure and the already-controlled adaptive pair tail.  This is the form
consumed by asymptotic lower-bound assembly. -/
theorem b4_orderTenPrefixHistoryMass_explicitError_le
    {q ell : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hell : 0 < ell)
    (hfloor : 2 * q ^ 10 ≤ ell)
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder)
    (hB4 : K6Prefix.b4Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    let N := queryBudget q ell
    let pUI := cubeProbability q hq.le hq1
    let M := edgeBudget q 8 N
    let D := degeneracyBudget q 4 M
    let c₂ := scaledPairBound q 12 N
    let c₃ := scaledTripleBound q (560 / ell) N
    let H := finitePatternOfMasks fullVertexMask
      (orderPrefixMask π tenPrefixLength)
    orderPrefixHistoryMass (unitInterval.toNNReal pUI : ℝ≥0∞)
        strategy π tenPrefixLength ≤
      3583180800 * (unitInterval.toNNReal pUI : ℝ≥0∞) ^ 5 *
          (N : ℝ≥0∞) ^ 3 +
        ((((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
            RandomBoard.bitBoardMeasure (Query N) pUI
              (RandomBoard.randomHostGoodEvent
                (2 * N) M D 90 c₂ c₃)ᶜ +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞)) := by
  dsimp only
  let N := queryBudget q ell
  let pUI := cubeProbability q hq.le hq1
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := scaledPairBound q 12 N
  let c₃ := scaledTripleBound q (560 / ell) N
  let H := finitePatternOfMasks fullVertexMask
    (orderPrefixMask π tenPrefixLength)
  have hbase := b4_orderTenPrefixHistoryMass_cubicScale_le
    (B₃ := 560 / ell) hq hq1 hell hfloor hpairSmall hedgeSmall
      strategy hfresh π hB4
  have hsplit := scaledHostEdgeGood_crudeSixVertex_le
    (ell := ell) (A := 4) (B₂ := 12) (B₃ := 560 / ell) (L := 90)
      hq hq1 strategy hfresh H
  have hsplit' :
      (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal pUI) strategy
            M D 90 c₂ c₃ ≤
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
            RandomBoard.bitBoardMeasure (Query N) pUI
              (RandomBoard.randomHostGoodEvent
                (2 * N) M D 90 c₂ c₃)ᶜ +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞) := by
    simpa [exceptionalBadMass, exceptionalGoodEvent, N, pUI, M, D, c₂, c₃, H]
      using hsplit
  dsimp only [N, pUI, M, D, c₂, c₃, H] at hbase hsplit' ⊢
  exact hbase.trans (add_le_add_left hsplit' _)

/-- Fully numeric small-`ell` shifted-`B₄` estimate.  The host error retains
ten positive powers of `q` even after the crude six-label count, and the
adaptive error is exactly the common pair tail used in the ordinary branch. -/
theorem b4_orderTenPrefixHistoryMass_smallEll_le
    {q ell : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * q ≤ (4 : ℝ) * √(8 * ell / 2))
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (queryBudget q ell))
    (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder)
    (hB4 : K6Prefix.b4Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    let N := queryBudget q ell
    let pUI := cubeProbability q hq.le (hqhalf.trans (by norm_num))
    let H := finitePatternOfMasks fullVertexMask
      (orderPrefixMask π tenPrefixLength)
    orderPrefixHistoryMass (unitInterval.toNNReal pUI : ℝ≥0∞)
        strategy π tenPrefixLength ≤
      3583180800 * (unitInterval.toNNReal pUI : ℝ≥0∞) ^ 5 *
          (N : ℝ≥0∞) ^ 3 +
        (ENNReal.ofReal (64 * ell ^ 6 * q ^ 10) +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞)) := by
  dsimp only
  let N := queryBudget q ell
  let pUI := cubeProbability q hq.le (hqhalf.trans (by norm_num))
  let M := edgeBudget q 8 N
  let D := degeneracyBudget q 4 M
  let c₂ := scaledPairBound q 12 N
  let c₃ := scaledTripleBound q (560 / ell) N
  let H := finitePatternOfMasks fullVertexMask
    (orderPrefixMask π tenPrefixLength)
  have hbase := b4_orderTenPrefixHistoryMass_cubicScale_le
    (B₃ := 560 / ell) hq (hqhalf.trans (by norm_num)) hell0 hscale
      hpairSmall hedgeSmall strategy hfresh π hB4
  have hbad := SmallEllBadMass.scaledSmallEllHostEdgeGood_crudeSixVertex_le
    hq hqhalf hell0 hell1 hscale hpairScale hdense strategy hfresh H
  have hbad' :
      (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass (unitInterval.toNNReal pUI) strategy
            M D 90 c₂ c₃ ≤
        ENNReal.ofReal (64 * ell ^ 6 * q ^ 10) +
          (pairTail 8 (unitInterval.toNNReal pUI) N H : ℝ≥0∞) := by
    simpa [exceptionalBadMass, exceptionalGoodEvent, N, pUI, M, D, c₂, c₃, H]
      using hbad
  dsimp only [N, pUI, M, D, c₂, c₃, H] at hbase hbad' ⊢
  exact hbase.trans (add_le_add_left hbad' _)

/-! ## Branch-indexed form and a strategy-independent vanishing error -/

/-- The complete shifted-`B₄` error attached to one relative edge order.

It is deliberately `NNReal`-valued: this makes finite summation and passage
to the limit use the ordinary continuous semiring topology.  Its coercion to
`ENNReal` is exactly the two error terms in
`b4_orderTenPrefixHistoryMass_smallEll_le`. -/
noncomputable def b4Error (q ell : ℝ≥0) (π : K6EdgeOrder) : ℝ≥0 :=
  64 * ell ^ 6 * q ^ 10 +
    pairTail 8 (q ^ 3) (nnrealQueryBudget q ell)
      (finitePatternOfMasks fullVertexMask
        (orderPrefixMask π tenPrefixLength))

/-- The shifted-`B₄` estimate in the exact branch-indexed interface used
by the unconditional four-case assembly. -/
theorem b4Case_hcount
    (q ell : ℝ≥0) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hscale : 2 * q ^ 10 ≤ ell)
    (hpairScale : 40 * q ^ 3 ≤ ell)
    (hdense : 160 * (q : ℝ) ≤
      (4 : ℝ) * √(8 * (ell : ℝ) / 2))
    (hpairSmall : 2 * q ^ 4 ≤ 12 * ell)
    (hedgeSmall : 2 * q ^ 7 ≤ 8 * ell)
    (strategy : K6Strategy (nnrealQueryBudget q ell))
    (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder)
    (hcase : prefixCaseOfOrder π = .shiftedBipartite) :
    orderPrefixHistoryMass (q ^ 3 : ℝ≥0∞) strategy π
        (casePrefixLength (prefixCaseOfOrder π)) ≤
      3583180800 *
          (q ^ 3 : ℝ≥0∞) ^ prefixExponent (prefixCaseOfOrder π) *
            (nnrealQueryBudget q ell : ℝ≥0∞) ^ 3 +
        (b4Error q ell π : ℝ≥0∞) := by
  have hB4 : K6Prefix.b4Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true := by
    rcases prefixCaseOfOrder_spec π with hord | hh3 | hk5 | hb4
    · have hbad : (PrefixCase.shiftedBipartite : PrefixCase) = .ordinary :=
        hcase.symm.trans hord.1
      cases hbad
    · have hbad : (PrefixCase.shiftedBipartite : PrefixCase) = .halfGraph :=
        hcase.symm.trans hh3.1
      cases hbad
    · have hbad : (PrefixCase.shiftedBipartite : PrefixCase) =
          .almostCompleteFive := hcase.symm.trans hk5.1
      cases hbad
    · exact hb4.2
  have hraw := b4_orderTenPrefixHistoryMass_smallEll_le
    (q := (q : ℝ)) (ell := (ell : ℝ))
    (by exact_mod_cast hq) (by exact_mod_cast hqhalf)
    (by exact_mod_cast hell0) (by exact_mod_cast hell1)
    (by exact_mod_cast hscale) (by exact_mod_cast hpairScale) hdense
    (by exact_mod_cast hpairSmall) (by exact_mod_cast hedgeSmall)
    strategy hfresh π hB4
  dsimp only at hraw
  rw [SmallEllBadMass.toNNReal_cubeProbability_eq q
    (hqhalf.trans (by norm_num))] at hraw
  simpa [hcase, casePrefixLength, prefixExponent, b4Error,
    nnrealQueryBudget] using hraw

/-- For every fixed relative edge order, the strategy-independent shifted-
`B₄` error vanishes at the floored cubic query budget. -/
theorem b4Error_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (π : K6EdgeOrder) :
    Tendsto (fun i ↦ b4Error (q i) ell π) l (𝓝 0) := by
  have hq0 : Tendsto q l (𝓝 0) := hq.mono_right inf_le_left
  have hscaleLower : ∀ᶠ i in l,
      ell / 2 ≤ q i ^ 10 *
        (nnrealQueryBudget (q i) ell : ℝ≥0) :=
    Filter.Eventually.of_forall fun i ↦
      (nnreal_normalized_queryBudget_bounds_half
        (hqpos i) (hsmall i)).1.le
  rcases cubic_query_scales_tendsto_atTop q
      (fun i ↦ nnrealQueryBudget (q i) ell) (ell / 2)
      (by positivity) hq hscaleLower with ⟨hlinear, hquadratic⟩
  have hpair : Tendsto (fun i ↦
      pairTail 8 (q i ^ 3) (nnrealQueryBudget (q i) ell)
        (finitePatternOfMasks fullVertexMask
          (orderPrefixMask π tenPrefixLength))) l (𝓝 0) :=
    pairTail_eight_tendsto_zero_of_density
      (fun i ↦ q i ^ 3) (fun i ↦ nnrealQueryBudget (q i) ell)
      (finitePatternOfMasks fullVertexMask
        (orderPrefixMask π tenPrefixLength))
      (fun i ↦ pow_le_one₀ (zero_le _) (hq1 i))
      (by convert hlinear using 1 <;> funext i <;> ring)
      (by convert hquadratic using 1 <;> funext i <;> ring)
  have hhost : Tendsto (fun i ↦
      (64 : ℝ≥0) * ell ^ 6 * q i ^ 10) l (𝓝 0) := by
    have hc : Tendsto (fun _ : ι ↦ (64 : ℝ≥0) * ell ^ 6) l
        (𝓝 ((64 : ℝ≥0) * ell ^ 6)) := tendsto_const_nhds
    simpa using hc.mul (hq0.pow 10)
  simpa [b4Error] using hhost.add hpair

/-- Since there are finitely many relative orders, the sum of all shifted-
`B₄` errors also vanishes. -/
theorem b4Error_sum_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    Tendsto (fun i ↦ ∑ π : K6EdgeOrder, b4Error (q i) ell π)
      l (𝓝 0) := by
  have hsum : Tendsto
      (fun i ↦ ∑ π : K6EdgeOrder, b4Error (q i) ell π) l
      (𝓝 (∑ _π : K6EdgeOrder, (0 : ℝ≥0))) := by
    apply tendsto_finset_sum Finset.univ
    intro π _
    exact b4Error_tendsto_zero_queryBudget
      q ell hell hq hqpos hq1 hsmall π
  simpa using hsum

end
end B4SharpScale
end OnlineRamsey
