import OnlineRamsey.ConcreteLowerAssembly
import OnlineRamsey.OrdinaryHistoryCount

/-!
# Uniform ordinary-prefix bounds over all edge orders

For every relative order whose nine-edge prefix is ordinary, the checked
finite table supplies a derivation.  Since the set of relative orders is
finite, we choose these derivations once and take the maximum of their
coefficients.  This produces one uniform `hcount` constant and a finite family
of explicit tails.  At the cubic query scale the sum of all those tails tends
to zero.
-/

open scoped BigOperators ENNReal NNReal
open Filter Topology

namespace OnlineRamsey
namespace OrdinaryAllOrders

open QueryComplexity LowerAssembly StoppingHistory StoppingCoverage
open PrefixSoundness RecurrenceInstantiation OrdinaryHistoryCount
open ConcreteLowerAssembly

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-! ## Fixed certificates and a uniform coefficient -/

/-- One fixed checked derivation for an ordinary order. -/
def ordinaryCertificate (π : K6EdgeOrder)
    (hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false) :
    Σ a, {D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask
          (orderedPrefixMask π ninePrefixLength)) a // 4 ≤ a} := by
  have hNine : K6Prefix.countBits K6Prefix.edgeCount
      (orderedPrefixMask π ninePrefixLength).1 = 9 :=
    countBits_orderedPrefixMask π ninePrefixLength
  let hex := ordinaryNineEdge_has_fixedDerivation
    (orderedPrefixMask π ninePrefixLength) hNine hOrdinary
  let a := Classical.choose hex
  let hexD := Classical.choose_spec hex
  let D := Classical.choose hexD
  exact ⟨a, D, Classical.choose_spec hexD⟩

/-- The cubic coefficient attached to one order, including the factor
`8^3 = 512` from the slackened pair recurrence.  Exceptional orders are
assigned coefficient zero. -/
def ordinaryCoefficientAt (π : K6EdgeOrder) : ℝ≥0 :=
  if hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false then
    512 * Derivation.coefficient (S := k6FinitePrefixSystem)
      (ordinaryCertificate π hOrdinary).2.1
  else 0

/-- One finite coefficient valid for every ordinary relative order. -/
def ordinaryUniformCoefficient : ℝ≥0 :=
  Finset.univ.sup ordinaryCoefficientAt

theorem ordinaryCoefficientAt_le_uniform (π : K6EdgeOrder) :
    ordinaryCoefficientAt π ≤ ordinaryUniformCoefficient := by
  exact Finset.le_sup (f := ordinaryCoefficientAt) (Finset.mem_univ π)

theorem selected_coefficient_le_uniform (π : K6EdgeOrder)
    (hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false) :
    512 * Derivation.coefficient (S := k6FinitePrefixSystem)
        (ordinaryCertificate π hOrdinary).2.1 ≤
      ordinaryUniformCoefficient := by
  calc
    512 * Derivation.coefficient (S := k6FinitePrefixSystem)
        (ordinaryCertificate π hOrdinary).2.1 =
        ordinaryCoefficientAt π := by
      simp [ordinaryCoefficientAt, hOrdinary]
    _ ≤ ordinaryUniformCoefficient := ordinaryCoefficientAt_le_uniform π

/-! ## The selected per-order tails -/

/-- The exact accumulated tail of the selected ordinary certificate.
Exceptional orders contribute zero. -/
def ordinaryTail (q : ℝ≥0) (hq1 : q ≤ 1) {N : ℕ} (hN : 0 < N)
    (π : K6EdgeOrder) : ℝ≥0 :=
  if hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false then
    Derivation.tail (S := k6FinitePrefixSystem)
      (M := finitePrefixSemantics 8 (q ^ 3) (by norm_num)
        (pow_le_one₀ (zero_le q) hq1) hN)
      (ordinaryCertificate π hOrdinary).2.1
  else 0

@[simp] theorem ordinaryTail_of_ordinary
    (q : ℝ≥0) (hq1 : q ≤ 1) {N : ℕ} (hN : 0 < N)
    (π : K6EdgeOrder)
    (hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false) :
    ordinaryTail q hq1 hN π =
      Derivation.tail (S := k6FinitePrefixSystem)
        (M := finitePrefixSemantics 8 (q ^ 3) (by norm_num)
          (pow_le_one₀ (zero_le q) hq1) hN)
        (ordinaryCertificate π hOrdinary).2.1 := by
  simp [ordinaryTail, hOrdinary]

/-! ## Uniform finite `hcount` -/

/-- Every ordinary order has the same main coefficient; all dependence on
the selected recurrence tree is confined to `ordinaryTail`. -/
theorem ordinary_orderPrefixHistoryMass_le_uniform
    (q : ℝ≥0) (hq1 : q ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder)
    (hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false) :
    orderPrefixHistoryMass (q ^ 3 : ℝ≥0∞) strategy π ninePrefixLength ≤
      (ordinaryUniformCoefficient : ℝ≥0∞) *
          (q ^ 3 : ℝ≥0∞) ^ 4 * (N : ℝ≥0∞) ^ 3 +
        (ordinaryTail q hq1 hN π : ℝ≥0∞) := by
  let cert := ordinaryCertificate π hOrdinary
  let a := cert.1
  let D := cert.2.1
  have hFour : 4 ≤ a := cert.2.2
  have hp3 : q ^ 3 ≤ (1 : ℝ≥0) := pow_le_one₀ (zero_le q) hq1
  have hprefix :
      extremalExpectedPrefixCopies (q ^ 3) hN
          (finitePatternOfMasks fullVertexMask
            (orderedPrefixMask π ninePrefixLength)) ≤
        Derivation.coefficient (S := k6FinitePrefixSystem) D *
            (q ^ 3) ^ 4 * (8 * (N : ℝ≥0)) ^ 3 +
          Derivation.tail (S := k6FinitePrefixSystem)
            (M := finitePrefixSemantics 8 (q ^ 3) (by norm_num) hp3 hN) D := by
    exact ordinaryNineEdge_fixedDerivation_bound D hFour (q ^ 3) hp3 hN
  have hcoefficient :
      512 * Derivation.coefficient (S := k6FinitePrefixSystem) D ≤
        ordinaryUniformCoefficient := by
    simpa [cert, D] using selected_coefficient_le_uniform π hOrdinary
  have hmain :
      Derivation.coefficient (S := k6FinitePrefixSystem) D *
          (q ^ 3) ^ 4 * (8 * (N : ℝ≥0)) ^ 3 ≤
        ordinaryUniformCoefficient * (q ^ 3) ^ 4 * (N : ℝ≥0) ^ 3 := by
    calc
      Derivation.coefficient (S := k6FinitePrefixSystem) D *
          (q ^ 3) ^ 4 * (8 * (N : ℝ≥0)) ^ 3 =
          (512 * Derivation.coefficient (S := k6FinitePrefixSystem) D) *
            (q ^ 3) ^ 4 * (N : ℝ≥0) ^ 3 := by ring
      _ ≤ ordinaryUniformCoefficient * (q ^ 3) ^ 4 * (N : ℝ≥0) ^ 3 := by
        gcongr
  have hvalue :
      extremalExpectedPrefixCopies (q ^ 3) hN
          (finitePatternOfMasks fullVertexMask
            (orderedPrefixMask π ninePrefixLength)) ≤
        ordinaryUniformCoefficient * (q ^ 3) ^ 4 * (N : ℝ≥0) ^ 3 +
          ordinaryTail q hq1 hN π := by
    refine hprefix.trans ?_
    rw [ordinaryTail_of_ordinary q hq1 hN π hOrdinary]
    exact add_le_add_right hmain _
  refine (orderPrefixHistoryMass_le_extremalExpectedPrefixCopies
    (q ^ 3) hp3 hN strategy hfresh π ninePrefixLength (by norm_num)
      (orderedPrefixMask π ninePrefixLength)
      (orderedPrefixPattern_edges π ninePrefixLength)).trans ?_
  exact_mod_cast hvalue

/-- Version in the exact branch-indexed shape expected by
`ConcreteLowerAssembly.successProbability_le_of_prefixBounds`. -/
theorem ordinaryCase_hcount
    (q : ℝ≥0) (hq1 : q ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder) (hcase : prefixCaseOfOrder π = .ordinary) :
    orderPrefixHistoryMass (q ^ 3 : ℝ≥0∞) strategy π
        (casePrefixLength (prefixCaseOfOrder π)) ≤
      (ordinaryUniformCoefficient : ℝ≥0∞) *
          (q ^ 3 : ℝ≥0∞) ^ prefixExponent (prefixCaseOfOrder π) *
            (N : ℝ≥0∞) ^ 3 +
        (ordinaryTail q hq1 hN π : ℝ≥0∞) := by
  have hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false := by
    rcases prefixCaseOfOrder_spec π with hord | hh3 | hk5 | hb4
    · exact hord.2
    · have hbad : (PrefixCase.ordinary : PrefixCase) = .halfGraph :=
        hcase.symm.trans hh3.1
      cases hbad
    · have hbad : (PrefixCase.ordinary : PrefixCase) = .almostCompleteFive :=
        hcase.symm.trans hk5.1
      cases hbad
    · have hbad : (PrefixCase.ordinary : PrefixCase) = .shiftedBipartite :=
        hcase.symm.trans hb4.1
      cases hbad
  simpa [hcase, casePrefixLength, prefixExponent] using
    ordinary_orderPrefixHistoryMass_le_uniform
      q hq1 hN strategy hfresh π hOrdinary

/-! ## Cubic-scale vanishing of all selected tails -/

/-- The chosen tail for each fixed order vanishes at
`N=floor(ell/q^10)`. -/
theorem ordinaryTail_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (π : K6EdgeOrder) :
    Tendsto (fun i ↦ ordinaryTail (q i) (hq1 i)
      (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π) l (𝓝 0) := by
  by_cases hOrdinary : K6Prefix.inExceptionalOrbit
      (orderedPrefixMask π ninePrefixLength).1 = false
  · let D := (ordinaryCertificate π hOrdinary).2.1
    have hscaleLower : ∀ᶠ i in l,
        ell / 2 ≤ q i ^ 10 *
          (nnrealQueryBudget (q i) ell : ℝ≥0) :=
      Filter.Eventually.of_forall fun i ↦
        (nnreal_normalized_queryBudget_bounds_half
          (hqpos i) (hsmall i)).1.le
    rcases cubic_query_scales_tendsto_atTop q
        (fun i ↦ nnrealQueryBudget (q i) ell) (ell / 2)
        (by positivity) hq hscaleLower with ⟨hlinear, hquadratic⟩
    have htail := finitePrefixSemantics_eight_tail_tendsto_zero_of_density
      (fun i ↦ q i ^ 3) (fun i ↦ nnrealQueryBudget (q i) ell)
      (fun i ↦ pow_le_one₀ (zero_le _) (hq1 i))
      (fun i ↦ nnrealQueryBudget_pos (hqpos i) (hsmall i))
      D (by convert hlinear using 1 <;> funext i <;> ring)
        (by convert hquadratic using 1 <;> funext i <;> ring)
    simpa [ordinaryTail, hOrdinary, D] using htail
  · simpa [ordinaryTail, hOrdinary] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ι ↦ (0 : ℝ≥0)) l (𝓝 0))

/-- Because there are only `15!` relative orders, the sum of all ordinary
recurrence tails also tends to zero. -/
theorem ordinaryTail_sum_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    Tendsto (fun i ↦ ∑ π : K6EdgeOrder,
      ordinaryTail (q i) (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π) l (𝓝 0) := by
  have hsum : Tendsto (fun i ↦ ∑ π : K6EdgeOrder,
      ordinaryTail (q i) (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π) l
      (𝓝 (∑ _π : K6EdgeOrder, (0 : ℝ≥0))) := by
    apply tendsto_finset_sum Finset.univ
    intro π _
    exact ordinaryTail_tendsto_zero_queryBudget
      q ell hell hq hqpos hq1 hsmall π
  simpa using hsum

/-- The complete ordinary branch of the all-orders `hcount` at the actual
floored cubic budget, together with simultaneous vanishing of its finite tail
sum. -/
theorem ordinary_allOrders_queryBudget_hcount
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    (∀ i, ∀ strategy : K6Strategy (nnrealQueryBudget (q i) ell),
      FreshForBudget strategy → ∀ π,
      prefixCaseOfOrder π = .ordinary →
      orderPrefixHistoryMass (q i ^ 3 : ℝ≥0∞) strategy π
          (casePrefixLength (prefixCaseOfOrder π)) ≤
        (ordinaryUniformCoefficient : ℝ≥0∞) *
            (q i ^ 3 : ℝ≥0∞) ^ prefixExponent (prefixCaseOfOrder π) *
              (nnrealQueryBudget (q i) ell : ℝ≥0∞) ^ 3 +
          (ordinaryTail (q i) (hq1 i)
            (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π : ℝ≥0∞)) ∧
      Tendsto (fun i ↦ ∑ π : K6EdgeOrder,
        ordinaryTail (q i) (hq1 i)
          (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π) l (𝓝 0) := by
  constructor
  · intro i strategy hfresh π hcase
    exact ordinaryCase_hcount (q i) (hq1 i)
      (nnrealQueryBudget_pos (hqpos i) (hsmall i))
      strategy hfresh π hcase
  · exact ordinaryTail_sum_tendsto_zero_queryBudget
      q ell hell hq hqpos hq1 hsmall

end
end OrdinaryAllOrders
end OnlineRamsey
