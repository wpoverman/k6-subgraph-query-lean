import OnlineRamsey.OrdinaryAllOrders
import OnlineRamsey.SmallEllBadMass

/-!
# Vanishing of the complete small-`ell` error

At the floored cubic query scale `N = floor(ell / q^10)`, this module
packages the three errors that remain after the deterministic prefix counts:

* the random-host term `64 * ell^6 * q^10` (for the host with `B₂ = 12`);
* the explicit adaptive pair tail for each relative edge order;
* the finite family of accumulated ordinary recurrence tails.

Their sum tends to zero as `q → 0⁺`.  The final uniform corollary says that,
eventually, the error attached to every one of the finitely many edge orders
is smaller than any prescribed positive slack.
-/

open scoped BigOperators ENNReal NNReal
open Filter Topology

namespace OnlineRamsey
namespace SmallEllError

open QueryComplexity LowerAssembly StoppingHistory StoppingCoverage
open PrefixSoundness RecurrenceInstantiation ConcreteLowerAssembly
open OrdinaryAllOrders StoppingPrefixCount

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-- The host-failure term left after the crude six-label count.  This is the
`NNReal` form of `ENNReal.ofReal (64 * ell^6 * q^10)` from
`SmallEllBadMass`. -/
def smallEllHostError (q ell : ℝ≥0) : ℝ≥0 :=
  64 * ell ^ 6 * q ^ 10

theorem coe_smallEllHostError_eq_ofReal (q ell : ℝ≥0) :
    (smallEllHostError q ell : ℝ≥0∞) =
      ENNReal.ofReal (64 * (ell : ℝ) ^ 6 * (q : ℝ) ^ 10) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1

/-- The selected stopping-prefix pattern for a relative edge order.  The
pattern parameter does not change the numerical pair tail, but retaining it
makes later applications match the exceptional prefix-count theorems
definitionally. -/
def selectedPrefixPattern (π : K6EdgeOrder) : K6FinitePattern :=
  finitePatternOfMasks fullVertexMask
    (orderPrefixMask π (casePrefixLength (prefixCaseOfOrder π)))

/-- The adaptive positive-answer overflow attached to one selected prefix. -/
def selectedPairTail (q ell : ℝ≥0) (π : K6EdgeOrder) : ℝ≥0 :=
  pairTail 8 (q ^ 3) (nnrealQueryBudget q ell) (selectedPrefixPattern π)

/-- A single nonnegative error which dominates the error of order `π`, no
matter whether `π` is ordinary or exceptional.  In an ordinary branch the
host and standalone pair terms are harmless extra upper bounds; in an
exceptional branch `ordinaryTail` is zero. -/
def unifiedPerOrderError (q ell : ℝ≥0) (hq1 : q ≤ 1)
    (hN : 0 < nnrealQueryBudget q ell) (π : K6EdgeOrder) : ℝ≥0 :=
  smallEllHostError q ell + selectedPairTail q ell π +
    ordinaryTail q hq1 hN π

/-- One aggregate which simultaneously dominates every per-order error.
There is one host term, followed by the two finite sums of order-dependent
tails. -/
def smallEllCombinedError (q ell : ℝ≥0) (hq1 : q ≤ 1)
    (hN : 0 < nnrealQueryBudget q ell) : ℝ≥0 :=
  smallEllHostError q ell +
    ∑ π : K6EdgeOrder, selectedPairTail q ell π +
    ∑ π : K6EdgeOrder, ordinaryTail q hq1 hN π

theorem unifiedPerOrderError_le_combined
    (q ell : ℝ≥0) (hq1 : q ≤ 1)
    (hN : 0 < nnrealQueryBudget q ell) (π : K6EdgeOrder) :
    unifiedPerOrderError q ell hq1 hN π ≤
      smallEllCombinedError q ell hq1 hN := by
  have hpair : selectedPairTail q ell π ≤
      ∑ π' : K6EdgeOrder, selectedPairTail q ell π' := by
    exact Finset.single_le_sum (fun _ _ ↦ zero_le _)
      (Finset.mem_univ π)
  have hord : ordinaryTail q hq1 hN π ≤
      ∑ π' : K6EdgeOrder, ordinaryTail q hq1 hN π' := by
    exact Finset.single_le_sum (fun _ _ ↦ zero_le _)
      (Finset.mem_univ π)
  exact add_le_add (add_le_add_left hpair _) hord

/-! ## The three limits -/

theorem smallEllHostError_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0)
    (hq : Tendsto q l (𝓝[>] 0)) :
    Tendsto (fun i ↦ smallEllHostError (q i) ell) l (𝓝 0) := by
  have hq0 : Tendsto q l (𝓝 0) := (tendsto_nhdsWithin_iff.mp hq).1
  simpa [smallEllHostError] using
    (hq0.pow 10).const_mul (64 * ell ^ 6)

/-- Each standalone adaptive pair tail vanishes at the floored cubic scale. -/
theorem selectedPairTail_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (π : K6EdgeOrder) :
    Tendsto (fun i ↦ selectedPairTail (q i) ell π) l (𝓝 0) := by
  have hscaleLower : ∀ᶠ i in l,
      ell / 2 ≤ q i ^ 10 *
        (nnrealQueryBudget (q i) ell : ℝ≥0) :=
    Filter.Eventually.of_forall fun i ↦
      (nnreal_normalized_queryBudget_bounds_half
        (hqpos i) (hsmall i)).1.le
  rcases cubic_query_scales_tendsto_atTop q
      (fun i ↦ nnrealQueryBudget (q i) ell) (ell / 2)
      (by positivity) hq hscaleLower with ⟨hlinear, hquadratic⟩
  simpa [selectedPairTail] using
    (pairTail_eight_tendsto_zero_of_density
      (fun i ↦ q i ^ 3)
      (fun i ↦ nnrealQueryBudget (q i) ell)
      (selectedPrefixPattern π)
      (fun i ↦ pow_le_one₀ (zero_le _) (hq1 i))
      hlinear
      (by
        convert hquadratic using 1
        funext i
        ring))

/-- Finiteness of the relative-order type makes the sum of all standalone
adaptive pair tails vanish as well. -/
theorem selectedPairTail_sum_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    Tendsto (fun i ↦ ∑ π : K6EdgeOrder,
      selectedPairTail (q i) ell π) l (𝓝 0) := by
  have hsum : Tendsto (fun i ↦ ∑ π : K6EdgeOrder,
      selectedPairTail (q i) ell π) l
      (𝓝 (∑ _π : K6EdgeOrder, (0 : ℝ≥0))) := by
    apply tendsto_finset_sum Finset.univ
    intro π _
    exact selectedPairTail_tendsto_zero_queryBudget
      q ell hell hq hqpos hq1 hsmall π
  simpa using hsum

/-! ## Combined and uniform forms -/

/-- The host error, all standalone adaptive pair tails, and all selected
ordinary derivation tails tend to zero simultaneously. -/
theorem smallEllCombinedError_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    Tendsto (fun i ↦ smallEllCombinedError (q i) ell (hq1 i)
      (nnrealQueryBudget_pos (hqpos i) (hsmall i))) l (𝓝 0) := by
  have hhost := smallEllHostError_tendsto_zero q ell hq
  have hpair := selectedPairTail_sum_tendsto_zero_queryBudget
    q ell hell hq hqpos hq1 hsmall
  have hord := ordinaryTail_sum_tendsto_zero_queryBudget
    q ell hell hq hqpos hq1 hsmall
  simpa [smallEllCombinedError] using (hhost.add hpair).add hord

/-- The `ENNReal` coercion of the complete error also tends to zero; this is
the codomain used by the finite all-orders assembly. -/
theorem coe_smallEllCombinedError_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    Tendsto (fun i ↦
      (smallEllCombinedError (q i) ell (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) : ℝ≥0∞))
      l (𝓝 0) := by
  exact ENNReal.tendsto_coe.mpr
    (smallEllCombinedError_tendsto_zero_queryBudget
      q ell hell hq hqpos hq1 hsmall)

/-- Multiplying the aggregate by any fixed finite constant preserves the
zero limit.  In particular, callers may take `C = 15!` when bounding the
sum over all relative edge orders. -/
theorem coe_const_mul_smallEllCombinedError_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell C : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    Tendsto (fun i ↦ (C : ℝ≥0∞) *
      (smallEllCombinedError (q i) ell (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) : ℝ≥0∞))
      l (𝓝 0) := by
  have hNN := (smallEllCombinedError_tendsto_zero_queryBudget
    q ell hell hq hqpos hq1 hsmall).const_mul C
  apply ENNReal.tendsto_coe.mpr
  simpa using hNN

/-- The concrete `15!` multiplier used by the all-orders assembly. -/
theorem coe_factorial_mul_smallEllCombinedError_tendsto_zero_queryBudget
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell) :
    Tendsto (fun i ↦ (Nat.factorial 15 : ℝ≥0∞) *
      (smallEllCombinedError (q i) ell (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) : ℝ≥0∞))
      l (𝓝 0) := by
  simpa using
    (coe_const_mul_smallEllCombinedError_tendsto_zero_queryBudget
      q ell (Nat.factorial 15 : ℝ≥0) hell hq hqpos hq1 hsmall)

/-- Epsilon form of the factorial-multiplied error used in the simplified
success-probability bound. -/
theorem eventually_factorial_mul_smallEllCombinedError_lt
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ i in l, (Nat.factorial 15 : ℝ≥0∞) *
      (smallEllCombinedError (q i) ell (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) : ℝ≥0∞) < ε := by
  exact (tendsto_order.mp
    (coe_factorial_mul_smallEllCombinedError_tendsto_zero_queryBudget
      q ell hell hq hqpos hq1 hsmall)).2 ε hε

/-- Epsilon form for the aggregate error itself. -/
theorem eventually_coe_smallEllCombinedError_lt
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ i in l,
      (smallEllCombinedError (q i) ell (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) : ℝ≥0∞) < ε := by
  exact (tendsto_order.mp
    (coe_smallEllCombinedError_tendsto_zero_queryBudget
      q ell hell hq hqpos hq1 hsmall)).2 ε hε

/-- Epsilon form: after passing far enough down the small-density filter,
every relative edge order has unified error below the same positive slack. -/
theorem eventually_unifiedPerOrderError_lt
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ π : K6EdgeOrder,
      unifiedPerOrderError (q i) ell (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π < ε := by
  have hcombined := smallEllCombinedError_tendsto_zero_queryBudget
    q ell hell hq hqpos hq1 hsmall
  have heventually := (tendsto_order.mp hcombined).2 ε hε
  filter_upwards [heventually] with i hi
  intro π
  exact (unifiedPerOrderError_le_combined
    (q i) ell (hq1 i)
      (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π).trans_lt hi

/-- The same uniform epsilon statement directly in `ENNReal`.  It permits
any positive (possibly infinite) slack and is ready for use in
`ConcreteLowerAssembly`. -/
theorem eventually_coe_unifiedPerOrderError_lt
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ π : K6EdgeOrder,
      (unifiedPerOrderError (q i) ell (hq1 i)
        (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π : ℝ≥0∞) < ε := by
  have hcombined := coe_smallEllCombinedError_tendsto_zero_queryBudget
    q ell hell hq hqpos hq1 hsmall
  have heventually := (tendsto_order.mp hcombined).2 ε hε
  filter_upwards [heventually] with i hi
  intro π
  have hleNN := unifiedPerOrderError_le_combined
    (q i) ell (hq1 i)
      (nnrealQueryBudget_pos (hqpos i) (hsmall i)) π
  exact (ENNReal.coe_le_coe.mpr hleNN).trans_lt hi

end
end SmallEllError
end OnlineRamsey
