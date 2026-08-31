import OnlineRamsey.CanonicalB4Completion
import OnlineRamsey.AdaptiveHostTruncation
import OnlineRamsey.ConcreteLowerAssembly

/-!
# Expected stopping-prefix bounds for all three exceptional orbits

This file combines the canonical ordered-prefix mask with the deterministic
`HostGood` estimates and an exact finite good/bad board decomposition.  The
error term is the probability that either the sampled host is not uniform or
the adaptive transcript exceeds the prescribed positive-edge budget.
-/

open scoped BigOperators ENNReal NNReal

namespace OnlineRamsey
namespace StoppingPrefixCount

open QueryComplexity PrefixSoundness RecurrenceInstantiation
open PatternGraphBridge ExceptionalPrefixBounds AdaptiveHostTruncation
open StoppingHistory StoppingCoverage

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Simultaneous uniform-host and transcript-edge goodness. -/
def exceptionalGoodEvent {N : ℕ} (strategy : K6Strategy N)
    (M D L c₂ c₃ : ℕ) : Set (Board (Query N)) :=
  RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃ ∩
    transcriptEdgeGoodEvent strategy M

/-- The exact finite bad mass retained by every exceptional `hcount`. -/
noncomputable def exceptionalBadMass {N : ℕ} (p : ℝ≥0)
    (strategy : K6Strategy N) (M D L c₂ c₃ : ℕ) : ℝ≥0∞ :=
  finiteBoardMass (bernoulliWeight (p : ℝ≥0∞))
    (exceptionalGoodEvent strategy M D L c₂ c₃)ᶜ

/-- The retained error is bounded by the independent random-host failure
mass plus the exact adaptive binomial tail for seeing more than `M` positive
answers. -/
theorem exceptionalBadMass_le_hostFailure_add_upperTail
    {N M D L c₂ c₃ : ℕ} (p : unitInterval)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy) :
    exceptionalBadMass (unitInterval.toNNReal p) strategy M D L c₂ c₃ ≤
      RandomBoard.bitBoardMeasure (Query N) p
          (RandomBoard.randomHostGoodEvent (2 * N) M D L c₂ c₃)ᶜ +
        bernoulliUpperTail (unitInterval.toNNReal p : ℝ≥0∞) N (M + 1) := by
  simpa [exceptionalBadMass, exceptionalGoodEvent] using
    (hostEdgeGood_compl_mass_le (N := N) (M := M) (D := D)
      (L := L) (c₂ := c₂) (c₃ := c₃) p strategy hfresh)

set_option maxHeartbeats 800000 in
/-- Generic bridge from a pointwise deterministic bound on good boards to a
per-order prefix-history bound.  The crude bad-board factor is exactly the
number `(2N)^6` of labelled maps; there is no time or automorphism
multiplicity. -/
theorem orderPrefixHistoryMass_le_good_add_exceptionalBadMass
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder) (r : K6PrefixLength) (hr : 0 < r.val)
    (g : Fin K6Prefix.graphCount)
    (hmatch : PatternMatchesOrderPrefix
      (finitePatternOfMasks fullVertexMask g) π r)
    (M D L c₂ c₃ B : ℕ)
    (hgood : ∀ board ∈ exceptionalGoodEvent strategy M D L c₂ c₃,
      prefixCopyCount hN (finitePatternOfMasks fullVertexMask g)
        (run strategy board N) ≤ B) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy π r ≤
      (B : ℝ≥0∞) + (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
        exceptionalBadMass p strategy M D L c₂ c₃ := by
  refine (orderPrefixHistoryMass_le_strategyExpectedPrefixCopies
    p hp hN strategy hfresh (finitePatternOfMasks fullVertexMask g)
      π r hr hmatch).trans ?_
  rw [strategyExpectedPrefixCopies_coe_eq_boardSum
    p hp hN strategy hfresh (finitePatternOfMasks fullVertexMask g)]
  let count : Board (Query N) → ℕ := fun board ↦ prefixCopyCount hN
    (finitePatternOfMasks fullVertexMask g) (run strategy board N)
  let good : Set (Board (Query N)) :=
    exceptionalGoodEvent strategy M D L c₂ c₃
  have hgood' : ∀ board ∈ good, count board ≤ B := by
    simpa [count, good] using hgood
  have hcrude : ∀ board, count board ≤ (2 * N) ^ 6 := fun board ↦ by
    dsimp only [count]
    simpa [PatternGraphBridge.fullPattern_active] using
      (prefixCopyCount_le hN (finitePatternOfMasks fullVertexMask g)
        (run strategy board N))
  have htrunc := weightedCount_le_goodBound_add_badMass
    (E := Query N) (bernoulliWeight (p : ℝ≥0∞))
    (sum_bernoulliWeight (p : ℝ≥0∞) (by exact_mod_cast hp))
    count good B ((2 * N) ^ 6) hgood' hcrude
  simpa only [count, good, exceptionalBadMass] using htrunc

theorem h3_orderNinePrefixHistoryMass_le
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder) {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (hH3 : K6Prefix.h3Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy π ninePrefixLength ≤
      (2 * ((6 * c₂ * (2 * L) * M) * M) : ℕ) +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass p strategy M D L c₂ c₃ := by
  apply orderPrefixHistoryMass_le_good_add_exceptionalBadMass
    p hp hN strategy hfresh π ninePrefixLength (by norm_num)
      (orderPrefixMask π ninePrefixLength)
      (orderPrefixPattern_matches π ninePrefixLength)
      M D L c₂ c₃ (2 * ((6 * c₂ * (2 * L) * M) * M))
  intro board hboard
  rcases hboard with ⟨hhost, hedges⟩
  change edgeCount (positiveGraph (run strategy board N)) ≤ M at hedges
  refine (h3Orbit_prefixCopyCount_sharp_le hN hD
    (RandomBoard.randomHost (2 * N) board) hhost
    (run strategy board N)
    (positiveGraph_run_le_randomHost strategy board) hedges
    (orderPrefixMask π ninePrefixLength) hH3).trans ?_
  gcongr

theorem k5_orderNinePrefixHistoryMass_le
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder) {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (hK5 : K6Prefix.k5MinusEdgePlusIsolateOrbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy π ninePrefixLength ≤
      (((24 * c₃ * (2 * L * L)) * M) * (2 * N) : ℕ) +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass p strategy M D L c₂ c₃ := by
  apply orderPrefixHistoryMass_le_good_add_exceptionalBadMass
    p hp hN strategy hfresh π ninePrefixLength (by norm_num)
      (orderPrefixMask π ninePrefixLength)
      (orderPrefixPattern_matches π ninePrefixLength)
      M D L c₂ c₃ (((24 * c₃ * (2 * L * L)) * M) * (2 * N))
  intro board hboard
  rcases hboard with ⟨hhost, hedges⟩
  change edgeCount (positiveGraph (run strategy board N)) ≤ M at hedges
  refine (k5Orbit_prefixCopyCount_sharp_le hN hD
    (RandomBoard.randomHost (2 * N) board) hhost
    (run strategy board N)
    (positiveGraph_run_le_randomHost strategy board) hedges
    (orderPrefixMask π ninePrefixLength) hK5).trans ?_
  simpa using Nat.mul_le_mul_right (2 * N)
    (Nat.mul_le_mul_left (24 * c₃ * (2 * L * L)) hedges)

/-- Pointwise `Q` bound for the actual canonical ten-edge continuation of a
classified `B₄` prefix. -/
theorem b4_canonicalTen_prefixCopyCount_le
    {N M D L c₂ c₃ : ℕ} (hN : 0 < N)
    (hD : 0 < D)
    (π : K6EdgeOrder)
    (hB4 : K6Prefix.b4Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true)
    (host : SimpleGraph (Vertex N))
    (hhost : RandomBoard.HostGood host M D L c₂ c₃)
    (h : Transcript (Query N)) (hsub : positiveGraph h ≤ host)
    (hedges : edgeCount (positiveGraph h) ≤ M) :
    prefixCopyCount hN (finitePatternOfMasks fullVertexMask
      (orderPrefixMask π tenPrefixLength)) h ≤
        (c₂ * c₂ * (24 * (2 * L * L))) * edgeCount (positiveGraph h) := by
  rw [fullPattern_prefixCopyCount_eq_labelledCopies]
  obtain ⟨iso⟩ := canonicalTenPrefix_iso_Q_of_nine_mem_b4Orbit π hB4
  rw [labelledCopies_eq_of_iso iso]
  exact HostGood.subgraphLabelledQ_sharp_le hD hhost hsub hedges

theorem b4_orderTenPrefixHistoryMass_le
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder) {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (hB4 : K6Prefix.b4Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    orderPrefixHistoryMass (p : ℝ≥0∞) strategy π tenPrefixLength ≤
      ((c₂ * c₂ * (24 * (2 * L * L))) * M : ℕ) +
        (((2 * N) ^ 6 : ℕ) : ℝ≥0∞) *
          exceptionalBadMass p strategy M D L c₂ c₃ := by
  apply orderPrefixHistoryMass_le_good_add_exceptionalBadMass
    p hp hN strategy hfresh π tenPrefixLength (by norm_num)
      (orderPrefixMask π tenPrefixLength)
      (orderPrefixPattern_matches π tenPrefixLength)
      M D L c₂ c₃ ((c₂ * c₂ * (24 * (2 * L * L))) * M)
  intro board hboard
  rcases hboard with ⟨hhost, hedges⟩
  change edgeCount (positiveGraph (run strategy board N)) ≤ M at hedges
  exact (b4_canonicalTen_prefixCopyCount_le hN hD π hB4
    (RandomBoard.randomHost (2 * N) board) hhost (run strategy board N)
      (positiveGraph_run_le_randomHost strategy board) hedges).trans
        (Nat.mul_le_mul_left (c₂ * c₂ * (24 * (2 * L * L))) hedges)

end
end StoppingPrefixCount
end OnlineRamsey
