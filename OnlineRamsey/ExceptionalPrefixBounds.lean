import OnlineRamsey.PatternGraphBridge
import OnlineRamsey.ExceptionalOrbitBridge
import OnlineRamsey.SharpExceptional

/-!
# Deterministic host bounds in executable-prefix form

The finite Bellman classifier counts mask embeddings, while the host lemmas
count labelled `SimpleGraph` copies.  This file composes the exact
representation equalities with the sharp host estimates for each canonical
exceptional representative.
-/

namespace OnlineRamsey
namespace ExceptionalPrefixBounds

open QueryComplexity PrefixSoundness RecurrenceInstantiation PatternGraphBridge
open ExceptionalOrbitBridge

noncomputable section

theorem h3Mask_prefixCopyCount_sharp_le {N M D L c₂ c₃ : ℕ}
    (hN : 0 < N) (hD : 0 < D)
    (host : SimpleGraph (Vertex N))
    (hhost : RandomBoard.HostGood host M D L c₂ c₃)
    (h : Transcript (Query N))
    (hsub : positiveGraph h ≤ host)
    (hedges : edgeCount (positiveGraph h) ≤ M) :
    prefixCopyCount hN
        (finitePatternOfMasks fullVertexMask h3Mask) h ≤
      2 * ((6 * c₂ * (2 * L) * M) *
        edgeCount (positiveGraph h)) := by
  rw [h3Mask_prefixCopyCount_eq hN h]
  exact HostGood.subgraphLabelledH3_sharp_le
    hD hhost hsub hedges

theorem k5MinusEdgePlusIsolateMask_prefixCopyCount_sharp_le
    {N M D L c₂ c₃ : ℕ}
    (hN : 0 < N) (hD : 0 < D)
    (host : SimpleGraph (Vertex N))
    (hhost : RandomBoard.HostGood host M D L c₂ c₃)
    (h : Transcript (Query N))
    (hsub : positiveGraph h ≤ host)
    (hedges : edgeCount (positiveGraph h) ≤ M) :
    prefixCopyCount hN
        (finitePatternOfMasks fullVertexMask
          k5MinusEdgePlusIsolateMask) h ≤
      ((24 * c₃ * (2 * L * L)) * edgeCount (positiveGraph h)) *
        Fintype.card (Vertex N) := by
  rw [k5MinusEdgePlusIsolateMask_prefixCopyCount_eq hN h]
  exact HostGood.subgraphLabelledK5MinusEdgeIsolated_sharp_le
    hD hhost hsub hedges

theorem qCompletionMask_prefixCopyCount_le
    {N M D L c₂ c₃ : ℕ}
    (hN : 0 < N)
    (host : SimpleGraph (Vertex N))
    (hhost : RandomBoard.HostGood host M D L c₂ c₃)
    (h : Transcript (Query N))
    (hsub : positiveGraph h ≤ host) :
    prefixCopyCount hN
        (finitePatternOfMasks fullVertexMask qCompletionMask) h ≤
      (c₂ * c₂ * (2 * c₂ * c₂)) *
        edgeCount (positiveGraph h) := by
  rw [qCompletionMask_prefixCopyCount_eq hN h]
  exact HostGood.subgraphLabelledQ_le hhost hsub

/-! ## Arbitrary members of the checked exceptional orbits -/

theorem h3Orbit_prefixCopyCount_sharp_le
    {N M D L c₂ c₃ : ℕ}
    (hN : 0 < N) (hD : 0 < D)
    (host : SimpleGraph (Vertex N))
    (hhost : RandomBoard.HostGood host M D L c₂ c₃)
    (h : Transcript (Query N))
    (hsub : positiveGraph h ≤ host)
    (hedges : edgeCount (positiveGraph h) ≤ M)
    (g : Fin K6Prefix.graphCount)
    (hg : K6Prefix.h3Orbit[g.1]! = true) :
    prefixCopyCount hN (finitePatternOfMasks fullVertexMask g) h ≤
      2 * ((6 * c₂ * (2 * L) * M) *
        edgeCount (positiveGraph h)) := by
  rw [fullPattern_prefixCopyCount_eq_labelledCopies]
  obtain ⟨iso⟩ := exists_iso_H3_of_mem_orbit g hg
  rw [labelledCopies_eq_of_iso iso]
  exact HostGood.subgraphLabelledH3_sharp_le hD hhost hsub hedges

theorem k5Orbit_prefixCopyCount_sharp_le
    {N M D L c₂ c₃ : ℕ}
    (hN : 0 < N) (hD : 0 < D)
    (host : SimpleGraph (Vertex N))
    (hhost : RandomBoard.HostGood host M D L c₂ c₃)
    (h : Transcript (Query N))
    (hsub : positiveGraph h ≤ host)
    (hedges : edgeCount (positiveGraph h) ≤ M)
    (g : Fin K6Prefix.graphCount)
    (hg : K6Prefix.k5MinusEdgePlusIsolateOrbit[g.1]! = true) :
    prefixCopyCount hN (finitePatternOfMasks fullVertexMask g) h ≤
      ((24 * c₃ * (2 * L * L)) * edgeCount (positiveGraph h)) *
        Fintype.card (Vertex N) := by
  rw [fullPattern_prefixCopyCount_eq_labelledCopies]
  obtain ⟨iso⟩ := exists_iso_K5MinusEdgeIsolated_of_mem_orbit g hg
  rw [labelledCopies_eq_of_iso iso]
  exact HostGood.subgraphLabelledK5MinusEdgeIsolated_sharp_le
    hD hhost hsub hedges

/-- An arbitrary checked `B₄` prefix admits the equivariant tenth-edge
completion, and that completion has the deterministic `Q` charge bound. -/
theorem b4Orbit_exists_qCompletion_prefixCopyCount_le
    {N M D L c₂ c₃ : ℕ}
    (hN : 0 < N)
    (host : SimpleGraph (Vertex N))
    (hhost : RandomBoard.HostGood host M D L c₂ c₃)
    (h : Transcript (Query N))
    (hsub : positiveGraph h ≤ host)
    (g : Fin K6Prefix.graphCount)
    (hg : K6Prefix.b4Orbit[g.1]! = true) :
    ∃ (g₁₀ : Fin K6Prefix.graphCount) (e : K6Edge),
      e ∈ (finitePatternOfMasks fullVertexMask g₁₀).edges ∧
      eraseFiniteEdge (finitePatternOfMasks fullVertexMask g₁₀) e =
        finitePatternOfMasks fullVertexMask g ∧
      prefixCopyCount hN (finitePatternOfMasks fullVertexMask g₁₀) h ≤
        (c₂ * c₂ * (2 * c₂ * c₂)) *
          edgeCount (positiveGraph h) := by
  obtain ⟨g₁₀, e, he, herase, ⟨iso⟩⟩ :=
    exists_qCompletion_of_mem_b4Orbit g hg
  refine ⟨g₁₀, e, he, herase, ?_⟩
  rw [fullPattern_prefixCopyCount_eq_labelledCopies]
  rw [labelledCopies_eq_of_iso iso]
  exact HostGood.subgraphLabelledQ_le hhost hsub

end
end ExceptionalPrefixBounds
end OnlineRamsey
