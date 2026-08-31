import OnlineRamsey.RecurrenceInstantiation
import OnlineRamsey.H3Labelled
import OnlineRamsey.ExceptionalLabelled

/-!
# From executable mask patterns to `SimpleGraph` copies

The Bellman table uses fifteen-bit edge masks, while the sharp exceptional
estimates use Mathlib `SimpleGraph`s.  This file gives the missing exact
representation bridge on the full six-label vertex mask.  No quotient by
isomorphism is involved: both sides count injective labelled maps.
-/

namespace OnlineRamsey
namespace PatternGraphBridge

open RecurrenceInstantiation PrefixSoundness QueryComplexity

noncomputable section

/-- The mathematical simple graph denoted by a finite mask pattern. -/
def patternGraph (H : K6FinitePattern) : SimpleGraph (Fin 6) where
  Adj u v := ∃ e ∈ H.edges,
    (edgeLo e = u ∧ edgeHi e = v) ∨
      (edgeLo e = v ∧ edgeHi e = u)
  symm := by
    rintro u v ⟨e, he, huv | huv⟩
    · exact ⟨e, he, Or.inr ⟨huv.1, huv.2⟩⟩
    · exact ⟨e, he, Or.inl ⟨huv.1, huv.2⟩⟩
  loopless := by
    rintro u ⟨e, _he, huu | huu⟩
    · exact (ne_of_lt (edgeLo_lt_edgeHi e)) (huu.1.trans huu.2.symm)
    · exact (ne_of_lt (edgeLo_lt_edgeHi e)) (huu.1.trans huu.2.symm)

@[simp] theorem patternGraph_adj (H : K6FinitePattern) (u v : Fin 6) :
    (patternGraph H).Adj u v ↔ ∃ e ∈ H.edges,
      (edgeLo e = u ∧ edgeHi e = v) ∨
        (edgeLo e = v ∧ edgeHi e = u) :=
  Iff.rfl

/-- Adjacency of the executable finite pattern has a computable decision
procedure, needed by the closed representative checks below. -/
instance patternGraphDecidableAdj (H : K6FinitePattern) :
    DecidableRel (patternGraph H).Adj := by
  intro u v
  change Decidable (∃ e ∈ H.edges,
    (edgeLo e = u ∧ edgeHi e = v) ∨
      (edgeLo e = v ∧ edgeHi e = u))
  infer_instance

/-- The concrete union-of-edges presentation of `H₃` is decidable.  We
name the instance here so the closed representative computation below uses
only executable decision procedures. -/
instance h3GraphDecidableAdj : DecidableRel H3Graph.Adj := by
  intro u v
  exact decidable_of_iff
    ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
     (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨
     (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
     (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨
     (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0) ∨
     (u = 0 ∧ v = 5) ∨ (u = 5 ∧ v = 0) ∨
     (u = 1 ∧ v = 4) ∨ (u = 4 ∧ v = 1) ∨
     (u = 1 ∧ v = 5) ∨ (u = 5 ∧ v = 1) ∨
     (u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2))
    (by
      simp [H3Graph, SimpleGraph.edge_adj]
      aesop)

/-- Turn a prefix embedding into a Mathlib graph copy when every pattern
label is active. -/
def prefixEmbeddingToCopy {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (hactive : activeLabels H = Finset.univ)
    (h : Transcript (Query N)) :
    PrefixEmbedding hN H h → (patternGraph H).Copy (positiveGraph h) :=
  fun f => by
    classical
    have hf : IsPrefixEmbedding hN H h f.1 :=
      (Finset.mem_filter.mp f.2).2
    let hom : patternGraph H →g positiveGraph h :=
      { toFun := f.1
        map_rel' := by
          rintro u v ⟨e, he, huv | huv⟩
          · rw [← huv.1, ← huv.2]
            exact hf.2.2.2 e he
          · rw [← huv.1, ← huv.2]
            exact (hf.2.2.2 e he).symm }
    refine ⟨hom, ?_⟩
    intro u v huv
    apply hf.2.2.1
    · rw [hactive]
      simp
    · rw [hactive]
      simp
    · exact huv

/-- Turn a Mathlib copy back into the executable prefix representation. -/
def copyToPrefixEmbedding {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (hactive : activeLabels H = Finset.univ)
    (hvalid : ValidPattern H) (h : Transcript (Query N)) :
    (patternGraph H).Copy (positiveGraph h) → PrefixEmbedding hN H h :=
  fun f => by
    classical
    refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    refine ⟨hvalid, ?_, ?_, ?_⟩
    · intro v hv
      exfalso
      apply hv
      rw [hactive]
      exact Finset.mem_univ v
    · intro u hu v hv huv
      exact f.injective huv
    · intro e he
      apply f.toHom.map_adj
      exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- The two representation maps are inverse without changing the underlying
six-label function. -/
def prefixEmbeddingEquivCopy {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (hactive : activeLabels H = Finset.univ)
    (hvalid : ValidPattern H) (h : Transcript (Query N)) :
    PrefixEmbedding hN H h ≃ (patternGraph H).Copy (positiveGraph h) where
  toFun := prefixEmbeddingToCopy hN H hactive h
  invFun := copyToPrefixEmbedding hN H hactive hvalid h
  left_inv := by
    intro f
    apply Subtype.ext
    rfl
  right_inv := by
    intro f
    apply SimpleGraph.Copy.ext
    intro v
    rfl

/-- Exact labelled-count equality for any valid pattern whose six labels are
all active. -/
theorem prefixCopyCount_eq_labelledCopies {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (hactive : activeLabels H = Finset.univ)
    (hvalid : ValidPattern H) (h : Transcript (Query N)) :
    prefixCopyCount hN H h = labelledCopies (positiveGraph h) (patternGraph H) := by
  classical
  calc
    prefixCopyCount hN H h = Fintype.card (PrefixEmbedding hN H h) := by
      simp [prefixCopyCount]
    _ = Fintype.card ((patternGraph H).Copy (positiveGraph h)) :=
      Fintype.card_congr (prefixEmbeddingEquivCopy hN H hactive hvalid h)
    _ = Nat.card ((patternGraph H).Copy (positiveGraph h)) :=
      Nat.card_eq_fintype_card.symm
    _ = labelledCopies (positiveGraph h) (patternGraph H) :=
      natCard_copy_eq_labelledCopies (positiveGraph h) (patternGraph H)

private theorem fullPattern_active_aux :
    ∀ g : Fin K6Prefix.graphCount,
      activeLabels (finitePatternOfMasks fullVertexMask g) = Finset.univ := by
  native_decide

theorem fullPattern_active (g : Fin K6Prefix.graphCount) :
    activeLabels (finitePatternOfMasks fullVertexMask g) = Finset.univ :=
  fullPattern_active_aux g

theorem fullPattern_valid (g : Fin K6Prefix.graphCount) :
    ValidPattern (finitePatternOfMasks fullVertexMask g) := by
  intro e he
  rw [edgeAllowedBy_iff_mem_activeLabels, fullPattern_active g]
  simp

/-- The exact count bridge in the form used for every nine-edge mask. -/
theorem fullPattern_prefixCopyCount_eq_labelledCopies {N : ℕ} (hN : 0 < N)
    (g : Fin K6Prefix.graphCount) (h : Transcript (Query N)) :
    prefixCopyCount hN (finitePatternOfMasks fullVertexMask g) h =
      labelledCopies (positiveGraph h)
        (patternGraph (finitePatternOfMasks fullVertexMask g)) :=
  prefixCopyCount_eq_labelledCopies hN _ (fullPattern_active g)
    (fullPattern_valid g) h

/-! ## Relabelling invariance of labelled copy counts -/

/-- Precomposing a labelled copy by a graph isomorphism gives an exact
equivalence of copy types. -/
def copyEquivOfIso {A B W : Type*}
    {GA : SimpleGraph A} {GB : SimpleGraph B} (e : GA ≃g GB)
    (G : SimpleGraph W) : GA.Copy G ≃ GB.Copy G where
  toFun f := f.comp e.symm.toCopy
  invFun f := f.comp e.toCopy
  left_inv := by
    intro f
    apply SimpleGraph.Copy.ext
    intro v
    simp
  right_inv := by
    intro f
    apply SimpleGraph.Copy.ext
    intro v
    simp

/-- `labelledCopies` depends only on the isomorphism type of the pattern,
with no hidden automorphism factor. -/
theorem labelledCopies_eq_of_iso {A B W : Type*}
    [Fintype A] [Fintype B] [Fintype W]
    {GA : SimpleGraph A} {GB : SimpleGraph B} (e : GA ≃g GB)
    (G : SimpleGraph W) :
    labelledCopies G GA = labelledCopies G GB := by
  rw [← natCard_copy_eq_labelledCopies,
    ← natCard_copy_eq_labelledCopies]
  exact Nat.card_congr (copyEquivOfIso e G)

/-! ## Canonical exceptional representative -/

/-- The `H₃` representative mask as an inhabitant of the finite graph type. -/
def h3Mask : Fin K6Prefix.graphCount :=
  ⟨K6Prefix.h3, by native_decide⟩

/-- The executable representative denotes exactly the concrete Mathlib
half-graph used by the deterministic charge. -/
theorem patternGraph_h3Mask :
    patternGraph (finitePatternOfMasks fullVertexMask h3Mask) = H3Graph := by
  ext u v
  fin_cases u <;> fin_cases v <;> native_decide

/-- Consequently the executable `H₃` prefix count is literally the
labelled `SimpleGraph` copy count. -/
theorem h3Mask_prefixCopyCount_eq {N : ℕ} (hN : 0 < N)
    (h : Transcript (Query N)) :
    prefixCopyCount hN (finitePatternOfMasks fullVertexMask h3Mask) h =
      labelledCopies (positiveGraph h) H3Graph := by
  rw [fullPattern_prefixCopyCount_eq_labelledCopies, patternGraph_h3Mask]

/-! ## The isolated `K₅-e` representative -/

/-- The checked isolated exceptional representative as a bounded mask. -/
def k5MinusEdgePlusIsolateMask : Fin K6Prefix.graphCount :=
  ⟨K6Prefix.k5MinusEdgePlusIsolate, by native_decide⟩

/-- Relabel the missing edge `{0,1}` of the executable representative to the
missing edge `{3,4}` used by `K5MinusEdgeGraph`; label `5` stays isolated. -/
def k5IsolatedRelabel : Fin 6 ≃ Fin 6 :=
  (Equiv.swap (0 : Fin 6) 3).trans (Equiv.swap (1 : Fin 6) 4)

/-- The executable isolated representative is graph-isomorphic to the
canonical charged pattern. -/
def patternGraph_k5MinusEdgePlusIsolate_iso :
    patternGraph (finitePatternOfMasks fullVertexMask
      k5MinusEdgePlusIsolateMask) ≃g K5MinusEdgeIsolatedGraph where
  toEquiv := k5IsolatedRelabel
  map_rel_iff' := by
    intro u v
    fin_cases u <;> fin_cases v <;>
      simp [patternGraph, finitePatternOfMasks, edgeFinsetOfMask,
        k5MinusEdgePlusIsolateMask, k5IsolatedRelabel,
        K5MinusEdgeIsolatedGraph, K5MinusEdgeGraph,
        finFiveIntoSix, SimpleGraph.edge_adj] <;> native_decide

/-- Exact count bridge for the second canonical exceptional mask. -/
theorem k5MinusEdgePlusIsolateMask_prefixCopyCount_eq {N : ℕ}
    (hN : 0 < N) (h : Transcript (Query N)) :
    prefixCopyCount hN
        (finitePatternOfMasks fullVertexMask k5MinusEdgePlusIsolateMask) h =
      labelledCopies (positiveGraph h) K5MinusEdgeIsolatedGraph := by
  rw [fullPattern_prefixCopyCount_eq_labelledCopies]
  exact labelledCopies_eq_of_iso
    patternGraph_k5MinusEdgePlusIsolate_iso (positiveGraph h)

/-! ## The shifted bipartite representative and its tenth edge -/

/-- The checked `B₄` representative as a bounded mask. -/
def b4Mask : Fin K6Prefix.graphCount :=
  ⟨K6Prefix.b4, by native_decide⟩

/-- `B₄ = K₂ ∨ I₄`, in the exact labels used by the checked mask. -/
def B4Graph : SimpleGraph (Fin 6) :=
  patternGraph (finitePatternOfMasks fullVertexMask b4Mask)

/-- The concrete ten-edge completion obtained by exposing leaf edge
`{2,3}`.  Its graph is the canonical `QGraph`. -/
def qCompletionMask : Fin K6Prefix.graphCount :=
  ⟨K6Prefix.maskOfPairs #[
    (0, 1),
    (0, 2), (0, 3), (0, 4), (0, 5),
    (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3)], by native_decide⟩

/-- The exposed tenth edge `{2,3}` in the fixed fifteen-edge enumeration. -/
def b4CompletionEdge : K6Edge := ⟨9, by native_decide⟩

theorem b4CompletionEdge_endpoints :
    edgeLo b4CompletionEdge = 2 ∧ edgeHi b4CompletionEdge = 3 := by
  native_decide

/-- At mask level the `Q` representative is literally `B₄` plus its
distinguished tenth edge. -/
theorem qCompletion_edges_eq_insert :
    (finitePatternOfMasks fullVertexMask qCompletionMask).edges =
      insert b4CompletionEdge
        (finitePatternOfMasks fullVertexMask b4Mask).edges := by
  native_decide

theorem b4CompletionEdge_mem_qCompletion :
    b4CompletionEdge ∈
      (finitePatternOfMasks fullVertexMask qCompletionMask).edges := by
  native_decide

theorem b4CompletionEdge_not_mem_b4 :
    b4CompletionEdge ∉
      (finitePatternOfMasks fullVertexMask b4Mask).edges := by
  native_decide

/-- Deleting that tenth edge recovers the checked nine-edge `B₄` prefix
exactly, not merely up to isomorphism. -/
theorem erase_qCompletionEdge_eq_b4 :
    eraseFiniteEdge
        (finitePatternOfMasks fullVertexMask qCompletionMask)
        b4CompletionEdge =
      finitePatternOfMasks fullVertexMask b4Mask := by
  native_decide

/-- Closed executable check for the `B₄` graph representative. -/
theorem patternGraph_b4Mask :
    patternGraph (finitePatternOfMasks fullVertexMask b4Mask) = B4Graph := by
  rfl

/-- Closed executable check for the tenth-edge completion. -/
theorem patternGraph_qCompletionMask :
    patternGraph (finitePatternOfMasks fullVertexMask qCompletionMask) =
      QGraph := by
  set_option maxHeartbeats 800000 in
    ext u v
    fin_cases u <;> fin_cases v <;>
      simp only [QGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj] <;>
        native_decide

theorem b4Mask_prefixCopyCount_eq {N : ℕ} (hN : 0 < N)
    (h : Transcript (Query N)) :
    prefixCopyCount hN (finitePatternOfMasks fullVertexMask b4Mask) h =
      labelledCopies (positiveGraph h) B4Graph := by
  rw [fullPattern_prefixCopyCount_eq_labelledCopies, patternGraph_b4Mask]

theorem qCompletionMask_prefixCopyCount_eq {N : ℕ} (hN : 0 < N)
    (h : Transcript (Query N)) :
    prefixCopyCount hN
        (finitePatternOfMasks fullVertexMask qCompletionMask) h =
      labelledCopies (positiveGraph h) QGraph := by
  rw [fullPattern_prefixCopyCount_eq_labelledCopies,
    patternGraph_qCompletionMask]

end

end PatternGraphBridge
end OnlineRamsey
