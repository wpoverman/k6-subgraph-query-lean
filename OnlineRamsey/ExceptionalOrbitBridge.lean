import OnlineRamsey.PatternGraphBridge

/-!
# Semantic witnesses for the checked exceptional orbits

The exhaustive certificate represents orbit membership by executable Boolean
arrays.  This file extracts the generating permutation and turns it into an
actual Mathlib graph isomorphism.  Searching the certificate's 720 listed
permutations mirrors `K6Prefix.orbit` directly and avoids an unrestricted
search through all functions on six vertices.
-/

namespace OnlineRamsey
namespace ExceptionalOrbitBridge

open PrefixSoundness PatternGraphBridge

noncomputable section

/-- The typed six-vertex permutation stored at one position of the executable
permutation array. -/
def permutationAt
    (i : Fin K6Prefix.permutations6.size) (v : Fin 6) : Fin 6 :=
  ⟨(K6Prefix.permutations6[i.1]!)[v.1]!, by
    have h : ∀ (j : Fin K6Prefix.permutations6.size) (w : Fin 6),
        (K6Prefix.permutations6[j.1]!)[w.1]! < 6 := by native_decide
    exact h i v⟩

private theorem permutationAt_bijective :
    ∀ i : Fin K6Prefix.permutations6.size,
      Function.Bijective (permutationAt i) := by
  native_decide

/-- The executable array entry as a genuine equivalence. -/
def permutationEquiv (i : Fin K6Prefix.permutations6.size) : Fin 6 ≃ Fin 6 :=
  Equiv.ofBijective (permutationAt i) (permutationAt_bijective i)

private theorem h3Relabel_lt :
    ∀ i : Fin K6Prefix.permutations6.size,
      K6Prefix.relabel K6Prefix.h3 K6Prefix.permutations6[i.1]! <
        K6Prefix.graphCount := by
  native_decide

def h3RelabelMask (i : Fin K6Prefix.permutations6.size) :
    Fin K6Prefix.graphCount :=
  ⟨K6Prefix.relabel K6Prefix.h3 K6Prefix.permutations6[i.1]!,
    h3Relabel_lt i⟩

private theorem h3Relabel_adj_aux :
    ∀ (i : Fin K6Prefix.permutations6.size) (u v : Fin 6),
      (patternGraph
        (finitePatternOfMasks fullVertexMask (h3RelabelMask i))).Adj
          (permutationAt i u) (permutationAt i v) ↔
        H3Graph.Adj u v := by
  native_decide

/-- Relabelling the representative mask by one listed permutation gives the
corresponding graph isomorphism. -/
def h3RelabelIso (i : Fin K6Prefix.permutations6.size) :
    H3Graph ≃g
      patternGraph (finitePatternOfMasks fullVertexMask (h3RelabelMask i)) where
  toEquiv := permutationEquiv i
  map_rel_iff' := by
    intro u v
    simpa [permutationEquiv] using h3Relabel_adj_aux i u v

private theorem h3Orbit_witness :
    ∀ g : Fin K6Prefix.graphCount,
      K6Prefix.h3Orbit[g.1]! = true →
        ∃ i : Fin K6Prefix.permutations6.size, h3RelabelMask i = g := by
  native_decide

/-- Membership in the checked `H₃` Boolean orbit supplies an actual graph
isomorphism to the charged canonical pattern. -/
theorem exists_iso_H3_of_mem_orbit
    (g : Fin K6Prefix.graphCount)
    (hg : K6Prefix.h3Orbit[g.1]! = true) :
    Nonempty
      (patternGraph (finitePatternOfMasks fullVertexMask g) ≃g H3Graph) := by
  obtain ⟨i, rfl⟩ := h3Orbit_witness g hg
  exact ⟨(h3RelabelIso i).symm⟩

/-! ## The isolated `K₅-e` orbit -/

private theorem k5Relabel_lt :
    ∀ i : Fin K6Prefix.permutations6.size,
      K6Prefix.relabel K6Prefix.k5MinusEdgePlusIsolate
          K6Prefix.permutations6[i.1]! < K6Prefix.graphCount := by
  native_decide

def k5RelabelMask (i : Fin K6Prefix.permutations6.size) :
    Fin K6Prefix.graphCount :=
  ⟨K6Prefix.relabel K6Prefix.k5MinusEdgePlusIsolate
      K6Prefix.permutations6[i.1]!, k5Relabel_lt i⟩

private theorem k5Relabel_adj_aux :
    ∀ (i : Fin K6Prefix.permutations6.size) (u v : Fin 6),
      (patternGraph
        (finitePatternOfMasks fullVertexMask (k5RelabelMask i))).Adj
          (permutationAt i u) (permutationAt i v) ↔
        (patternGraph (finitePatternOfMasks fullVertexMask
          k5MinusEdgePlusIsolateMask)).Adj u v := by
  native_decide

def k5RelabelIso (i : Fin K6Prefix.permutations6.size) :
    patternGraph (finitePatternOfMasks fullVertexMask
      k5MinusEdgePlusIsolateMask) ≃g
      patternGraph (finitePatternOfMasks fullVertexMask (k5RelabelMask i)) where
  toEquiv := permutationEquiv i
  map_rel_iff' := by
    intro u v
    simpa [permutationEquiv] using k5Relabel_adj_aux i u v

private theorem k5Orbit_witness :
    ∀ g : Fin K6Prefix.graphCount,
      K6Prefix.k5MinusEdgePlusIsolateOrbit[g.1]! = true →
        ∃ i : Fin K6Prefix.permutations6.size, k5RelabelMask i = g := by
  native_decide

theorem exists_iso_K5MinusEdgeIsolated_of_mem_orbit
    (g : Fin K6Prefix.graphCount)
    (hg : K6Prefix.k5MinusEdgePlusIsolateOrbit[g.1]! = true) :
    Nonempty (patternGraph (finitePatternOfMasks fullVertexMask g) ≃g
      K5MinusEdgeIsolatedGraph) := by
  obtain ⟨i, rfl⟩ := k5Orbit_witness g hg
  exact ⟨(k5RelabelIso i).symm.trans
    patternGraph_k5MinusEdgePlusIsolate_iso⟩

/-! ## The `B₄` orbit -/

private theorem b4Relabel_lt :
    ∀ i : Fin K6Prefix.permutations6.size,
      K6Prefix.relabel K6Prefix.b4 K6Prefix.permutations6[i.1]! <
        K6Prefix.graphCount := by
  native_decide

def b4RelabelMask (i : Fin K6Prefix.permutations6.size) :
    Fin K6Prefix.graphCount :=
  ⟨K6Prefix.relabel K6Prefix.b4 K6Prefix.permutations6[i.1]!,
    b4Relabel_lt i⟩

private theorem b4Relabel_adj_aux :
    ∀ (i : Fin K6Prefix.permutations6.size) (u v : Fin 6),
      (patternGraph
        (finitePatternOfMasks fullVertexMask (b4RelabelMask i))).Adj
          (permutationAt i u) (permutationAt i v) ↔
        (patternGraph
          (finitePatternOfMasks fullVertexMask b4Mask)).Adj u v := by
  native_decide

def b4RelabelIso (i : Fin K6Prefix.permutations6.size) :
    B4Graph ≃g
      patternGraph (finitePatternOfMasks fullVertexMask (b4RelabelMask i)) where
  toEquiv := permutationEquiv i
  map_rel_iff' := by
    intro u v
    simpa [permutationEquiv, B4Graph] using b4Relabel_adj_aux i u v

private theorem b4Orbit_witness :
    ∀ g : Fin K6Prefix.graphCount,
      K6Prefix.b4Orbit[g.1]! = true →
        ∃ i : Fin K6Prefix.permutations6.size, b4RelabelMask i = g := by
  native_decide

theorem exists_iso_B4_of_mem_orbit
    (g : Fin K6Prefix.graphCount)
    (hg : K6Prefix.b4Orbit[g.1]! = true) :
    Nonempty
      (patternGraph (finitePatternOfMasks fullVertexMask g) ≃g B4Graph) := by
  obtain ⟨i, rfl⟩ := b4Orbit_witness g hg
  exact ⟨(b4RelabelIso i).symm⟩

/-! ## Equivariant tenth-edge completion of `B₄` -/

private theorem qRelabel_lt :
    ∀ i : Fin K6Prefix.permutations6.size,
      K6Prefix.relabel qCompletionMask.1 K6Prefix.permutations6[i.1]! <
        K6Prefix.graphCount := by
  native_decide

def qRelabelMask (i : Fin K6Prefix.permutations6.size) :
    Fin K6Prefix.graphCount :=
  ⟨K6Prefix.relabel qCompletionMask.1 K6Prefix.permutations6[i.1]!,
    qRelabel_lt i⟩

private theorem qRelabel_adj_aux :
    ∀ (i : Fin K6Prefix.permutations6.size) (u v : Fin 6),
      (patternGraph
        (finitePatternOfMasks fullVertexMask (qRelabelMask i))).Adj
          (permutationAt i u) (permutationAt i v) ↔
        (patternGraph (finitePatternOfMasks fullVertexMask
          qCompletionMask)).Adj u v := by
  native_decide

def qRelabelIso (i : Fin K6Prefix.permutations6.size) :
    patternGraph (finitePatternOfMasks fullVertexMask qCompletionMask) ≃g
      patternGraph (finitePatternOfMasks fullVertexMask (qRelabelMask i)) where
  toEquiv := permutationEquiv i
  map_rel_iff' := by
    intro u v
    simpa [permutationEquiv] using qRelabel_adj_aux i u v

private theorem b4Relabel_has_qCompletion :
    ∀ i : Fin K6Prefix.permutations6.size,
      ∃ e : K6Edge,
        e ∈ (finitePatternOfMasks fullVertexMask (qRelabelMask i)).edges ∧
        eraseFiniteEdge
            (finitePatternOfMasks fullVertexMask (qRelabelMask i)) e =
          finitePatternOfMasks fullVertexMask (b4RelabelMask i) := by
  native_decide

/-- Every mask in the checked `B₄` orbit has a concrete tenth-edge
extension isomorphic to `Q`, and deleting that distinguished edge recovers
the original nine-edge mask exactly. -/
theorem exists_qCompletion_of_mem_b4Orbit
    (g : Fin K6Prefix.graphCount)
    (hg : K6Prefix.b4Orbit[g.1]! = true) :
    ∃ (g₁₀ : Fin K6Prefix.graphCount) (e : K6Edge),
      e ∈ (finitePatternOfMasks fullVertexMask g₁₀).edges ∧
      eraseFiniteEdge (finitePatternOfMasks fullVertexMask g₁₀) e =
        finitePatternOfMasks fullVertexMask g ∧
      Nonempty
        (patternGraph (finitePatternOfMasks fullVertexMask g₁₀) ≃g
          QGraph) := by
  obtain ⟨i, rfl⟩ := b4Orbit_witness g hg
  obtain ⟨e, he, herase⟩ := b4Relabel_has_qCompletion i
  refine ⟨qRelabelMask i, e, he, herase, ?_⟩
  have hiso := (qRelabelIso i).symm
  rw [patternGraph_qCompletionMask] at hiso
  exact ⟨hiso⟩

end
end ExceptionalOrbitBridge
end OnlineRamsey
