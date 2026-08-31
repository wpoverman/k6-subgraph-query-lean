import OnlineRamsey.StoppingPrefixMask
import OnlineRamsey.ExceptionalOrbitBridge

/-!
# The canonical tenth edge after a `B₄` stopping prefix

The checked classification is made after nine edges, whereas the shifted
bipartite branch is stopped after ten.  This file verifies that the *actual*
tenth edge of every relative order completes a classified `B₄` prefix to
the graph `Q` used by the sharp deterministic estimate.  In particular, it
does not replace the stopping order's tenth edge by an existentially chosen
completion.
-/

namespace OnlineRamsey
namespace StoppingPrefixCount

open PrefixSoundness PatternGraphBridge ExceptionalOrbitBridge
open StoppingHistory

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Executable insertion of one recurrence edge into a graph mask.  Using
bitwise `or` keeps the finite completion check computationally transparent. -/
def insertEdgeMask (g : Fin K6Prefix.graphCount)
    (d : PrefixSoundness.K6Edge) : Fin K6Prefix.graphCount :=
  ⟨g.1 ||| K6Prefix.bit d.1, by
    change g.1 ||| K6Prefix.bit d.1 < 2 ^ 15
    apply Nat.or_lt_two_pow g.2
    simpa [K6Prefix.bit, Nat.one_shiftLeft] using
      (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) d.2)⟩

@[simp] theorem edgeFinsetOfMask_insertEdgeMask
    (g : Fin K6Prefix.graphCount) (d : PrefixSoundness.K6Edge) :
    edgeFinsetOfMask (insertEdgeMask g d) =
      insert d (edgeFinsetOfMask g) :=
by
  ext e
  simp only [edgeFinsetOfMask, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert]
  change
    (g.1 ||| K6Prefix.bit d.1).testBit e.1 = true ↔
      e = d ∨ g.1.testBit e.1 = true
  rw [show K6Prefix.bit d.1 = 2 ^ d.1 by
    simp [K6Prefix.bit, Nat.one_shiftLeft],
    Nat.testBit_or, Nat.testBit_two_pow]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (he | hde)
    · exact Or.inr he
    · exact Or.inl (Fin.ext hde.symm)
  · rintro (hed | he)
    · exact Or.inr (congrArg Fin.val hed).symm
    · exact Or.inl he

/-- The tenth source edge in a relative order. -/
def tenthPrefixEdge (π : K6EdgeOrder) : PrefixSoundness.K6Edge :=
  sourceEdgeIndex (π ⟨9, by omega⟩)

/-- The first ten edges are exactly the first nine plus the next edge. -/
theorem orderPrefixEdgeSet_ten_eq_insert (π : K6EdgeOrder) :
    orderPrefixEdgeSet π tenPrefixLength =
      insert (tenthPrefixEdge π)
        (orderPrefixEdgeSet π ninePrefixLength) := by
  ext d
  constructor
  · intro hd
    rw [orderPrefixEdgeSet, Finset.mem_image] at hd
    rcases hd with ⟨j, _hj, rfl⟩
    by_cases hj : j.val < 9
    · rw [Finset.mem_insert]
      right
      rw [orderPrefixEdgeSet, Finset.mem_image]
      refine ⟨⟨j.val, hj⟩, Finset.mem_univ _, ?_⟩
      congr 2
    · have hjlt : j.val < 10 := by simpa using j.isLt
      have hj9 : j.val = 9 := by omega
      rw [Finset.mem_insert]
      left
      unfold tenthPrefixEdge
      congr 2
      apply Fin.ext
      exact hj9
  · intro hd
    rw [Finset.mem_insert] at hd
    rcases hd with hd | hd
    · subst d
      rw [orderPrefixEdgeSet, Finset.mem_image]
      refine ⟨⟨9, by simp⟩, Finset.mem_univ _, ?_⟩
      rfl
    · rw [orderPrefixEdgeSet, Finset.mem_image] at hd
      rcases hd with ⟨j, _hj, rfl⟩
      rw [orderPrefixEdgeSet, Finset.mem_image]
      have hjlt : j.val < 9 := by simpa using j.isLt
      refine ⟨⟨j.val, by simpa using (hjlt.trans (by decide : 9 < 10))⟩,
        Finset.mem_univ _, ?_⟩
      congr 2

theorem tenthPrefixEdge_not_mem_nine (π : K6EdgeOrder) :
    tenthPrefixEdge π ∉ orderPrefixEdgeSet π ninePrefixLength := by
  intro hmem
  rw [orderPrefixEdgeSet, Finset.mem_image] at hmem
  rcases hmem with ⟨j, _hj, hj⟩
  have hs := sourceEdgeIndex_injective hj
  have hp := π.injective hs
  have hv := congrArg (fun i : Fin 15 ↦ i.val) hp
  simp [tenthPrefixEdge, prefixIndex] at hv
  omega

/-- At mask level, the canonical ten-edge prefix is insertion of the actual
tenth edge into the canonical nine-edge prefix. -/
theorem orderPrefixMask_ten_eq_insertEdgeMask (π : K6EdgeOrder) :
    orderPrefixMask π tenPrefixLength =
      insertEdgeMask (orderPrefixMask π ninePrefixLength)
        (tenthPrefixEdge π) := by
  apply edgeFinsetOfMask_injective
  rw [edgeFinsetOfMask_orderPrefixMask,
    edgeFinsetOfMask_insertEdgeMask,
    edgeFinsetOfMask_orderPrefixMask,
    orderPrefixEdgeSet_ten_eq_insert]

private theorem b4_insertEdge_qRelabel_witness :
    ∀ (g : Fin K6Prefix.graphCount) (d : PrefixSoundness.K6Edge),
      K6Prefix.b4Orbit[g.1]! = true →
      d ∉ edgeFinsetOfMask g →
      ∃ i : Fin K6Prefix.permutations6.size,
        qRelabelMask i = insertEdgeMask g d := by
  native_decide

theorem insertEdgeMask_iso_Q_of_mem_b4Orbit
    (g : Fin K6Prefix.graphCount) (d : PrefixSoundness.K6Edge)
    (hg : K6Prefix.b4Orbit[g.1]! = true)
    (hd : d ∉ edgeFinsetOfMask g) :
    Nonempty
      (patternGraph (finitePatternOfMasks fullVertexMask
        (insertEdgeMask g d)) ≃g QGraph) := by
  obtain ⟨i, hi⟩ := b4_insertEdge_qRelabel_witness g d hg hd
  rw [← hi]
  have hiso := (qRelabelIso i).symm
  rw [patternGraph_qCompletionMask] at hiso
  exact ⟨hiso⟩

/-- The concrete bridge needed in the shifted-bipartite `hcount`: whenever
the first nine edges of `π` are in the checked `B₄` orbit, the first ten
edges of that *same order* form a labelled copy of `Q` up to isomorphism. -/
theorem canonicalTenPrefix_iso_Q_of_nine_mem_b4Orbit
    (π : K6EdgeOrder)
    (hB4 : K6Prefix.b4Orbit[
      (orderPrefixMask π ninePrefixLength).1]! = true) :
    Nonempty
      (patternGraph (finitePatternOfMasks fullVertexMask
          (orderPrefixMask π tenPrefixLength)) ≃g QGraph) := by
  have hnot : tenthPrefixEdge π ∉
      edgeFinsetOfMask (orderPrefixMask π ninePrefixLength) := by
    simpa using tenthPrefixEdge_not_mem_nine π
  rw [orderPrefixMask_ten_eq_insertEdgeMask]
  exact insertEdgeMask_iso_Q_of_mem_b4Orbit
    (orderPrefixMask π ninePrefixLength) (tenthPrefixEdge π) hB4 hnot

end
end StoppingPrefixCount
end OnlineRamsey
