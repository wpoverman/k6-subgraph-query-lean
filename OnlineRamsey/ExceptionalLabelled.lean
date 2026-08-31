import OnlineRamsey.H3Labelled
import Mathlib.Tactic.FinCases

/-!
# Labelled bridges for all exceptional nine-edge patterns

Besides re-exporting the `H₃` bridge, this file accounts exactly for the
free isolated label in `(K₅-e) ⊔ K₁`.  Restricting a six-label copy to
its first five labels gives a labelled `K₅-e` copy, while its last image is
an arbitrary ambient vertex.  The resulting injection proves the required
single ambient-vertex factor without an isomorphism-counting assumption.
-/

namespace OnlineRamsey

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical inclusion of the five non-isolated labels. -/
def finFiveIntoSix : Fin 5 ↪ Fin 6 := Fin.castLEEmb (by decide)

/-- The concrete six-vertex graph `(K₅-e) ⊔ K₁`, with label `5`
isolated. -/
def K5MinusEdgeIsolatedGraph : SimpleGraph (Fin 6) :=
  K5MinusEdgeGraph.map finFiveIntoSix

/-- The first five labels induce the canonical `K₅-e` copy. -/
def k5IntoK5MinusEdgeIsolated :
    K5MinusEdgeGraph.Copy K5MinusEdgeIsolatedGraph :=
  (SimpleGraph.Embedding.map finFiveIntoSix K5MinusEdgeGraph).toCopy

@[simp] theorem k5IntoK5MinusEdgeIsolated_apply (i : Fin 5) :
    k5IntoK5MinusEdgeIsolated i = finFiveIntoSix i := rfl

/-- Forget the isolated label while retaining its ambient image separately. -/
def restrictK5AndFreeVertex (G : SimpleGraph V)
    (f : K5MinusEdgeIsolatedGraph.Copy G) :
    K5MinusEdgeGraph.Copy G × V :=
  (f.comp k5IntoK5MinusEdgeIsolated, f 5)

theorem restrictK5AndFreeVertex_injective (G : SimpleGraph V) :
    Function.Injective (restrictK5AndFreeVertex G) := by
  intro f g hfg
  have hrest : f.comp k5IntoK5MinusEdgeIsolated =
      g.comp k5IntoK5MinusEdgeIsolated := congrArg Prod.fst hfg
  have hfree : f 5 = g 5 := congrArg Prod.snd hfg
  apply SimpleGraph.Copy.ext
  intro i
  fin_cases i
  · simpa using congrArg (fun c : K5MinusEdgeGraph.Copy G => c 0) hrest
  · simpa using congrArg (fun c : K5MinusEdgeGraph.Copy G => c 1) hrest
  · simpa using congrArg (fun c : K5MinusEdgeGraph.Copy G => c 2) hrest
  · simpa using congrArg (fun c : K5MinusEdgeGraph.Copy G => c 3) hrest
  · simpa using congrArg (fun c : K5MinusEdgeGraph.Copy G => c 4) hrest
  · exact hfree

/-- Adding one isolated labelled vertex costs at most one factor of the
ambient vertex cardinality. -/
theorem labelledCopies_K5MinusEdgeIsolated_le (G : SimpleGraph V) :
    labelledCopies G K5MinusEdgeIsolatedGraph ≤
      labelledCopies G K5MinusEdgeGraph * Fintype.card V := by
  classical
  calc
    labelledCopies G K5MinusEdgeIsolatedGraph =
        Fintype.card (K5MinusEdgeIsolatedGraph.Copy G) := by
      rw [← natCard_copy_eq_labelledCopies]
      exact Nat.card_eq_fintype_card
    _ ≤ Fintype.card (K5MinusEdgeGraph.Copy G × V) :=
      Fintype.card_le_of_injective (restrictK5AndFreeVertex G)
        (restrictK5AndFreeVertex_injective G)
    _ = Fintype.card (K5MinusEdgeGraph.Copy G) * Fintype.card V := by
      rw [Fintype.card_prod]
    _ = labelledCopies G K5MinusEdgeGraph * Fintype.card V := by
      rw [← natCard_copy_eq_labelledCopies]
      rw [Nat.card_eq_fintype_card]

/-- Combined with the checked five-vertex labelled charge, the exceptional
six-vertex pattern has the exact free-vertex factor expected in the paper. -/
theorem labelledCopies_K5MinusEdgeIsolated_le_six_mul_card_mul_charge
    (G : SimpleGraph V) :
    labelledCopies G K5MinusEdgeIsolatedGraph ≤
      (6 * Fintype.card V) * k5MinusEdgeCharge G := by
  calc
    labelledCopies G K5MinusEdgeIsolatedGraph ≤
        labelledCopies G K5MinusEdgeGraph * Fintype.card V :=
      labelledCopies_K5MinusEdgeIsolated_le G
    _ ≤ (6 * k5MinusEdgeCharge G) * Fintype.card V :=
      Nat.mul_le_mul_right _ (labelledCopies_K5MinusEdge_le_six_mul_charge G)
    _ = (6 * Fintype.card V) * k5MinusEdgeCharge G := by ring

end

end OnlineRamsey
