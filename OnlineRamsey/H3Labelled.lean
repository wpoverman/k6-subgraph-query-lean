import OnlineRamsey.LabelledCharges
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.FinCases

/-!
# A labelled-copy bridge for the exceptional half graph

The deterministic `H₃` estimate is expressed by `h3Charge`.  This file
connects that permissive charge to the actual labelled six-vertex copy count.
The charge remembers the degree-five root, its pendant neighbour, a triangle
in the root link, a distinguished triangle vertex, and one further neighbour
of that vertex in the link.  A labelled `H₃` copy determines such data;
only the two symmetric labels in the remaining triangle can be interchanged.
-/

open scoped BigOperators

namespace OnlineRamsey

section

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance h3PropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The nested finite configurations counted by `h3Charge`. -/
noncomputable def h3Configurations (G : SimpleGraph V) :
    Finset (Σ _root : V, Σ _pendant : V, Σ _T : Finset V, Σ _z : V, V) := by
  classical
  exact Finset.univ.sigma fun root =>
    (neighbors G root).sigma fun _pendant =>
      ((linkGraph G root).cliqueFinset 3).sigma fun T =>
        T.sigma fun z => neighbors (linkGraph G root) z

@[simp] theorem mem_h3Configurations (G : SimpleGraph V)
    (root pendant : V) (T : Finset V) (z y : V) :
    Sigma.mk root (Sigma.mk pendant (Sigma.mk T (Sigma.mk z y))) ∈
        h3Configurations G ↔
      pendant ∈ neighbors G root ∧
      T ∈ (linkGraph G root).cliqueFinset 3 ∧
      z ∈ T ∧ y ∈ neighbors (linkGraph G root) z := by
  classical
  simp [h3Configurations]

theorem h3Configurations_card (G : SimpleGraph V) :
    (h3Configurations G).card = h3Charge G := by
  classical
  simp [h3Configurations, h3Charge, pawExtensionMass, degree,
    Finset.card_sigma]

/-- The triangle on labels `1,2,5` left after deleting the root and pendant
labels from the canonical `H₃`. -/
noncomputable def h3TriangleVertices (G : SimpleGraph V)
    (f : H3Graph.Copy G) : Finset V :=
  {f 1, f 2, f 5}

/-- The charge record extracted from a labelled `H₃` copy. -/
noncomputable def h3CopyData (G : SimpleGraph V) (f : H3Graph.Copy G) :
    Σ _root : V, Σ _pendant : V, Σ _T : Finset V, Σ _z : V, V :=
  ⟨f 0, f 3, h3TriangleVertices G f, f 1, f 4⟩

/-- Every labelled `H₃` copy produces one of the configurations counted
by `h3Charge`. -/
noncomputable def h3CopyToConfiguration (G : SimpleGraph V)
    (f : H3Graph.Copy G) : ↑(h3Configurations G) := by
  classical
  have hmap {i j : Fin 6} (hij : H3Graph.Adj i j) : G.Adj (f i) (f j) :=
    f.toHom.map_adj hij
  have h01 : G.Adj (f 0) (f 1) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h02 : G.Adj (f 0) (f 2) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h03 : G.Adj (f 0) (f 3) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h04 : G.Adj (f 0) (f 4) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h05 : G.Adj (f 0) (f 5) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h12 : G.Adj (f 1) (f 2) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h15 : G.Adj (f 1) (f 5) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h25 : G.Adj (f 2) (f 5) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  have h14 : G.Adj (f 1) (f 4) :=
    hmap (by simp [H3Graph, SimpleGraph.edge_adj])
  refine ⟨h3CopyData G f, ?_⟩
  rw [mem_h3Configurations]
  refine ⟨(mem_neighbors G (f 0) (f 3)).mpr h03, ?_, ?_, ?_⟩
  · change ({f 1, f 2, f 5} : Finset V) ∈
      (linkGraph G (f 0)).cliqueFinset 3
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    have h12ne : f 1 ≠ f 2 := f.injective.ne (by decide)
    have h15ne : f 1 ≠ f 5 := f.injective.ne (by decide)
    have h25ne : f 2 ≠ f 5 := f.injective.ne (by decide)
    constructor
    · simp [linkGraph_adj, h12ne, h15ne, h25ne, h12, h15, h25,
        h01, h02, h05]
    · simp [h12ne, h15ne, h25ne]
  · change f 1 ∈ ({f 1, f 2, f 5} : Finset V)
    simp
  · rw [mem_neighbors, linkGraph_adj]
    exact ⟨h14, h01, h04⟩

/-- A classical enumeration of all labelled `H₃` copies. -/
noncomputable def h3CopyFinset (G : SimpleGraph V) :
    Finset (H3Graph.Copy G) := by
  classical
  exact Finset.univ

theorem h3CopyFinset_card (G : SimpleGraph V) :
    (h3CopyFinset G).card = labelledCopies G H3Graph := by
  classical
  calc
    (h3CopyFinset G).card = Fintype.card (H3Graph.Copy G) := by
      simp [h3CopyFinset]
    _ = Nat.card (H3Graph.Copy G) := Nat.card_eq_fintype_card.symm
    _ = labelledCopies G H3Graph := natCard_copy_eq_labelledCopies G H3Graph

/-- Within a fixed charge fiber, remember the image of label `2`.  It lies
in the two-element set obtained from the recorded triangle by deleting its
distinguished label `1`. -/
noncomputable def h3FiberChoice (G : SimpleGraph V)
    (q : ↑(h3Configurations G))
    (f : {f : H3Graph.Copy G // h3CopyToConfiguration G f = q}) :
    ↑(q.1.2.2.1.erase q.1.2.2.2.1) := by
  classical
  have hdata : h3CopyData G f.1 = q.1 := congrArg Subtype.val f.2
  have hT : h3TriangleVertices G f.1 = q.1.2.2.1 :=
    congrArg (fun d => d.2.2.1) hdata
  have hz : f.1 1 = q.1.2.2.2.1 :=
    congrArg (fun d => d.2.2.2.1) hdata
  refine ⟨f.1 2, ?_⟩
  rw [← hT, ← hz]
  have h21 : f.1 2 ≠ f.1 1 := f.1.injective.ne (by decide)
  simp [h3TriangleVertices, h21]

theorem card_h3FiberChoice_target (G : SimpleGraph V)
    (q : ↑(h3Configurations G)) :
    Fintype.card ↑(q.1.2.2.1.erase q.1.2.2.2.1) = 2 := by
  classical
  have hmem := (mem_h3Configurations G q.1.1 q.1.2.1 q.1.2.2.1
    q.1.2.2.2.1 q.1.2.2.2.2).mp q.2
  have hcard : q.1.2.2.1.card = 3 :=
    (SimpleGraph.mem_cliqueFinset_iff.mp hmem.2.1).card_eq
  rw [Fintype.card_coe, Finset.card_erase_of_mem hmem.2.2.1, hcard]

theorem h3FiberChoice_injective (G : SimpleGraph V)
    (q : ↑(h3Configurations G)) :
    Function.Injective (h3FiberChoice G q) := by
  classical
  intro f g hchoice
  have hfdata : h3CopyData G f.1 = q.1 := congrArg Subtype.val f.2
  have hgdata : h3CopyData G g.1 = q.1 := congrArg Subtype.val g.2
  have hdata : h3CopyData G f.1 = h3CopyData G g.1 :=
    hfdata.trans hgdata.symm
  have h0 : f.1 0 = g.1 0 := congrArg (fun d => d.1) hdata
  have h3 : f.1 3 = g.1 3 := congrArg (fun d => d.2.1) hdata
  have hT : h3TriangleVertices G f.1 = h3TriangleVertices G g.1 :=
    congrArg (fun d => d.2.2.1) hdata
  have h1 : f.1 1 = g.1 1 := congrArg (fun d => d.2.2.2.1) hdata
  have h4 : f.1 4 = g.1 4 := congrArg (fun d => d.2.2.2.2) hdata
  have h2 : f.1 2 = g.1 2 := congrArg Subtype.val hchoice
  have h5 : f.1 5 = g.1 5 := by
    have hf5 : f.1 5 ∈ h3TriangleVertices G g.1 := by
      rw [← hT]
      simp [h3TriangleVertices]
    simp only [h3TriangleVertices, Finset.mem_insert,
      Finset.mem_singleton] at hf5
    rcases hf5 with hf5 | hf5 | hf5
    · exact False.elim (f.1.injective.ne (by decide : (5 : Fin 6) ≠ 1)
        (hf5.trans h1.symm))
    · exact False.elim (f.1.injective.ne (by decide : (5 : Fin 6) ≠ 2)
        (hf5.trans h2.symm))
    · exact hf5
  apply Subtype.ext
  apply SimpleGraph.Copy.ext
  intro i
  fin_cases i <;> assumption

theorem card_h3CopyConfigurationFiber_le_two (G : SimpleGraph V)
    (q : ↑(h3Configurations G)) :
    ((h3CopyFinset G).filter fun f => h3CopyToConfiguration G f = q).card ≤ 2 := by
  classical
  let s := (h3CopyFinset G).filter fun f => h3CopyToConfiguration G f = q
  let choice : ↑s → ↑(q.1.2.2.1.erase q.1.2.2.2.1) := fun f =>
    h3FiberChoice G q ⟨f.1, (Finset.mem_filter.mp f.2).2⟩
  have hchoice : Function.Injective choice := by
    intro f g hfg
    apply Subtype.ext
    have hfiber := h3FiberChoice_injective G q hfg
    exact congrArg
      (fun z : {z : H3Graph.Copy G // h3CopyToConfiguration G z = q} => z.1)
      hfiber
  calc
    ((h3CopyFinset G).filter fun f => h3CopyToConfiguration G f = q).card =
        Fintype.card ↑s := by
      change s.card = Fintype.card ↑s
      exact (Fintype.card_coe s).symm
    _ ≤ Fintype.card ↑(q.1.2.2.1.erase q.1.2.2.2.1) :=
      Fintype.card_le_of_injective choice hchoice
    _ = 2 := card_h3FiberChoice_target G q

/-- The labelled exceptional half-graph count is bounded by twice the
deterministic charge. -/
theorem labelledCopies_H3_le_two_mul_charge (G : SimpleGraph V) :
    labelledCopies G H3Graph ≤ 2 * h3Charge G := by
  classical
  rw [← h3CopyFinset_card]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := h3CopyToConfiguration G)
    (t := (Finset.univ : Finset ↑(h3Configurations G)))
    (by intro f _hf; exact Finset.mem_univ (h3CopyToConfiguration G f))]
  calc
    (∑ q : ↑(h3Configurations G),
        ((h3CopyFinset G).filter fun f => h3CopyToConfiguration G f = q).card) ≤
        ∑ _q : ↑(h3Configurations G), 2 := by
      apply Finset.sum_le_sum
      intro q _hq
      exact card_h3CopyConfigurationFiber_le_two G q
    _ = 2 * (h3Configurations G).card := by simp [Nat.mul_comm]
    _ = 2 * h3Charge G := by rw [h3Configurations_card]

end

end OnlineRamsey
