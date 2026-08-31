import OnlineRamsey.Deterministic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.FinCases

/-!
# Labelled-copy bridges for deterministic charging sums

This module turns the permissive finite configurations counted by the
`K₅-e` and `Q` charging sums into explicit targets for labelled graph copies.
The constructions are finite and deterministic.
-/

open scoped BigOperators

namespace OnlineRamsey

/-- `labelledCopies` is the finite cardinal of the copy type, expressed using
the instance-independent `Nat.card`.  Keeping this lemma graph-generic avoids
unfolding large concrete pattern relations in later cardinal calculations. -/
theorem natCard_copy_eq_labelledCopies {A B : Type*}
    [Fintype A] [Fintype B] (G : SimpleGraph B) (H : SimpleGraph A) :
    Nat.card (H.Copy G) = labelledCopies G H := by
  classical
  unfold labelledCopies SimpleGraph.labelledCopyCount
  exact Nat.card_eq_fintype_card

section K5MinusEdgeLabelledBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Charge configurations for `K₅-e`: a triangle and an ordered pair of
common extensions. -/
noncomputable def k5MinusEdgeConfigurations (G : SimpleGraph V) :
    Finset (Σ _T : Finset V, V × V) := by
  classical
  exact (G.cliqueFinset 3).sigma fun T =>
    (commonNeighborsFinset G T).product (commonNeighborsFinset G T)

/-- A proof-local classical enumeration of all labelled `K₅-e` copies. -/
noncomputable def k5MinusEdgeCopyFinset (G : SimpleGraph V) :
    Finset (K5MinusEdgeGraph.Copy G) := by
  classical
  exact Finset.univ

/-- The classical enumeration contains every labelled copy. -/
noncomputable def k5MinusEdgeCopyFinsetEquiv (G : SimpleGraph V) :
    ↑(k5MinusEdgeCopyFinset G) ≃ K5MinusEdgeGraph.Copy G := by
  classical
  exact
    { toFun := Subtype.val
      invFun := fun f => ⟨f, by simp [k5MinusEdgeCopyFinset]⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }

theorem k5MinusEdgeCopyFinset_card (G : SimpleGraph V) :
    (k5MinusEdgeCopyFinset G).card = labelledCopies G K5MinusEdgeGraph := by
  classical
  calc
    (k5MinusEdgeCopyFinset G).card =
        Fintype.card ↑(k5MinusEdgeCopyFinset G) :=
      (Fintype.card_coe _).symm
    _ = Nat.card ↑(k5MinusEdgeCopyFinset G) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (K5MinusEdgeGraph.Copy G) :=
      Nat.card_congr (k5MinusEdgeCopyFinsetEquiv G)
    _ = labelledCopies G K5MinusEdgeGraph :=
      natCard_copy_eq_labelledCopies G K5MinusEdgeGraph

@[simp] theorem mem_k5MinusEdgeConfigurations (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (T : Finset V) (x y : V) :
    Sigma.mk T (x, y) ∈ k5MinusEdgeConfigurations G ↔
      T ∈ G.cliqueFinset 3 ∧
        x ∈ commonNeighborsFinset G T ∧
        y ∈ commonNeighborsFinset G T := by
  classical
  simp [k5MinusEdgeConfigurations]

theorem k5MinusEdgeConfigurations_card (G : SimpleGraph V) :
    (k5MinusEdgeConfigurations G).card = k5MinusEdgeCharge G := by
  classical
  simp [k5MinusEdgeConfigurations, k5MinusEdgeCharge, codegree,
    Finset.card_sigma, Finset.card_product]

/-- The first three vertices form the distinguished triangle in `K₅-e`. -/
noncomputable def k5FirstThreeCopy :
    (⊤ : SimpleGraph (Fin 3)).Copy K5MinusEdgeGraph := by
  let hom : (⊤ : SimpleGraph (Fin 3)) →g K5MinusEdgeGraph :=
    { toFun := Fin.castLE (by decide : 3 ≤ 5)
      map_rel' := by
        intro i j hij
        have hij' : i ≠ j := (SimpleGraph.top_adj i j).mp hij
        fin_cases i <;> fin_cases j <;>
          simp_all [K5MinusEdgeGraph, SimpleGraph.edge_adj] }
  exact ⟨hom, Fin.castLE_injective (by decide : 3 ≤ 5)⟩

/-- The vertex set of the distinguished triangle of a labelled `K₅-e` copy. -/
noncomputable def k5TriangleVertices (G : SimpleGraph V)
    (f : K5MinusEdgeGraph.Copy G) : Finset V := by
  classical
  exact Finset.univ.map (f.comp k5FirstThreeCopy).toEmbedding

theorem k5TriangleVertices_mem_cliqueFinset (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (f : K5MinusEdgeGraph.Copy G) :
    k5TriangleVertices G f ∈ G.cliqueFinset 3 := by
  classical
  apply SimpleGraph.mem_cliqueFinset_iff.mpr
  simpa [k5TriangleVertices] using
    (SimpleGraph.isNClique_map_copy_top (G := G) (f.comp k5FirstThreeCopy))

noncomputable def k5CopyData (G : SimpleGraph V)
    (f : K5MinusEdgeGraph.Copy G) : Σ _T : Finset V, V × V :=
  ⟨k5TriangleVertices G f, (f 3, f 4)⟩

/-- A labelled `K₅-e` copy gives a triangle with two common extensions. -/
noncomputable def k5CopyToConfiguration (G : SimpleGraph V)
    (f : K5MinusEdgeGraph.Copy G) : ↑(k5MinusEdgeConfigurations G) := by
  classical
  have hmap {i j : Fin 5} (hij : K5MinusEdgeGraph.Adj i j) :
      G.Adj (f i) (f j) := f.toHom.map_adj hij
  have h03 : G.Adj (f 0) (f 3) :=
    hmap (by simp [K5MinusEdgeGraph, SimpleGraph.edge_adj])
  have h13 : G.Adj (f 1) (f 3) :=
    hmap (by simp [K5MinusEdgeGraph, SimpleGraph.edge_adj])
  have h23 : G.Adj (f 2) (f 3) :=
    hmap (by simp [K5MinusEdgeGraph, SimpleGraph.edge_adj])
  have h04 : G.Adj (f 0) (f 4) :=
    hmap (by simp [K5MinusEdgeGraph, SimpleGraph.edge_adj])
  have h14 : G.Adj (f 1) (f 4) :=
    hmap (by simp [K5MinusEdgeGraph, SimpleGraph.edge_adj])
  have h24 : G.Adj (f 2) (f 4) :=
    hmap (by simp [K5MinusEdgeGraph, SimpleGraph.edge_adj])
  refine ⟨k5CopyData G f, ?_⟩
  apply (mem_k5MinusEdgeConfigurations G
    (k5TriangleVertices G f) (f 3) (f 4)).mpr
  refine ⟨k5TriangleVertices_mem_cliqueFinset G f, ?_, ?_⟩
  · apply (mem_commonNeighborsFinset G (k5TriangleVertices G f) (f 3)).mpr
    intro v hv
    simp only [k5TriangleVertices, Finset.mem_map] at hv
    obtain ⟨i, _hi, rfl⟩ := hv
    fin_cases i
    · exact h03
    · exact h13
    · exact h23
  · apply (mem_commonNeighborsFinset G (k5TriangleVertices G f) (f 4)).mpr
    intro v hv
    simp only [k5TriangleVertices, Finset.mem_map] at hv
    obtain ⟨i, _hi, rfl⟩ := hv
    fin_cases i
    · exact h04
    · exact h14
    · exact h24

/-- Remember the three triangle labels inside a fixed charge fiber. -/
noncomputable def k5FiberToEmbedding (G : SimpleGraph V)
    (q : ↑(k5MinusEdgeConfigurations G))
    (f : {f : K5MinusEdgeGraph.Copy G // k5CopyToConfiguration G f = q}) :
    Fin 3 ↪ ↑q.1.1 := by
  classical
  have hdata : k5CopyData G f.1 = q.1 := congrArg Subtype.val f.2
  have hT : k5TriangleVertices G f.1 = q.1.1 := congrArg Sigma.fst hdata
  exact
    { toFun := fun i => ⟨(f.1.comp k5FirstThreeCopy) i, by
          have hi : (f.1.comp k5FirstThreeCopy) i ∈
              k5TriangleVertices G f.1 := by
            unfold k5TriangleVertices
            apply Finset.mem_map.mpr
            exact ⟨i, Finset.mem_univ i, rfl⟩
          rw [hT] at hi
          exact hi⟩
      inj' := fun i j hij =>
        (f.1.comp k5FirstThreeCopy).injective (congrArg Subtype.val hij) }

theorem k5FiberToEmbedding_injective (G : SimpleGraph V)
    (q : ↑(k5MinusEdgeConfigurations G)) :
    Function.Injective (k5FiberToEmbedding G q) := by
  intro f g hfg
  have hdataF : k5CopyData G f.1 = q.1 := congrArg Subtype.val f.2
  have hdataG : k5CopyData G g.1 = q.1 := congrArg Subtype.val g.2
  have hdata : k5CopyData G f.1 = k5CopyData G g.1 :=
    hdataF.trans hdataG.symm
  have h3 : f.1 3 = g.1 3 := congrArg (fun p => p.2.1) hdata
  have h4 : f.1 4 = g.1 4 := congrArg (fun p => p.2.2) hdata
  have hfirst (i : Fin 3) :
      (f.1.comp k5FirstThreeCopy) i = (g.1.comp k5FirstThreeCopy) i := by
    have hi := congrArg (fun e : Fin 3 ↪ ↑q.1.1 => e i) hfg
    exact congrArg Subtype.val hi
  apply Subtype.ext
  apply SimpleGraph.Copy.ext
  intro i
  fin_cases i
  · simpa using hfirst 0
  · simpa using hfirst 1
  · simpa using hfirst 2
  · exact h3
  · exact h4

theorem card_k5CopyConfigurationFiber_le_six (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (q : ↑(k5MinusEdgeConfigurations G)) :
    ((k5MinusEdgeCopyFinset G).filter fun f =>
      k5CopyToConfiguration G f = q).card ≤ 6 := by
  classical
  let s := (k5MinusEdgeCopyFinset G).filter fun f =>
    k5CopyToConfiguration G f = q
  let emb : ↑s → (Fin 3 ↪ ↑q.1.1) := fun f =>
    k5FiberToEmbedding G q ⟨f.1, (Finset.mem_filter.mp f.2).2⟩
  have hemb : Function.Injective emb := by
    intro f g hfg
    apply Subtype.ext
    have hfiber := k5FiberToEmbedding_injective G q hfg
    exact congrArg
      (fun z : {z : K5MinusEdgeGraph.Copy G //
        k5CopyToConfiguration G z = q} => z.1) hfiber
  calc
    ((k5MinusEdgeCopyFinset G).filter fun f =>
        k5CopyToConfiguration G f = q).card = Fintype.card ↑s := by
      change s.card = Fintype.card ↑s
      exact (Fintype.card_coe s).symm
    _ ≤ Fintype.card (Fin 3 ↪ ↑q.1.1) :=
      Fintype.card_le_of_injective emb hemb
    _ = 6 := by
      rw [Fintype.card_embedding_eq]
      have hcardT : Fintype.card ↑q.1.1 = 3 := by
        simpa using
          (SimpleGraph.mem_cliqueFinset_iff.mp
            ((mem_k5MinusEdgeConfigurations G q.1.1 q.1.2.1 q.1.2.2).mp q.2).1).card_eq
      rw [hcardT, Fintype.card_fin, Nat.descFactorial_self]
      decide

/-- The only multiplicity lost by the charge is the `3!` triangle labelling. -/
theorem labelledCopies_K5MinusEdge_le_six_mul_charge (G : SimpleGraph V) :
    labelledCopies G K5MinusEdgeGraph ≤ 6 * k5MinusEdgeCharge G := by
  classical
  rw [← k5MinusEdgeCopyFinset_card]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := k5CopyToConfiguration G)
    (t := (Finset.univ : Finset ↑(k5MinusEdgeConfigurations G)))
    (by intro f _hf; exact Finset.mem_univ (k5CopyToConfiguration G f))]
  calc
    (∑ q : ↑(k5MinusEdgeConfigurations G),
        ((k5MinusEdgeCopyFinset G).filter fun f =>
          k5CopyToConfiguration G f = q).card) ≤
        ∑ _q : ↑(k5MinusEdgeConfigurations G), 6 := by
      apply Finset.sum_le_sum
      intro q _hq
      exact card_k5CopyConfigurationFiber_le_six G q
    _ = 6 * Fintype.card ↑(k5MinusEdgeConfigurations G) := by
      simp [Nat.mul_comm]
    _ = 6 * (k5MinusEdgeConfigurations G).card := by simp
    _ = 6 * k5MinusEdgeCharge G := by
      rw [k5MinusEdgeConfigurations_card]

end K5MinusEdgeLabelledBridge

section QLabelledBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered edges of `G` lying completely inside `S`. -/
noncomputable def insideOrderedEdges (G : SimpleGraph V) (S : Finset V) :
    Finset (V × V) := by
  classical
  exact (S.product S).filter fun e => G.Adj e.1 e.2

@[simp] theorem mem_insideOrderedEdges (G : SimpleGraph V) (S : Finset V)
    (x y : V) :
    (x, y) ∈ insideOrderedEdges G S ↔ x ∈ S ∧ y ∈ S ∧ G.Adj x y := by
  classical
  simp only [insideOrderedEdges, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hxy, hadj⟩
    exact ⟨(Finset.mem_product.mp hxy).1, (Finset.mem_product.mp hxy).2, hadj⟩
  · rintro ⟨hx, hy, hadj⟩
    exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hadj⟩

theorem insideOrderedEdges_card (G : SimpleGraph V) (S : Finset V) :
    (insideOrderedEdges G S).card = insideOrderedEdgeMass G S := by
  rfl

/-- Configurations counted by `qCharge`. -/
noncomputable def qConfigurations (G : SimpleGraph V) :
    Finset (Σ _ab : V × V, Σ _cd : V × V, V × V) := by
  classical
  exact (orderedEdges G).sigma fun ab =>
    (insideOrderedEdges G (commonNeighborsFinset G {ab.1, ab.2})).sigma fun _cd =>
      (commonNeighborsFinset G {ab.1, ab.2}).product
        (commonNeighborsFinset G {ab.1, ab.2})

/-- A proof-local classical enumeration of all labelled `Q` copies. -/
noncomputable def qCopyFinset (G : SimpleGraph V) : Finset (QGraph.Copy G) := by
  classical
  exact Finset.univ

/-- The classical enumeration contains every labelled `Q` copy. -/
noncomputable def qCopyFinsetEquiv (G : SimpleGraph V) :
    ↑(qCopyFinset G) ≃ QGraph.Copy G := by
  classical
  exact
    { toFun := Subtype.val
      invFun := fun f => ⟨f, by simp [qCopyFinset]⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }

theorem qCopyFinset_card (G : SimpleGraph V) :
    (qCopyFinset G).card = labelledCopies G QGraph := by
  classical
  calc
    (qCopyFinset G).card = Fintype.card ↑(qCopyFinset G) :=
      (Fintype.card_coe _).symm
    _ = Nat.card ↑(qCopyFinset G) := Nat.card_eq_fintype_card.symm
    _ = Nat.card (QGraph.Copy G) := Nat.card_congr (qCopyFinsetEquiv G)
    _ = labelledCopies G QGraph := natCard_copy_eq_labelledCopies G QGraph

theorem qConfigurations_card (G : SimpleGraph V) :
    (qConfigurations G).card = qCharge G := by
  classical
  simp [qConfigurations, qCharge, insideOrderedEdges_card, codegree,
    Finset.card_sigma, Finset.card_product, insideOrderedEdgeMass,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] <;> ring

/-- The six images of a labelled `Q` copy, grouped as the charge data. -/
def qCopyData (G : SimpleGraph V) (f : QGraph.Copy G) :
    Σ _ab : V × V, Σ _cd : V × V, V × V :=
  ⟨(f 0, f 1), ⟨(f 2, f 3), (f 4, f 5)⟩⟩

/-- Every labelled `Q` copy is one of the more permissive charge configurations. -/
noncomputable def qCopyToConfiguration (G : SimpleGraph V)
    (f : QGraph.Copy G) : ↑(qConfigurations G) := by
  classical
  have hmap {i j : Fin 6} (hij : QGraph.Adj i j) : G.Adj (f i) (f j) :=
    f.toHom.map_adj hij
  have h01 : G.Adj (f 0) (f 1) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h02 : G.Adj (f 0) (f 2) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h03 : G.Adj (f 0) (f 3) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h04 : G.Adj (f 0) (f 4) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h05 : G.Adj (f 0) (f 5) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h12 : G.Adj (f 1) (f 2) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h13 : G.Adj (f 1) (f 3) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h14 : G.Adj (f 1) (f 4) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h15 : G.Adj (f 1) (f 5) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  have h23 : G.Adj (f 2) (f 3) := hmap (by simp [QGraph, SimpleGraph.edge_adj])
  refine ⟨qCopyData G f, ?_⟩
  change Sigma.mk (f 0, f 1) (Sigma.mk (f 2, f 3) (f 4, f 5)) ∈
    qConfigurations G
  unfold qConfigurations
  rw [Finset.mem_sigma]
  refine ⟨(mem_orderedEdges G (f 0) (f 1)).mpr h01, ?_⟩
  rw [Finset.mem_sigma]
  have h2 : f 2 ∈ commonNeighborsFinset G {f 0, f 1} := by
    rw [mem_commonNeighborsFinset]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h02
    · exact h12
  have h3 : f 3 ∈ commonNeighborsFinset G {f 0, f 1} := by
    rw [mem_commonNeighborsFinset]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h03
    · exact h13
  have h4 : f 4 ∈ commonNeighborsFinset G {f 0, f 1} := by
    rw [mem_commonNeighborsFinset]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h04
    · exact h14
  have h5 : f 5 ∈ commonNeighborsFinset G {f 0, f 1} := by
    rw [mem_commonNeighborsFinset]
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h05
    · exact h15
  refine ⟨(mem_insideOrderedEdges G _ (f 2) (f 3)).mpr ⟨h2, h3, h23⟩, ?_⟩
  exact Finset.mem_product.mpr ⟨h4, h5⟩

theorem qCopyToConfiguration_injective (G : SimpleGraph V) :
    Function.Injective (qCopyToConfiguration G) := by
  intro f g hfg
  have hdata : qCopyData G f = qCopyData G g := congrArg Subtype.val hfg
  have h0 : f 0 = g 0 := congrArg (fun p => p.1.1) hdata
  have h1 : f 1 = g 1 := congrArg (fun p => p.1.2) hdata
  have h2 : f 2 = g 2 := congrArg (fun p => p.2.1.1) hdata
  have h3 : f 3 = g 3 := congrArg (fun p => p.2.1.2) hdata
  have h4 : f 4 = g 4 := congrArg (fun p => p.2.2.1) hdata
  have h5 : f 5 = g 5 := congrArg (fun p => p.2.2.2) hdata
  apply SimpleGraph.Copy.ext
  intro i
  fin_cases i <;> assumption

/-- The `Q` charge dominates labelled copies with constant one. -/
theorem labelledCopies_Q_le_qCharge (G : SimpleGraph V) :
    labelledCopies G QGraph ≤ qCharge G := by
  classical
  calc
    labelledCopies G QGraph = (qCopyFinset G).card :=
      (qCopyFinset_card G).symm
    _ ≤ (qConfigurations G).card := by
      apply Finset.card_le_card_of_injOn
        (fun f => (qCopyToConfiguration G f).1)
      · intro f _hf
        exact (qCopyToConfiguration G f).2
      · intro f _hf g _hg hfg
        apply qCopyToConfiguration_injective G
        apply Subtype.ext
        exact hfg
    _ = qCharge G := qConfigurations_card G

end QLabelledBridge

end OnlineRamsey
