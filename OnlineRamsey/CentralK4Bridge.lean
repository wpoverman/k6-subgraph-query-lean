import OnlineRamsey.SharpCounting
import OnlineRamsey.LabelledCharges

/-!
# Rooted central-edge mass and labelled four-cliques

The `Q` charge retains a rooted `K₄` incidence sum.  This file turns that
sum into a genuine labelled `K₄` count by an explicit injection.  The
inequality direction is all the sharp exceptional estimate needs.
-/

open scoped BigOperators

namespace OnlineRamsey

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- Ordered central edges together with an ordered edge in their common
neighborhood. -/
noncomputable def centralK4Configurations (G : SimpleGraph V) :
    Finset (Σ _ab : V × V, V × V) := by
  classical
  exact (orderedEdges G).sigma fun ab ↦
    insideOrderedEdges G (commonNeighborsFinset G {ab.1, ab.2})

theorem centralK4Configurations_card (G : SimpleGraph V) :
    (centralK4Configurations G).card = centralK4Mass G := by
  classical
  simp [centralK4Configurations, centralK4Mass, Finset.card_sigma,
    insideOrderedEdges_card]

def centralFin4TupleFun (a b c d : V) (i : Fin 4) : V :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

@[simp] theorem centralFin4TupleFun_zero (a b c d : V) :
    centralFin4TupleFun a b c d 0 = a := rfl

@[simp] theorem centralFin4TupleFun_one (a b c d : V) :
    centralFin4TupleFun a b c d 1 = b := rfl

@[simp] theorem centralFin4TupleFun_two (a b c d : V) :
    centralFin4TupleFun a b c d 2 = c := rfl

@[simp] theorem centralFin4TupleFun_three (a b c d : V) :
    centralFin4TupleFun a b c d 3 = d := rfl

/-- A rooted central-edge configuration is a labelled four-clique. -/
noncomputable def centralK4ConfigurationToCopy (G : SimpleGraph V)
    (z : ↑(centralK4Configurations G)) : K4Graph.Copy G := by
  classical
  rcases z with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hz⟩
  have hz' := Finset.mem_sigma.mp hz
  have hab : G.Adj a b := by
    simpa using (mem_orderedEdges G a b).mp hz'.1
  have hinside := (mem_insideOrderedEdges G
    (commonNeighborsFinset G {a, b}) c d).mp hz'.2
  have hc := (mem_commonNeighborsFinset G {a, b} c).mp hinside.1
  have hd := (mem_commonNeighborsFinset G {a, b} d).mp hinside.2.1
  have hcd : G.Adj c d := hinside.2.2
  have hac : G.Adj a c := hc a (by simp)
  have hbc : G.Adj b c := hc b (by simp)
  have had : G.Adj a d := hd a (by simp)
  have hbd : G.Adj b d := hd b (by simp)
  have hba : G.Adj b a := hab.symm
  have hca : G.Adj c a := hac.symm
  have hcb : G.Adj c b := hbc.symm
  have hda : G.Adj d a := had.symm
  have hdb : G.Adj d b := hbd.symm
  have hdc : G.Adj d c := hcd.symm
  let hom : K4Graph →g G :=
    { toFun := centralFin4TupleFun a b c d
      map_rel' := by
        intro i j hij
        have hij' : i ≠ j := (SimpleGraph.top_adj i j).mp hij
        fin_cases i <;> fin_cases j <;>
          simp_all [centralFin4TupleFun] }
  exact ⟨hom, SimpleGraph.Hom.injective_of_top_hom hom⟩

theorem centralK4ConfigurationToCopy_injective (G : SimpleGraph V) :
    Function.Injective (centralK4ConfigurationToCopy G) := by
  intro z w hzw
  rcases z with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hz⟩
  rcases w with ⟨⟨⟨a', b'⟩, ⟨c', d'⟩⟩, hw⟩
  have h0 : a = a' := congrArg
    (fun f : K4Graph.Copy G ↦ f 0) hzw
  have h1 : b = b' := congrArg
    (fun f : K4Graph.Copy G ↦ f 1) hzw
  have h2 : c = c' := congrArg
    (fun f : K4Graph.Copy G ↦ f 2) hzw
  have h3 : d = d' := congrArg
    (fun f : K4Graph.Copy G ↦ f 3) hzw
  subst a'
  subst b'
  subst c'
  subst d'
  rfl

/-- The rooted incidence sum injects into the labelled `K₄` copies. -/
theorem centralK4Mass_le_labelledCopies_k4 (G : SimpleGraph V) :
    centralK4Mass G ≤ labelledCopies G K4Graph := by
  classical
  calc
    centralK4Mass G = (centralK4Configurations G).card :=
      (centralK4Configurations_card G).symm
    _ = Fintype.card ↑(centralK4Configurations G) := by simp
    _ ≤ Fintype.card (K4Graph.Copy G) :=
      Fintype.card_le_of_injective
        (centralK4ConfigurationToCopy G)
        (centralK4ConfigurationToCopy_injective G)
    _ = Nat.card (K4Graph.Copy G) := Nat.card_eq_fintype_card.symm
    _ = labelledCopies G K4Graph :=
      natCard_copy_eq_labelledCopies G K4Graph

end
end OnlineRamsey
