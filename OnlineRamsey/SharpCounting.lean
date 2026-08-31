import OnlineRamsey.HostCounting
import OnlineRamsey.LabelledCharges
import Mathlib.Data.List.NodupEquivFin

/-!
# Sharp deterministic counting bridges

This module closes deterministic interfaces used by the lower-bound proof:
it turns the hereditary deletion certificate into an actual degeneracy order,
and packages labelled-copy estimates from the charging sums.
-/

open scoped BigOperators

namespace OnlineRamsey

section PeelingOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A deletion list obtained by repeatedly choosing a low-degree vertex. -/
noncomputable def peelingList (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) : Finset V → List V
  | U => if hU : U.Nonempty then
      let v := Classical.choose (hG U hU)
      v :: peelingList G D hG (U.erase v)
    else []
termination_by U => U.card
decreasing_by
  have hv : Classical.choose (hG U hU) ∈ U :=
    (Classical.choose_spec (hG U hU)).1
  exact Finset.card_erase_lt_of_mem hv

theorem peelingList_eq_cons (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) (U : Finset V) (hU : U.Nonempty) :
    peelingList G D hG U =
      Classical.choose (hG U hU) ::
        peelingList G D hG (U.erase (Classical.choose (hG U hU))) := by
  rw [peelingList]
  simp [hU]

theorem peelingList_eq_nil (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) (U : Finset V) (hU : ¬ U.Nonempty) :
    peelingList G D hG U = [] := by
  rw [peelingList]
  simp [hU]

theorem peelingList_toFinset (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) (U : Finset V) :
    (peelingList G D hG U).toFinset = U := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
      by_cases hU : U.Nonempty
      · let v := Classical.choose (hG U hU)
        have hv : v ∈ U := (Classical.choose_spec (hG U hU)).1
        have hsub : U.erase v ⊂ U := Finset.erase_ssubset hv
        rw [peelingList_eq_cons G D hG U hU]
        change (v :: peelingList G D hG (U.erase v)).toFinset = U
        rw [List.toFinset_cons, ih (U.erase v) hsub]
        exact Finset.insert_erase hv
      · rw [peelingList_eq_nil G D hG U hU]
        simpa using (Finset.not_nonempty_iff_eq_empty.mp hU).symm

theorem peelingList_nodup (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) (U : Finset V) :
    (peelingList G D hG U).Nodup := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
      by_cases hU : U.Nonempty
      · let v := Classical.choose (hG U hU)
        have hv : v ∈ U := (Classical.choose_spec (hG U hU)).1
        have hsub : U.erase v ⊂ U := Finset.erase_ssubset hv
        rw [peelingList_eq_cons G D hG U hU]
        apply List.nodup_cons.mpr
        constructor
        · rw [← List.mem_toFinset, peelingList_toFinset]
          exact Finset.notMem_erase v U
        · exact ih (U.erase v) hsub
      · rw [peelingList_eq_nil G D hG U hU]
        exact List.nodup_nil

/-- Later neighbors, phrased directly in terms of positions in a list. -/
noncomputable def laterNeighborsInList (G : SimpleGraph V)
    (U : Finset V) (l : List V) (v : V) : Finset V := by
  classical
  exact U.filter fun w => G.Adj v w ∧ l.idxOf v < l.idxOf w

@[simp] theorem mem_laterNeighborsInList (G : SimpleGraph V)
    (U : Finset V) (l : List V) (v w : V) :
    w ∈ laterNeighborsInList G U l v ↔
      w ∈ U ∧ G.Adj v w ∧ l.idxOf v < l.idxOf w := by
  classical
  simp [laterNeighborsInList]

/-- Every vertex has at most `D` later neighbors in its deletion list. -/
theorem peelingList_laterNeighbors_le (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) (U : Finset V) :
    ∀ v ∈ U,
      (laterNeighborsInList G U (peelingList G D hG U) v).card ≤ D := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
      intro x hxU
      have hU : U.Nonempty := ⟨x, hxU⟩
      let v := Classical.choose (hG U hU)
      have hvU : v ∈ U := (Classical.choose_spec (hG U hU)).1
      have hvlow : (U ∩ neighbors G v).card ≤ D :=
        (Classical.choose_spec (hG U hU)).2
      have hsub : U.erase v ⊂ U := Finset.erase_ssubset hvU
      rw [peelingList_eq_cons G D hG U hU]
      change
        (laterNeighborsInList G U
          (v :: peelingList G D hG (U.erase v)) x).card ≤ D
      by_cases hxv : x = v
      · subst x
        apply (Finset.card_le_card ?_).trans hvlow
        intro w hw
        rw [mem_laterNeighborsInList] at hw
        rw [Finset.mem_inter, mem_neighbors]
        exact ⟨hw.1, hw.2.1⟩
      · have hxErase : x ∈ U.erase v := Finset.mem_erase.mpr ⟨hxv, hxU⟩
        have hrec := ih (U.erase v) hsub x hxErase
        apply (Finset.card_le_card ?_).trans hrec
        intro w hw
        rw [mem_laterNeighborsInList] at hw ⊢
        have hxshift : (v :: peelingList G D hG (U.erase v)).idxOf x =
            (peelingList G D hG (U.erase v)).idxOf x + 1 := by
          simpa [Nat.succ_eq_add_one] using List.idxOf_cons_ne
            (peelingList G D hG (U.erase v)) (Ne.symm hxv)
        have hwv : w ≠ v := by
          intro hwv
          subst w
          have hz : (v :: peelingList G D hG (U.erase v)).idxOf v = 0 := by simp
          omega
        have hwshift : (v :: peelingList G D hG (U.erase v)).idxOf w =
            (peelingList G D hG (U.erase v)).idxOf w + 1 := by
          simpa [Nat.succ_eq_add_one] using List.idxOf_cons_ne
            (peelingList G D hG (U.erase v)) (Ne.symm hwv)
        refine ⟨Finset.mem_erase.mpr ⟨hwv, hw.1⟩, hw.2.1, ?_⟩
        rw [hxshift, hwshift] at hw
        omega

private noncomputable def orderOfCompleteList (l : List V) (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hlen : l.length = Fintype.card V) :
    V ≃ Fin (Fintype.card V) :=
  (hnd.getEquivOfForallMemList l hall).symm.trans
    (Equiv.cast (congrArg Fin hlen))

private theorem orderOfCompleteList_apply (l : List V) (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hlen : l.length = Fintype.card V) (v : V) :
    (orderOfCompleteList l hnd hall hlen v : ℕ) = l.idxOf v := by
  unfold orderOfCompleteList
  rw [Equiv.trans_apply]
  have hcast (i : Fin l.length) :
      ((Equiv.cast (congrArg Fin hlen)) i : ℕ) = (i : ℕ) := by
    change ((cast (congrArg Fin hlen) i : Fin (Fintype.card V)) : ℕ) = (i : ℕ)
    rw [Fin.cast_eq_cast', Fin.coe_cast]
  rw [hcast]
  rfl

/-- The concrete total order read off from the hereditary deletion list. -/
noncomputable def hereditaryDegeneracyOrder (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) :
    V ≃ Fin (Fintype.card V) := by
  classical
  let l := peelingList G D hG Finset.univ
  have hnd : l.Nodup := peelingList_nodup G D hG Finset.univ
  have hall : ∀ v : V, v ∈ l := by
    intro v
    rw [← List.mem_toFinset, peelingList_toFinset]
    exact Finset.mem_univ v
  have hlen : l.length = Fintype.card V := by
    calc
      l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ = Fintype.card V := by rw [peelingList_toFinset, Finset.card_univ]
  exact orderOfCompleteList l hnd hall hlen

theorem hereditaryDegeneracyOrder_apply (G : SimpleGraph V) (D : ℕ)
    (hG : HereditarilyLowDegree G D) (v : V) :
    (hereditaryDegeneracyOrder G D hG v : ℕ) =
      (peelingList G D hG Finset.univ).idxOf v := by
  classical
  unfold hereditaryDegeneracyOrder
  exact orderOfCompleteList_apply _ _ _ _ v

/-- On a finite graph, the hereditary deletion condition produces an
explicit degeneracy order. -/
theorem HereditarilyLowDegree.isDegenerate {G : SimpleGraph V} {D : ℕ}
    (hG : HereditarilyLowDegree G D) : IsDegenerate G D := by
  classical
  refine ⟨hereditaryDegeneracyOrder G D hG, ?_⟩
  intro v
  have hbound := peelingList_laterNeighbors_le G D hG Finset.univ v
    (Finset.mem_univ v)
  apply (Finset.card_le_card ?_).trans hbound
  intro w hw
  rw [mem_forwardNeighbors] at hw
  rw [mem_laterNeighborsInList]
  have hlt := hw.2
  rw [Fin.lt_iff_val_lt_val] at hlt
  rw [hereditaryDegeneracyOrder_apply G D hG v,
    hereditaryDegeneracyOrder_apply G D hG w] at hlt
  exact ⟨Finset.mem_univ w, hw.1, hlt⟩

end PeelingOrder

section TriangleDegeneracy

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance triangleAdjDecidable (G : SimpleGraph V) :
    DecidableRel G.Adj := Classical.decRel _

noncomputable def forwardPairConfigurations (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) : Finset (Σ _v : V, Finset V) := by
  classical
  exact Finset.univ.sigma fun v =>
    (forwardNeighbors G order v).powersetCard 2

private theorem threeClique_nonempty (G : SimpleGraph V)
    (K : ↑(G.cliqueFinset 3)) : K.1.Nonempty := by
  apply Finset.card_pos.mp
  rw [(SimpleGraph.mem_cliqueFinset_iff.mp K.2).card_eq]
  decide

noncomputable def triangleEarliestVertex (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3)) : V :=
  Classical.choose (K.1.exists_min_image order (threeClique_nonempty G K))

theorem triangleEarliestVertex_mem (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3)) :
    triangleEarliestVertex G order K ∈ K.1 := by
  exact (Classical.choose_spec
    (K.1.exists_min_image order (threeClique_nonempty G K))).1

theorem triangleEarliestVertex_min (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3))
    (w : V) (hw : w ∈ K.1) :
    order (triangleEarliestVertex G order K) ≤ order w := by
  exact (Classical.choose_spec
    (K.1.exists_min_image order (threeClique_nonempty G K))).2 w hw

noncomputable def triangleToForwardPair (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3)) :
    ↑(forwardPairConfigurations G order) := by
  classical
  let v := triangleEarliestVertex G order K
  let P := K.1.erase v
  have hvK : v ∈ K.1 := triangleEarliestVertex_mem G order K
  have hKclique := SimpleGraph.mem_cliqueFinset_iff.mp K.2
  have hPcard : P.card = 2 := by
    simp [P, Finset.card_erase_of_mem hvK, hKclique.card_eq]
  have hPforward : P ⊆ forwardNeighbors G order v := by
    intro w hw
    rw [mem_forwardNeighbors]
    have hwK : w ∈ K.1 := Finset.mem_of_mem_erase hw
    have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
    have hadj : G.Adj v w := hKclique.isClique hvK hwK (Ne.symm hwne)
    have hle := triangleEarliestVertex_min G order K w hwK
    exact ⟨hadj, lt_of_le_of_ne hle (fun heq => hwne (order.injective heq).symm)⟩
  refine ⟨⟨v, P⟩, ?_⟩
  simp only [forwardPairConfigurations, Finset.mem_sigma, Finset.mem_univ,
    true_and, Finset.mem_powersetCard]
  exact ⟨hPforward, hPcard⟩

theorem triangleToForwardPair_injective (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    Function.Injective (triangleToForwardPair G order) := by
  intro K L hKL
  apply Subtype.ext
  have hdata := congrArg Subtype.val hKL
  have hv : triangleEarliestVertex G order K =
      triangleEarliestVertex G order L := congrArg Sigma.fst hdata
  have hP : K.1.erase (triangleEarliestVertex G order K) =
      L.1.erase (triangleEarliestVertex G order L) := congrArg Sigma.snd hdata
  calc
    K.1 = insert (triangleEarliestVertex G order K)
        (K.1.erase (triangleEarliestVertex G order K)) :=
      (Finset.insert_erase (triangleEarliestVertex_mem G order K)).symm
    _ = insert (triangleEarliestVertex G order L)
        (L.1.erase (triangleEarliestVertex G order L)) := congrArg₂ insert hv hP
    _ = L.1 := Finset.insert_erase (triangleEarliestVertex_mem G order L)

/-- A `D`-degeneracy order gives the linear triangle bound `D e(G)`. -/
theorem triangleCount_le_mul_edges_of_degeneracyOrder (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) {D : ℕ}
    (horder : IsDegeneracyOrder G order D) :
    triangleCount G ≤ D * edgeCount G := by
  classical
  have hconfig : triangleCount G ≤ (forwardPairConfigurations G order).card := by
    unfold triangleCount
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective (triangleToForwardPair G order)
      (triangleToForwardPair_injective G order)
  calc
    triangleCount G ≤ (forwardPairConfigurations G order).card := hconfig
    _ = ∑ v : V, (forwardNeighbors G order v).card.choose 2 := by
      simp [forwardPairConfigurations, Finset.card_sigma]
    _ ≤ ∑ v : V, D * (forwardNeighbors G order v).card := by
      apply Finset.sum_le_sum
      intro v _hv
      let d := (forwardNeighbors G order v).card
      calc
        d.choose 2 ≤ d ^ 2 := Nat.choose_le_pow d 2
        _ = d * d := by ring
        _ ≤ D * d := Nat.mul_le_mul_right d (horder v)
    _ = D * orientedEdgeMass G order := by
      simp [orientedEdgeMass, Finset.mul_sum]
    _ = D * edgeCount G := by rw [orientedEdgeMass_eq_edgeCount]

end TriangleDegeneracy

section SmallSetSharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Keep only edges whose two endpoints lie in `B`; vertices outside `B`
remain in the ambient type but are isolated. -/
def supportedGraph (G : SimpleGraph V) (B : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ B ∧ y ∈ B
  symm := by
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := by
    intro x h
    exact G.irrefl h.1

@[simp] theorem supportedGraph_adj (G : SimpleGraph V) (B : Finset V)
    (x y : V) :
    (supportedGraph G B).Adj x y ↔ G.Adj x y ∧ x ∈ B ∧ y ∈ B := Iff.rfl

theorem supportedGraph_le (G : SimpleGraph V) (B : Finset V) :
    supportedGraph G B ≤ G := by
  intro x y hxy
  exact hxy.1

theorem edgeCount_supportedGraph_le_edgesSpanned (G : SimpleGraph V)
    (B : Finset V) :
    edgeCount (supportedGraph G B) ≤ RandomBoard.edgesSpanned G B := by
  classical
  unfold edgeCount RandomBoard.edgesSpanned
  rw [Set.ncard_eq_toFinset_card']
  apply Finset.card_le_card
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at he
      rw [Set.mem_toFinset, Set.mem_inter_iff, SimpleGraph.mem_edgeSet]
      exact ⟨he.1, by
        change s(x, y) ∈ B.sym2
        rw [Finset.mk_mem_sym2_iff]
        exact ⟨he.2.1, he.2.2⟩⟩

/-- A linear edge bound on every small set gives hereditary degree at most
`2L` on the graph supported by any one such set. -/
theorem SmallSetCertificate.supportedHereditarilyLowDegree
    {G : SimpleGraph V} {D L : ℕ}
    (hsmall : RandomBoard.SmallSetCertificate G D L)
    (B : Finset V) (hB : B.card ≤ D) :
    HereditarilyLowDegree (supportedGraph G B) (2 * L) := by
  classical
  intro U hU
  by_cases hout : ∃ v ∈ U, v ∉ B
  · obtain ⟨v, hvU, hvB⟩ := hout
    refine ⟨v, hvU, ?_⟩
    have hempty : U ∩ neighbors (supportedGraph G B) v = ∅ := by
      ext w
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      intro hw
      have hadj := (mem_neighbors (supportedGraph G B) v w).mp hw.2
      exact hvB hadj.2.1
    rw [hempty]
    simp
  · push_neg at hout
    have hUB : U ⊆ B := fun v hv => hout v hv
    have hUcard : U.card ≤ D := (Finset.card_le_card hUB).trans hB
    by_contra hnone
    push_neg at hnone
    have hsumlt :
        (2 * L) * U.card <
          ∑ v ∈ U, internalDegree (supportedGraph G B) U v := by
      have hs := Finset.sum_lt_sum_of_nonempty hU
        (fun v hv => hnone v hv)
      simpa [Nat.mul_comm] using hs
    have hspanlt :
        (2 * L) * U.card <
          2 * RandomBoard.edgesSpanned (supportedGraph G B) U := by
      simpa [sum_internalDegree_eq_twice_edgesSpanned] using hsumlt
    have hmono := edgesSpanned_mono (supportedGraph_le G B) U
    have hcert := hsmall U hUcard
    have hle :
        2 * RandomBoard.edgesSpanned (supportedGraph G B) U ≤
          (2 * L) * U.card := by
      calc
        2 * RandomBoard.edgesSpanned (supportedGraph G B) U ≤
            2 * RandomBoard.edgesSpanned G U := Nat.mul_le_mul_left 2 hmono
        _ ≤ 2 * (L * U.card) := Nat.mul_le_mul_left 2 hcert
        _ = (2 * L) * U.card := by ring
    exact (Nat.not_lt_of_ge hle) hspanlt

/-- Triangles lying in `B` are triangles of the graph supported on `B`. -/
theorem trianglesIn_le_supportedTriangleCount (G : SimpleGraph V)
    (B : Finset V) :
    trianglesIn G B ≤ triangleCount (supportedGraph G B) := by
  classical
  unfold trianglesIn triangleCount
  apply Finset.card_le_card
  intro T hT
  rw [Finset.mem_filter] at hT
  apply SimpleGraph.mem_cliqueFinset_iff.mpr
  have hclique := SimpleGraph.mem_cliqueFinset_iff.mp hT.1
  refine ⟨?_, hclique.card_eq⟩
  intro x hx y hy hxy
  exact ⟨hclique.isClique hx hy hxy, hT.2 hx, hT.2 hy⟩

/-- Sharp finite consequence of the small-set certificate: every set of
size at most `D` spans only linearly many triangles. -/
theorem SmallSetCertificate.trianglesIn_le
    {G : SimpleGraph V} {D L : ℕ}
    (hsmall : RandomBoard.SmallSetCertificate G D L)
    (B : Finset V) (hB : B.card ≤ D) :
    trianglesIn G B ≤ (2 * L * L) * B.card := by
  classical
  have hdeg :=
    (SmallSetCertificate.supportedHereditarilyLowDegree hsmall B hB).isDegenerate
  obtain ⟨order, horder⟩ := hdeg
  calc
    trianglesIn G B ≤ triangleCount (supportedGraph G B) :=
      trianglesIn_le_supportedTriangleCount G B
    _ ≤ (2 * L) * edgeCount (supportedGraph G B) :=
      triangleCount_le_mul_edges_of_degeneracyOrder _ order horder
    _ ≤ (2 * L) * RandomBoard.edgesSpanned G B :=
      Nat.mul_le_mul_left (2 * L) (edgeCount_supportedGraph_le_edgesSpanned G B)
    _ ≤ (2 * L) * (L * B.card) :=
      Nat.mul_le_mul_left (2 * L) (hsmall B hB)
    _ = (2 * L * L) * B.card := by ring

/-- The paper's local-triangle input follows uniformly for the forward
neighborhoods of a supplied degeneracy order. -/
theorem SmallSetCertificate.localTriangleLinear
    {G : SimpleGraph V} {D L : ℕ}
    (hsmall : RandomBoard.SmallSetCertificate G D L)
    (order : V ≃ Fin (Fintype.card V))
    (horder : IsDegeneracyOrder G order D) :
    LocalTriangleLinear G order (2 * L * L) := by
  intro v
  exact SmallSetCertificate.trianglesIn_le hsmall _ (horder v)

/-- Consequently the earliest-vertex `K₄` charge is linear in the edge
count with a constant depending only on the small-set parameter. -/
theorem SmallSetCertificate.k4Charge_le
    {G : SimpleGraph V} {D L : ℕ}
    (hsmall : RandomBoard.SmallSetCertificate G D L)
    (order : V ≃ Fin (Fintype.card V))
    (horder : IsDegeneracyOrder G order D) :
    k4Charge G order ≤ (2 * L * L) * edgeCount G := by
  apply k4Charge_le_edges G order
    (SmallSetCertificate.localTriangleLinear hsmall order horder)
  rw [orientedEdgeMass_eq_edgeCount]

end SmallSetSharpness

section SharpLinkTriangles

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance linkTriangleAdjDecidable (G : SimpleGraph V) :
    DecidableRel G.Adj := Classical.decRel _

/-- Ordered edges inside all forward neighborhoods.  This deliberately keeps
both orientations, costing a harmless factor two and making the finite map
from triangles completely explicit. -/
noncomputable def forwardOrderedEdgeConfigurations (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    Finset (Σ _v : V, V × V) := by
  classical
  exact Finset.univ.sigma fun v =>
    insideOrderedEdges G (forwardNeighbors G order v)

theorem insideOrderedEdgeMass_le_twice_edgesSpanned (G : SimpleGraph V)
    (B : Finset V) :
    insideOrderedEdgeMass G B ≤ 2 * RandomBoard.edgesSpanned G B := by
  classical
  have heq : insideOrderedEdges G B = orderedEdges (supportedGraph G B) := by
    ext e
    rcases e with ⟨x, y⟩
    simp only [mem_insideOrderedEdges, mem_orderedEdges, supportedGraph_adj]
    tauto
  calc
    insideOrderedEdgeMass G B = (insideOrderedEdges G B).card := rfl
    _ = (orderedEdges (supportedGraph G B)).card := congrArg Finset.card heq
    _ = 2 * edgeCount (supportedGraph G B) := card_orderedEdges _
    _ ≤ 2 * RandomBoard.edgesSpanned G B :=
      Nat.mul_le_mul_left 2 (edgeCount_supportedGraph_le_edgesSpanned G B)

private theorem triangleRemaining_card_two (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3)) :
    (K.1.erase (triangleEarliestVertex G order K)).card = 2 := by
  rw [Finset.card_erase_of_mem (triangleEarliestVertex_mem G order K),
    (SimpleGraph.mem_cliqueFinset_iff.mp K.2).card_eq]

/-- A deterministic ordering of the two vertices remaining after deleting
the earliest vertex of a triangle. -/
noncomputable def triangleRemainingPair (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3)) : V × V :=
  let h := Finset.card_eq_two.mp (triangleRemaining_card_two G order K)
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem triangleRemainingPair_spec (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3)) :
    (triangleRemainingPair G order K).1 ≠
        (triangleRemainingPair G order K).2 ∧
      K.1.erase (triangleEarliestVertex G order K) =
        {(triangleRemainingPair G order K).1,
          (triangleRemainingPair G order K).2} := by
  classical
  unfold triangleRemainingPair
  exact Classical.choose_spec (Classical.choose_spec
    (Finset.card_eq_two.mp (triangleRemaining_card_two G order K)))

noncomputable def triangleToForwardOrderedEdge (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 3)) :
    ↑(forwardOrderedEdgeConfigurations G order) := by
  classical
  let v := triangleEarliestVertex G order K
  let x := (triangleRemainingPair G order K).1
  let y := (triangleRemainingPair G order K).2
  have hspec := triangleRemainingPair_spec G order K
  have hxP : x ∈ K.1.erase v := by
    rw [hspec.2]
    exact Finset.mem_insert_self x {y}
  have hyP : y ∈ K.1.erase v := by
    rw [hspec.2]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have hvK : v ∈ K.1 := triangleEarliestVertex_mem G order K
  have hKclique := SimpleGraph.mem_cliqueFinset_iff.mp K.2
  have hxK : x ∈ K.1 := Finset.mem_of_mem_erase hxP
  have hyK : y ∈ K.1 := Finset.mem_of_mem_erase hyP
  have hxy : G.Adj x y := hKclique.isClique hxK hyK hspec.1
  have hxForward : x ∈ forwardNeighbors G order v := by
    rw [mem_forwardNeighbors]
    have hxne : x ≠ v := (Finset.mem_erase.mp hxP).1
    exact ⟨hKclique.isClique hvK hxK (Ne.symm hxne),
      lt_of_le_of_ne (triangleEarliestVertex_min G order K x hxK)
        (fun heq => hxne (order.injective heq).symm)⟩
  have hyForward : y ∈ forwardNeighbors G order v := by
    rw [mem_forwardNeighbors]
    have hyne : y ≠ v := (Finset.mem_erase.mp hyP).1
    exact ⟨hKclique.isClique hvK hyK (Ne.symm hyne),
      lt_of_le_of_ne (triangleEarliestVertex_min G order K y hyK)
        (fun heq => hyne (order.injective heq).symm)⟩
  refine ⟨⟨v, (x, y)⟩, ?_⟩
  simp only [forwardOrderedEdgeConfigurations, Finset.mem_sigma, Finset.mem_univ,
    true_and]
  exact (mem_insideOrderedEdges G _ x y).mpr ⟨hxForward, hyForward, hxy⟩

theorem triangleToForwardOrderedEdge_injective (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    Function.Injective (triangleToForwardOrderedEdge G order) := by
  intro K L hKL
  apply Subtype.ext
  have hdata := congrArg Subtype.val hKL
  have hv : triangleEarliestVertex G order K =
      triangleEarliestVertex G order L := congrArg Sigma.fst hdata
  have hp : triangleRemainingPair G order K =
      triangleRemainingPair G order L := congrArg Sigma.snd hdata
  calc
    K.1 = insert (triangleEarliestVertex G order K)
        (K.1.erase (triangleEarliestVertex G order K)) :=
      (Finset.insert_erase (triangleEarliestVertex_mem G order K)).symm
    _ = insert (triangleEarliestVertex G order K)
        {(triangleRemainingPair G order K).1,
          (triangleRemainingPair G order K).2} := by
      rw [(triangleRemainingPair_spec G order K).2]
    _ = insert (triangleEarliestVertex G order L)
        {(triangleRemainingPair G order L).1,
          (triangleRemainingPair G order L).2} := by rw [hv, hp]
    _ = insert (triangleEarliestVertex G order L)
        (L.1.erase (triangleEarliestVertex G order L)) := by
      rw [(triangleRemainingPair_spec G order L).2]
    _ = L.1 := Finset.insert_erase (triangleEarliestVertex_mem G order L)

/-- Forward-edge charging bounds triangles by twice the sum of the spanned
edges in forward neighborhoods. -/
theorem triangleCount_le_twice_forwardEdgeMass (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    triangleCount G ≤
      ∑ v : V, 2 * RandomBoard.edgesSpanned G (forwardNeighbors G order v) := by
  classical
  calc
    triangleCount G ≤ (forwardOrderedEdgeConfigurations G order).card := by
      unfold triangleCount
      rw [← Fintype.card_coe, ← Fintype.card_coe]
      exact Fintype.card_le_of_injective (triangleToForwardOrderedEdge G order)
        (triangleToForwardOrderedEdge_injective G order)
    _ = ∑ v : V,
        insideOrderedEdgeMass G (forwardNeighbors G order v) := by
      simp [forwardOrderedEdgeConfigurations, Finset.card_sigma,
        insideOrderedEdges_card]
    _ ≤ ∑ v : V,
        2 * RandomBoard.edgesSpanned G (forwardNeighbors G order v) := by
      apply Finset.sum_le_sum
      intro v _hv
      exact insideOrderedEdgeMass_le_twice_edgesSpanned G _

/-- The exact `ForwardEdgeLinear` certificate yields a global linear triangle
bound. -/
theorem triangleCount_le_of_forwardEdgeLinear (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) {L : ℕ}
    (hforward : ForwardEdgeLinear G order L) :
    triangleCount G ≤ (2 * L) * edgeCount G := by
  calc
    triangleCount G ≤
        ∑ v : V, 2 * RandomBoard.edgesSpanned G (forwardNeighbors G order v) :=
      triangleCount_le_twice_forwardEdgeMass G order
    _ ≤ ∑ v : V, 2 * (L * (forwardNeighbors G order v).card) := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Nat.mul_le_mul_left 2 (hforward v)
    _ = (2 * L) * orientedEdgeMass G order := by
      unfold orientedEdgeMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      ring
    _ = (2 * L) * edgeCount G := by rw [orientedEdgeMass_eq_edgeCount]

/-- The sharp link-triangle estimate needed by the half-graph charge. -/
theorem SmallSetCertificate.linkTriangleLinear
    {G : SimpleGraph V} {D L : ℕ}
    (hsmall : RandomBoard.SmallSetCertificate G D L)
    (order : V ≃ Fin (Fintype.card V))
    (horder : IsDegeneracyOrder G order D) :
    LinkTriangleLinear G (2 * L) := by
  intro v
  have hlinkOrder : IsDegeneracyOrder (linkGraph G v) order D :=
    IsDegeneracyOrder.anti (linkGraph_le G v) horder
  have hlinkSmall : RandomBoard.SmallSetCertificate (linkGraph G v) D L :=
    SmallSetCertificate.anti (linkGraph_le G v) hsmall
  exact triangleCount_le_of_forwardEdgeLinear (linkGraph G v) order
    (SmallSetCertificate.forwardEdgeLinear hlinkSmall hlinkOrder)

/-- The paper-scale half-graph charge bound: a host small-set certificate
supplies the missing linear triangle estimate in every link graph. -/
theorem HostGood.subgraphH3Charge_sharp_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G)
    (hE : edgeCount F ≤ M) :
    h3Charge F ≤ (6 * c₂ * (2 * L) * M) * edgeCount F := by
  obtain ⟨order, horder⟩ :=
    (HostGood.subgraphHereditarilyLowDegree hD h hFG hE).isDegenerate
  exact h3Charge_le F (HostGood.subgraphPairCodegreeLE h hFG)
    (SmallSetCertificate.linkTriangleLinear
      (HostGood.subgraphSmallSetCertificate h hFG) order horder) hE

end SharpLinkTriangles

section K4SharpBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance graphAdjDecidable (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-- The image of a labelled four-clique. -/
noncomputable def sharpK4CopyVertices (G : SimpleGraph V)
    (f : K4Graph.Copy G) : Finset V := by
  classical
  exact Finset.univ.map f.toEmbedding

theorem sharpK4CopyVertices_mem (G : SimpleGraph V)
    (f : K4Graph.Copy G) : sharpK4CopyVertices G f ∈ G.cliqueFinset 4 := by
  classical
  apply SimpleGraph.mem_cliqueFinset_iff.mpr
  simpa [K4Graph, sharpK4CopyVertices] using
    (SimpleGraph.isNClique_map_copy_top (G := G) f)

noncomputable def sharpK4CopyFiberEquiv (G : SimpleGraph V) (K : Finset V)
    (hK : K ∈ G.cliqueFinset 4) :
    {f : K4Graph.Copy G // sharpK4CopyVertices G f = K} ≃ (Fin 4 ↪ ↑K) := by
  classical
  have hKClique : G.IsNClique 4 K :=
    SimpleGraph.mem_cliqueFinset_iff.mp hK
  let forward : {f : K4Graph.Copy G // sharpK4CopyVertices G f = K} →
      (Fin 4 ↪ ↑K) := fun f =>
    { toFun := fun i => ⟨f.1 i, by
          have hi : f.1 i ∈ sharpK4CopyVertices G f.1 := by
            unfold sharpK4CopyVertices
            apply Finset.mem_map.mpr
            exact ⟨i, Finset.mem_univ i, rfl⟩
          rw [f.2] at hi
          exact hi⟩
      inj' := by
        intro i j hij
        apply f.1.injective
        exact congrArg Subtype.val hij }
  let backward : (Fin 4 ↪ ↑K) →
      {f : K4Graph.Copy G // sharpK4CopyVertices G f = K} := fun e =>
    let f : K4Graph.Copy G :=
      { toHom :=
          { toFun := fun i => (e i : V)
            map_rel' := by
              intro i j hij
              have hij' : i ≠ j := (SimpleGraph.top_adj i j).mp hij
              apply hKClique.isClique (e i).property (e j).property
              intro heq
              apply hij'
              apply e.injective
              exact Subtype.ext heq }
        injective' := by
          intro i j hij
          apply e.injective
          exact Subtype.ext hij }
    ⟨f, by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [sharpK4CopyVertices, Finset.mem_map] at hx
        obtain ⟨i, _hi, rfl⟩ := hx
        exact (e i).property
      · simpa [sharpK4CopyVertices] using hKClique.card_eq.le⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro f
        apply Subtype.ext
        apply SimpleGraph.Copy.ext
        intro i
        rfl
      right_inv := by
        intro e
        apply DFunLike.ext _ _
        intro i
        apply Subtype.ext
        rfl }

theorem sharp_card_k4CopyFiber (G : SimpleGraph V) (K : Finset V)
    (hK : K ∈ G.cliqueFinset 4) :
    ((Finset.univ : Finset (K4Graph.Copy G)).filter fun f =>
      sharpK4CopyVertices G f = K).card = 24 := by
  classical
  have hfilter :
      Fintype.card {f : K4Graph.Copy G // sharpK4CopyVertices G f = K} =
        ((Finset.univ : Finset (K4Graph.Copy G)).filter fun f =>
          sharpK4CopyVertices G f = K).card := by
    apply Fintype.card_of_subtype
    simp
  rw [← hfilter, Fintype.card_congr (sharpK4CopyFiberEquiv G K hK),
    Fintype.card_embedding_eq]
  have hcardK : Fintype.card ↑K = 4 := by
    simpa using (SimpleGraph.mem_cliqueFinset_iff.mp hK).card_eq
  rw [hcardK, Fintype.card_fin, Nat.descFactorial_self]
  decide

/-- A four-clique together with a labelling of its four vertices. -/
abbrev K4IndexedClique (G : SimpleGraph V) :=
  Σ K : ↑(G.cliqueFinset 4), Fin 4 ↪ ↑K.1

noncomputable def k4CopyToIndexedClique (G : SimpleGraph V)
    (f : K4Graph.Copy G) : K4IndexedClique G := by
  classical
  let K : ↑(G.cliqueFinset 4) :=
    ⟨sharpK4CopyVertices G f, sharpK4CopyVertices_mem G f⟩
  refine ⟨K, ?_⟩
  exact
    { toFun := fun i => ⟨f i, by
          unfold K sharpK4CopyVertices
          apply Finset.mem_map.mpr
          exact ⟨i, Finset.mem_univ i, rfl⟩⟩
      inj' := fun _ _ h => f.injective (congrArg Subtype.val h) }

theorem k4CopyToIndexedClique_injective (G : SimpleGraph V) :
    Function.Injective (k4CopyToIndexedClique G) := by
  intro f g hfg
  apply SimpleGraph.Copy.ext
  intro i
  have hfun := congrArg
    (fun z : K4IndexedClique G => fun j : Fin 4 => (z.2 j : V)) hfg
  exact congrFun hfun i

theorem card_k4IndexedClique (G : SimpleGraph V) :
    Fintype.card (K4IndexedClique G) = 24 * (G.cliqueFinset 4).card := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ K : ↑(G.cliqueFinset 4), Fintype.card (Fin 4 ↪ ↑K.1)) =
        ∑ _K : ↑(G.cliqueFinset 4), 24 := by
      apply Finset.sum_congr rfl
      intro K _hK
      rw [Fintype.card_embedding_eq]
      have hcardK : Fintype.card ↑K.1 = 4 := by
        simpa using (SimpleGraph.mem_cliqueFinset_iff.mp K.2).card_eq
      rw [hcardK, Fintype.card_fin, Nat.descFactorial_self]
      decide
    _ = 24 * (G.cliqueFinset 4).card := by simp [Nat.mul_comm]

/-- The universal `4!` bound relating labelled and set-valued four-cliques. -/
theorem labelledCopies_k4_le_24_mul_cliqueCount (G : SimpleGraph V) :
    labelledCopies G K4Graph ≤ 24 * (G.cliqueFinset 4).card := by
  classical
  rw [← natCard_copy_eq_labelledCopies G K4Graph]
  rw [← card_k4IndexedClique G]
  simpa [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective (k4CopyToIndexedClique G)
      (k4CopyToIndexedClique_injective G)

/-- The finite configurations whose cardinal is the earliest-vertex charge. -/
noncomputable def k4ChargeConfigurations (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) : Finset (Σ _v : V, Finset V) := by
  classical
  exact Finset.univ.sigma fun v =>
    (G.cliqueFinset 3).filter fun T => T ⊆ forwardNeighbors G order v

theorem k4ChargeConfigurations_card (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    (k4ChargeConfigurations G order).card = k4Charge G order := by
  classical
  simp [k4ChargeConfigurations, k4Charge, trianglesIn, Finset.card_sigma]

private theorem fourClique_nonempty (G : SimpleGraph V)
    (K : ↑(G.cliqueFinset 4)) : K.1.Nonempty := by
  have hcard : K.1.card = 4 :=
    (SimpleGraph.mem_cliqueFinset_iff.mp K.2).card_eq
  apply Finset.card_pos.mp
  rw [hcard]
  decide

/-- The earliest vertex of a four-clique in a fixed total order. -/
noncomputable def k4EarliestVertex (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 4)) : V :=
  Classical.choose (K.1.exists_min_image order (fourClique_nonempty G K))

theorem k4EarliestVertex_mem (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 4)) :
    k4EarliestVertex G order K ∈ K.1 :=
  (Classical.choose_spec
    (K.1.exists_min_image order (fourClique_nonempty G K))).1

theorem k4EarliestVertex_min (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 4))
    (w : V) (hw : w ∈ K.1) :
    order (k4EarliestVertex G order K) ≤ order w :=
  (Classical.choose_spec
    (K.1.exists_min_image order (fourClique_nonempty G K))).2 w hw

noncomputable def k4CliqueToChargeConfiguration (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (K : ↑(G.cliqueFinset 4)) :
    ↑(k4ChargeConfigurations G order) := by
  classical
  let v := k4EarliestVertex G order K
  let T := K.1.erase v
  have hvK : v ∈ K.1 := k4EarliestVertex_mem G order K
  have hKclique : G.IsNClique 4 K.1 :=
    SimpleGraph.mem_cliqueFinset_iff.mp K.2
  have hTcard : T.card = 3 := by
    simp [T, Finset.card_erase_of_mem hvK, hKclique.card_eq]
  have hTclique : T ∈ G.cliqueFinset 3 := by
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    refine ⟨?_, hTcard⟩
    intro x hx y hy hxy
    exact hKclique.isClique (Finset.mem_of_mem_erase hx)
      (Finset.mem_of_mem_erase hy) hxy
  have hTforward : T ⊆ forwardNeighbors G order v := by
    intro w hw
    rw [mem_forwardNeighbors]
    have hwK : w ∈ K.1 := Finset.mem_of_mem_erase hw
    have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
    have hadj : G.Adj v w := hKclique.isClique hvK hwK (Ne.symm hwne)
    have hle := k4EarliestVertex_min G order K w hwK
    exact ⟨hadj, lt_of_le_of_ne hle (fun heq => hwne (order.injective heq).symm)⟩
  refine ⟨⟨v, T⟩, ?_⟩
  simp only [k4ChargeConfigurations, Finset.mem_sigma, Finset.mem_univ, true_and,
    Finset.mem_filter]
  exact ⟨hTclique, hTforward⟩

theorem k4CliqueToChargeConfiguration_injective (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    Function.Injective (k4CliqueToChargeConfiguration G order) := by
  intro K L hKL
  apply Subtype.ext
  have hdata := congrArg Subtype.val hKL
  have hv : k4EarliestVertex G order K = k4EarliestVertex G order L :=
    congrArg Sigma.fst hdata
  have hT : K.1.erase (k4EarliestVertex G order K) =
      L.1.erase (k4EarliestVertex G order L) := congrArg Sigma.snd hdata
  calc
    K.1 = insert (k4EarliestVertex G order K)
        (K.1.erase (k4EarliestVertex G order K)) :=
      (Finset.insert_erase (k4EarliestVertex_mem G order K)).symm
    _ = insert (k4EarliestVertex G order L)
        (L.1.erase (k4EarliestVertex G order L)) := congrArg₂ insert hv hT
    _ = L.1 := Finset.insert_erase (k4EarliestVertex_mem G order L)

/-- Every four-clique is charged exactly once (only the inequality is needed
downstream). -/
theorem cliqueCount_four_le_k4Charge (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    (G.cliqueFinset 4).card ≤ k4Charge G order := by
  classical
  calc
    (G.cliqueFinset 4).card ≤ (k4ChargeConfigurations G order).card := by
      rw [← Fintype.card_coe, ← Fintype.card_coe]
      exact Fintype.card_le_of_injective
        (k4CliqueToChargeConfiguration G order)
        (k4CliqueToChargeConfiguration_injective G order)
    _ = k4Charge G order := k4ChargeConfigurations_card G order

/-- Labelled four-cliques are bounded by `24` times the earliest-vertex
charge. -/
theorem labelledCopies_k4_le_24_mul_charge (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    labelledCopies G K4Graph ≤ 24 * k4Charge G order := by
  exact (labelledCopies_k4_le_24_mul_cliqueCount G).trans
    (Nat.mul_le_mul_left 24 (cliqueCount_four_le_k4Charge G order))

/-- A good host supplies an actual degeneracy order for every queried
subgraph within the edge budget. -/
theorem HostGood.subgraphIsDegenerate
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) : IsDegenerate F D :=
  (HostGood.subgraphHereditarilyLowDegree hD h hFG hE).isDegenerate

/-- Fully labelled `K₄` bound obtained from the host certificate, with no
order remaining as a premise. -/
theorem HostGood.subgraphLabelledK4_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    labelledCopies F K4Graph ≤ (24 * (D * D)) * edgeCount F := by
  classical
  obtain ⟨order, horder⟩ := HostGood.subgraphIsDegenerate hD h hFG hE
  calc
    labelledCopies F K4Graph ≤ 24 * k4Charge F order :=
      labelledCopies_k4_le_24_mul_charge F order
    _ ≤ 24 * ((D * D) * edgeCount F) :=
      Nat.mul_le_mul_left 24 (k4Charge_le_of_degeneracyOrder horder)
    _ = (24 * (D * D)) * edgeCount F := by ring

/-- Paper-scale labelled `K₄` estimate: the constant depends on the
small-set density parameter `L`, not on the ambient host size or `D`. -/
theorem HostGood.subgraphLabelledK4_sharp_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    labelledCopies F K4Graph ≤
      (24 * (2 * L * L)) * edgeCount F := by
  classical
  obtain ⟨order, horder⟩ := HostGood.subgraphIsDegenerate hD h hFG hE
  have hsmall : RandomBoard.SmallSetCertificate F D L :=
    HostGood.subgraphSmallSetCertificate h hFG
  calc
    labelledCopies F K4Graph ≤ 24 * k4Charge F order :=
      labelledCopies_k4_le_24_mul_charge F order
    _ ≤ 24 * ((2 * L * L) * edgeCount F) :=
      Nat.mul_le_mul_left 24
        (SmallSetCertificate.k4Charge_le hsmall order horder)
    _ = (24 * (2 * L * L)) * edgeCount F := by ring

end K4SharpBridge

section K4IncidenceSharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance incidenceAdjDecidable (G : SimpleGraph V) :
    DecidableRel G.Adj := Classical.decRel _

/-- A triangle together with one common neighbor. -/
noncomputable def commonTriangleConfigurations (G : SimpleGraph V) :
    Finset (Σ _T : Finset V, V) := by
  classical
  exact (G.cliqueFinset 3).sigma fun T => commonNeighborsFinset G T

theorem commonTriangleConfigurations_card (G : SimpleGraph V) :
    (commonTriangleConfigurations G).card = commonTriangleIncidences G := by
  classical
  simp [commonTriangleConfigurations, commonTriangleIncidences, codegree,
    Finset.card_sigma]

abbrev RootedFourClique (G : SimpleGraph V) :=
  Σ K : ↑(G.cliqueFinset 4), ↑K.1

noncomputable def commonTriangleToRootedFourClique (G : SimpleGraph V)
    (q : ↑(commonTriangleConfigurations G)) : RootedFourClique G := by
  classical
  let T : Finset V := q.1.1
  let x : V := q.1.2
  have hq := q.2
  have hT : T ∈ G.cliqueFinset 3 := by
    simpa [commonTriangleConfigurations, T, x] using (Finset.mem_sigma.mp hq).1
  have hxCommon : x ∈ commonNeighborsFinset G T := by
    simpa [commonTriangleConfigurations, T, x] using (Finset.mem_sigma.mp hq).2
  have hxAdj : ∀ v ∈ T, G.Adj v x :=
    (mem_commonNeighborsFinset G T x).mp hxCommon
  have hxT : x ∉ T := by
    intro hx
    exact G.irrefl (hxAdj x hx)
  have hTclique := SimpleGraph.mem_cliqueFinset_iff.mp hT
  have hK : insert x T ∈ G.cliqueFinset 4 := by
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    refine ⟨?_, by simp [Finset.card_insert_of_notMem hxT, hTclique.card_eq]⟩
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha <;>
      rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (hab rfl).elim
    · exact (hxAdj b hb).symm
    · exact hxAdj a ha
    · exact hTclique.isClique ha hb hab
  exact ⟨⟨insert x T, hK⟩, ⟨x, Finset.mem_insert_self x T⟩⟩

theorem commonTriangleToRootedFourClique_injective (G : SimpleGraph V) :
    Function.Injective (commonTriangleToRootedFourClique G) := by
  intro q r hqr
  apply Subtype.ext
  have hdata := congrArg
    (fun z : RootedFourClique G => (z.1.1, (z.2 : V))) hqr
  have hK : insert q.1.2 q.1.1 = insert r.1.2 r.1.1 := congrArg Prod.fst hdata
  have hx : q.1.2 = r.1.2 := congrArg Prod.snd hdata
  have hqmem := (Finset.mem_sigma.mp q.2).2
  have hrmem := (Finset.mem_sigma.mp r.2).2
  have hqx : q.1.2 ∉ q.1.1 := by
    intro hm
    exact (SimpleGraph.loopless G q.1.2)
      ((mem_commonNeighborsFinset G q.1.1 q.1.2).mp hqmem q.1.2 hm)
  have hrx : r.1.2 ∉ r.1.1 := by
    intro hm
    exact (SimpleGraph.loopless G r.1.2)
      ((mem_commonNeighborsFinset G r.1.1 r.1.2).mp hrmem r.1.2 hm)
  have hT : q.1.1 = r.1.1 := by
    calc
      q.1.1 = (insert q.1.2 q.1.1).erase q.1.2 := by simp [hqx]
      _ = (insert r.1.2 r.1.1).erase q.1.2 :=
        congrArg (fun S : Finset V => S.erase q.1.2) hK
      _ = r.1.1 := by rw [hx]; simp [hrx]
  apply Sigma.ext hT
  exact heq_of_eq hx

theorem card_rootedFourClique (G : SimpleGraph V) :
    Fintype.card (RootedFourClique G) = 4 * (G.cliqueFinset 4).card := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ K : ↑(G.cliqueFinset 4), Fintype.card ↑K.1) =
        ∑ _K : ↑(G.cliqueFinset 4), 4 := by
      apply Finset.sum_congr rfl
      intro K _hK
      simpa using (SimpleGraph.mem_cliqueFinset_iff.mp K.2).card_eq
    _ = 4 * (G.cliqueFinset 4).card := by simp [Nat.mul_comm]

/-- Every four-clique supports exactly four triangle/common-neighbor roots;
the inequality form avoids quotienting by label conventions. -/
theorem commonTriangleIncidences_le_four_mul_cliqueCount (G : SimpleGraph V) :
    commonTriangleIncidences G ≤ 4 * (G.cliqueFinset 4).card := by
  classical
  rw [← commonTriangleConfigurations_card G, ← Fintype.card_coe,
    ← card_rootedFourClique G]
  exact Fintype.card_le_of_injective (commonTriangleToRootedFourClique G)
    (commonTriangleToRootedFourClique_injective G)

/-- Triple codegrees plus the sharp `K₄` charge give the paper-scale
`K₅-e` charge bound. -/
theorem k5MinusEdgeCharge_le_k4Charge (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) {c₃ : ℕ}
    (h₃ : TripleCodegreeLE G c₃) :
    k5MinusEdgeCharge G ≤ (4 * c₃) * k4Charge G order := by
  calc
    k5MinusEdgeCharge G ≤ c₃ * commonTriangleIncidences G :=
      k5MinusEdgeCharge_le G h₃
    _ ≤ c₃ * (4 * (G.cliqueFinset 4).card) :=
      Nat.mul_le_mul_left c₃ (commonTriangleIncidences_le_four_mul_cliqueCount G)
    _ ≤ c₃ * (4 * k4Charge G order) :=
      Nat.mul_le_mul_left c₃
        (Nat.mul_le_mul_left 4 (cliqueCount_four_le_k4Charge G order))
    _ = (4 * c₃) * k4Charge G order := by ring

/-- Fully labelled, paper-scale `K₅-e` estimate on every queried subgraph. -/
theorem HostGood.subgraphLabelledK5MinusEdge_sharp_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    labelledCopies F K5MinusEdgeGraph ≤
      (24 * c₃ * (2 * L * L)) * edgeCount F := by
  classical
  obtain ⟨order, horder⟩ := HostGood.subgraphIsDegenerate hD h hFG hE
  have hsmall : RandomBoard.SmallSetCertificate F D L :=
    HostGood.subgraphSmallSetCertificate h hFG
  have htriple : TripleCodegreeLE F c₃ :=
    HostGood.subgraphTripleCodegreeLE h hFG
  calc
    labelledCopies F K5MinusEdgeGraph ≤ 6 * k5MinusEdgeCharge F :=
      labelledCopies_K5MinusEdge_le_six_mul_charge F
    _ ≤ 6 * ((4 * c₃) * k4Charge F order) :=
      Nat.mul_le_mul_left 6 (k5MinusEdgeCharge_le_k4Charge F order htriple)
    _ ≤ 6 * ((4 * c₃) * ((2 * L * L) * edgeCount F)) :=
      Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left (4 * c₃)
        (SmallSetCertificate.k4Charge_le hsmall order horder))
    _ = (24 * c₃ * (2 * L * L)) * edgeCount F := by ring

end K4IncidenceSharpness

end OnlineRamsey
