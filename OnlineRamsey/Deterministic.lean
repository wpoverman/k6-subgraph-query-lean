import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring

/-!
# Deterministic graph-counting infrastructure for the `K_6` query proof

This file isolates the deterministic part of the proof from probability and
adaptivity.  It uses `SimpleGraph.labelledCopyCount` for the actual notion of
an injective, non-induced labelled copy and introduces explicit finite sums for
the charging arguments used for `K₄`, `H₃`, `K₅ - e`, and `Q`.

The exact labelled/unlabelled bridge constructions remain explicit obligations
listed in `DeterministicStatus.md`.  Every exported theorem in this file has a
proof term, and the file contains no proof placeholders or declarations
extending the trusted base.
-/

open scoped BigOperators

namespace OnlineRamsey

section FiniteGraphBasics

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-! ## Labelled, non-induced copies -/

/-- The number of injective graph homomorphisms from `H` to `G`. -/
noncomputable abbrev labelledCopies (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  G.labelledCopyCount H

/-! ## Finite neighborhoods and codegrees -/

/-- A finite version of the neighborhood, with all instances chosen locally. -/
noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

@[simp] theorem mem_neighbors (G : SimpleGraph V) (v w : V) :
    w ∈ neighbors G v ↔ G.Adj v w := by
  classical
  simp [neighbors]

/-- Degree, expressed using `neighbors` so that it can be used uniformly below. -/
noncomputable def degree (G : SimpleGraph V) (v : V) : ℕ :=
  (neighbors G v).card

/-- The common neighbors of every vertex in the finite set `S`. -/
noncomputable def commonNeighborsFinset (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => ∀ v ∈ S, G.Adj v x

@[simp] theorem mem_commonNeighborsFinset (G : SimpleGraph V) (S : Finset V) (x : V) :
    x ∈ commonNeighborsFinset G S ↔ ∀ v ∈ S, G.Adj v x := by
  classical
  simp [commonNeighborsFinset]

/-- The codegree of a finite set of vertices. -/
noncomputable def codegree (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (commonNeighborsFinset G S).card

/-- A uniform `j`-codegree bound. -/
def CodegreeLE (G : SimpleGraph V) (j D : ℕ) : Prop :=
  ∀ S : Finset V, S.card = j → codegree G S ≤ D

abbrev PairCodegreeLE (G : SimpleGraph V) (D : ℕ) : Prop := CodegreeLE G 2 D
abbrev TripleCodegreeLE (G : SimpleGraph V) (D : ℕ) : Prop := CodegreeLE G 3 D

theorem neighbors_mono {F G : SimpleGraph V} (hFG : F ≤ G) (v : V) :
    neighbors F v ⊆ neighbors G v := by
  classical
  intro x hx
  rw [mem_neighbors] at hx ⊢
  exact hFG hx

theorem degree_mono {F G : SimpleGraph V} (hFG : F ≤ G) (v : V) :
    degree F v ≤ degree G v := by
  exact Finset.card_le_card (neighbors_mono hFG v)

theorem commonNeighborsFinset_mono {F G : SimpleGraph V} (hFG : F ≤ G)
    (S : Finset V) :
    commonNeighborsFinset F S ⊆ commonNeighborsFinset G S := by
  classical
  intro x hx
  rw [mem_commonNeighborsFinset] at hx ⊢
  intro v hv
  exact hFG (hx v hv)

theorem codegree_mono {F G : SimpleGraph V} (hFG : F ≤ G) (S : Finset V) :
    codegree F S ≤ codegree G S := by
  exact Finset.card_le_card (commonNeighborsFinset_mono hFG S)

theorem CodegreeLE.anti {F G : SimpleGraph V} {j D : ℕ}
    (hFG : F ≤ G) (hG : CodegreeLE G j D) : CodegreeLE F j D := by
  intro S hS
  exact (codegree_mono hFG S).trans (hG S hS)

/-! ## Links -/

/--
The link of `v`, kept on the same ambient vertex type.  Vertices outside
`N_G(v)` are isolated.  This avoids repeated subtype transports later.
-/
def linkGraph (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ G.Adj v x ∧ G.Adj v y
  symm := by
    intro x y h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    intro x h
    exact G.irrefl h.1

@[simp] theorem linkGraph_adj (G : SimpleGraph V) (v x y : V) :
    (linkGraph G v).Adj x y ↔ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y := Iff.rfl

theorem linkGraph_le (G : SimpleGraph V) (v : V) : linkGraph G v ≤ G := by
  intro x y hxy
  exact hxy.1

theorem linkGraph_mono {F G : SimpleGraph V} (hFG : F ≤ G) (v : V) :
    linkGraph F v ≤ linkGraph G v := by
  intro x y hxy
  exact ⟨hFG hxy.1, hFG hxy.2.1, hFG hxy.2.2⟩

theorem neighbors_link_subset_common (G : SimpleGraph V) (v x : V) :
    neighbors (linkGraph G v) x ⊆ commonNeighborsFinset G {v, x} := by
  classical
  intro y hy
  have hy' := (mem_neighbors (linkGraph G v) x y).mp hy
  rw [mem_commonNeighborsFinset]
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hy'.2.2
  · exact hy'.1

theorem degree_link_le_codegree (G : SimpleGraph V) (v x : V) :
    degree (linkGraph G v) x ≤ codegree G {v, x} := by
  exact Finset.card_le_card (neighbors_link_subset_common G v x)

/-- A maximum-degree bound stated without introducing a `max` operator. -/
def MaxDegreeLE (G : SimpleGraph V) (D : ℕ) : Prop := ∀ v, degree G v ≤ D

theorem pairCodegree_bounds_link_degree (G : SimpleGraph V) {D : ℕ}
    (h₂ : PairCodegreeLE G D) (v : V) : MaxDegreeLE (linkGraph G v) D := by
  classical
  intro x
  by_cases hx : x = v
  · subst x
    simp [degree, neighbors, linkGraph]
  · have hvx : v ≠ x := Ne.symm hx
    exact (degree_link_le_codegree G v x).trans (h₂ {v, x} (by simp [hvx]))

/-! ## Edge and triangle counts -/

noncomputable def edgeCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

noncomputable def triangleCount (G : SimpleGraph V) : ℕ := by
  classical
  exact (G.cliqueFinset 3).card

/-- The triangles all of whose vertices lie in `S`. -/
noncomputable def trianglesIn (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact ((G.cliqueFinset 3).filter fun T => T ⊆ S).card

theorem edgeCount_mono {F G : SimpleGraph V} (hFG : F ≤ G) :
    edgeCount F ≤ edgeCount G := by
  classical
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hFG)

theorem triangleCount_mono {F G : SimpleGraph V} (hFG : F ≤ G) :
    triangleCount F ≤ triangleCount G := by
  classical
  exact Finset.card_le_card (SimpleGraph.cliqueFinset_mono G hFG)

theorem trianglesIn_le_triangleCount (G : SimpleGraph V) (S : Finset V) :
    trianglesIn G S ≤ triangleCount G := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem trianglesIn_mono (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) :
    trianglesIn G S ≤ trianglesIn G T := by
  classical
  apply Finset.card_le_card
  intro K hK
  simp only [trianglesIn, Finset.mem_filter] at hK ⊢
  exact ⟨hK.1, hK.2.trans hST⟩

theorem sum_degrees_eq_twice_edgeCount (G : SimpleGraph V) :
    (∑ v : V, degree G v) = 2 * edgeCount G := by
  classical
  simpa [degree, neighbors, SimpleGraph.degree,
    SimpleGraph.neighborFinset_eq_filter, edgeCount] using
      G.sum_degrees_eq_twice_card_edges

theorem edgeCount_link_le (G : SimpleGraph V) (v : V) :
    edgeCount (linkGraph G v) ≤ edgeCount G :=
  edgeCount_mono (linkGraph_le G v)

end FiniteGraphBasics

section Degeneracy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Later neighbors of a vertex in a fixed total ordering. -/
noncomputable def forwardNeighbors (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (v : V) : Finset V := by
  classical
  exact (neighbors G v).filter fun w => order v < order w

@[simp] theorem mem_forwardNeighbors (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (v w : V) :
    w ∈ forwardNeighbors G order v ↔ G.Adj v w ∧ order v < order w := by
  classical
  simp [forwardNeighbors]

/-- A concrete degeneracy ordering. -/
def IsDegeneracyOrder (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (D : ℕ) : Prop :=
  ∀ v, (forwardNeighbors G order v).card ≤ D

def IsDegenerate (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∃ order : V ≃ Fin (Fintype.card V), IsDegeneracyOrder G order D

theorem forwardNeighbors_mono {F G : SimpleGraph V} (hFG : F ≤ G)
    (order : V ≃ Fin (Fintype.card V)) (v : V) :
    forwardNeighbors F order v ⊆ forwardNeighbors G order v := by
  classical
  intro w hw
  rw [mem_forwardNeighbors] at hw ⊢
  exact ⟨hFG hw.1, hw.2⟩

theorem IsDegeneracyOrder.anti {F G : SimpleGraph V}
    {order : V ≃ Fin (Fintype.card V)} {D : ℕ}
    (hFG : F ≤ G) (hG : IsDegeneracyOrder G order D) :
    IsDegeneracyOrder F order D := by
  intro v
  exact (Finset.card_le_card (forwardNeighbors_mono hFG order v)).trans (hG v)

theorem IsDegenerate.anti {F G : SimpleGraph V} {D : ℕ}
    (hFG : F ≤ G) (hG : IsDegenerate G D) : IsDegenerate F D := by
  rcases hG with ⟨order, horder⟩
  exact ⟨order, IsDegeneracyOrder.anti hFG horder⟩

theorem IsDegenerate.link {G : SimpleGraph V} {D : ℕ}
    (hG : IsDegenerate G D) (v : V) : IsDegenerate (linkGraph G v) D :=
  IsDegenerate.anti (linkGraph_le G v) hG

/-- Hereditary low degree, the deletion formulation of degeneracy. -/
def HereditarilyLowDegree (G : SimpleGraph V) (D : ℕ) : Prop :=
  ∀ U : Finset V, U.Nonempty →
    ∃ v ∈ U, (U ∩ neighbors G v).card ≤ D

/-- A degeneracy ordering supplies a low-degree vertex in every induced subgraph. -/
theorem IsDegeneracyOrder.hereditarilyLowDegree {G : SimpleGraph V}
    {order : V ≃ Fin (Fintype.card V)} {D : ℕ}
    (horder : IsDegeneracyOrder G order D) : HereditarilyLowDegree G D := by
  classical
  intro U hU
  obtain ⟨v, hvU, hvmin⟩ := U.exists_min_image order hU
  refine ⟨v, hvU, (Finset.card_le_card ?_).trans (horder v)⟩
  intro w hw
  simp only [Finset.mem_inter] at hw
  have hadj : G.Adj v w := (mem_neighbors G v w).mp hw.2
  rw [mem_forwardNeighbors]
  have hne : order v ≠ order w := fun hvw => hadj.ne (order.injective hvw)
  exact ⟨hadj, lt_of_le_of_ne (hvmin w hw.1) hne⟩

theorem IsDegenerate.hereditarilyLowDegree {G : SimpleGraph V} {D : ℕ}
    (hG : IsDegenerate G D) : HereditarilyLowDegree G D := by
  rcases hG with ⟨order, horder⟩
  exact IsDegeneracyOrder.hereditarilyLowDegree horder

theorem HereditarilyLowDegree.anti {F G : SimpleGraph V} {D : ℕ}
    (hFG : F ≤ G) (hG : HereditarilyLowDegree G D) :
    HereditarilyLowDegree F D := by
  classical
  intro U hU
  rcases hG U hU with ⟨v, hvU, hv⟩
  refine ⟨v, hvU, ?_⟩
  refine (Finset.card_le_card ?_).trans hv
  intro w hw
  simp only [Finset.mem_inter] at hw ⊢
  exact ⟨hw.1, neighbors_mono hFG v hw.2⟩

end Degeneracy

section ChargingSums

variable {ι V : Type*} [Fintype V] [DecidableEq V]

/-! ## Reusable arithmetic behind the extension bounds -/

theorem sum_sq_le_mul_sum (s : Finset ι) (r : ι → ℕ) (D : ℕ)
    (hr : ∀ i ∈ s, r i ≤ D) :
    (∑ i ∈ s, r i * r i) ≤ D * ∑ i ∈ s, r i := by
  calc
    (∑ i ∈ s, r i * r i) ≤ ∑ i ∈ s, D * r i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_right (r i) (hr i hi)
    _ = D * ∑ i ∈ s, r i := by rw [Finset.mul_sum]

theorem weighted_sum_sq_le (s : Finset ι) (w r : ι → ℕ) (D : ℕ)
    (hr : ∀ i ∈ s, r i ≤ D) :
    (∑ i ∈ s, w i * (r i * r i)) ≤ (D * D) * ∑ i ∈ s, w i := by
  calc
    (∑ i ∈ s, w i * (r i * r i)) ≤ ∑ i ∈ s, (D * D) * w i := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        w i * (r i * r i) ≤ w i * (D * D) := by
          exact Nat.mul_le_mul_left (w i) (Nat.mul_le_mul (hr i hi) (hr i hi))
        _ = (D * D) * w i := by ac_rfl
    _ = (D * D) * ∑ i ∈ s, w i := by rw [Finset.mul_sum]

/-! ## The `K₄` charge -/

/-- The total number of triangles in the forward neighborhoods of an order. -/
noncomputable def k4Charge (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) : ℕ :=
  ∑ v : V, trianglesIn G (forwardNeighbors G order v)

noncomputable def orientedEdgeMass (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) : ℕ :=
  ∑ v : V, (forwardNeighbors G order v).card

def LocalTriangleLinear (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (L : ℕ) : Prop :=
  ∀ v, trianglesIn G (forwardNeighbors G order v) ≤
    L * (forwardNeighbors G order v).card

theorem k4Charge_le_orientedEdgeMass (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) {L : ℕ}
    (hlocal : LocalTriangleLinear G order L) :
    k4Charge G order ≤ L * orientedEdgeMass G order := by
  classical
  unfold k4Charge orientedEdgeMass
  calc
    (∑ v : V, trianglesIn G (forwardNeighbors G order v)) ≤
        ∑ v : V, L * (forwardNeighbors G order v).card := by
      apply Finset.sum_le_sum
      intro v hv
      exact hlocal v
    _ = L * ∑ v : V, (forwardNeighbors G order v).card := by
      rw [Finset.mul_sum]

theorem k4Charge_le_edges (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) {L : ℕ}
    (hlocal : LocalTriangleLinear G order L)
    (haccount : orientedEdgeMass G order ≤ edgeCount G) :
    k4Charge G order ≤ L * edgeCount G := by
  exact (k4Charge_le_orientedEdgeMass G order hlocal).trans
    (Nat.mul_le_mul_left L haccount)

/-! ## Paw and `H₃` charges -/

/--
For each triangle, choose one of its three vertices and then one of that
vertex's neighbors.  This is the exact extension sum used to dominate paws.
-/
noncomputable def pawExtensionMass (G : SimpleGraph V) : ℕ := by
  classical
  exact ∑ T ∈ G.cliqueFinset 3, ∑ v ∈ T, degree G v

theorem pawExtensionMass_le (G : SimpleGraph V) {D : ℕ}
    (hD : MaxDegreeLE G D) :
    pawExtensionMass G ≤ (3 * D) * triangleCount G := by
  classical
  unfold pawExtensionMass triangleCount
  calc
    (∑ T ∈ G.cliqueFinset 3, ∑ v ∈ T, degree G v) ≤
        ∑ T ∈ G.cliqueFinset 3, 3 * D := by
      apply Finset.sum_le_sum
      intro T hT
      have hcard : T.card = 3 :=
        (SimpleGraph.mem_cliqueFinset_iff.mp hT).card_eq
      calc
        (∑ v ∈ T, degree G v) ≤ ∑ _v ∈ T, D := by
          apply Finset.sum_le_sum
          intro v hv
          exact hD v
        _ = T.card * D := by simp
        _ = 3 * D := by rw [hcard]
    _ = (3 * D) * (G.cliqueFinset 3).card := by
      simp [Nat.mul_comm]

/-- The degree-weighted paw extension sum arising after rooting `H₃` at `a₁`. -/
noncomputable def h3Charge (G : SimpleGraph V) : ℕ :=
  ∑ v : V, degree G v * pawExtensionMass (linkGraph G v)

def LinkTriangleLinear (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∀ v, triangleCount (linkGraph G v) ≤ L * edgeCount (linkGraph G v)

theorem h3Charge_le (G : SimpleGraph V) {D L M : ℕ}
    (h₂ : PairCodegreeLE G D)
    (htri : LinkTriangleLinear G L)
    (hE : edgeCount G ≤ M) :
    h3Charge G ≤ (6 * D * L * M) * edgeCount G := by
  classical
  have hpaw : ∀ v : V, pawExtensionMass (linkGraph G v) ≤ 3 * D * L * M := by
    intro v
    calc
      pawExtensionMass (linkGraph G v) ≤
          (3 * D) * triangleCount (linkGraph G v) :=
        pawExtensionMass_le (linkGraph G v) (pairCodegree_bounds_link_degree G h₂ v)
      _ ≤ (3 * D) * (L * edgeCount (linkGraph G v)) :=
        Nat.mul_le_mul_left _ (htri v)
      _ ≤ (3 * D) * (L * edgeCount G) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left L (edgeCount_link_le G v))
      _ ≤ (3 * D) * (L * M) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left L hE)
      _ = 3 * D * L * M := by ring
  unfold h3Charge
  calc
    (∑ v : V, degree G v * pawExtensionMass (linkGraph G v)) ≤
        ∑ v : V, degree G v * (3 * D * L * M) := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.mul_le_mul_left _ (hpaw v)
    _ = ∑ v : V, (3 * D * L * M) * degree G v := by
      apply Finset.sum_congr rfl
      intro v hv
      ac_rfl
    _ = (3 * D * L * M) * ∑ v : V, degree G v := by
      rw [Finset.mul_sum]
    _ = (3 * D * L * M) * (2 * edgeCount G) := by
      rw [sum_degrees_eq_twice_edgeCount]
    _ = (6 * D * L * M) * edgeCount G := by ring

/-! ## `K₅ - e` charge -/

/-- Sum, over triangles, of the number of ordered pairs of common extensions. -/
noncomputable def k5MinusEdgeCharge (G : SimpleGraph V) : ℕ := by
  classical
  exact ∑ T ∈ G.cliqueFinset 3, codegree G T * codegree G T

noncomputable def commonTriangleIncidences (G : SimpleGraph V) : ℕ := by
  classical
  exact ∑ T ∈ G.cliqueFinset 3, codegree G T

theorem k5MinusEdgeCharge_le (G : SimpleGraph V) {D : ℕ}
    (h₃ : TripleCodegreeLE G D) :
    k5MinusEdgeCharge G ≤ D * commonTriangleIncidences G := by
  classical
  unfold k5MinusEdgeCharge commonTriangleIncidences
  apply sum_sq_le_mul_sum
  intro T hT
  exact h₃ T (SimpleGraph.mem_cliqueFinset_iff.mp hT).card_eq

theorem k5MinusEdgeCharge_le_edges (G : SimpleGraph V) {D C : ℕ}
    (h₃ : TripleCodegreeLE G D)
    (hinc : commonTriangleIncidences G ≤ C * edgeCount G) :
    k5MinusEdgeCharge G ≤ (D * C) * edgeCount G := by
  calc
    k5MinusEdgeCharge G ≤ D * commonTriangleIncidences G :=
      k5MinusEdgeCharge_le G h₃
    _ ≤ D * (C * edgeCount G) := Nat.mul_le_mul_left D hinc
    _ = (D * C) * edgeCount G := by ring

/-! ## `Q = K₂ ∨ (K₂ ⊔ 2K₁)` charge -/

/-- Ordered adjacent pairs; each undirected edge occurs twice. -/
noncomputable def orderedEdges (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun e => G.Adj e.1 e.2

@[simp] theorem mem_orderedEdges (G : SimpleGraph V) (x y : V) :
    (x, y) ∈ orderedEdges G ↔ G.Adj x y := by
  classical
  simp [orderedEdges]

/-- Every undirected edge contributes its two orientations. -/
theorem card_orderedEdges (G : SimpleGraph V) :
    (orderedEdges G).card = 2 * edgeCount G := by
  classical
  simpa [orderedEdges, edgeCount] using G.two_mul_card_edgeFinset.symm

/-- Ordered edges of `G` lying completely inside `S`. -/
noncomputable def insideOrderedEdgeMass (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact ((S.product S).filter fun e => G.Adj e.1 e.2).card

/-- The common-neighborhood edge sum appearing in the rooted `K₄` identity. -/
noncomputable def centralK4Mass (G : SimpleGraph V) : ℕ := by
  classical
  exact ∑ e ∈ orderedEdges G,
    insideOrderedEdgeMass G (commonNeighborsFinset G {e.1, e.2})

/-- The rooted `Q` extension sum before applying the pair-codegree bound. -/
noncomputable def qCharge (G : SimpleGraph V) : ℕ := by
  classical
  exact ∑ e ∈ orderedEdges G,
    insideOrderedEdgeMass G (commonNeighborsFinset G {e.1, e.2}) *
      (codegree G {e.1, e.2} * codegree G {e.1, e.2})


theorem qCharge_le (G : SimpleGraph V) {D : ℕ}
    (h₂ : PairCodegreeLE G D) :
    qCharge G ≤ (D * D) * centralK4Mass G := by
  classical
  unfold qCharge centralK4Mass
  apply weighted_sum_sq_le
  intro e he
  have hadj : G.Adj e.1 e.2 := by
    simpa [orderedEdges] using he
  exact h₂ {e.1, e.2} (by simp [hadj.ne, hadj.ne'])

theorem qCharge_le_edges (G : SimpleGraph V) {D C : ℕ}
    (h₂ : PairCodegreeLE G D)
    (hk4 : centralK4Mass G ≤ C * edgeCount G) :
    qCharge G ≤ (D * D * C) * edgeCount G := by
  calc
    qCharge G ≤ (D * D) * centralK4Mass G := qCharge_le G h₂
    _ ≤ (D * D) * (C * edgeCount G) := Nat.mul_le_mul_left _ hk4
    _ = (D * D * C) * edgeCount G := by ring

end ChargingSums

section FixedPatterns

/-! ## The fixed graphs from the paper -/

/-- `K₄`, on the canonical four-vertex type. -/
abbrev K4Graph : SimpleGraph (Fin 4) := ⊤

/-- The paw: a triangle with a pendant edge at vertex `0`. -/
def pawGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.edge 0 1 ⊔ SimpleGraph.edge 0 2 ⊔
  SimpleGraph.edge 1 2 ⊔ SimpleGraph.edge 0 3

/-- The six-vertex split half-graph `H₃`. -/
def H3Graph : SimpleGraph (Fin 6) :=
  SimpleGraph.edge 0 1 ⊔ SimpleGraph.edge 0 2 ⊔ SimpleGraph.edge 1 2 ⊔
  SimpleGraph.edge 0 3 ⊔ SimpleGraph.edge 0 4 ⊔ SimpleGraph.edge 0 5 ⊔
  SimpleGraph.edge 1 4 ⊔ SimpleGraph.edge 1 5 ⊔ SimpleGraph.edge 2 5

/-- `K₅` with the edge `{3,4}` removed. -/
def K5MinusEdgeGraph : SimpleGraph (Fin 5) :=
  (⊤ : SimpleGraph (Fin 5)) \ SimpleGraph.edge 3 4

/-- `Q = K₂ ∨ (K₂ ⊔ 2K₁)`, with central edge `{0,1}`. -/
def QGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.edge 0 1 ⊔
  SimpleGraph.edge 0 2 ⊔ SimpleGraph.edge 0 3 ⊔
  SimpleGraph.edge 0 4 ⊔ SimpleGraph.edge 0 5 ⊔
  SimpleGraph.edge 1 2 ⊔ SimpleGraph.edge 1 3 ⊔
  SimpleGraph.edge 1 4 ⊔ SimpleGraph.edge 1 5 ⊔
  SimpleGraph.edge 2 3

end FixedPatterns

/-!
The source-level exact-factor constructions developed during this pass are
kept below as a non-kernel-checked draft.  They are intentionally commented
out until their dependent finite-fiber encodings are repaired against the
Lean 4.24 elaborator.  No theorem from this block is exported.
-/
/-
section CentralK4Bridge

variable {V : Type*} [Fintype V]

/-- Read four entries of two ordered pairs as a function on `Fin 4`. -/
def fin4TupleFun (a b c d : V) : Fin 4 → V :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d Fin.elim0)))

@[simp] theorem fin4TupleFun_zero (a b c d : V) : fin4TupleFun a b c d 0 = a := rfl
@[simp] theorem fin4TupleFun_one (a b c d : V) : fin4TupleFun a b c d 1 = b := rfl
@[simp] theorem fin4TupleFun_two (a b c d : V) : fin4TupleFun a b c d 2 = c := rfl
@[simp] theorem fin4TupleFun_three (a b c d : V) : fin4TupleFun a b c d 3 = d := rfl

/-- A central-edge tuple determines a labelled four-clique. -/
noncomputable def centralK4TupleToCopy (G : SimpleGraph V)
    (p : ↑(centralK4Tuples G)) : K4Graph.Copy G := by
  classical
  rcases p with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hp⟩
  have hp' := (mem_centralK4Tuples G a b c d).mp hp
  have hab : G.Adj a b := hp'.1
  have hcd : G.Adj c d := hp'.2.1
  have hc := (mem_commonNeighborsFinset G {a, b} c).mp hp'.2.2.1
  have hd := (mem_commonNeighborsFinset G {a, b} d).mp hp'.2.2.2
  have hac : G.Adj a c := hc a (by simp)
  have hbc : G.Adj b c := hc b (by simp)
  have had : G.Adj a d := hd a (by simp)
  have hbd : G.Adj b d := hd b (by simp)
  have hba := hab.symm
  have hdc := hcd.symm
  have hca := hac.symm
  have hcb := hbc.symm
  have hda := had.symm
  have hdb := hbd.symm
  let hom : K4Graph →g G :=
    { toFun := fin4TupleFun a b c d
      map_rel' := by
        intro i j hij
        have hij' : i ≠ j := (SimpleGraph.top_adj i j).mp hij
        fin_cases i <;> fin_cases j <;> simp_all [fin4TupleFun] }
  exact ⟨hom, SimpleGraph.Hom.injective_of_top_hom hom⟩

/-- A labelled four-clique determines its two ordered edge pairs. -/
noncomputable def centralK4CopyToTuple (G : SimpleGraph V)
    (f : K4Graph.Copy G) : ↑(centralK4Tuples G) := by
  classical
  have hadj (i j : Fin 4) (hij : i ≠ j) : G.Adj (f i) (f j) :=
    f.toHom.map_adj ((SimpleGraph.top_adj i j).mpr hij)
  refine ⟨((f 0, f 1), (f 2, f 3)), ?_⟩
  apply (mem_centralK4Tuples G (f 0) (f 1) (f 2) (f 3)).mpr
  refine ⟨hadj 0 1 (by decide), hadj 2 3 (by decide), ?_, ?_⟩
  · apply (mem_commonNeighborsFinset G {f 0, f 1} (f 2)).mpr
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hadj 0 2 (by decide)
    · exact hadj 1 2 (by decide)
  · apply (mem_commonNeighborsFinset G {f 0, f 1} (f 3)).mpr
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hadj 0 3 (by decide)
    · exact hadj 1 3 (by decide)

/-- Central-edge tuples and labelled four-cliques are canonically equivalent. -/
noncomputable def centralK4TupleEquivCopy (G : SimpleGraph V) :
    ↑(centralK4Tuples G) ≃ K4Graph.Copy G where
  toFun := centralK4TupleToCopy G
  invFun := centralK4CopyToTuple G
  left_inv := by
    rintro ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, hp⟩
    apply Subtype.ext
    rfl
  right_inv := by
    intro f
    apply SimpleGraph.Copy.ext
    intro i
    fin_cases i <;> rfl

end CentralK4Bridge

section K4LabelledBridge

variable {V : Type*} [Fintype V]

/-! ## The exact labelled factor for `K₄` -/

/-- The image of the four labels of a labelled `K₄` copy. -/
noncomputable def k4CopyVertices (G : SimpleGraph V)
    (f : K4Graph.Copy G) : Finset V := by
  classical
  exact Finset.univ.map f.toEmbedding

theorem k4CopyVertices_mem_cliqueFinset (G : SimpleGraph V)
    (f : K4Graph.Copy G) : k4CopyVertices G f ∈ G.cliqueFinset 4 := by
  classical
  apply SimpleGraph.mem_cliqueFinset_iff.mpr
  simpa [K4Graph, k4CopyVertices] using
    (SimpleGraph.isNClique_map_copy_top (G := G) f)

/--
Once its four-element image `K` is fixed, a labelled `K₄` copy is the same
thing as an embedding of the four labels into the subtype `K`.  Since both
types have four elements, these embeddings are precisely the `4!` labellings.
-/
noncomputable def k4CopyFiberEquiv (G : SimpleGraph V) (K : Finset V)
    (hK : K ∈ G.cliqueFinset 4) :
    {f : K4Graph.Copy G // k4CopyVertices G f = K} ≃ (Fin 4 ↪ ↑K) := by
  classical
  have hKClique : G.IsNClique 4 K :=
    SimpleGraph.mem_cliqueFinset_iff.mp hK
  let forward : {f : K4Graph.Copy G // k4CopyVertices G f = K} →
      (Fin 4 ↪ ↑K) := fun f =>
    { toFun := fun i => ⟨f.1 i, by
          have hi : f.1 i ∈ k4CopyVertices G f.1 := by
            simp [k4CopyVertices]
          rw [f.2] at hi
          exact hi⟩
      inj' := by
        intro i j hij
        apply f.1.injective
        exact congrArg Subtype.val hij }
  let backward : (Fin 4 ↪ ↑K) →
      {f : K4Graph.Copy G // k4CopyVertices G f = K} := fun e =>
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
        simp only [k4CopyVertices, Finset.mem_map] at hx
        obtain ⟨i, _hi, rfl⟩ := hx
        exact (e i).property
      · simpa [k4CopyVertices] using hKClique.card_eq.le⟩
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

/-- Every unlabelled four-clique has exactly `4! = 24` labelled copies. -/
theorem card_k4CopyFiber (G : SimpleGraph V) (K : Finset V)
    (hK : K ∈ G.cliqueFinset 4) :
    ((Finset.univ : Finset (K4Graph.Copy G)).filter fun f =>
      k4CopyVertices G f = K).card = 24 := by
  classical
  have hfilter :
      Fintype.card {f : K4Graph.Copy G // k4CopyVertices G f = K} =
        ((Finset.univ : Finset (K4Graph.Copy G)).filter fun f =>
          k4CopyVertices G f = K).card := by
    apply Fintype.card_of_subtype
    simp
  rw [← hfilter, Fintype.card_congr (k4CopyFiberEquiv G K hK),
    Fintype.card_embedding_eq]
  have hcardK : Fintype.card ↑K = 4 := by
    simpa using (SimpleGraph.mem_cliqueFinset_iff.mp hK).card_eq
  rw [hcardK, Fintype.card_fin, Nat.descFactorial_self]
  decide

/-- The labelled `K₄` count is `24` times the unlabelled clique-set count. -/
theorem labelledCopies_k4_eq_24_mul_cliqueFinsetCard (G : SimpleGraph V) :
    labelledCopies G K4Graph = 24 * (G.cliqueFinset 4).card := by
  classical
  change Fintype.card (K4Graph.Copy G) = 24 * (G.cliqueFinset 4).card
  rw [← Finset.card_univ]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := k4CopyVertices G) (t := G.cliqueFinset 4)
    (by intro f _hf; exact k4CopyVertices_mem_cliqueFinset G f)]
  calc
    (∑ K ∈ G.cliqueFinset 4,
        #{f ∈ (Finset.univ : Finset (K4Graph.Copy G)) |
          k4CopyVertices G f = K}) =
        ∑ _K ∈ G.cliqueFinset 4, 24 := by
      apply Finset.sum_congr rfl
      intro K hK
      exact card_k4CopyFiber G K hK
    _ = 24 * (G.cliqueFinset 4).card := by
      simp [Nat.mul_comm]

/-- The central-edge sum is literally the labelled `K₄` count. -/
theorem centralK4Mass_eq_labelledCopies_k4 (G : SimpleGraph V) :
    centralK4Mass G = labelledCopies G K4Graph := by
  classical
  calc
    centralK4Mass G = (centralK4Tuples G).card :=
      centralK4Mass_eq_card_tuples G
    _ = Fintype.card ↑(centralK4Tuples G) := by simp
    _ = Fintype.card (K4Graph.Copy G) :=
      Fintype.card_congr (centralK4TupleEquivCopy G)
    _ = labelledCopies G K4Graph := by
      rfl

/-- Equivalently, the central-edge sum is `24` per four-clique. -/
theorem centralK4Mass_eq_24_mul_k4SetCount (G : SimpleGraph V) :
    centralK4Mass G = 24 * (G.cliqueFinset 4).card :=
  (centralK4Mass_eq_labelledCopies_k4 G).trans
    (labelledCopies_k4_eq_24_mul_cliqueFinsetCard G)

/-- The labelled count is six times the triangle/common-neighbor incidence sum. -/
theorem labelledCopies_k4_eq_six_mul_commonTriangleIncidences
    (G : SimpleGraph V) :
    labelledCopies G K4Graph = 6 * commonTriangleIncidences G := by
  rw [labelledCopies_k4_eq_24_mul_cliqueFinsetCard,
    commonTriangleIncidences_eq_four_mul_k4SetCount]
  ring

/-- Earliest-vertex charging, including the exact labelled factor. -/
theorem labelledCopies_k4_eq_24_mul_charge (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    labelledCopies G K4Graph = 24 * k4Charge G order := by
  rw [k4Charge_eq_k4SetCount]
  exact labelledCopies_k4_eq_24_mul_cliqueFinsetCard G

end K4LabelledBridge

section PatternChargeBridges

variable {V : Type*} [Fintype V]

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
    (f : K5MinusEdgeGraph.Copy G) :
    k5TriangleVertices G f ∈ G.cliqueFinset 3 := by
  classical
  apply SimpleGraph.mem_cliqueFinset_iff.mpr
  simpa [k5TriangleVertices] using
    (SimpleGraph.isNClique_map_copy_top (G := G)
      (f.comp k5FirstThreeCopy))

noncomputable def k5CopyData (G : SimpleGraph V) (f : K5MinusEdgeGraph.Copy G) :
    Finset V × (V × V) :=
  (k5TriangleVertices G f, (f 3, f 4))

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

/-- Remembering the three triangle labels inside a fixed charge fiber. -/
noncomputable def k5FiberToEmbedding (G : SimpleGraph V)
    (q : ↑(k5MinusEdgeConfigurations G))
    (f : {f : K5MinusEdgeGraph.Copy G // k5CopyToConfiguration G f = q}) :
    Fin 3 ↪ ↑q.1.1 := by
  classical
  have hdata : k5CopyData G f.1 = q.1 := congrArg Subtype.val f.2
  have hT : k5TriangleVertices G f.1 = q.1.1 := congrArg Prod.fst hdata
  exact
    { toFun := fun i => ⟨(f.1.comp k5FirstThreeCopy) i, by
          have hi : (f.1.comp k5FirstThreeCopy) i ∈
              k5TriangleVertices G f.1 := by
            simp [k5TriangleVertices]
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
  apply SimpleGraph.Copy.ext
  intro i
  fin_cases i
  · simpa using hfirst 0
  · simpa using hfirst 1
  · simpa using hfirst 2
  · exact h3
  · exact h4

theorem card_k5CopyConfigurationFiber_le_six (G : SimpleGraph V)
    (q : ↑(k5MinusEdgeConfigurations G)) :
    ((Finset.univ : Finset (K5MinusEdgeGraph.Copy G)).filter fun f =>
      k5CopyToConfiguration G f = q).card ≤ 6 := by
  classical
  have hfilter :
      Fintype.card {f : K5MinusEdgeGraph.Copy G //
          k5CopyToConfiguration G f = q} =
        ((Finset.univ : Finset (K5MinusEdgeGraph.Copy G)).filter fun f =>
          k5CopyToConfiguration G f = q).card := by
    apply Fintype.card_of_subtype
    simp
  rw [← hfilter]
  calc
    Fintype.card {f : K5MinusEdgeGraph.Copy G //
        k5CopyToConfiguration G f = q} ≤ Fintype.card (Fin 3 ↪ ↑q.1.1) :=
      Fintype.card_le_of_injective (k5FiberToEmbedding G q)
        (k5FiberToEmbedding_injective G q)
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
  change Fintype.card (K5MinusEdgeGraph.Copy G) ≤ 6 * k5MinusEdgeCharge G
  rw [← Finset.card_univ]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := k5CopyToConfiguration G)
    (t := (Finset.univ : Finset ↑(k5MinusEdgeConfigurations G))) (by simp)]
  calc
    (∑ q : ↑(k5MinusEdgeConfigurations G),
        #{f ∈ (Finset.univ : Finset (K5MinusEdgeGraph.Copy G)) |
          k5CopyToConfiguration G f = q}) ≤
        ∑ _q : ↑(k5MinusEdgeConfigurations G), 6 := by
      apply Finset.sum_le_sum
      intro q _hq
      exact card_k5CopyConfigurationFiber_le_six G q
    _ = 6 * Fintype.card ↑(k5MinusEdgeConfigurations G) := by
      simp [Nat.mul_comm]
    _ = 6 * (k5MinusEdgeConfigurations G).card := by simp
    _ = 6 * k5MinusEdgeCharge G := by
      rw [k5MinusEdgeCharge_eq_card_configurations]

/-- The six images of a labelled `Q` copy, grouped as the `qCharge` data. -/
def qCopyData (G : SimpleGraph V) (f : QGraph.Copy G) :
    (V × V) × ((V × V) × (V × V)) :=
  ((f 0, f 1), ((f 2, f 3), (f 4, f 5)))

/-- Every labelled `Q` copy is one of the (more permissive) `qCharge` configurations. -/
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
  apply (mem_qConfigurations G (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)).mpr
  refine ⟨h01, ?_, ?_, ?_⟩
  · apply (mem_insideOrderedEdges G
      (commonNeighborsFinset G {f 0, f 1}) (f 2) (f 3)).mpr
    refine ⟨?_, ?_, h23⟩
    · apply (mem_commonNeighborsFinset G {f 0, f 1} (f 2)).mpr
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h02
      · exact h12
    · apply (mem_commonNeighborsFinset G {f 0, f 1} (f 3)).mpr
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h03
      · exact h13
  · apply (mem_commonNeighborsFinset G {f 0, f 1} (f 4)).mpr
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h04
    · exact h14
  · apply (mem_commonNeighborsFinset G {f 0, f 1} (f 5)).mpr
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h05
    · exact h15

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
    labelledCopies G QGraph = Fintype.card (QGraph.Copy G) := by rfl
    _ ≤ Fintype.card ↑(qConfigurations G) :=
      Fintype.card_le_of_injective (qCopyToConfiguration G)
        (qCopyToConfiguration_injective G)
    _ = (qConfigurations G).card := by simp
    _ = qCharge G := (qCharge_eq_card_configurations G).symm

end PatternChargeBridges

-/

end OnlineRamsey
