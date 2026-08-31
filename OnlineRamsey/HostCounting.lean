import OnlineRamsey.Deterministic
import OnlineRamsey.RandomBoard
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Deterministic consequences of a good random host

This module connects the certificate predicates in `RandomBoard` to the
finite graph-counting notions in `Deterministic`.  It deliberately states
finite, pointwise implications; no probability or asymptotic argument is used
here.
-/

open scoped BigOperators

namespace OnlineRamsey

section Bridges

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set-`ncard` codegree used by `RandomBoard` agrees with the explicit
finite common-neighbor finset used by `Deterministic`. -/
theorem commonNeighborCount_eq_codegree (G : SimpleGraph V) (S : Finset V) :
    RandomBoard.commonNeighborCount G S = codegree G S := by
  classical
  unfold RandomBoard.commonNeighborCount RandomBoard.commonNeighborSet codegree
    commonNeighborsFinset
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

theorem CodegreeAtMost.toCodegreeLE {G : SimpleGraph V} {j D : ℕ}
    (h : RandomBoard.CodegreeAtMost G j D) : CodegreeLE G j D := by
  intro S hS
  rw [← commonNeighborCount_eq_codegree]
  exact h S hS

/-- Spanned-edge counts are monotone in the graph. -/
theorem edgesSpanned_mono {F G : SimpleGraph V} (hFG : F ≤ G) (U : Finset V) :
    RandomBoard.edgesSpanned F U ≤ RandomBoard.edgesSpanned G U := by
  classical
  unfold RandomBoard.edgesSpanned
  apply Set.ncard_mono
  intro e he
  exact ⟨SimpleGraph.edgeSet_mono hFG he.1, he.2⟩

/-- The spanned-edge count is bounded by the total number of edges. -/
theorem edgesSpanned_le_edgeCount (G : SimpleGraph V) (U : Finset V) :
    RandomBoard.edgesSpanned G U ≤ edgeCount G := by
  classical
  unfold RandomBoard.edgesSpanned edgeCount
  rw [Set.ncard_eq_toFinset_card']
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_inter, Set.mem_toFinset] at he
  exact SimpleGraph.mem_edgeFinset.mpr he.1

/-- Spanned edges are the edges of the graph induced on the subtype `U`. -/
theorem edgesSpanned_eq_inducedEdgeCount (G : SimpleGraph V) (U : Finset V) :
    RandomBoard.edgesSpanned G U = edgeCount (G.induce (U : Set V)) := by
  classical
  unfold RandomBoard.edgesSpanned edgeCount
  rw [Set.ncard_eq_toFinset_card']
  have hfin :
      (G.edgeSet ∩ (U.sym2 : Set (Sym2 V))).toFinset =
        G.edgeFinset ∩ U.sym2 := by
    ext e
    simp only [Set.mem_toFinset, Set.mem_inter_iff, Finset.mem_inter,
      SimpleGraph.mem_edgeFinset]
    rfl
  rw [hfin]
  let f : Sym2 {x // x ∈ (U : Set V)} ↪ Sym2 V :=
    (Function.Embedding.subtype (U : Set V)).sym2Map
  calc
    (G.edgeFinset ∩ U.sym2).card =
        ((G.induce (U : Set V)).edgeFinset.map f).card := by
      apply congrArg Finset.card
      symm
      change
        (G.induce (U : Set V)).edgeFinset.map
            (Function.Embedding.subtype (U : Set V)).sym2Map =
          G.edgeFinset ∩ U.sym2
      simp_rw [Finset.ext_iff, Sym2.forall, Finset.mem_inter,
        Finset.mk_mem_sym2_iff, Finset.mem_map, Sym2.exists,
        Set.mem_toFinset, SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj,
        Function.Embedding.sym2Map_apply, Function.Embedding.coe_subtype,
        Sym2.map_pair_eq, Sym2.eq_iff]
      intro v w
      constructor
      · rintro ⟨x, y, hadj, ⟨hv, hw⟩ | ⟨hw, hv⟩⟩
        all_goals rw [← hv, ← hw]
        · exact ⟨hadj, x.prop, y.prop⟩
        · exact ⟨hadj.symm, y.prop, x.prop⟩
      · intro ⟨hadj, hv, hw⟩
        use ⟨v, hv⟩, ⟨w, hw⟩, hadj
        tauto
    _ = (G.induce (U : Set V)).edgeFinset.card := by simp

/-- Degree inside `U`, in the notation used by hereditary degeneracy. -/
noncomputable def internalDegree (G : SimpleGraph V) (U : Finset V) (v : V) : ℕ :=
  (U ∩ neighbors G v).card

theorem inducedDegree_eq_internalDegree (G : SimpleGraph V) (U : Finset V)
    (v : V) (hv : v ∈ U) :
    degree (G.induce (U : Set V)) ⟨v, hv⟩ = internalDegree G U v := by
  classical
  unfold degree internalDegree
  apply Finset.card_nbij (fun w : {x // x ∈ (U : Set V)} => w.1)
  · intro w hw
    have hwAdj : (G.induce (U : Set V)).Adj ⟨v, hv⟩ w :=
      (mem_neighbors (G.induce (U : Set V)) ⟨v, hv⟩ w).mp (by simpa using hw)
    show w.1 ∈ U ∩ neighbors G v
    rw [Finset.mem_inter, mem_neighbors]
    exact ⟨w.2, hwAdj⟩
  · intro x _hx y _hy hxy
    exact Subtype.ext hxy
  · intro w hw
    change w ∈ U ∩ neighbors G v at hw
    rcases Finset.mem_inter.mp hw with ⟨hwU, hwN⟩
    refine ⟨⟨w, hwU⟩, ?_, rfl⟩
    show ⟨w, hwU⟩ ∈ neighbors (G.induce (U : Set V)) ⟨v, hv⟩
    rw [mem_neighbors]
    exact (mem_neighbors G v w).mp hwN

/-- Handshaking inside an arbitrary finite vertex set. -/
theorem sum_internalDegree_eq_twice_edgesSpanned (G : SimpleGraph V)
    (U : Finset V) :
    (∑ v ∈ U, internalDegree G U v) =
      2 * RandomBoard.edgesSpanned G U := by
  classical
  have hsum :
      (∑ v : {x // x ∈ U}, degree (G.induce (U : Set V)) v) =
        ∑ v ∈ U, internalDegree G U v := by
    calc
      (∑ v : {x // x ∈ U}, degree (G.induce (U : Set V)) v) =
          ∑ v ∈ U.attach, degree (G.induce (U : Set V)) v := by
        rw [Finset.attach_eq_univ]
      _ = ∑ v ∈ U.attach, internalDegree G U v := by
        apply Finset.sum_congr rfl
        intro v _hv
        exact inducedDegree_eq_internalDegree G U v v.2
      _ = ∑ v ∈ U, internalDegree G U v := by
        simpa using U.sum_attach (fun v => internalDegree G U v)
  calc
    (∑ v ∈ U, internalDegree G U v) =
        ∑ v : {x // x ∈ U}, degree (G.induce (U : Set V)) v := hsum.symm
    _ = 2 * edgeCount (G.induce (U : Set V)) :=
      sum_degrees_eq_twice_edgeCount _
    _ = 2 * RandomBoard.edgesSpanned G U :=
      congrArg (2 * ·) (edgesSpanned_eq_inducedEdgeCount G U).symm

theorem internalDegree_le_card (G : SimpleGraph V) (U : Finset V) (v : V) :
    internalDegree G U v ≤ U.card := by
  classical
  exact Finset.card_le_card Finset.inter_subset_left

/-- Both deterministic set certificates pass from a host to a subgraph. -/
theorem DenseSetCertificate.anti {F G : SimpleGraph V} {M D : ℕ}
    (hFG : F ≤ G) (hG : RandomBoard.DenseSetCertificate G M D) :
    RandomBoard.DenseSetCertificate F M D := by
  intro U hlow hupp
  exact (Nat.mul_le_mul_left 2 (edgesSpanned_mono hFG U)).trans_lt
    (hG U hlow hupp)

theorem SmallSetCertificate.anti {F G : SimpleGraph V} {D L : ℕ}
    (hFG : F ≤ G) (hG : RandomBoard.SmallSetCertificate G D L) :
    RandomBoard.SmallSetCertificate F D L := by
  intro U hU
  exact (edgesSpanned_mono hFG U).trans (hG U hU)

/-- The dense-set certificate gives the deletion formulation of degeneracy
for every subgraph with at most `M` edges. -/
theorem DenseSetCertificate.hereditarilyLowDegree
    {F G : SimpleGraph V} {M D : ℕ} (hD : 0 < D)
    (hdense : RandomBoard.DenseSetCertificate G M D)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    HereditarilyLowDegree F D := by
  classical
  intro U hU
  by_cases hsmall : U.card ≤ D
  · rcases hU with ⟨v, hv⟩
    exact ⟨v, hv, (internalDegree_le_card F U v).trans hsmall⟩
  · have hlow : D ≤ U.card := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
    by_contra hnone
    push_neg at hnone
    have hsumlt :
        D * U.card < ∑ v ∈ U, internalDegree F U v := by
      have := Finset.sum_lt_sum_of_nonempty hU (fun v hv => hnone v hv)
      simpa [Nat.mul_comm] using this
    have hspanlt :
        D * U.card < 2 * RandomBoard.edgesSpanned F U := by
      simpa [sum_internalDegree_eq_twice_edgesSpanned F U] using hsumlt
    have hspanM : RandomBoard.edgesSpanned F U ≤ M :=
      (edgesSpanned_le_edgeCount F U).trans hE
    have hcardUpper : U.card ≤ 2 * M / D := by
      apply (Nat.le_div_iff_mul_le hD).2
      simpa [Nat.mul_comm] using
        (hspanlt.le.trans (Nat.mul_le_mul_left 2 hspanM))
    have hhost := hdense U hlow hcardUpper
    have hback :
        D * U.card < 2 * RandomBoard.edgesSpanned G U :=
      hspanlt.trans_le (Nat.mul_le_mul_left 2 (edgesSpanned_mono hFG U))
    exact Nat.lt_asymm hhost hback

/-- The codegree components of `HostGood` imply the deterministic codegree
bounds used by the charging lemmas. -/
theorem HostGood.pairCodegreeLE {G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) : PairCodegreeLE G c₂ :=
  CodegreeAtMost.toCodegreeLE h.1

theorem HostGood.tripleCodegreeLE {G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) : TripleCodegreeLE G c₃ :=
  CodegreeAtMost.toCodegreeLE h.2.1

theorem HostGood.denseSetCertificate {G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) :
    RandomBoard.DenseSetCertificate G M D := h.2.2.1

theorem HostGood.smallSetCertificate {G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) :
    RandomBoard.SmallSetCertificate G D L := h.2.2.2

theorem HostGood.subgraphHereditarilyLowDegree
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ} (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    HereditarilyLowDegree F D :=
  DenseSetCertificate.hereditarilyLowDegree hD
    (HostGood.denseSetCertificate h) hFG hE

theorem HostGood.subgraphSmallSetCertificate
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G) :
    RandomBoard.SmallSetCertificate F D L :=
  SmallSetCertificate.anti hFG (HostGood.smallSetCertificate h)

end Bridges

section OrderCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordered edge representatives selected by a total vertex order. -/
noncomputable def forwardDarts (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) : Finset (Σ _ : V, V) := by
  classical
  exact Finset.univ.sigma fun v => forwardNeighbors G order v

@[simp] theorem mem_forwardDarts (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (v w : V) :
    Sigma.mk v w ∈ forwardDarts G order ↔
      G.Adj v w ∧ order v < order w := by
  classical
  simp [forwardDarts]

theorem card_forwardDarts_eq_edgeCount (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    (forwardDarts G order).card = edgeCount G := by
  classical
  unfold edgeCount
  apply Finset.card_nbij (fun e : Σ _ : V, V => s(e.1, e.2))
  · intro e he
    rcases e with ⟨v, w⟩
    apply SimpleGraph.mem_edgeFinset.mpr
    exact (mem_forwardDarts G order v w).mp (by simpa using he) |>.1
  · rintro ⟨v, w⟩ hvw ⟨x, y⟩ hxy heq
    have hvw' := (mem_forwardDarts G order v w).mp (by simpa using hvw)
    have hxy' := (mem_forwardDarts G order x y).mp (by simpa using hxy)
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨hv, hw⟩
    · rfl
    · exfalso
      change v = y at hv
      change w = x at hw
      have hyx : order y < order x := by
        rw [← hv, ← hw]
        exact hvw'.2
      exact Nat.lt_asymm hxy'.2 hyx
  · intro e he
    induction e using Sym2.inductionOn with
    | _ v w =>
        have hadj : G.Adj v w := SimpleGraph.mem_edgeFinset.mp he
        have hne : order v ≠ order w := fun h => hadj.ne (order.injective h)
        rcases lt_or_gt_of_ne hne with hvw | hwv
        · refine ⟨⟨v, w⟩, ?_, rfl⟩
          exact (mem_forwardDarts G order v w).mpr ⟨hadj, hvw⟩
        · refine ⟨⟨w, v⟩, ?_, Sym2.eq_swap⟩
          exact (mem_forwardDarts G order w v).mpr ⟨hadj.symm, hwv⟩

/-- Every undirected edge has exactly one forward orientation. -/
theorem orientedEdgeMass_eq_edgeCount (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) :
    orientedEdgeMass G order = edgeCount G := by
  classical
  calc
    orientedEdgeMass G order = (forwardDarts G order).card := by
      simp [orientedEdgeMass, forwardDarts]
    _ = edgeCount G := card_forwardDarts_eq_edgeCount G order

/-- Restricting triangles to `S` gives at most all three-subsets of `S`. -/
theorem trianglesIn_le_choose (G : SimpleGraph V) (S : Finset V) :
    trianglesIn G S ≤ S.card.choose 3 := by
  classical
  unfold trianglesIn
  rw [← Finset.card_powersetCard 3 S]
  apply Finset.card_le_card
  intro T hT
  rw [Finset.mem_filter] at hT
  rw [Finset.mem_powersetCard]
  exact ⟨hT.2, (SimpleGraph.mem_cliqueFinset_iff.mp hT.1).card_eq⟩

/-- A coarse, certificate-independent local triangle estimate.  It is useful
as a fully formal fallback while the sharper small-set edge-to-triangle
incidence argument is still absent. -/
theorem IsDegeneracyOrder.localTriangleCubic {G : SimpleGraph V}
    {order : V ≃ Fin (Fintype.card V)} {D : ℕ}
    (horder : IsDegeneracyOrder G order D) :
    LocalTriangleLinear G order (D * D) := by
  intro v
  let n := (forwardNeighbors G order v).card
  calc
    trianglesIn G (forwardNeighbors G order v) ≤ n.choose 3 :=
      trianglesIn_le_choose G _
    _ ≤ n ^ 3 := Nat.choose_le_pow n 3
    _ = n * n * n := by ring
    _ ≤ D * D * n := Nat.mul_le_mul_right n
      (Nat.mul_le_mul (horder v) (horder v))
    _ = (D * D) * (forwardNeighbors G order v).card := by rfl

/-- Consequently the `K₄` charging sum has a completely explicit bound. -/
theorem k4Charge_le_of_degeneracyOrder {G : SimpleGraph V}
    {order : V ≃ Fin (Fintype.card V)} {D : ℕ}
    (horder : IsDegeneracyOrder G order D) :
    k4Charge G order ≤ (D * D) * edgeCount G := by
  apply k4Charge_le_edges G order horder.localTriangleCubic
  rw [orientedEdgeMass_eq_edgeCount]

/-- The exact conclusion obtained by applying a small-set certificate to all
forward neighborhoods of a degeneracy order. -/
def ForwardEdgeLinear (G : SimpleGraph V)
    (order : V ≃ Fin (Fintype.card V)) (L : ℕ) : Prop :=
  ∀ v, RandomBoard.edgesSpanned G (forwardNeighbors G order v) ≤
    L * (forwardNeighbors G order v).card

theorem SmallSetCertificate.forwardEdgeLinear {G : SimpleGraph V}
    {order : V ≃ Fin (Fintype.card V)} {D L : ℕ}
    (hsmall : RandomBoard.SmallSetCertificate G D L)
    (horder : IsDegeneracyOrder G order D) :
    ForwardEdgeLinear G order L := by
  intro v
  exact hsmall _ (horder v)

theorem HostGood.subgraphForwardEdgeLinear
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    {order : V ≃ Fin (Fintype.card V)}
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G)
    (horder : IsDegeneracyOrder F order D) :
    ForwardEdgeLinear F order L :=
  SmallSetCertificate.forwardEdgeLinear
    (HostGood.subgraphSmallSetCertificate h hFG) horder

end OrderCounting

section CoarseChargeBounds

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A uniform fallback triangle/edge estimate on a finite ambient type. -/
theorem triangleCount_le_ambientCube_mul_edges (G : SimpleGraph V) :
    triangleCount G ≤ (Fintype.card V) ^ 3 * edgeCount G := by
  classical
  by_cases hE : edgeCount G = 0
  · have hbot : G = ⊥ := by
      apply SimpleGraph.edgeFinset_eq_empty.mp
      exact Finset.card_eq_zero.mp (by simpa [edgeCount] using hE)
    subst G
    simp [triangleCount, edgeCount]
  · have hone : 1 ≤ edgeCount G := Nat.one_le_iff_ne_zero.mpr hE
    calc
      triangleCount G ≤ (Fintype.card V).choose 3 := by
        exact SimpleGraph.card_cliqueFinset_le
      _ ≤ (Fintype.card V) ^ 3 := Nat.choose_le_pow _ _
      _ ≤ (Fintype.card V) ^ 3 * edgeCount G := by
        simpa using Nat.mul_le_mul_left ((Fintype.card V) ^ 3) hone

theorem linkTriangleLinear_ambientCube (G : SimpleGraph V) :
    LinkTriangleLinear G ((Fintype.card V) ^ 3) := by
  intro v
  exact triangleCount_le_ambientCube_mul_edges (linkGraph G v)

theorem commonTriangleIncidences_le (G : SimpleGraph V) {D : ℕ}
    (h₃ : TripleCodegreeLE G D) :
    commonTriangleIncidences G ≤ D * triangleCount G := by
  classical
  unfold commonTriangleIncidences triangleCount
  calc
    (∑ T ∈ G.cliqueFinset 3, codegree G T) ≤
        ∑ _T ∈ G.cliqueFinset 3, D := by
      apply Finset.sum_le_sum
      intro T hT
      exact h₃ T (SimpleGraph.mem_cliqueFinset_iff.mp hT).card_eq
    _ = D * (G.cliqueFinset 3).card := by
      simp [Nat.mul_comm]

theorem commonTriangleIncidences_le_ambientCube_edges
    (G : SimpleGraph V) {D : ℕ} (h₃ : TripleCodegreeLE G D) :
    commonTriangleIncidences G ≤
      (D * (Fintype.card V) ^ 3) * edgeCount G := by
  calc
    commonTriangleIncidences G ≤ D * triangleCount G :=
      commonTriangleIncidences_le G h₃
    _ ≤ D * ((Fintype.card V) ^ 3 * edgeCount G) :=
      Nat.mul_le_mul_left D (triangleCount_le_ambientCube_mul_edges G)
    _ = (D * (Fintype.card V) ^ 3) * edgeCount G := by ring

theorem k5MinusEdgeCharge_le_ambientCube_edges
    (G : SimpleGraph V) {D : ℕ} (h₃ : TripleCodegreeLE G D) :
    k5MinusEdgeCharge G ≤
      (D * (D * (Fintype.card V) ^ 3)) * edgeCount G := by
  exact k5MinusEdgeCharge_le_edges G h₃
    (commonTriangleIncidences_le_ambientCube_edges G h₃)

theorem insideOrderedEdgeMass_le_square (G : SimpleGraph V) (S : Finset V) :
    insideOrderedEdgeMass G S ≤ S.card * S.card := by
  classical
  unfold insideOrderedEdgeMass
  calc
    ((S.product S).filter fun e => G.Adj e.1 e.2).card ≤
        (S.product S).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = S.card * S.card := Finset.card_product S S

theorem centralK4Mass_le_pairCodegree (G : SimpleGraph V) {D : ℕ}
    (h₂ : PairCodegreeLE G D) :
    centralK4Mass G ≤ (2 * D * D) * edgeCount G := by
  classical
  unfold centralK4Mass
  calc
    (∑ e ∈ orderedEdges G,
        insideOrderedEdgeMass G (commonNeighborsFinset G {e.1, e.2})) ≤
        ∑ _e ∈ orderedEdges G, D * D := by
      apply Finset.sum_le_sum
      intro e he
      have hadj : G.Adj e.1 e.2 := by
        simpa using (mem_orderedEdges G e.1 e.2).mp he
      have hcode : codegree G {e.1, e.2} ≤ D :=
        h₂ {e.1, e.2} (by simp [hadj.ne, hadj.ne'])
      exact (insideOrderedEdgeMass_le_square G _).trans
        (Nat.mul_le_mul hcode hcode)
    _ = (2 * D * D) * edgeCount G := by
      simp [card_orderedEdges]
      ring

theorem qCharge_le_pairCodegree_edges (G : SimpleGraph V) {D : ℕ}
    (h₂ : PairCodegreeLE G D) :
    qCharge G ≤ (D * D * (2 * D * D)) * edgeCount G := by
  exact qCharge_le_edges G h₂ (centralK4Mass_le_pairCodegree G h₂)

theorem HostGood.subgraphPairCodegreeLE
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G) :
    PairCodegreeLE F c₂ :=
  CodegreeLE.anti hFG (HostGood.pairCodegreeLE h)

theorem HostGood.subgraphTripleCodegreeLE
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G) :
    TripleCodegreeLE F c₃ :=
  CodegreeLE.anti hFG (HostGood.tripleCodegreeLE h)

/-- Explicit host-certified bounds for the three charge sums whose estimates
only need codegrees (plus the universal finite triangle/edge fallback). -/
theorem HostGood.subgraphH3Charge_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G)
    (hE : edgeCount F ≤ M) :
    h3Charge F ≤
      (6 * c₂ * ((Fintype.card V) ^ 3) * M) * edgeCount F := by
  exact h3Charge_le F (HostGood.subgraphPairCodegreeLE h hFG)
    (linkTriangleLinear_ambientCube F) hE

theorem HostGood.subgraphK5MinusEdgeCharge_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G) :
    k5MinusEdgeCharge F ≤
      (c₃ * (c₃ * (Fintype.card V) ^ 3)) * edgeCount F := by
  exact k5MinusEdgeCharge_le_ambientCube_edges F
    (HostGood.subgraphTripleCodegreeLE h hFG)

theorem HostGood.subgraphQCharge_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃) (hFG : F ≤ G) :
    qCharge F ≤
      (c₂ * c₂ * (2 * c₂ * c₂)) * edgeCount F := by
  exact qCharge_le_pairCodegree_edges F (HostGood.subgraphPairCodegreeLE h hFG)

end CoarseChargeBounds

end OnlineRamsey
