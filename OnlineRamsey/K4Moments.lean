import OnlineRamsey.AdaptiveQuery
import OnlineRamsey.UpperBound
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Exact finite-board moments for four-clique indicators

This file supplies the probability/combinatorics interface left abstract in
`OnlineRamsey.UpperBound`.  We work directly with the explicit finite product
mass from `OnlineRamsey.AdaptiveQuery`; consequently no measurability layer is
needed.

An `edgeFamily` assigns to every four-set the finite set of board coordinates
which have to be positive.  The abstract formulation is intentional: all
probability calculations depend only on the cardinalities of one edge set and
of unions of two edge sets.  For the ordinary graph model these cardinalities
are `6` and `12 - choose |A ∩ B| 2`, respectively.
-/

namespace OnlineRamsey
namespace K4Moments

open scoped ENNReal

universe u v

variable {V : Type u} {Q : Type v} [DecidableEq V]
  [Fintype Q] [DecidableEq Q]

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Event that every coordinate in `S` is positive. -/
def AllTrue (S : Finset Q) : Set (Board Q) :=
  {board | ∀ q ∈ S, board q = true}

/-- The `{0,1}`-valued indicator of `AllTrue S`, in `ENNReal`. -/
noncomputable def allTrueIndicator (S : Finset Q) (board : Board Q) : ℝ≥0∞ :=
  if board ∈ AllTrue S then 1 else 0

/-- Expectation under the explicit finite Bernoulli product board. -/
noncomputable def expectation (p : ℝ≥0∞) (X : Board Q → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ board : Board Q, boardWeight (bernoulliWeight p) board * X board

/-- Exact cylinder probability: all coordinates of `S` are positive. -/
theorem finiteBoardMass_allTrue (p : ℝ≥0∞) (hp : p ≤ 1) (S : Finset Q) :
    finiteBoardMass (bernoulliWeight p) (AllTrue S) = p ^ S.card := by
  classical
  have hset : AllTrue S = assignmentCylinder S (fun _ => true) := by
    ext board
    simp [AllTrue, assignmentCylinder]
  rw [hset, finiteBoardMass_assignmentCylinder (bernoulliWeight p)
    (sum_bernoulliWeight p hp)]
  simp [bernoulliWeight]

/-- Exact expectation of one all-positive indicator. -/
theorem expectation_allTrueIndicator (p : ℝ≥0∞) (hp : p ≤ 1)
    (S : Finset Q) :
    expectation p (allTrueIndicator S) = p ^ S.card := by
  classical
  rw [← finiteBoardMass_allTrue p hp S]
  unfold expectation finiteBoardMass allTrueIndicator
  apply Finset.sum_congr rfl
  intro board _
  by_cases h : board ∈ AllTrue S <;> simp [h]

/-- Products of clique indicators are indicators of the union of their
required coordinates. -/
theorem allTrueIndicator_mul (S T : Finset Q) (board : Board Q) :
    allTrueIndicator S board * allTrueIndicator T board =
      allTrueIndicator (S ∪ T) board := by
  classical
  by_cases hS : board ∈ AllTrue S <;>
    by_cases hT : board ∈ AllTrue T <;>
      simp only [allTrueIndicator, hS, hT, if_true, if_false,
        one_mul, zero_mul]
  · have hST : board ∈ AllTrue (S ∪ T) := by
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hS q hq
      · exact hT q hq
    simp [allTrueIndicator, hST]
  · have hST : board ∉ AllTrue (S ∪ T) := by
      intro h
      exact hT (fun q hq => h q (Finset.mem_union_right S hq))
    simp [allTrueIndicator, hST]
  · have hST : board ∉ AllTrue (S ∪ T) := by
      intro h
      exact hS (fun q hq => h q (Finset.mem_union_left T hq))
    simp [allTrueIndicator, hST]
  · have hST : board ∉ AllTrue (S ∪ T) := by
      intro h
      exact hS (fun q hq => h q (Finset.mem_union_left T hq))
    simp [allTrueIndicator, hST]

/-- Exact joint moment of two all-positive indicators. -/
theorem expectation_indicator_mul (p : ℝ≥0∞) (hp : p ≤ 1)
    (S T : Finset Q) :
    expectation p (fun board => allTrueIndicator S board * allTrueIndicator T board) =
      p ^ (S ∪ T).card := by
  simp_rw [allTrueIndicator_mul]
  exact expectation_allTrueIndicator p hp (S ∪ T)

/-- Count of successful four-sets, represented in `ENNReal`. -/
noncomputable def k4Count (U : Finset V) (edgeFamily : Finset V → Finset Q)
    (board : Board Q) : ℝ≥0∞ :=
  ∑ A ∈ U.powersetCard 4, allTrueIndicator (edgeFamily A) board

/-- Linearity of the explicit finite expectation for a finite sum. -/
theorem expectation_sum {I : Type*} [Fintype I]
    (p : ℝ≥0∞) (f : I → Board Q → ℝ≥0∞) :
    expectation p (fun board => ∑ i, f i board) =
      ∑ i, expectation p (f i) := by
  classical
  unfold expectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Linearity over a specified finite index set. -/
theorem expectation_finset_sum {I : Type*} [DecidableEq I]
    (p : ℝ≥0∞) (s : Finset I) (f : I → Board Q → ℝ≥0∞) :
    expectation p (fun board => ∑ i ∈ s, f i board) =
      ∑ i ∈ s, expectation p (f i) := by
  classical
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Exact first moment before imposing the six-edge cardinality. -/
theorem k4Count_firstMoment (p : ℝ≥0∞) (hp : p ≤ 1)
    (U : Finset V) (edgeFamily : Finset V → Finset Q) :
    expectation p (k4Count U edgeFamily) =
      ∑ A ∈ U.powersetCard 4, p ^ (edgeFamily A).card := by
  classical
  unfold k4Count
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro A _
  exact expectation_allTrueIndicator p hp (edgeFamily A)

/-- In the graph case, every four-set asks for six edge coordinates. -/
theorem k4Count_firstMoment_sixEdges (p : ℝ≥0∞) (hp : p ≤ 1)
    (U : Finset V) (edgeFamily : Finset V → Finset Q)
    (hsix : ∀ A ∈ U.powersetCard 4, (edgeFamily A).card = 6) :
    expectation p (k4Count U edgeFamily) =
      (Nat.choose U.card 4 : ℝ≥0∞) * p ^ 6 := by
  rw [k4Count_firstMoment p hp U edgeFamily]
  calc
    (∑ A ∈ U.powersetCard 4, p ^ (edgeFamily A).card) =
        ∑ _A ∈ U.powersetCard 4, p ^ 6 := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [hsix A hA]
    _ = (Nat.choose U.card 4 : ℝ≥0∞) * p ^ 6 := by simp

/-- Pointwise expansion of the square of the four-clique count into ordered
pairs of indicators. -/
theorem k4Count_sq (U : Finset V) (edgeFamily : Finset V → Finset Q)
    (board : Board Q) :
    k4Count U edgeFamily board ^ 2 =
      ∑ AB ∈ U.powersetCard 4 ×ˢ U.powersetCard 4,
        allTrueIndicator (edgeFamily AB.1) board *
          allTrueIndicator (edgeFamily AB.2) board := by
  classical
  unfold k4Count
  rw [pow_two, Finset.sum_mul_sum]
  simp [Finset.sum_product]

/-- Exact second moment in terms of the union of the coordinates required by
an ordered pair of four-sets. -/
theorem k4Count_secondMoment (p : ℝ≥0∞) (hp : p ≤ 1)
    (U : Finset V) (edgeFamily : Finset V → Finset Q) :
    expectation p (fun board => k4Count U edgeFamily board ^ 2) =
      ∑ AB ∈ U.powersetCard 4 ×ˢ U.powersetCard 4,
        p ^ (edgeFamily AB.1 ∪ edgeFamily AB.2).card := by
  classical
  simp_rw [k4Count_sq U edgeFamily]
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro AB _
  exact expectation_indicator_mul p hp (edgeFamily AB.1) (edgeFamily AB.2)

/-- Exact graph-model second moment, assuming only the elementary union-size
formula for the chosen encoding of unordered edges. -/
theorem k4Count_secondMoment_overlap (p : ℝ≥0∞) (hp : p ≤ 1)
    (U : Finset V) (edgeFamily : Finset V → Finset Q)
    (hunion : ∀ A ∈ U.powersetCard 4, ∀ B ∈ U.powersetCard 4,
      (edgeFamily A ∪ edgeFamily B).card =
        12 - Nat.choose (A ∩ B).card 2) :
    expectation p (fun board => k4Count U edgeFamily board ^ 2) =
      ∑ AB ∈ U.powersetCard 4 ×ˢ U.powersetCard 4,
        p ^ (12 - Nat.choose (AB.1 ∩ AB.2).card 2) := by
  rw [k4Count_secondMoment p hp U edgeFamily]
  apply Finset.sum_congr rfl
  intro AB hAB
  rcases Finset.mem_product.mp hAB with ⟨hA, hB⟩
  rw [hunion AB.1 hA AB.2 hB]

/-- The complete five-overlap expansion of the exact second moment.  This is
the finite-product probability bridge to `k4PairEdgeWeight_identity`. -/
theorem k4Count_secondMoment_fiveTerms (p : ℝ≥0∞) (hp : p ≤ 1)
    (U : Finset V) (edgeFamily : Finset V → Finset Q)
    (hunion : ∀ A ∈ U.powersetCard 4, ∀ B ∈ U.powersetCard 4,
      (edgeFamily A ∪ edgeFamily B).card =
        12 - Nat.choose (A ∩ B).card 2) :
    expectation p (fun board => k4Count U edgeFamily board ^ 2) =
      ∑ k ∈ Finset.range 5,
        (Nat.choose U.card 4 * Nat.choose 4 k *
          Nat.choose (U.card - 4) (4 - k) : ℝ≥0∞) *
          p ^ (12 - Nat.choose k 2) := by
  rw [k4Count_secondMoment_overlap p hp U edgeFamily hunion]
  -- The overlap-counting proof is coefficient-semiring independent.  We use
  -- the same fiber decomposition directly in `ENNReal`.
  let pairs := U.powersetCard 4 ×ˢ U.powersetCard 4
  let overlap : Finset V × Finset V → ℕ := fun AB => (AB.1 ∩ AB.2).card
  have hmap : ∀ AB ∈ pairs, overlap AB ∈ Finset.range 5 := by
    intro AB hAB
    rcases Finset.mem_product.mp hAB with ⟨hA, _⟩
    have hcard := (Finset.mem_powersetCard.mp hA).2
    have hle := Finset.card_le_card (Finset.inter_subset_left : AB.1 ∩ AB.2 ⊆ AB.1)
    simp only [overlap, Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmap
    (fun k => p ^ (12 - Nat.choose k 2))]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < 5 := Finset.mem_range.mp hk
  have hk4 : k ≤ 4 := by omega
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [K6Upper.card_orderedK4Pairs_with_intersection U k hk4]
  norm_cast

/-! ## Concrete unordered-edge realization -/

/-- The six non-loop unordered pairs spanned by a vertex set.  Defining this
as the mapped edge finset of the complete graph on the subtype makes diagonal
deletion canonical. -/
noncomputable def cliqueEdges (A : Finset V) : Finset (Sym2 V) := by
  classical
  exact (⊤ : SimpleGraph (↥A)).edgeFinset.map
    (Function.Embedding.subtype (fun v : V => v ∈ A)).sym2Map

@[simp] theorem mem_cliqueEdges {A : Finset V} {v w : V} :
    s(v, w) ∈ cliqueEdges A ↔ v ∈ A ∧ w ∈ A ∧ v ≠ w := by
  classical
  rw [cliqueEdges, Finset.mem_map]
  constructor
  · rintro ⟨e, he, hmap⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hxySub : x ≠ y := by simpa using he
      have hxy : (x : V) ≠ (y : V) := by
        intro h
        apply hxySub
        exact Subtype.ext h
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq,
        Sym2.eq_iff] at hmap
      rcases hmap with hmap | hmap
      · rcases hmap with ⟨hx, hy⟩
        subst v
        subst w
        exact ⟨x.property, y.property, hxy⟩
      · rcases hmap with ⟨hx, hy⟩
        subst w
        subst v
        exact ⟨y.property, x.property, hxy.symm⟩
  · rintro ⟨hv, hw, hvw⟩
    let x : ↥A := ⟨v, hv⟩
    let y : ↥A := ⟨w, hw⟩
    refine ⟨s(x, y), ?_, ?_⟩
    · simpa [x, y, Sym2.mk_isDiag_iff]
    · simp [x, y]

/-- A complete graph on `A` has exactly `choose |A| 2` edges. -/
theorem card_cliqueEdges (A : Finset V) :
    (cliqueEdges A).card = Nat.choose A.card 2 := by
  classical
  unfold cliqueEdges
  rw [Finset.card_map, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

/-- Common required coordinates are precisely the edges spanned by the
intersection of the two vertex sets. -/
theorem cliqueEdges_inter (A B : Finset V) :
    cliqueEdges A ∩ cliqueEdges B = cliqueEdges (A ∩ B) := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ v w => simp [and_assoc, and_left_comm, and_comm]

/-- Exact union size for the two six-edge sets belonging to four-sets. -/
theorem card_cliqueEdges_union_of_card_four (A B : Finset V)
    (hA : A.card = 4) (hB : B.card = 4) :
    (cliqueEdges A ∪ cliqueEdges B).card =
      12 - Nat.choose (A ∩ B).card 2 := by
  classical
  rw [Finset.card_union, cliqueEdges_inter, card_cliqueEdges, card_cliqueEdges,
    card_cliqueEdges, hA, hB]
  norm_num [Nat.choose]

/-- Fully concrete exact first moment for `K₄` copies in the Bernoulli graph
on a finite vertex type. -/
theorem graphK4Count_firstMoment (p : ℝ≥0∞) (hp : p ≤ 1) (U : Finset V)
    [Fintype V] :
    expectation p (k4Count U cliqueEdges) =
      (Nat.choose U.card 4 : ℝ≥0∞) * p ^ 6 := by
  classical
  apply k4Count_firstMoment_sixEdges p hp U cliqueEdges
  intro A hA
  rw [card_cliqueEdges, (Finset.mem_powersetCard.mp hA).2]
  norm_num [Nat.choose]

/-- Fully concrete five-overlap second-moment formula for the Bernoulli graph. -/
theorem graphK4Count_secondMoment (p : ℝ≥0∞) (hp : p ≤ 1) (U : Finset V)
    [Fintype V] :
    expectation p (fun board => k4Count U cliqueEdges board ^ 2) =
      ∑ k ∈ Finset.range 5,
        (Nat.choose U.card 4 * Nat.choose 4 k *
          Nat.choose (U.card - 4) (4 - k) : ℝ≥0∞) *
          p ^ (12 - Nat.choose k 2) := by
  classical
  apply k4Count_secondMoment_fiveTerms p hp U cliqueEdges
  intro A hA B hB
  exact card_cliqueEdges_union_of_card_four A B
    (Finset.mem_powersetCard.mp hA).2 (Finset.mem_powersetCard.mp hB).2

end K4Moments
end OnlineRamsey
