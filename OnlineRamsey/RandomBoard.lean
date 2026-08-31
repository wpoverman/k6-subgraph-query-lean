import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.UnitInterval
import OnlineRamsey.AdaptiveQuery

/-!
# The random board used in the `K₆` subgraph-query argument

This file contains the kernel-checked probability infrastructure for the
finite Bernoulli board and its exact finite witness bounds.

The random host is represented by `bitBoardMeasure E p`, the finite product of
Bernoulli laws on an arbitrary finite coordinate type `E`.  Taking
`E = Sym2 (Fin n)` and applying `randomHost` gives the usual `G(n,p)` graph;
diagonal coordinates are discarded by `SimpleGraph.fromEdgeSet`.

The most useful result below for the random-extremal argument is
`measure_someWitness_le`: if a bad event has a finite collection of witnesses,
each consisting of a prescribed collection of present edges, its probability
is at most the sum of `p ^ |witness|` over the witnesses.  This is the exact
union-bound step used in the dense-set and small-set estimates.

The real-valued MGF/Hoeffding layer is not claimed here: Lean/Mathlib 4.24
requires additional measurability and coercion work for that formulation.
The adaptive finite-product development already proves an exact binomial law;
see `RANDOM_STATUS.md` for the remaining tail and asymptotic estimates.
-/

open scoped ENNReal NNReal

open Filter MeasureTheory ProbabilityTheory Set

namespace OnlineRamsey.RandomBoard

/-! ## Simple graphs extracted from Bernoulli boards -/

/-- A finite random host graph on `n` labeled vertices. -/
abbrev Host (n : ℕ) := SimpleGraph (Fin n)

/-- Turn symmetric-pair bits into a simple graph.  Diagonal bits are ignored
by `SimpleGraph.fromEdgeSet`. -/
def graphOfBoard {V : Type*} (ω : Sym2 V → Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ω e = true}

/-- The random host graph on `Fin n` associated with a board realization. -/
def randomHost (n : ℕ) (ω : Sym2 (Fin n) → Bool) : Host n :=
  graphOfBoard ω

/-- The pointwise incidence bridge between the Bernoulli board and the graph
extracted from it.  The second conjunct is the loop deletion performed by
`SimpleGraph.fromEdgeSet`. -/
@[simp]
theorem graphOfBoard_adj {V : Type*} (ω : Sym2 V → Bool) (v w : V) :
    (graphOfBoard ω).Adj v w ↔ ω s(v, w) = true ∧ v ≠ w := by
  simp [graphOfBoard, SimpleGraph.fromEdgeSet_adj]

/-- The incidence bridge specialized to the finite random host. -/
@[simp]
theorem randomHost_adj (n : ℕ) (ω : Sym2 (Fin n) → Bool) (v w : Fin n) :
    (randomHost n ω).Adj v w ↔ ω s(v, w) = true ∧ v ≠ w := by
  simp [randomHost]

/-- Adjacency in a graph extracted from a Boolean board is decidable.  Naming
this instance lets the finite `edgeFinset` API elaborate in theorem
statements, before a proof-local `classical` tactic is available. -/
instance randomHost_decidableAdj (n : ℕ) (ω : Sym2 (Fin n) → Bool) :
    DecidableRel (randomHost n ω).Adj := fun v w =>
  decidable_of_iff (ω s(v, w) = true ∧ v ≠ w) (randomHost_adj n ω v w).symm

/-! ## Predicates appearing in the uniform host event -/

/-- The vertices adjacent to every vertex of `S`. -/
def commonNeighborSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Set V :=
  {w | ∀ v ∈ S, G.Adj v w}

/-- A vertex is a common neighbor in the extracted graph exactly when all of
its incident board coordinates to the root set are `true` (and none is a
loop). -/
@[simp]
theorem mem_commonNeighborSet_randomHost (n : ℕ)
    (ω : Sym2 (Fin n) → Bool) (S : Finset (Fin n)) (w : Fin n) :
    w ∈ commonNeighborSet (randomHost n ω) S ↔
      ∀ v ∈ S, ω s(v, w) = true ∧ v ≠ w := by
  simp [commonNeighborSet]

/-- The number of common neighbors of a finite set of vertices. -/
noncomputable def commonNeighborCount {V : Type*} (G : SimpleGraph V)
    (S : Finset V) : ℕ :=
  (commonNeighborSet G S).ncard

/-- Deterministic block-indicator formula for the common-neighbor count.  This
is the exact pointwise identity to which the codegree concentration argument
will be applied. -/
theorem commonNeighborCount_randomHost_eq_sum (n : ℕ)
    (ω : Sym2 (Fin n) → Bool) (S : Finset (Fin n)) :
    commonNeighborCount (randomHost n ω) S =
      ∑ w : Fin n,
        if (∀ v ∈ S, ω s(v, w) = true ∧ v ≠ w) then (1 : ℕ) else 0 := by
  classical
  unfold commonNeighborCount commonNeighborSet
  rw [Set.ncard_eq_toFinset_card']
  simp only [randomHost_adj]
  rw [show
    (∑ w : Fin n,
      if (∀ v ∈ S, ω s(v, w) = true ∧ v ≠ w) then (1 : ℕ) else 0) =
        ((Finset.univ.filter fun w : Fin n =>
          ∀ v ∈ S, ω s(v, w) = true ∧ v ≠ w).card) by simp]
  apply congrArg Finset.card
  ext w
  simp

/-- The number of (unordered) edges of `G` spanned by `U`.

This set-based definition avoids introducing a decidable adjacency relation
for an arbitrary graph.  On finite vertex types it is the cardinality of the
usual induced edge finset. -/
noncomputable def edgesSpanned {V : Type*} (G : SimpleGraph V)
    (U : Finset V) : ℕ :=
  (G.edgeSet ∩ (U.sym2 : Set (Sym2 V))).ncard

/-- Uniform `j`-codegree bound. -/
def CodegreeAtMost {V : Type*} (G : SimpleGraph V) (j B : ℕ) : Prop :=
  ∀ S : Finset V, S.card = j → commonNeighborCount G S ≤ B

/-- The dense-set certificate used to force degeneracy of every sparse
subgraph of the host.  The range `D ≤ |U| ≤ 2M/D` is exactly the range in
Lemma 3.2 of the paper-style proof. -/
def DenseSetCertificate {V : Type*} (G : SimpleGraph V) (M D : ℕ) : Prop :=
  ∀ U : Finset V,
    D ≤ U.card → U.card ≤ 2 * M / D →
      2 * edgesSpanned G U < D * U.card

/-- Every vertex set of size at most `D` spans at most `L|U|` edges. -/
def SmallSetCertificate {V : Type*} (G : SimpleGraph V) (D L : ℕ) : Prop :=
  ∀ U : Finset V, U.card ≤ D → edgesSpanned G U ≤ L * U.card

/-- The four genuinely random properties from which the deterministic host
counting argument derives all five conclusions of its uniform-host
proposition. -/
def HostGood {V : Type*} (G : SimpleGraph V)
    (M D L pairBound tripleBound : ℕ) : Prop :=
  CodegreeAtMost G 2 pairBound ∧
    CodegreeAtMost G 3 tripleBound ∧
    DenseSetCertificate G M D ∧
    SmallSetCertificate G D L

/-- The corresponding event in the native `G(n,p)` sample space. -/
def hostGoodEvent (n M D L pairBound tripleBound : ℕ) : Set (Host n) :=
  {G | HostGood G M D L pairBound tripleBound}

@[simp]
theorem mem_hostGoodEvent {n M D L pairBound tripleBound : ℕ} {G : Host n} :
    G ∈ hostGoodEvent n M D L pairBound tripleBound ↔
      HostGood G M D L pairBound tripleBound :=
  Iff.rfl

/-! ## A coordinatewise Bernoulli board -/

/-- One `p`-Bernoulli bit, with `true` having probability `p`. -/
theorem toNNReal_le_one (p : unitInterval) : unitInterval.toNNReal p ≤ 1 := by
  change (p : ℝ) ≤ 1
  exact unitInterval.le_one p

/-- One `p`-Bernoulli bit, with `true` having probability `p`. -/
noncomputable def bernoulliBit (p : unitInterval) : Measure Bool :=
  (PMF.bernoulli (unitInterval.toNNReal p) (toNNReal_le_one p)).toMeasure

instance bernoulliBit.isProbabilityMeasure (p : unitInterval) :
    IsProbabilityMeasure (bernoulliBit p) := by
  dsimp [bernoulliBit]
  infer_instance

/-- Independent `p`-Bernoulli bits indexed by a finite coordinate type `E`. -/
noncomputable def bitBoardMeasure (E : Type*) [Fintype E] (p : unitInterval) :
    Measure (E → Bool) :=
  Measure.pi fun _ : E => bernoulliBit p

instance bitBoardMeasure.isProbabilityMeasure (E : Type*) [Fintype E]
    (p : unitInterval) : IsProbabilityMeasure (bitBoardMeasure E p) := by
  dsimp [bitBoardMeasure, bernoulliBit]
  infer_instance

/-- A cylinder requiring every coordinate in `s` to be `true`, with all other
coordinates unrestricted. -/
noncomputable def allTrueOn {E : Type*} (s : Finset E) : Set (E → Bool) := by
  classical
  exact Set.univ.pi fun e => if e ∈ s then ({true} : Set Bool) else Set.univ

@[simp]
theorem mem_allTrueOn_iff {E : Type*} {s : Finset E} {ω : E → Bool} :
    ω ∈ allTrueOn s ↔ ∀ e ∈ s, ω e = true := by
  classical
  unfold allTrueOn
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h e he
    simpa [he] using h e
  · intro h e
    by_cases he : e ∈ s
    · simpa [he] using h e he
    · simp [he]

theorem measurableSet_allTrueOn {E : Type*} [Fintype E] (s : Finset E) :
    MeasurableSet (allTrueOn s) := by
  classical
  refine MeasurableSet.pi Set.countable_univ ?_
  intro e he
  by_cases hes : e ∈ s <;> simp [hes]

@[simp]
theorem bernoulliBit_singleton_true (p : unitInterval) :
    bernoulliBit p ({true} : Set Bool) =
      (unitInterval.toNNReal p : ENNReal) := by
  rw [bernoulliBit,
    PMF.toMeasure_apply_singleton _ true (MeasurableSet.singleton true)]
  simp

@[simp]
theorem bernoulliBit_singleton_false (p : unitInterval) :
    bernoulliBit p ({false} : Set Bool) =
      1 - (unitInterval.toNNReal p : ENNReal) := by
  rw [bernoulliBit,
    PMF.toMeasure_apply_singleton _ false (MeasurableSet.singleton false)]
  simp

/-- The singleton mass of a native Bernoulli coordinate agrees with the
weight function used by the adaptive finite-board development. -/
@[simp]
theorem bernoulliBit_singleton (p : unitInterval) (b : Bool) :
    bernoulliBit p ({b} : Set Bool) =
      OnlineRamsey.bernoulliWeight (unitInterval.toNNReal p : ENNReal) b := by
  cases b <;> simp [OnlineRamsey.bernoulliWeight]

@[simp]
theorem bernoulliBit_bool_univ (p : unitInterval) :
    bernoulliBit p ({false, true} : Set Bool) = 1 := by
  rw [show ({false, true} : Set Bool) = Set.univ by
    ext b
    cases b <;> simp]
  exact measure_univ

/-- Exact probability that every bit in a prescribed finite set is present. -/
@[simp]
theorem measure_allTrueOn {E : Type*} [Fintype E] (p : unitInterval)
    (s : Finset E) :
    bitBoardMeasure E p (allTrueOn s) =
      (unitInterval.toNNReal p : ENNReal) ^ s.card := by
  classical
  rw [bitBoardMeasure, allTrueOn, Measure.pi_pi]
  calc
    (∏ e : E,
        bernoulliBit p
          (if e ∈ s then ({true} : Set Bool) else Set.univ)) =
        ∏ e : E, if e ∈ s then
          (unitInterval.toNNReal p : ENNReal) else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases hes : e ∈ s <;>
        simp [hes, OnlineRamsey.bernoulliWeight]
    _ = ∏ e ∈ s, (unitInterval.toNNReal p : ENNReal) := by
      symm
      calc
        (∏ e ∈ s, (unitInterval.toNNReal p : ENNReal)) =
            ∏ e ∈ s, if e ∈ s then
              (unitInterval.toNNReal p : ENNReal) else 1 := by
          apply Finset.prod_congr rfl
          intro e he
          simp [he]
        _ = ∏ e ∈ (Finset.univ : Finset E), if e ∈ s then
              (unitInterval.toNNReal p : ENNReal) else 1 := by
          apply Finset.prod_subset (Finset.subset_univ s)
          intro e heuniv henot
          simp [henot]
        _ = ∏ e : E, if e ∈ s then
              (unitInterval.toNNReal p : ENNReal) else 1 := rfl
    _ = (unitInterval.toNNReal p : ENNReal) ^ s.card := by simp

/-- Exact mass of an arbitrary finite coordinate assignment under the native
product measure.  This is the measure-theoretic bridge to the adaptive-board
cylinder law. -/
theorem measure_assignmentCylinder {E : Type*} [Fintype E] [DecidableEq E]
    (p : unitInterval) (domain : Finset E) (value : OnlineRamsey.Board E) :
    bitBoardMeasure E p (OnlineRamsey.assignmentCylinder domain value) =
      ∏ e ∈ domain,
        OnlineRamsey.bernoulliWeight
          (unitInterval.toNNReal p : ENNReal) (value e) := by
  have hcylinder : OnlineRamsey.assignmentCylinder domain value =
      Set.univ.pi
        (fun e => if e ∈ domain then ({value e} : Set Bool) else Set.univ) := by
    ext ω
    constructor
    · intro h e
      by_cases he : e ∈ domain
      · simpa [he] using h e he
      · simp [he]
    · intro h e he
      simpa [he] using h e
  rw [hcylinder, bitBoardMeasure, Measure.pi_pi]
  calc
    (∏ e : E,
        bernoulliBit p
          (if e ∈ domain then ({value e} : Set Bool) else Set.univ)) =
        ∏ e : E, if e ∈ domain then
          OnlineRamsey.bernoulliWeight
            (unitInterval.toNNReal p : ENNReal) (value e) else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases hed : e ∈ domain <;> simp [hed]
    _ = ∏ e ∈ domain,
        OnlineRamsey.bernoulliWeight
          (unitInterval.toNNReal p : ENNReal) (value e) := by
      symm
      calc
        (∏ e ∈ domain,
            OnlineRamsey.bernoulliWeight
              (unitInterval.toNNReal p : ENNReal) (value e)) =
            ∏ e ∈ domain, if e ∈ domain then
              OnlineRamsey.bernoulliWeight
                (unitInterval.toNNReal p : ENNReal) (value e) else 1 := by
          apply Finset.prod_congr rfl
          intro e he
          simp [he]
        _ = ∏ e ∈ (Finset.univ : Finset E), if e ∈ domain then
              OnlineRamsey.bernoulliWeight
                (unitInterval.toNNReal p : ENNReal) (value e) else 1 := by
          apply Finset.prod_subset (Finset.subset_univ domain)
          intro e heuniv henot
          simp [henot]
        _ = ∏ e : E, if e ∈ domain then
              OnlineRamsey.bernoulliWeight
                (unitInterval.toNNReal p : ENNReal) (value e) else 1 := rfl

/-- The native finite product measure satisfies the exact cylinder law used
by `adaptive_path_mass`.  Consequently, a fresh deterministic adaptive query
path has the same all-bit product law under `bitBoardMeasure` as a fixed list
of coordinates. -/
theorem bitBoardMeasure_bernoulliCylinderLaw {E : Type*} [Fintype E]
    [DecidableEq E] (p : unitInterval) :
    OnlineRamsey.BernoulliCylinderLaw
      (fun A => bitBoardMeasure E p A)
      (OnlineRamsey.bernoulliWeight
        (unitInterval.toNNReal p : ENNReal)) := by
  intro h hnodup
  rw [OnlineRamsey.cylinder_eq_assignmentCylinder h hnodup]
  change bitBoardMeasure E p
    (OnlineRamsey.assignmentCylinder
      (OnlineRamsey.queryFinset h) (OnlineRamsey.transcriptAssignment h)) = _
  rw [measure_assignmentCylinder]
  exact OnlineRamsey.assignment_product_eq_transcriptWeight
    (OnlineRamsey.bernoulliWeight
      (unitInterval.toNNReal p : ENNReal)) h hnodup

/-- Fresh adaptive queries see independent Bernoulli bits under the native
product measure. -/
theorem bitBoardMeasure_adaptive_path_mass {E : Type*} [Fintype E]
    [DecidableEq E] (p : unitInterval) (strategy : OnlineRamsey.Strategy E)
    (bits : List Bool) (hfresh : OnlineRamsey.FreshPath strategy bits) :
    bitBoardMeasure E p (OnlineRamsey.pathEvent strategy bits) =
      (bits.map (OnlineRamsey.bernoulliWeight
        (unitInterval.toNNReal p : ENNReal))).prod := by
  exact OnlineRamsey.adaptive_path_mass
    (fun A => bitBoardMeasure E p A)
    (OnlineRamsey.bernoulliWeight
      (unitInterval.toNNReal p : ENNReal))
    (bitBoardMeasure_bernoulliCylinderLaw p) strategy bits hfresh

/-- The event that the graph extracted from the board has all four uniform
host properties. -/
def randomHostGoodEvent (n M D L pairBound tripleBound : ℕ) :
    Set (Sym2 (Fin n) → Bool) :=
  {ω | HostGood (randomHost n ω) M D L pairBound tripleBound}

/-- The event that at least one member of a finite witness family is entirely
present on the board. -/
def someWitness {E ι : Type*} (W : ι → Finset E) : Set (E → Bool) :=
  ⋃ i, allTrueOn (W i)

theorem measurableSet_someWitness {E ι : Type*} [Fintype E] [Fintype ι]
    (W : ι → Finset E) : MeasurableSet (someWitness W) := by
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_allTrueOn (W i)

/-- Exact witness union bound.  This is the formal version of
`number of witnesses × p^(witness size)`, before replacing the finite sum by a
coarser cardinality estimate. -/
theorem measure_someWitness_le {E ι : Type*} [Fintype E] [Fintype ι]
    (p : unitInterval) (W : ι → Finset E) :
    bitBoardMeasure E p (someWitness W) ≤
      ∑ i : ι, (unitInterval.toNNReal p : ENNReal) ^ (W i).card := by
  calc
    bitBoardMeasure E p (someWitness W) =
        bitBoardMeasure E p (⋃ i, allTrueOn (W i)) := rfl
    _ ≤ ∑ i : ι, bitBoardMeasure E p (allTrueOn (W i)) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ i : ι, (unitInterval.toNNReal p : ENNReal) ^ (W i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact measure_allTrueOn p (W i)

/-- Uniform-size form of `measure_someWitness_le`. -/
theorem measure_someWitness_le_card_mul {E ι : Type*} [Fintype E] [Fintype ι]
    (p : unitInterval) (W : ι → Finset E) (r : ℕ)
    (hcard : ∀ i, (W i).card = r) :
    bitBoardMeasure E p (someWitness W) ≤
      (Fintype.card ι : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ r := by
  calc
    bitBoardMeasure E p (someWitness W) ≤
        ∑ i : ι, (unitInterval.toNNReal p : ENNReal) ^ (W i).card :=
      measure_someWitness_le p W
    _ = (Fintype.card ι : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ r := by
      simp [hcard]

/-! ## Explicit codegree witnesses -/

/-- The finite type of `k`-subsets of `Fin n`.  Using a subtype of
`powersetCard` makes its cardinality formula kernel-transparent. -/
abbrev VertexSubset (n k : ℕ) :=
  ↥((Finset.univ : Finset (Fin n)).powersetCard k)

@[simp]
theorem card_vertexSubset (n k : ℕ) :
    Fintype.card (VertexSubset n k) = Nat.choose n k := by
  rw [Fintype.card_coe, Finset.card_powersetCard]
  simp

/-- A codegree witness consists of a `j`-set of roots and an `R`-set chosen
from its complement. -/
def CodegreeWitness (n j R : ℕ) :=
  Σ S : VertexSubset n j,
    ↥(((Finset.univ : Finset (Fin n)) \ S.1).powersetCard R)

noncomputable instance codegreeWitnessFintype (n j R : ℕ) :
    Fintype (CodegreeWitness n j R) := by
  unfold CodegreeWitness
  infer_instance

/-- The root set of a codegree witness. -/
def codegreeRoots {n j R : ℕ} (w : CodegreeWitness n j R) :
    Finset (Fin n) :=
  w.1.1

/-- The proposed common-neighbor set of a codegree witness. -/
def codegreeTips {n j R : ℕ} (w : CodegreeWitness n j R) :
    Finset (Fin n) :=
  w.2.1

@[simp]
theorem card_codegreeRoots {n j R : ℕ} (w : CodegreeWitness n j R) :
    (codegreeRoots w).card = j :=
  (Finset.mem_powersetCard.mp w.1.2).2

@[simp]
theorem card_codegreeTips {n j R : ℕ} (w : CodegreeWitness n j R) :
    (codegreeTips w).card = R :=
  (Finset.mem_powersetCard.mp w.2.2).2

theorem codegreeTips_subset_compl {n j R : ℕ}
    (w : CodegreeWitness n j R) :
    codegreeTips w ⊆ (Finset.univ : Finset (Fin n)) \ codegreeRoots w :=
  (Finset.mem_powersetCard.mp w.2.2).1

theorem disjoint_codegreeRoots_codegreeTips {n j R : ℕ}
    (w : CodegreeWitness n j R) :
    Disjoint (codegreeRoots w) (codegreeTips w) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hvroot hvtip
  have hvout := codegreeTips_subset_compl w hvtip
  exact (Finset.mem_sdiff.mp hvout).2 hvroot

/-- The codegree witness family has exactly
`choose n j * choose (n-j) R` members. -/
@[simp]
theorem card_codegreeWitness (n j R : ℕ) :
    Fintype.card (CodegreeWitness n j R) =
      Nat.choose n j * Nat.choose (n - j) R := by
  classical
  unfold CodegreeWitness
  rw [Fintype.card_sigma]
  have hfiber : ∀ S : VertexSubset n j,
      Fintype.card
          ↥(((Finset.univ : Finset (Fin n)) \ S.1).powersetCard R) =
        Nat.choose (n - j) R := by
    intro S
    have hSsub : S.1 ⊆ (Finset.univ : Finset (Fin n)) :=
      (Finset.mem_powersetCard.mp S.2).1
    have hScard : S.1.card = j :=
      (Finset.mem_powersetCard.mp S.2).2
    rw [Fintype.card_coe, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset hSsub]
    simp [hScard]
  simp_rw [hfiber]
  simp

/-- The `jR` board coordinates which must all be present for a codegree
witness to occur. -/
def codegreeEdges {n j R : ℕ} (w : CodegreeWitness n j R) :
    Finset (Sym2 (Fin n)) :=
  ((codegreeRoots w).product (codegreeTips w)).image
    (fun vw => s(vw.1, vw.2))

/-- Disjointness of the two vertex classes rules out the only possible
orientation collision in `Sym2`, so a codegree witness has exactly `jR`
distinct required edges. -/
@[simp]
theorem card_codegreeEdges {n j R : ℕ} (w : CodegreeWitness n j R) :
    (codegreeEdges w).card = j * R := by
  have hinj : Set.InjOn
      (fun vw : Fin n × Fin n => s(vw.1, vw.2))
      ↑((codegreeRoots w).product (codegreeTips w)) := by
    intro a ha b hb hab
    rcases Finset.mem_product.mp ha with ⟨haRoot, haTip⟩
    rcases Finset.mem_product.mp hb with ⟨hbRoot, hbTip⟩
    rcases Sym2.eq_iff.mp hab with hsame | hswap
    · exact Prod.ext hsame.1 hsame.2
    · have haTip' : a.1 ∈ codegreeTips w := by
        simpa [hswap.1] using hbTip
      exact False.elim
        ((Finset.disjoint_left.mp
          (disjoint_codegreeRoots_codegreeTips w)) haRoot haTip')
  unfold codegreeEdges
  calc
    (((codegreeRoots w).product (codegreeTips w)).image
        (fun vw => s(vw.1, vw.2))).card =
        ((codegreeRoots w).product (codegreeTips w)).card :=
      Finset.card_image_iff.mpr hinj
    _ = (codegreeRoots w).card * (codegreeTips w).card :=
      Finset.card_product _ _
    _ = j * R := by simp

/-- The event that some `j`-set has at least `R` common neighbors. -/
def codegreeAtLeastEvent (n j R : ℕ) : Set (Sym2 (Fin n) → Bool) :=
  {ω | ∃ S : Finset (Fin n), S.card = j ∧
    R ≤ commonNeighborCount (randomHost n ω) S}

/-- Every codegree failure supplies one of the explicit finite witnesses. -/
theorem codegreeAtLeastEvent_subset_someWitness (n j R : ℕ) :
    codegreeAtLeastEvent n j R ⊆
      someWitness (fun w : CodegreeWitness n j R => codegreeEdges w) := by
  classical
  intro ω hω
  rcases hω with ⟨S, hScard, hR⟩
  let CN : Finset (Fin n) :=
    (commonNeighborSet (randomHost n ω) S).toFinset
  have hCNcard : CN.card = commonNeighborCount (randomHost n ω) S := by
    dsimp [CN, commonNeighborCount]
    exact (Set.ncard_eq_toFinset_card'
      (commonNeighborSet (randomHost n ω) S)).symm
  have hR' : R ≤ CN.card := by
    rwa [hCNcard]
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hR'
  have hWout : W ⊆ (Finset.univ : Finset (Fin n)) \ S := by
    intro v hvW
    have hvCNfin : v ∈ CN := hWsub hvW
    have hvCN : v ∈ commonNeighborSet (randomHost n ω) S := by
      simpa [CN] using hvCNfin
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, ?_⟩
    intro hvS
    exact (randomHost n ω).loopless v (hvCN v hvS)
  let root : VertexSubset n j :=
    ⟨S, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S, hScard⟩⟩
  let tips :
      ↥(((Finset.univ : Finset (Fin n)) \ root.1).powersetCard R) :=
    ⟨W, Finset.mem_powersetCard.mpr
      ⟨by simpa [root] using hWout, hWcard⟩⟩
  let witness : CodegreeWitness n j R := ⟨root, tips⟩
  change ω ∈ ⋃ i : CodegreeWitness n j R, allTrueOn (codegreeEdges i)
  refine Set.mem_iUnion.mpr ⟨witness, ?_⟩
  rw [mem_allTrueOn_iff]
  intro e he
  unfold codegreeEdges at he
  rcases Finset.mem_image.mp he with ⟨vw, hvw, rfl⟩
  rcases Finset.mem_product.mp hvw with ⟨hvRoot, hvTip⟩
  have hvS : vw.1 ∈ S := by
    simpa [codegreeRoots, witness, root] using hvRoot
  have hvW : vw.2 ∈ W := by
    simpa [codegreeTips, witness, tips] using hvTip
  have hvCNfin : vw.2 ∈ CN := hWsub hvW
  have hvCN : vw.2 ∈ commonNeighborSet (randomHost n ω) S := by
    simpa [CN] using hvCNfin
  exact ((randomHost_adj n ω vw.1 vw.2).mp (hvCN vw.1 hvS)).1

/-- Exact union bound for the explicit codegree witness family. -/
theorem measure_someCodegreeWitness_le (n j R : ℕ) (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (someWitness (fun w : CodegreeWitness n j R => codegreeEdges w)) ≤
      (Nat.choose n j * Nat.choose (n - j) R : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ (j * R) := by
  have h := measure_someWitness_le_card_mul p
    (fun w : CodegreeWitness n j R => codegreeEdges w) (j * R)
    (fun w => card_codegreeEdges w)
  simpa using h

/-- The finite non-asymptotic codegree tail used for `j=2` and `j=3`:

`P[Δ_j(G(n,p)) ≥ R] ≤ choose(n,j) choose(n-j,R) p^(jR)`. -/
theorem measure_codegreeAtLeastEvent_le (n j R : ℕ) (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p (codegreeAtLeastEvent n j R) ≤
      (Nat.choose n j * Nat.choose (n - j) R : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ (j * R) := by
  calc
    bitBoardMeasure (Sym2 (Fin n)) p (codegreeAtLeastEvent n j R) ≤
        bitBoardMeasure (Sym2 (Fin n)) p
          (someWitness
            (fun w : CodegreeWitness n j R => codegreeEdges w)) :=
      measure_mono (codegreeAtLeastEvent_subset_someWitness n j R)
    _ ≤ (Nat.choose n j * Nat.choose (n - j) R : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ (j * R) :=
      measure_someCodegreeWitness_le n j R p

/-! ## Fixed-size dense-set witnesses -/

/-- All unordered non-loop pairs spanned by the vertex set `U`, obtained by
mapping the edge finset of the complete graph on the finite subtype `U` into
the ambient vertex type. -/
def spannedPairs {n : ℕ} (U : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  ((⊤ : SimpleGraph U).edgeFinset).map
    (Function.Embedding.subtype (fun v : Fin n => v ∈ U)).sym2Map

@[simp]
theorem pair_mem_spannedPairs {n : ℕ} (U : Finset (Fin n))
    (v w : Fin n) :
    s(v, w) ∈ spannedPairs U ↔ v ≠ w ∧ v ∈ U ∧ w ∈ U := by
  classical
  simp only [spannedPairs, Finset.mem_map, SimpleGraph.edgeFinset_top,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.sym2Map_apply]
  constructor
  · rintro ⟨a, hdiag, hmap⟩
    induction a using Sym2.inductionOn with
    | _ x y =>
      have hxy : x ≠ y := Sym2.mk_isDiag_iff.not.mp hdiag
      rw [Sym2.map_pair_eq] at hmap
      rcases Sym2.eq_iff.mp hmap with hsame | hswap
      · rcases hsame with ⟨hx, hy⟩
        subst v
        subst w
        exact ⟨fun h => hxy (Subtype.ext h), x.2, y.2⟩
      · rcases hswap with ⟨hx, hy⟩
        subst w
        subst v
        exact ⟨fun h => hxy (Subtype.ext h.symm), y.2, x.2⟩
  · rintro ⟨hvw, hv, hw⟩
    refine ⟨s(⟨v, hv⟩, ⟨w, hw⟩), ?_, ?_⟩
    · exact Sym2.mk_isDiag_iff.not.mpr fun h =>
        hvw (congrArg Subtype.val h)
    · simp [Sym2.map_pair_eq]

/-- A `k`-vertex set spans exactly `choose k 2` possible graph edges. -/
@[simp]
theorem card_spannedPairs {n : ℕ} (U : Finset (Fin n)) :
    (spannedPairs U).card = Nat.choose U.card 2 := by
  classical
  unfold spannedPairs
  rw [Finset.card_map,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_coe]

/-- The present graph edges spanned by `U`, expressed in the native board
sample space. -/
def presentSpannedEdges {n : ℕ} (ω : Sym2 (Fin n) → Bool)
    (U : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (spannedPairs U).filter fun e => ω e = true

@[simp]
theorem pair_mem_presentSpannedEdges {n : ℕ}
    (ω : Sym2 (Fin n) → Bool) (U : Finset (Fin n)) (v w : Fin n) :
    s(v, w) ∈ presentSpannedEdges ω U ↔
      v ∈ U ∧ w ∈ U ∧ (randomHost n ω).Adj v w := by
  simp [presentSpannedEdges, randomHost_adj, and_assoc, and_left_comm, and_comm]

/-- The board-native finset count agrees with the graph-theoretic number of
edges spanned by `U`. -/
@[simp]
theorem card_presentSpannedEdges {n : ℕ}
    (ω : Sym2 (Fin n) → Bool) (U : Finset (Fin n)) :
    (presentSpannedEdges ω U).card = edgesSpanned (randomHost n ω) U := by
  classical
  unfold edgesSpanned
  rw [← Set.ncard_coe_finset]
  apply congrArg Set.ncard
  ext e
  induction e using Sym2.inductionOn
  simp [presentSpannedEdges, randomHost_adj,
    and_assoc, and_left_comm, and_comm]

/-- A dense-set witness is a `k`-set of vertices together with `r` of the
possible edges spanned by it. -/
def SpannedEdgeWitness (n k r : ℕ) :=
  Σ U : VertexSubset n k,
    ↥((spannedPairs U.1).powersetCard r)

noncomputable instance spannedEdgeWitnessFintype (n k r : ℕ) :
    Fintype (SpannedEdgeWitness n k r) := by
  unfold SpannedEdgeWitness
  infer_instance

/-- The vertex set of a fixed-size dense-set witness. -/
def spannedWitnessVertices {n k r : ℕ}
    (w : SpannedEdgeWitness n k r) : Finset (Fin n) :=
  w.1.1

/-- The `r` board coordinates required by a fixed-size dense-set witness. -/
def spannedWitnessEdges {n k r : ℕ}
    (w : SpannedEdgeWitness n k r) : Finset (Sym2 (Fin n)) :=
  w.2.1

@[simp]
theorem card_spannedWitnessVertices {n k r : ℕ}
    (w : SpannedEdgeWitness n k r) :
    (spannedWitnessVertices w).card = k :=
  (Finset.mem_powersetCard.mp w.1.2).2

@[simp]
theorem card_spannedWitnessEdges {n k r : ℕ}
    (w : SpannedEdgeWitness n k r) :
    (spannedWitnessEdges w).card = r :=
  (Finset.mem_powersetCard.mp w.2.2).2

theorem spannedWitnessEdges_subset {n k r : ℕ}
    (w : SpannedEdgeWitness n k r) :
    spannedWitnessEdges w ⊆ spannedPairs (spannedWitnessVertices w) :=
  (Finset.mem_powersetCard.mp w.2.2).1

/-- There are exactly
`choose n k * choose (choose k 2) r` fixed-size dense-set witnesses. -/
@[simp]
theorem card_spannedEdgeWitness (n k r : ℕ) :
    Fintype.card (SpannedEdgeWitness n k r) =
      Nat.choose n k * Nat.choose (Nat.choose k 2) r := by
  classical
  unfold SpannedEdgeWitness
  rw [Fintype.card_sigma]
  have hfiber : ∀ U : VertexSubset n k,
      Fintype.card ↥((spannedPairs U.1).powersetCard r) =
        Nat.choose (Nat.choose k 2) r := by
    intro U
    rw [Fintype.card_coe, Finset.card_powersetCard, card_spannedPairs]
    rw [(Finset.mem_powersetCard.mp U.2).2]
  simp_rw [hfiber]
  simp

/-- The event that some `k`-vertex set spans at least `r` present graph
edges. -/
def spannedEdgeAtLeastEvent (n k r : ℕ) :
    Set (Sym2 (Fin n) → Bool) :=
  {ω | ∃ U : Finset (Fin n), U.card = k ∧
    r ≤ edgesSpanned (randomHost n ω) U}

/-- Every fixed-size dense-set failure supplies an explicit set of `r`
present spanned edges. -/
theorem spannedEdgeAtLeastEvent_subset_someWitness (n k r : ℕ) :
    spannedEdgeAtLeastEvent n k r ⊆
      someWitness
        (fun w : SpannedEdgeWitness n k r => spannedWitnessEdges w) := by
  classical
  intro ω hω
  rcases hω with ⟨U, hUcard, hr⟩
  have hr' : r ≤ (presentSpannedEdges ω U).card := by
    simpa using hr
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hr'
  have hRspanned : R ⊆ spannedPairs U := by
    intro e heR
    exact (Finset.mem_filter.mp (hRsub heR)).1
  let vertices : VertexSubset n k :=
    ⟨U, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ U, hUcard⟩⟩
  let edges : ↥((spannedPairs vertices.1).powersetCard r) :=
    ⟨R, Finset.mem_powersetCard.mpr
      ⟨by simpa [vertices] using hRspanned, hRcard⟩⟩
  let witness : SpannedEdgeWitness n k r := ⟨vertices, edges⟩
  change ω ∈ ⋃ i : SpannedEdgeWitness n k r,
    allTrueOn (spannedWitnessEdges i)
  refine Set.mem_iUnion.mpr ⟨witness, ?_⟩
  rw [mem_allTrueOn_iff]
  intro e he
  have heR : e ∈ R := by
    simpa [spannedWitnessEdges, witness, edges] using he
  exact (Finset.mem_filter.mp (hRsub heR)).2

/-- Exact witness union bound before identifying the bad graph event. -/
theorem measure_someSpannedEdgeWitness_le (n k r : ℕ)
    (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (someWitness
          (fun w : SpannedEdgeWitness n k r => spannedWitnessEdges w)) ≤
      (Nat.choose n k * Nat.choose (Nat.choose k 2) r : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ r := by
  have h := measure_someWitness_le_card_mul p
    (fun w : SpannedEdgeWitness n k r => spannedWitnessEdges w) r
    (fun w => card_spannedWitnessEdges w)
  simpa using h

/-- Generic finite dense-set estimate, specializing to both the dense range
in Lemma 3.2 and the small-set range in Lemma 3.3:

`P[∃ U, |U|=k, e(U)≥r] ≤ choose(n,k) choose(choose(k,2),r) p^r`. -/
theorem measure_spannedEdgeAtLeastEvent_le (n k r : ℕ)
    (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (spannedEdgeAtLeastEvent n k r) ≤
      (Nat.choose n k * Nat.choose (Nat.choose k 2) r : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ r := by
  calc
    bitBoardMeasure (Sym2 (Fin n)) p
        (spannedEdgeAtLeastEvent n k r) ≤
      bitBoardMeasure (Sym2 (Fin n)) p
        (someWitness
          (fun w : SpannedEdgeWitness n k r => spannedWitnessEdges w)) :=
      measure_mono (spannedEdgeAtLeastEvent_subset_someWitness n k r)
    _ ≤ (Nat.choose n k * Nat.choose (Nat.choose k 2) r : ENNReal) *
        (unitInterval.toNNReal p : ENNReal) ^ r :=
      measure_someSpannedEdgeWitness_le n k r p

/-! ## Finite degeneracy-witness union bound -/

/-- The union of the fixed-size spanned-edge events over a finite set of
allowed vertex-set sizes, with a size-dependent edge threshold. -/
def spannedEdgeAtLeastInSizesEvent (n : ℕ) (sizes : Finset ℕ)
    (threshold : ℕ → ℕ) : Set (Sym2 (Fin n) → Bool) :=
  ⋃ k ∈ sizes, spannedEdgeAtLeastEvent n k (threshold k)

/-- Sum the generic fixed-size witness estimate over any finite collection of
sizes. -/
theorem measure_spannedEdgeAtLeastInSizesEvent_le (n : ℕ)
    (sizes : Finset ℕ) (threshold : ℕ → ℕ) (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (spannedEdgeAtLeastInSizesEvent n sizes threshold) ≤
      ∑ k ∈ sizes,
        (Nat.choose n k * Nat.choose (Nat.choose k 2) (threshold k) : ENNReal) *
          (unitInterval.toNNReal p : ENNReal) ^ threshold k := by
  unfold spannedEdgeAtLeastInSizesEvent
  calc
    bitBoardMeasure (Sym2 (Fin n)) p
        (⋃ k ∈ sizes, spannedEdgeAtLeastEvent n k (threshold k)) ≤
      ∑ k ∈ sizes,
        bitBoardMeasure (Sym2 (Fin n)) p
          (spannedEdgeAtLeastEvent n k (threshold k)) :=
      measure_biUnion_finset_le sizes
        (fun k => spannedEdgeAtLeastEvent n k (threshold k))
    _ ≤ ∑ k ∈ sizes,
        (Nat.choose n k * Nat.choose (Nat.choose k 2) (threshold k) : ENNReal) *
          (unitInterval.toNNReal p : ENNReal) ^ threshold k := by
      apply Finset.sum_le_sum
      intro k hk
      exact measure_spannedEdgeAtLeastEvent_le n k (threshold k) p

/-- The host contains a degeneracy obstruction of a size compatible with an
`M`-edge graph: a set `U` with `D+1 ≤ |U| ≤ floor(2M/D)` and at least
`ceil(D|U|/2)` spanned host edges.

The deterministic peeling argument shows that every graph with at most `M`
edges which is not `(D-1)`-degenerate supplies such a set.  That graph-theoretic
implication is deliberately kept separate from this probability event. -/
def degeneracyWitnessFailureEvent (n M D : ℕ) :
    Set (Sym2 (Fin n) → Bool) :=
  {ω | ∃ U : Finset (Fin n),
    D + 1 ≤ U.card ∧ U.card ≤ 2 * M / D ∧
      D * U.card ⌈/⌉ 2 ≤ edgesSpanned (randomHost n ω) U}

/-- A degeneracy obstruction lies in the union of its fixed-cardinality
witness events. -/
theorem degeneracyWitnessFailureEvent_subset_sizesUnion (n M D : ℕ) :
    degeneracyWitnessFailureEvent n M D ⊆
      spannedEdgeAtLeastInSizesEvent n
        (Finset.Icc (D + 1) (2 * M / D))
        (fun k => D * k ⌈/⌉ 2) := by
  intro ω hω
  rcases hω with ⟨U, hlo, hhi, hedge⟩
  change ω ∈ ⋃ k ∈ Finset.Icc (D + 1) (2 * M / D),
    spannedEdgeAtLeastEvent n k (D * k ⌈/⌉ 2)
  refine Set.mem_iUnion.mpr ⟨U.card, ?_⟩
  refine Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, ?_⟩
  exact ⟨U, rfl, hedge⟩

/-- The exact finite union bound from the degeneracy witness audit:

`P[∃ U, D+1≤|U|≤⌊2M/D⌋, e(U)≥⌈D|U|/2⌉]`

is at most the sum, over the indicated sizes `k`, of

`choose(n,k) choose(choose(k,2),ceil(Dk/2)) p^ceil(Dk/2)`. -/
theorem measure_degeneracyWitnessFailureEvent_le (n M D : ℕ)
    (p : unitInterval) :
    bitBoardMeasure (Sym2 (Fin n)) p
        (degeneracyWitnessFailureEvent n M D) ≤
      ∑ k ∈ Finset.Icc (D + 1) (2 * M / D),
        (Nat.choose n k *
            Nat.choose (Nat.choose k 2) (D * k ⌈/⌉ 2) : ENNReal) *
          (unitInterval.toNNReal p : ENNReal) ^ (D * k ⌈/⌉ 2) := by
  calc
    bitBoardMeasure (Sym2 (Fin n)) p
        (degeneracyWitnessFailureEvent n M D) ≤
      bitBoardMeasure (Sym2 (Fin n)) p
        (spannedEdgeAtLeastInSizesEvent n
          (Finset.Icc (D + 1) (2 * M / D))
          (fun k => D * k ⌈/⌉ 2)) :=
      measure_mono (degeneracyWitnessFailureEvent_subset_sizesUnion n M D)
    _ ≤ ∑ k ∈ Finset.Icc (D + 1) (2 * M / D),
        (Nat.choose n k *
            Nat.choose (Nat.choose k 2) (D * k ⌈/⌉ 2) : ENNReal) *
          (unitInterval.toNNReal p : ENNReal) ^ (D * k ⌈/⌉ 2) :=
      measure_spannedEdgeAtLeastInSizesEvent_le n
        (Finset.Icc (D + 1) (2 * M / D))
        (fun k => D * k ⌈/⌉ 2) p

/-! ## Reusable finite union bounds -/

/-- Union bound for a finite indexed family of events. -/
theorem measure_iUnion_le_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E : ι → Set Ω) :
    μ (⋃ i, E i) ≤ ∑ i : ι, μ (E i) :=
  measure_iUnion_fintype_le μ E

/-- Union bound when every event has the same upper bound. -/
theorem measure_iUnion_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) (E : ι → Set Ω) (δ : ENNReal)
    (hE : ∀ i, μ (E i) ≤ δ) :
    μ (⋃ i, E i) ≤ (Fintype.card ι : ENNReal) * δ := by
  calc
    μ (⋃ i, E i) ≤ ∑ i : ι, μ (E i) := measure_iUnion_le_sum μ E
    _ ≤ ∑ _i : ι, δ := by
      apply Finset.sum_le_sum
      intro i hi
      exact hE i
    _ = (Fintype.card ι : ENNReal) * δ := by simp

/-- Failure probability when a good event is the intersection of finitely many
component events. -/
theorem measure_compl_iInter_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) (E : ι → Set Ω) (δ : ENNReal)
    (hE : ∀ i, μ (E i)ᶜ ≤ δ) :
    μ (⋂ i, E i)ᶜ ≤ (Fintype.card ι : ENNReal) * δ := by
  rw [compl_iInter]
  exact measure_iUnion_le_card_mul μ (fun i => (E i)ᶜ) δ hE

/-- Combining the random-host failure event with the separate edge-count
failure event. -/
theorem measure_union_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) (a b : ENNReal)
    (hA : μ A ≤ a) (hB : μ B ≤ b) :
    μ (A ∪ B) ≤ a + b := by
  calc
    μ (A ∪ B) ≤ μ A + μ B := measure_union_le A B
    _ ≤ a + b := add_le_add hA hB

/-! ## Truncating an expectation on a rare bad event -/

/-- If a nonnegative random quantity is bounded by `A` on a measurable good
event and by `B` everywhere, its expectation is at most
`A + B * P[bad]`.  The statement is made for the lower integral, so no
integrability hypothesis is needed and natural-valued copy counts can be
inserted by coercion to `ENNReal`. -/
theorem lintegral_le_good_add_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ENNReal)
    (G : Set Ω) (A B : ENNReal) (hG : MeasurableSet G)
    (hgood : ∀ ω ∈ G, X ω ≤ A) (hglobal : ∀ ω, X ω ≤ B) :
    (∫⁻ ω, X ω ∂μ) ≤ A + B * μ Gᶜ := by
  calc
    (∫⁻ ω, X ω ∂μ) ≤
        ∫⁻ ω, G.indicator (fun _ => A) ω +
          Gᶜ.indicator (fun _ => B) ω ∂μ := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ G
      · simpa [hω] using hgood ω hω
      · simpa [hω] using hglobal ω
    _ = A * μ G + B * μ Gᶜ := by
      rw [lintegral_add_left (measurable_const.indicator hG),
        lintegral_indicator_const hG, lintegral_indicator_const hG.compl]
    _ ≤ A + B * μ Gᶜ :=
      add_le_add_right (mul_le_of_le_one_right bot_le prob_le_one) _

/-! ## The asymptotic fact used after concentration -/

/-- Exponential decay beats every real power at infinity.  The paper applies
this after substituting a positive power of `p⁻¹` for `x`. -/
theorem exponential_isLittleO_every_rpow (c : ℝ) (hc : 0 < c) (K : ℝ) :
    (fun x : ℝ => Real.exp (-c * x)) =o[atTop]
      (fun x : ℝ => x ^ (-K)) :=
  isLittleO_exp_neg_mul_rpow_atTop hc (-K)

end OnlineRamsey.RandomBoard
