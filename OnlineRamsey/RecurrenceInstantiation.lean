import OnlineRamsey.AdaptiveTail
import OnlineRamsey.AsymptoticScale
import OnlineRamsey.PrefixSoundness
import OnlineRamsey.QueryComplexity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# A finite semantics for the prefix recurrence

This file defines the actual finite expectation of labelled prefix embeddings
along a fresh adaptive query tree.  Probabilities are finite sums over Boolean
answer vectors, so no measurability or integrability hypotheses are hidden.

The embedding representation is tailored to the six-vertex bit-mask patterns
used by `PrefixSoundness`: inactive labels are sent to a fixed dummy vertex,
active labels are injective, and every selected mask edge must occur positively
in the replayed transcript.  The dummy convention gives a fixed finite function
type while retaining the correct number of choices for isolated active labels.
-/

open scoped BigOperators NNReal ENNReal
open Filter Topology

namespace OnlineRamsey.RecurrenceInstantiation

open PrefixSoundness QueryComplexity

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Exact finite answer-vector expectation -/

/-- Bernoulli coordinate weights in `NNReal`. -/
def nnBernoulliWeight (p : ℝ≥0) : Bool → ℝ≥0
  | false => 1 - p
  | true => p

@[simp] theorem nnBernoulliWeight_false (p : ℝ≥0) :
    nnBernoulliWeight p false = 1 - p := rfl

@[simp] theorem nnBernoulliWeight_true (p : ℝ≥0) :
    nnBernoulliWeight p true = p := rfl

theorem sum_nnBernoulliWeight (p : ℝ≥0) (hp : p ≤ 1) :
    (∑ bit : Bool, nnBernoulliWeight p bit) = 1 := by
  simpa [nnBernoulliWeight, add_comm] using (tsub_add_cancel_of_le hp)

/-- A length-`N` answer vector, indexed in chronological order. -/
abbrev AnswerPath (N : ℕ) := Fin N → Bool

/-- Product Bernoulli mass of one complete answer vector. -/
def answerPathWeight (p : ℝ≥0) {N : ℕ} (bits : AnswerPath N) : ℝ≥0 :=
  ∏ i, nnBernoulliWeight p (bits i)

theorem sum_answerPathWeight (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    (∑ bits : AnswerPath N, answerPathWeight p bits) = 1 := by
  rw [show (∑ bits : AnswerPath N, answerPathWeight p bits) =
      ∏ _i : Fin N, ∑ bit : Bool, nnBernoulliWeight p bit by
        simpa [answerPathWeight] using
          (Fintype.prod_sum
            (fun (_i : Fin N) (bit : Bool) ↦ nnBernoulliWeight p bit)).symm]
  rw [sum_nnBernoulliWeight p hp]
  simp

/-- Convert the chronological function vector to the newest-first list used
by `replay`.  Reversal changes no product mass and makes index `0` the first
answer revealed by the strategy. -/
def answerList {N : ℕ} (bits : AnswerPath N) : List Bool :=
  (List.ofFn bits).reverse

@[simp] theorem length_answerList {N : ℕ} (bits : AnswerPath N) :
    (answerList bits).length = N := by
  simp [answerList]

/-- Equivalence between chronological function vectors and the newest-first
list vectors consumed by `replay`. -/
def answerPathVectorEquiv (n : ℕ) : AnswerPath n ≃ List.Vector Bool n where
  toFun bits := (List.Vector.ofFn bits).reverse
  invFun bits := bits.reverse.get
  left_inv bits := by
    funext i
    change ((List.Vector.ofFn bits).reverse.reverse).get i = bits i
    rw [List.Vector.reverse_reverse]
    simp
  right_inv bits := by
    change (List.Vector.ofFn bits.reverse.get).reverse = bits
    rw [List.Vector.ofFn_get, List.Vector.reverse_reverse]

@[simp] theorem answerPathVectorEquiv_apply_toList {n : ℕ}
    (bits : AnswerPath n) :
    (answerPathVectorEquiv n bits).toList = answerList bits := by
  rw [show answerPathVectorEquiv n bits =
    (List.Vector.ofFn bits).reverse by rfl]
  rw [List.Vector.toList_reverse, List.Vector.toList_ofFn]
  rfl

/-- Product Bernoulli mass written on a newest-first list vector. -/
def vectorWeight (p : ℝ≥0) {n : ℕ} (bits : List.Vector Bool n) : ℝ≥0 :=
  (bits.toList.map (nnBernoulliWeight p)).prod

@[simp] theorem vectorWeight_answerPathVectorEquiv (p : ℝ≥0) {n : ℕ}
    (bits : AnswerPath n) :
    vectorWeight p (answerPathVectorEquiv n bits) = answerPathWeight p bits := by
  rw [vectorWeight, answerPathVectorEquiv_apply_toList]
  rw [answerList, List.map_reverse, List.prod_reverse, List.map_ofFn,
    List.prod_ofFn]
  rfl

theorem answerPath_weighted_sum_eq_vectorSum (p : ℝ≥0) (n : ℕ)
    (f : List Bool → ℝ≥0) :
    (∑ bits : AnswerPath n,
        answerPathWeight p bits * f (answerList bits)) =
      ∑ bits : List.Vector Bool n,
        vectorWeight p bits * f bits.toList := by
  apply Fintype.sum_equiv (answerPathVectorEquiv n)
  intro bits
  rw [vectorWeight_answerPathVectorEquiv,
    answerPathVectorEquiv_apply_toList]

@[simp] theorem vectorWeight_cons (p : ℝ≥0) {n : ℕ} (bit : Bool)
    (tail : List.Vector Bool n) :
    vectorWeight p (bit ::ᵥ tail) =
      nnBernoulliWeight p bit * vectorWeight p tail := by
  simp [vectorWeight]

/-- Splitting a nonempty newest-first vector into its head and tail. -/
def vectorConsEquiv (n : ℕ) :
    Bool × List.Vector Bool n ≃ List.Vector Bool (n + 1) where
  toFun pair := pair.1 ::ᵥ pair.2
  invFun bits := (bits.head, bits.tail)
  left_inv pair := by
    rcases pair with ⟨bit, bits⟩
    rfl
  right_inv bits := List.Vector.cons_head_tail bits

theorem sum_vector_succ {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : List.Vector Bool (n + 1) → M) :
    (∑ bits : List.Vector Bool (n + 1), f bits) =
      ∑ bit : Bool, ∑ tail : List.Vector Bool n, f (bit ::ᵥ tail) := by
  calc
    (∑ bits : List.Vector Bool (n + 1), f bits) =
        ∑ pair : Bool × List.Vector Bool n, f ((vectorConsEquiv n) pair) :=
      (Equiv.sum_comp (vectorConsEquiv n) f).symm
    _ = ∑ bit : Bool, ∑ tail : List.Vector Bool n, f (bit ::ᵥ tail) :=
      Fintype.sum_prod_type _

theorem weighted_vector_sum_succ (p : ℝ≥0) (n : ℕ)
    (f : List Bool → ℝ≥0) :
    (∑ bits : List.Vector Bool (n + 1),
        vectorWeight p bits * f bits.toList) =
      ∑ bit : Bool, ∑ tail : List.Vector Bool n,
        (nnBernoulliWeight p bit * vectorWeight p tail) *
          f (bit :: tail.toList) := by
  rw [sum_vector_succ]
  simp only [vectorWeight_cons, List.Vector.toList_cons]

/-! ## The six-label mask embedding count -/

/-- Active labels of a finite mask pattern. -/
def activeLabels (H : K6FinitePattern) : Finset (Fin 6) :=
  Finset.univ.filter fun v ↦ H.vertices.1.testBit v.1 = true

@[simp] theorem mem_activeLabels (H : K6FinitePattern) (v : Fin 6) :
    v ∈ activeLabels H ↔ H.vertices.1.testBit v.1 = true := by
  simp [activeLabels]

private theorem card_activeLabels_aux : ∀ vertices : Fin K6Prefix.vertexSetCount,
    (Finset.univ.filter
      (fun v : Fin 6 ↦ vertices.1.testBit v.1 = true)).card =
      K6Prefix.countBits K6Prefix.vertexCount vertices.1 := by
  native_decide

theorem card_activeLabels (H : K6FinitePattern) :
    (activeLabels H).card = k6FinitePrefixSystem.vertexCount H := by
  exact card_activeLabels_aux H.vertices

/-- Lower endpoint of one of the fifteen fixed edge positions. -/
def edgeLo (e : K6Edge) : Fin 6 :=
  ⟨(K6Prefix.edgePairs[e.1]!).1, by
    have : ∀ i : Fin K6Prefix.edgeCount,
        (K6Prefix.edgePairs[i.1]!).1 < 6 := by native_decide
    exact this e⟩

/-- Upper endpoint of one of the fifteen fixed edge positions. -/
def edgeHi (e : K6Edge) : Fin 6 :=
  ⟨(K6Prefix.edgePairs[e.1]!).2, by
    have : ∀ i : Fin K6Prefix.edgeCount,
        (K6Prefix.edgePairs[i.1]!).2 < 6 := by native_decide
    exact this e⟩

theorem edgeLo_lt_edgeHi (e : K6Edge) : edgeLo e < edgeHi e := by
  fin_cases e <;> decide

private theorem active_erasePair_aux :
    ∀ (vertices : Fin K6Prefix.vertexSetCount) (e : K6Edge) (v : Fin 6),
      edgeAllowedBy vertices.1 e = true →
      ((erasePairVertices vertices e).1.testBit v.1 = true ↔
        vertices.1.testBit v.1 = true ∧ v ≠ edgeLo e ∧ v ≠ edgeHi e) := by
  native_decide

theorem mem_activeLabels_eraseFinitePair (H : K6FinitePattern)
    (e : K6Edge) (hallowed : edgeAllowedBy H.vertices.1 e = true) (v : Fin 6) :
    v ∈ activeLabels (eraseFinitePair H e) ↔
      v ∈ activeLabels H ∧ v ≠ edgeLo e ∧ v ≠ edgeHi e := by
  simpa [eraseFinitePair, mem_activeLabels] using
    active_erasePair_aux H.vertices e v hallowed

private theorem edgeAllowedBy_aux :
    ∀ (vertices : Fin K6Prefix.vertexSetCount) (e : K6Edge),
      edgeAllowedBy vertices.1 e = true ↔
        vertices.1.testBit (edgeLo e).1 = true ∧
          vertices.1.testBit (edgeHi e).1 = true := by
  native_decide

theorem edgeAllowedBy_iff_mem_activeLabels (H : K6FinitePattern) (e : K6Edge) :
    edgeAllowedBy H.vertices.1 e = true ↔
      edgeLo e ∈ activeLabels H ∧ edgeHi e ∈ activeLabels H := by
  simpa [mem_activeLabels] using edgeAllowedBy_aux H.vertices e

/-- The canonical dummy target used for inactive labels. -/
def dummyVertex {N : ℕ} (hN : 0 < N) : Vertex N :=
  ⟨0, by omega⟩

/-- Reset the two endpoints deleted by a pair recurrence to the canonical
inactive-label value. -/
def resetPair {N : ℕ} (hN : 0 < N) (e : K6Edge)
    (f : Fin 6 → Vertex N) : Fin 6 → Vertex N :=
  fun v ↦ if v = edgeLo e ∨ v = edgeHi e then dummyVertex hN else f v

theorem resetPair_of_ne {N : ℕ} (hN : 0 < N) (e : K6Edge)
    (f : Fin 6 → Vertex N) (v : Fin 6)
    (hlo : v ≠ edgeLo e) (hhi : v ≠ edgeHi e) :
    resetPair hN e f v = f v := by
  simp [resetPair, hlo, hhi]

theorem resetPair_edgeLo {N : ℕ} (hN : 0 < N) (e : K6Edge)
    (f : Fin 6 → Vertex N) :
    resetPair hN e f (edgeLo e) = dummyVertex hN := by
  simp [resetPair]

theorem resetPair_edgeHi {N : ℕ} (hN : 0 < N) (e : K6Edge)
    (f : Fin 6 → Vertex N) :
    resetPair hN e f (edgeHi e) = dummyVertex hN := by
  simp [resetPair]

/-- A total six-label map is canonical when inactive labels are sent to the
dummy vertex. -/
def CanonicalMap {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (f : Fin 6 → Vertex N) : Prop :=
  ∀ v, v ∉ activeLabels H → f v = dummyVertex hN

/-- Every selected edge has both endpoints in the active vertex mask.  Invalid
bit-mask states occur in the ambient finite type but do not denote graphs. -/
def ValidPattern (H : K6FinitePattern) : Prop :=
  ∀ e ∈ H.edges, edgeAllowedBy H.vertices.1 e = true

/-- Predicate saying that `f` is a labelled embedding of the active mask
pattern in the positive graph of `h`. -/
def IsPrefixEmbedding {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (h : Transcript (Query N)) (f : Fin 6 → Vertex N) : Prop :=
  ValidPattern H ∧
  CanonicalMap hN H f ∧
    Set.InjOn f (activeLabels H : Set (Fin 6)) ∧
      ∀ e ∈ H.edges,
        (positiveGraph h).Adj (f (edgeLo e)) (f (edgeHi e))

theorem resetPair_isPrefixEmbedding {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (h : Transcript (Query N)) (e : K6Edge)
    (f : Fin 6 → Vertex N) (hf : IsPrefixEmbedding hN H h f)
    (he : e ∈ H.edges) :
    IsPrefixEmbedding hN (eraseFinitePair H e) h (resetPair hN e f) := by
  have hallowed : edgeAllowedBy H.vertices.1 e = true := hf.1 e he
  have hactive := (edgeAllowedBy_iff_mem_activeLabels H e).mp hallowed
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    have hd' : d ∈ (H.edges.erase e).filter
        (fun x ↦ edgeAllowedBy (erasePairVertices H.vertices e).1 x = true) := by
      simpa [eraseFinitePair] using hd
    exact (Finset.mem_filter.mp hd').2
  · intro v hv
    rw [mem_activeLabels_eraseFinitePair H e hallowed] at hv
    simp only [not_and_or] at hv
    rcases hv with hv | hv | hv
    · have hparentInactive : v ∉ activeLabels H := hv
      by_cases hlo : v = edgeLo e
      · subst v
        exact resetPair_edgeLo hN e f
      · by_cases hhi : v = edgeHi e
        · subst v
          exact resetPair_edgeHi hN e f
        · rw [resetPair_of_ne hN e f v hlo hhi]
          exact hf.2.1 v hparentInactive
    · by_cases hlo : v = edgeLo e
      · subst v
        exact resetPair_edgeLo hN e f
      · contradiction
    · by_cases hhi : v = edgeHi e
      · subst v
        exact resetPair_edgeHi hN e f
      · contradiction
  · intro u hu v hv huv
    have hu' := (mem_activeLabels_eraseFinitePair H e hallowed u).mp hu
    have hv' := (mem_activeLabels_eraseFinitePair H e hallowed v).mp hv
    rw [resetPair_of_ne hN e f u hu'.2.1 hu'.2.2,
      resetPair_of_ne hN e f v hv'.2.1 hv'.2.2] at huv
    exact hf.2.2.1 hu'.1 hv'.1 huv
  · intro d hd
    have hd' : d ∈ (H.edges.erase e).filter
        (fun x ↦ edgeAllowedBy (erasePairVertices H.vertices e).1 x = true) := by
      simpa [eraseFinitePair] using hd
    have hderase : d ∈ H.edges.erase e := (Finset.mem_filter.mp hd').1
    have hdH : d ∈ H.edges := (Finset.mem_erase.mp hderase).2
    have hdallowed :
        edgeAllowedBy (erasePairVertices H.vertices e).1 d = true :=
      (Finset.mem_filter.mp hd').2
    have hdactive :=
      (edgeAllowedBy_iff_mem_activeLabels (eraseFinitePair H e) d).mp (by
        simpa [eraseFinitePair] using hdallowed)
    have hlo := (mem_activeLabels_eraseFinitePair H e hallowed (edgeLo d)).mp
      hdactive.1
    have hhi := (mem_activeLabels_eraseFinitePair H e hallowed (edgeHi d)).mp
      hdactive.2
    rw [resetPair_of_ne hN e f (edgeLo d) hlo.2.1 hlo.2.2,
      resetPair_of_ne hN e f (edgeHi d) hhi.2.1 hhi.2.2]
    exact hf.2.2.2 d hdH

/-- Finite set of all labelled prefix embeddings. -/
def prefixEmbeddingFinset {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (h : Transcript (Query N)) : Finset (Fin 6 → Vertex N) :=
  Finset.univ.filter (IsPrefixEmbedding hN H h)

/-- Actual labelled prefix-copy count in a transcript. -/
def prefixCopyCount {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (h : Transcript (Query N)) : ℕ :=
  (prefixEmbeddingFinset hN H h).card

/-- The finite type underlying `prefixEmbeddingFinset`. -/
abbrev PrefixEmbedding {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (h : Transcript (Query N)) :=
  {f : Fin 6 → Vertex N // f ∈ prefixEmbeddingFinset hN H h}

/-- Encode a parent embedding by the oriented host edge occupied by the
selected pattern edge and the restriction obtained after deleting its two
endpoints. -/
def pairEncode {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (h : Transcript (Query N)) (e : K6Edge) (he : e ∈ H.edges) :
    PrefixEmbedding hN H h →
      (positiveGraph h).Dart × PrefixEmbedding hN (eraseFinitePair H e) h :=
  fun f ↦
    let hf : IsPrefixEmbedding hN H h f.1 := (Finset.mem_filter.mp f.2).2
    let dart : (positiveGraph h).Dart :=
      ⟨(f.1 (edgeLo e), f.1 (edgeHi e)), hf.2.2.2 e he⟩
    let child : PrefixEmbedding hN (eraseFinitePair H e) h :=
      ⟨resetPair hN e f.1, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, resetPair_isPrefixEmbedding hN H h e f.1 hf he⟩⟩
    (dart, child)

theorem pairEncode_injective {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (h : Transcript (Query N))
    (e : K6Edge) (he : e ∈ H.edges) :
    Function.Injective (pairEncode hN H h e he) := by
  intro f g hfg
  apply Subtype.ext
  funext v
  have hdart := congrArg (fun x ↦ x.1) hfg
  have hchild := congrArg (fun x ↦ x.2) hfg
  have hreset : resetPair hN e f.1 = resetPair hN e g.1 :=
    congrArg Subtype.val hchild
  by_cases hlo : v = edgeLo e
  · subst v
    exact congrArg (fun d : (positiveGraph h).Dart ↦ d.fst) hdart
  · by_cases hhi : v = edgeHi e
    · subst v
      exact congrArg (fun d : (positiveGraph h).Dart ↦ d.snd) hdart
    · have hv := congrFun hreset v
      simpa [resetPair_of_ne hN e f.1 v hlo hhi,
        resetPair_of_ne hN e g.1 v hlo hhi] using hv

/-- Deterministic pair-deletion inequality.  The exact factor two is the two
orientations of the selected unordered positive edge. -/
theorem prefixCopyCount_pair_le_edgeCount {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (h : Transcript (Query N))
    (e : K6Edge) (he : e ∈ H.edges) :
    prefixCopyCount hN H h ≤
      2 * (positiveGraph h).edgeFinset.card *
        prefixCopyCount hN (eraseFinitePair H e) h := by
  calc
    prefixCopyCount hN H h = Fintype.card (PrefixEmbedding hN H h) := by
      simp [prefixCopyCount]
    _ ≤ Fintype.card ((positiveGraph h).Dart ×
          PrefixEmbedding hN (eraseFinitePair H e) h) :=
      Fintype.card_le_of_injective (pairEncode hN H h e he)
        (pairEncode_injective hN H h e he)
    _ = 2 * (positiveGraph h).edgeFinset.card *
        prefixCopyCount hN (eraseFinitePair H e) h := by
      rw [Fintype.card_prod, (positiveGraph h).dart_card_eq_twice_card_edges]
      simp [prefixCopyCount]

/-- Distinct positive query coordinates appearing in a transcript. -/
def positiveCoordinates {N : ℕ} (h : Transcript (Query N)) : Finset (Query N) :=
  ((h.filter fun entry ↦ entry.2 = true).map Prod.fst).toFinset

@[simp] theorem mem_positiveCoordinates {N : ℕ} (h : Transcript (Query N))
    (q : Query N) :
    q ∈ positiveCoordinates h ↔ (q, true) ∈ h := by
  simp [positiveCoordinates]

theorem positiveCoordinates_card_le_trueCount {N : ℕ}
    (h : Transcript (Query N)) :
    (positiveCoordinates h).card ≤ (answers h).count true := by
  calc
    (positiveCoordinates h).card ≤
        ((h.filter fun entry ↦ entry.2 = true).map Prod.fst).length :=
      List.toFinset_card_le _
    _ = (answers h).count true := by
      induction h with
      | nil => simp [answers]
      | cons entry tail ih =>
          simp only [List.length_map] at ih ⊢
          cases entry with
          | mk q bit => cases bit <;> simpa [answers] using ih

theorem positiveGraph_edgeFinset_subset_positiveCoordinates {N : ℕ}
    (h : Transcript (Query N)) :
    (positiveGraph h).edgeFinset ⊆ positiveCoordinates h := by
  intro q hq
  obtain ⟨u, v⟩ := q
  have hadj : (positiveGraph h).Adj u v := by
    rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hq
  exact (mem_positiveCoordinates h s(u, v)).mpr hadj.2

theorem positiveGraph_edgeCount_le_trueCount {N : ℕ}
    (h : Transcript (Query N)) :
    (positiveGraph h).edgeFinset.card ≤ (answers h).count true :=
  (Finset.card_le_card (positiveGraph_edgeFinset_subset_positiveCoordinates h)).trans
    (positiveCoordinates_card_le_trueCount h)

/-- Sharp transcript-level pair recurrence in terms of the number of positive
answers. -/
theorem prefixCopyCount_pair_le_trueCount {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (h : Transcript (Query N))
    (e : K6Edge) (he : e ∈ H.edges) :
    prefixCopyCount hN H h ≤
      2 * (answers h).count true *
        prefixCopyCount hN (eraseFinitePair H e) h := by
  exact (prefixCopyCount_pair_le_edgeCount hN H h e he).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2
      (positiveGraph_edgeCount_le_trueCount h)))

/-! ## Last-exposure infrastructure for the edge recurrence -/

theorem prefixEmbeddingFinset_mono {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) {h h' : Transcript (Query N)}
    (hsub : ∀ entry, entry ∈ h → entry ∈ h') :
    prefixEmbeddingFinset hN H h ⊆ prefixEmbeddingFinset hN H h' := by
  intro f hf
  simp only [prefixEmbeddingFinset, Finset.mem_filter] at hf ⊢
  refine ⟨Finset.mem_univ _, hf.2.1, hf.2.2.1, hf.2.2.2.1, ?_⟩
  intro e he
  exact (positiveGraph_mono_of_mem hsub) (hf.2.2.2.2 e he)

/-- Candidate `H-e` embeddings just before the strategy queries the missing
image edge. -/
def edgeCandidateFinset {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) (e : K6Edge) (h : Transcript (Query N)) :
    Finset (Fin 6 → Vertex N) :=
  (prefixEmbeddingFinset hN (eraseFiniteEdge H e) h).filter fun f ↦
    s(f (edgeLo e), f (edgeHi e)) = strategy h

/-- All embeddings ever charged as candidates along one newest-first answer
path.  Union, rather than a numeric sum, makes the no-double-charge invariant
explicit. -/
def edgeAttemptFinset {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) (e : K6Edge) : List Bool →
      Finset (Fin 6 → Vertex N)
  | [] => ∅
  | bit :: bits =>
      edgeAttemptFinset hN strategy H e bits ∪
        edgeCandidateFinset hN strategy H e (replay strategy bits)

theorem edgeAttempt_mem_implies_query_mem {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (bits : List Bool) (f : Fin 6 → Vertex N)
    (hf : f ∈ edgeAttemptFinset hN strategy H e bits) :
    s(f (edgeLo e), f (edgeHi e)) ∈ queries (replay strategy bits) := by
  induction bits with
  | nil => simp [edgeAttemptFinset] at hf
  | cons bit bits ih =>
      rw [edgeAttemptFinset, Finset.mem_union] at hf
      simp only [replay_cons, queries, List.map_cons, List.mem_cons]
      rcases hf with hf | hf
      · exact Or.inr (ih hf)
      · exact Or.inl (Finset.mem_filter.mp hf).2

theorem edgeAttemptFinset_subset_final {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (bits : List Bool) :
    edgeAttemptFinset hN strategy H e bits ⊆
      prefixEmbeddingFinset hN (eraseFiniteEdge H e)
        (replay strategy bits) := by
  induction bits with
  | nil => simp [edgeAttemptFinset]
  | cons bit bits ih =>
      intro f hf
      rw [edgeAttemptFinset, Finset.mem_union] at hf
      have hmono :
          prefixEmbeddingFinset hN (eraseFiniteEdge H e)
              (replay strategy bits) ⊆
            prefixEmbeddingFinset hN (eraseFiniteEdge H e)
              (replay strategy (bit :: bits)) := by
        apply prefixEmbeddingFinset_mono
        intro entry hentry
        simp [replay, hentry]
      rcases hf with hf | hf
      · exact hmono (ih hf)
      · exact hmono (Finset.mem_filter.mp hf).1

theorem edgeAttemptFinset_disjoint_candidate {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (bit : Bool) (bits : List Bool)
    (hfresh : FreshPath strategy (bit :: bits)) :
    Disjoint (edgeAttemptFinset hN strategy H e bits)
      (edgeCandidateFinset hN strategy H e (replay strategy bits)) := by
  rw [Finset.disjoint_left]
  intro f hattempt hcandidate
  have hpast := edgeAttempt_mem_implies_query_mem hN strategy H e bits f hattempt
  have hnow := (Finset.mem_filter.mp hcandidate).2
  have hfreshNow := ((freshPath_cons strategy bit bits).mp hfresh).1
  exact hfreshNow (hnow.symm ▸ hpast)

theorem edgeAttemptFinset_card_cons {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (bit : Bool) (bits : List Bool)
    (hfresh : FreshPath strategy (bit :: bits)) :
    (edgeAttemptFinset hN strategy H e (bit :: bits)).card =
      (edgeAttemptFinset hN strategy H e bits).card +
        (edgeCandidateFinset hN strategy H e (replay strategy bits)).card := by
  rw [edgeAttemptFinset, Finset.card_union_of_disjoint
    (edgeAttemptFinset_disjoint_candidate hN strategy H e bit bits hfresh)]

theorem edgeAttemptFinset_card_le_childCopies {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (bits : List Bool) :
    (edgeAttemptFinset hN strategy H e bits).card ≤
      prefixCopyCount hN (eraseFiniteEdge H e) (replay strategy bits) := by
  exact Finset.card_le_card
    (edgeAttemptFinset_subset_final hN strategy H e bits)

/-- The source coordinate of a mask edge. -/
def edgeCoord (e : K6Edge) : Sym2 (Fin 6) := s(edgeLo e, edgeHi e)

theorem edgeCoord_injective : Function.Injective edgeCoord := by
  native_decide

theorem mappedEdge_injective {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (h : Transcript (Query N))
    (f : Fin 6 → Vertex N) (hf : IsPrefixEmbedding hN H h f)
    {d e : K6Edge} (hd : d ∈ H.edges) (he : e ∈ H.edges)
    (hmap : s(f (edgeLo d), f (edgeHi d)) =
      s(f (edgeLo e), f (edgeHi e))) : d = e := by
  have hdactive := (edgeAllowedBy_iff_mem_activeLabels H d).mp (hf.1 d hd)
  have heactive := (edgeAllowedBy_iff_mem_activeLabels H e).mp (hf.1 e he)
  have hinj := hf.2.2.1
  apply edgeCoord_injective
  change s(edgeLo d, edgeHi d) = s(edgeLo e, edgeHi e)
  rw [Sym2.eq_iff] at hmap ⊢
  rcases hmap with hmap | hmap
  · left
    exact ⟨hinj hdactive.1 heactive.1 hmap.1,
      hinj hdactive.2 heactive.2 hmap.2⟩
  · right
    exact ⟨hinj hdactive.1 heactive.2 hmap.1,
      hinj hdactive.2 heactive.1 hmap.2⟩

theorem positiveGraph_cons_true_adj_iff {N : ℕ} (q : Query N)
    (h : Transcript (Query N)) (u v : Vertex N) :
    (positiveGraph ((q, true) :: h)).Adj u v ↔
      (positiveGraph h).Adj u v ∨ (u ≠ v ∧ s(u, v) = q) := by
  simp only [positiveGraph_adj, List.mem_cons, Prod.mk.injEq, true_and]
  tauto

theorem positiveGraph_cons_false {N : ℕ} (q : Query N)
    (h : Transcript (Query N)) :
    positiveGraph ((q, false) :: h) = positiveGraph h := by
  ext u v
  simp [positiveGraph_adj]

theorem prefixCopyCount_cons_false {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (q : Query N) (h : Transcript (Query N)) :
    prefixCopyCount hN H ((q, false) :: h) = prefixCopyCount hN H h := by
  unfold prefixCopyCount prefixEmbeddingFinset IsPrefixEmbedding
  congr 1
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hvalid, hcanonical, hinj, hedges⟩
    exact ⟨hvalid, hcanonical, hinj, fun e he ↦ by
      simpa [positiveGraph_adj] using hedges e he⟩
  · rintro ⟨hvalid, hcanonical, hinj, hedges⟩
    exact ⟨hvalid, hcanonical, hinj, fun e he ↦ by
      simpa [positiveGraph_adj] using hedges e he⟩

private theorem eraseEdge_embedding_of_other_edges
    {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (h : Transcript (Query N)) (e : K6Edge)
    (f : Fin 6 → Vertex N) (hvalid : ValidPattern H)
    (hcanonical : CanonicalMap hN H f)
    (hinj : Set.InjOn f (activeLabels H : Set (Fin 6)))
    (hedges : ∀ d ∈ H.edges, d ≠ e →
      (positiveGraph h).Adj (f (edgeLo d)) (f (edgeHi d))) :
    IsPrefixEmbedding hN (eraseFiniteEdge H e) h f := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    exact hvalid d (Finset.mem_erase.mp hd).2
  · simpa [eraseFiniteEdge, CanonicalMap, activeLabels] using hcanonical
  · simpa [eraseFiniteEdge, activeLabels] using hinj
  · intro d hd
    have hd' := Finset.mem_erase.mp hd
    exact hedges d hd'.2 hd'.1

/-- Every embedding newly created by one positive query is charged to a
candidate of at least one edge-deletion child. -/
theorem newEmbedding_subset_edgeCandidates {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern)
    (h : Transcript (Query N)) :
    prefixEmbeddingFinset hN H
          ((strategy h, true) :: h) \ prefixEmbeddingFinset hN H h ⊆
      H.edges.biUnion fun e ↦ edgeCandidateFinset hN strategy H e h := by
  intro f hfnew
  have hfAfter : IsPrefixEmbedding hN H ((strategy h, true) :: h) f :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hfnew).1).2
  have hfNotBefore : f ∉ prefixEmbeddingFinset hN H h :=
    (Finset.mem_sdiff.mp hfnew).2
  have hexists : ∃ e ∈ H.edges,
      ¬(positiveGraph h).Adj (f (edgeLo e)) (f (edgeHi e)) := by
    by_contra hnone
    have hall : ∀ e ∈ H.edges,
        (positiveGraph h).Adj (f (edgeLo e)) (f (edgeHi e)) := by
      intro e he
      by_contra hnot
      exact hnone ⟨e, he, hnot⟩
    apply hfNotBefore
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfAfter.1,
      hfAfter.2.1, hfAfter.2.2.1, hall⟩
  rcases hexists with ⟨e, he, heMissing⟩
  rw [Finset.mem_biUnion]
  refine ⟨e, he, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply eraseEdge_embedding_of_other_edges hN H h e f
      hfAfter.1 hfAfter.2.1 hfAfter.2.2.1
    intro d hd hde
    have hdAfter := hfAfter.2.2.2 d hd
    rw [positiveGraph_cons_true_adj_iff] at hdAfter
    rcases hdAfter with hdBefore | hdNew
    · exact hdBefore
    · exfalso
      have heAfter := hfAfter.2.2.2 e he
      rw [positiveGraph_cons_true_adj_iff] at heAfter
      have heNew : s(f (edgeLo e), f (edgeHi e)) = strategy h := by
        rcases heAfter with heBefore | heNew
        · exact False.elim (heMissing heBefore)
        · exact heNew.2
      exact hde (mappedEdge_injective hN H ((strategy h, true) :: h) f
        hfAfter hd he (hdNew.2.trans heNew.symm))
  · have heAfter := hfAfter.2.2.2 e he
    rw [positiveGraph_cons_true_adj_iff] at heAfter
    rcases heAfter with heBefore | heNew
    · exact False.elim (heMissing heBefore)
    · exact heNew.2

/-- One positive query increases the parent count by at most the sum of its
edge-deletion candidate counts. -/
theorem prefixCopyCount_true_step_le {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern)
    (h : Transcript (Query N)) :
    prefixCopyCount hN H ((strategy h, true) :: h) ≤
      prefixCopyCount hN H h +
        ∑ e ∈ H.edges, (edgeCandidateFinset hN strategy H e h).card := by
  have hmono : prefixEmbeddingFinset hN H h ⊆
      prefixEmbeddingFinset hN H ((strategy h, true) :: h) := by
    apply prefixEmbeddingFinset_mono
    intro entry hentry
    simp [hentry]
  have hdiff := Finset.card_le_card
    (newEmbedding_subset_edgeCandidates hN strategy H h)
  have hunion := Finset.card_biUnion_le
    (s := H.edges) (t := fun e ↦ edgeCandidateFinset hN strategy H e h)
  have hcard := Finset.card_sdiff_add_card_eq_card hmono
  dsimp [prefixCopyCount]
  omega

/-- Number of successful candidate charges to a fixed source edge along an
answer path. -/
def edgeSuccessCharge {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) (e : K6Edge) : List Bool → ℕ
  | [] => 0
  | bit :: bits =>
      edgeSuccessCharge hN strategy H e bits +
        if bit then
          (edgeCandidateFinset hN strategy H e (replay strategy bits)).card
        else 0

theorem prefixCopyCount_empty_of_nonempty {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (hNonempty : H.edges.Nonempty) :
    prefixCopyCount hN H [] = 0 := by
  rw [prefixCopyCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro f hf
  have hemb := (Finset.mem_filter.mp hf).2
  rcases hNonempty with ⟨e, he⟩
  simpa [positiveGraph_adj] using hemb.2.2.2 e he

theorem prefixCopyCount_le_successCharges {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern)
    (hNonempty : H.edges.Nonempty) (bits : List Bool) :
    prefixCopyCount hN H (replay strategy bits) ≤
      ∑ e ∈ H.edges, edgeSuccessCharge hN strategy H e bits := by
  induction bits with
  | nil => simp [edgeSuccessCharge, prefixCopyCount_empty_of_nonempty hN H hNonempty]
  | cons bit bits ih =>
      cases bit with
      | false =>
          rw [replay_cons, prefixCopyCount_cons_false]
          simpa [edgeSuccessCharge] using ih
      | true =>
          have hstep := prefixCopyCount_true_step_le hN strategy H
            (replay strategy bits)
          calc
            prefixCopyCount hN H (replay strategy (true :: bits)) ≤
                prefixCopyCount hN H (replay strategy bits) +
                  ∑ e ∈ H.edges,
                    (edgeCandidateFinset hN strategy H e
                      (replay strategy bits)).card := by
                simpa [replay] using hstep
            _ ≤ (∑ e ∈ H.edges,
                  edgeSuccessCharge hN strategy H e bits) +
                ∑ e ∈ H.edges,
                  (edgeCandidateFinset hN strategy H e
                    (replay strategy bits)).card := Nat.add_le_add_right ih _
            _ = ∑ e ∈ H.edges,
                edgeSuccessCharge hN strategy H e (true :: bits) := by
              simp only [edgeSuccessCharge, if_true, Finset.sum_add_distrib]

theorem edgeSuccessCharge_le_attemptCard {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (bits : List Bool) (hfresh : FreshPath strategy bits) :
    edgeSuccessCharge hN strategy H e bits ≤
      (edgeAttemptFinset hN strategy H e bits).card := by
  induction bits with
  | nil => simp [edgeSuccessCharge, edgeAttemptFinset]
  | cons bit bits ih =>
      have htail := ((freshPath_cons strategy bit bits).mp hfresh).2
      rw [edgeAttemptFinset_card_cons hN strategy H e bit bits hfresh]
      cases bit <;> simp only [edgeSuccessCharge, if_false, if_true]
      · exact (ih htail).trans (Nat.le_add_right _ _)
      · exact Nat.add_le_add_right (ih htail) _

private theorem freshPath_of_append_left_list {Q : Type}
    (strategy : Strategy Q) (extension bits : List Bool)
    (hfresh : FreshPath strategy (extension ++ bits)) :
    FreshPath strategy bits := by
  induction extension with
  | nil => simpa using hfresh
  | cons bit extension ih =>
      exact ih
        (((freshPath_cons strategy bit (extension ++ bits)).mp hfresh).2)

/-- Budget-level freshness implies freshness of every shorter answer list. -/
theorem freshPath_of_freshForBudget {N : ℕ}
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (bits : List Bool) (hlen : bits.length ≤ N) :
    FreshPath strategy bits := by
  let extension := List.replicate (N - bits.length) false
  let fullList := extension ++ bits
  have hlength : fullList.length = N := by
    simp [fullList, extension]
    omega
  let full : List.Vector Bool N := ⟨fullList, hlength⟩
  apply freshPath_of_append_left_list strategy extension bits
  change FreshPath strategy full.toList
  exact hfresh full

/-- Exact finite expectation for one deterministic strategy. -/
def strategyExpectedPrefixCopies (p : ℝ≥0) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) : ℝ≥0 :=
  ∑ bits : AnswerPath N,
    answerPathWeight p bits *
      (prefixCopyCount hN H (replay strategy (answerList bits)) : ℝ≥0)

/-- Expected number of successful charges to one source edge during the first
`n` queries. -/
def expectedEdgeSuccess (p : ℝ≥0) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (n : ℕ) : ℝ≥0 :=
  ∑ bits : List.Vector Bool n,
    vectorWeight p bits *
      (edgeSuccessCharge hN strategy H e bits.toList : ℝ≥0)

/-- Expected number of distinct attempts charged to one source edge during
the first `n` queries. -/
def expectedEdgeAttempt (p : ℝ≥0) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (n : ℕ) : ℝ≥0 :=
  ∑ bits : List.Vector Bool n,
    vectorWeight p bits *
      ((edgeAttemptFinset hN strategy H e bits.toList).card : ℝ≥0)

/-- Expected number of candidates present immediately before query `n+1`. -/
def expectedEdgeCandidate (p : ℝ≥0) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern) (e : K6Edge)
    (n : ℕ) : ℝ≥0 :=
  ∑ bits : List.Vector Bool n,
    vectorWeight p bits *
      ((edgeCandidateFinset hN strategy H e
        (replay strategy bits.toList)).card : ℝ≥0)

theorem expectedEdgeSuccess_succ (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) (e : K6Edge) (n : ℕ) :
    expectedEdgeSuccess p hN strategy H e (n + 1) =
      expectedEdgeSuccess p hN strategy H e n +
        p * expectedEdgeCandidate p hN strategy H e n := by
  unfold expectedEdgeSuccess expectedEdgeCandidate
  rw [sum_vector_succ, Fintype.sum_bool]
  simp only [vectorWeight_cons, List.Vector.toList_cons,
    nnBernoulliWeight_true, nnBernoulliWeight_false, edgeSuccessCharge,
    if_true, if_false]
  rw [← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro tail _
  simp only [Bool.false_eq_true, if_false, Nat.cast_add]
  set q : ℝ≥0 := 1 - p
  have hnorm : p + q = 1 := by
    rw [show q = 1 - p by rfl]
    simpa [add_comm] using tsub_add_cancel_of_le hp
  calc
    _ = (p + q) * vectorWeight p tail *
          (edgeSuccessCharge hN strategy H e tail.toList : ℝ≥0) +
        p * vectorWeight p tail *
          ((edgeCandidateFinset hN strategy H e
            (replay strategy tail.toList)).card : ℝ≥0) := by ring
    _ = _ := by rw [hnorm]; ring

theorem expectedEdgeAttempt_succ (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (hfresh : FreshForBudget strategy) (H : K6FinitePattern) (e : K6Edge)
    (n : ℕ) (hn : n + 1 ≤ N) :
    expectedEdgeAttempt p hN strategy H e (n + 1) =
      expectedEdgeAttempt p hN strategy H e n +
        expectedEdgeCandidate p hN strategy H e n := by
  unfold expectedEdgeAttempt expectedEdgeCandidate
  rw [sum_vector_succ, Fintype.sum_bool]
  simp only [vectorWeight_cons, List.Vector.toList_cons,
    nnBernoulliWeight_true, nnBernoulliWeight_false]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro tail _
  have hfalse := edgeAttemptFinset_card_cons hN strategy H e false tail.toList
    (freshPath_of_freshForBudget strategy hfresh (false :: tail.toList) (by
      simp
      omega))
  have htrue := edgeAttemptFinset_card_cons hN strategy H e true tail.toList
    (freshPath_of_freshForBudget strategy hfresh (true :: tail.toList) (by
      simp
      omega))
  rw [hfalse, htrue]
  push_cast
  set q : ℝ≥0 := 1 - p
  have hnorm : p + q = 1 := by
    rw [show q = 1 - p by rfl]
    simpa [add_comm] using tsub_add_cancel_of_le hp
  calc
    _ = (p + q) * vectorWeight p tail *
          (((edgeAttemptFinset hN strategy H e tail.toList).card : ℝ≥0) +
            ((edgeCandidateFinset hN strategy H e
              (replay strategy tail.toList)).card : ℝ≥0)) := by ring
    _ = _ := by rw [hnorm]; ring

/-- Exact finite Bernoulli identity: every attempted copy is completed by its
queried missing edge with probability exactly `p`. -/
theorem expectedEdgeSuccess_eq_mul_expectedEdgeAttempt
    (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (hfresh : FreshForBudget strategy) (H : K6FinitePattern) (e : K6Edge)
    (n : ℕ) (hn : n ≤ N) :
    expectedEdgeSuccess p hN strategy H e n =
      p * expectedEdgeAttempt p hN strategy H e n := by
  induction n with
  | zero =>
      simp [expectedEdgeSuccess, expectedEdgeAttempt,
        vectorWeight, edgeSuccessCharge, edgeAttemptFinset]
  | succ n ih =>
      rw [show n + 1 = n.succ by omega,
        expectedEdgeSuccess_succ p hp hN strategy H e n,
        expectedEdgeAttempt_succ p hp hN strategy hfresh H e n (by omega),
        ih (by omega)]
      ring

theorem strategyExpectedPrefixCopies_eq_vectorSum (p : ℝ≥0)
    {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) :
    strategyExpectedPrefixCopies p hN strategy H =
      ∑ bits : List.Vector Bool N,
        vectorWeight p bits *
          (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0) := by
  exact answerPath_weighted_sum_eq_vectorSum p N fun bits ↦
    (prefixCopyCount hN H (replay strategy bits) : ℝ≥0)

theorem expectedEdgeAttempt_le_child (p : ℝ≥0)
    {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) (e : K6Edge) :
    expectedEdgeAttempt p hN strategy H e N ≤
      strategyExpectedPrefixCopies p hN strategy (eraseFiniteEdge H e) := by
  rw [strategyExpectedPrefixCopies_eq_vectorSum]
  unfold expectedEdgeAttempt
  apply Finset.sum_le_sum
  intro bits _
  apply mul_le_mul_left'
  exact_mod_cast
    edgeAttemptFinset_card_le_childCopies hN strategy H e bits.toList

theorem expectedEdgeSuccess_le_child (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (hfresh : FreshForBudget strategy) (H : K6FinitePattern) (e : K6Edge) :
    expectedEdgeSuccess p hN strategy H e N ≤
      p * strategyExpectedPrefixCopies p hN strategy (eraseFiniteEdge H e) := by
  rw [expectedEdgeSuccess_eq_mul_expectedEdgeAttempt
    p hp hN strategy hfresh H e N (le_refl N)]
  exact mul_le_mul_left' (expectedEdgeAttempt_le_child p hN strategy H e) p

/-- Exact fixed-strategy last-positive-exposure recurrence. -/
theorem strategyExpectedPrefixCopies_edge_le
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (H : K6FinitePattern) (hNonempty : H.edges.Nonempty) :
    strategyExpectedPrefixCopies p hN strategy H ≤
      p * ∑ e ∈ H.edges,
        strategyExpectedPrefixCopies p hN strategy (eraseFiniteEdge H e) := by
  rw [strategyExpectedPrefixCopies_eq_vectorSum]
  calc
    (∑ bits : List.Vector Bool N,
        vectorWeight p bits *
          (prefixCopyCount hN H (replay strategy bits.toList) : ℝ≥0)) ≤
      ∑ bits : List.Vector Bool N,
        vectorWeight p bits *
          (∑ e ∈ H.edges,
            (edgeSuccessCharge hN strategy H e bits.toList : ℝ≥0)) := by
      apply Finset.sum_le_sum
      intro bits _
      apply mul_le_mul_left'
      exact_mod_cast
        prefixCopyCount_le_successCharges hN strategy H hNonempty bits.toList
    _ = ∑ bits : List.Vector Bool N, ∑ e ∈ H.edges,
          vectorWeight p bits *
            (edgeSuccessCharge hN strategy H e bits.toList : ℝ≥0) := by
      apply Finset.sum_congr rfl
      intro bits _
      rw [Finset.mul_sum]
    _ = ∑ e ∈ H.edges, expectedEdgeSuccess p hN strategy H e N := by
      unfold expectedEdgeSuccess
      rw [Finset.sum_comm]
    _ ≤ ∑ e ∈ H.edges,
          p * strategyExpectedPrefixCopies p hN strategy
            (eraseFiniteEdge H e) := by
      gcongr with e he
      exact expectedEdgeSuccess_le_child p hp hN strategy hfresh H e
    _ = p * ∑ e ∈ H.edges,
          strategyExpectedPrefixCopies p hN strategy (eraseFiniteEdge H e) := by
      rw [Finset.mul_sum]

/-- Number of positive answers in a complete answer path. -/
def answerPathTrueCount {N : ℕ} (bits : AnswerPath N) : ℕ :=
  (answerList bits).count true

/-- Exact mass of the event on which the positive-answer count exceeds the
real threshold `pN`. -/
def pairBadMass (kappa p : ℝ≥0) (N : ℕ) : ℝ≥0 :=
  ∑ bits : AnswerPath N,
    if kappa * p * N < (answerPathTrueCount bits : ℝ≥0)
    then answerPathWeight p bits else 0

@[simp] theorem coe_nnBernoulliWeight (p : ℝ≥0) (bit : Bool) :
    (nnBernoulliWeight p bit : ℝ≥0∞) =
      OnlineRamsey.bernoulliWeight (p : ℝ≥0∞) bit := by
  cases bit <;> simp [nnBernoulliWeight, OnlineRamsey.bernoulliWeight]

theorem vectorWeight_eq_count (p : ℝ≥0) {N : ℕ}
    (bits : List.Vector Bool N) :
    vectorWeight p bits =
      p ^ bits.toList.count true *
        (1 - p) ^ (N - bits.toList.count true) := by
  have hprod : ∀ xs : List Bool,
      (xs.map (nnBernoulliWeight p)).prod =
        p ^ xs.count true * (1 - p) ^ xs.count false := by
    intro xs
    induction xs with
    | nil => simp
    | cons bit xs ih =>
        cases bit <;>
          simp [nnBernoulliWeight, ih, pow_succ, mul_assoc, mul_left_comm,
            mul_comm]
  rw [vectorWeight, hprod,
    OnlineRamsey.vector_count_false_eq_sub_count_true]

/-- The `NNReal` Boolean-vector upper tail, in the power form from
`AdaptiveTail`. -/
def nnrealVectorUpperTail (p : ℝ≥0) (N R : ℕ) : ℝ≥0 :=
  ∑ bits : List.Vector Bool N,
    if R ≤ bits.toList.count true then
      p ^ bits.toList.count true *
        (1 - p) ^ (N - bits.toList.count true)
    else 0

theorem coe_nnrealVectorUpperTail (p : ℝ≥0) (N R : ℕ) :
    (nnrealVectorUpperTail p N R : ℝ≥0∞) =
      OnlineRamsey.bernoulliUpperTail (p : ℝ≥0∞) N R := by
  rw [← OnlineRamsey.sum_support_bernoulli_eq_upperTail]
  unfold nnrealVectorUpperTail
  push_cast
  apply Fintype.sum_equiv (OnlineRamsey.trueSupportEquiv N)
  intro bits
  change
    (↑(if R ≤ bits.toList.count true then
      p ^ bits.toList.count true *
        (1 - p) ^ (N - bits.toList.count true)
      else 0) : ℝ≥0∞) =
      if R ≤ (OnlineRamsey.trueSupport bits).card then
        (p : ℝ≥0∞) ^ (OnlineRamsey.trueSupport bits).card *
          (1 - (p : ℝ≥0∞)) ^ (N - (OnlineRamsey.trueSupport bits).card)
      else 0
  rw [OnlineRamsey.card_trueSupport]
  by_cases h : R ≤ bits.toList.count true
  · simp [h]
  · simp [h]

theorem nnrealVectorUpperTail_le_choose_mul_pow
    (p : ℝ≥0) (hp : p ≤ 1) (N R : ℕ) :
    nnrealVectorUpperTail p N R ≤ (Nat.choose N R : ℝ≥0) * p ^ R := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_nnrealVectorUpperTail]
  simpa using OnlineRamsey.bernoulliUpperTail_le_choose_mul_pow
    (p : ℝ≥0∞) (by exact_mod_cast hp) N R

theorem nnreal_vectorWeight_upperTail_le_choose_mul_pow
    (p : ℝ≥0) (hp : p ≤ 1) (N R : ℕ) :
    (∑ bits : List.Vector Bool N,
      if R ≤ bits.toList.count true then vectorWeight p bits else 0) ≤
        (Nat.choose N R : ℝ≥0) * p ^ R := by
  rw [show
    (∑ bits : List.Vector Bool N,
      if R ≤ bits.toList.count true then vectorWeight p bits else 0) =
        nnrealVectorUpperTail p N R by
      unfold nnrealVectorUpperTail
      apply Finset.sum_congr rfl
      intro bits _
      by_cases h : R ≤ bits.toList.count true
      · simp [h, vectorWeight_eq_count]
      · simp [h]]
  exact nnrealVectorUpperTail_le_choose_mul_pow p hp N R

/-- Any Boolean-vector event forcing at least `R` successes has mass at most
`choose N R * p^R`. -/
theorem nnreal_vector_event_mass_le_choose_mul_pow
    (p : ℝ≥0) (hp : p ≤ 1) (N R : ℕ)
    (P : List.Vector Bool N → Prop) [DecidablePred P]
    (hP : ∀ bits, P bits → R ≤ bits.toList.count true) :
    (∑ bits : List.Vector Bool N,
      if P bits then vectorWeight p bits else 0) ≤
        (Nat.choose N R : ℝ≥0) * p ^ R := by
  calc
    (∑ bits : List.Vector Bool N,
      if P bits then vectorWeight p bits else 0) ≤
        ∑ bits : List.Vector Bool N,
          if R ≤ bits.toList.count true then vectorWeight p bits else 0 := by
      apply Finset.sum_le_sum
      intro bits _
      by_cases h : P bits
      · simp [h, hP bits h]
      · simp [h]
    _ ≤ (Nat.choose N R : ℝ≥0) * p ^ R :=
      nnreal_vectorWeight_upperTail_le_choose_mul_pow p hp N R

/-- Factorial-moment bound for the pair-recurrence bad mass.  Choosing `R`
just above `κ p N` converts the remaining tail problem into the standard
estimate for `choose N R * p^R`. -/
theorem pairBadMass_le_choose_mul_pow
    (kappa p : ℝ≥0) (hp : p ≤ 1) (N R : ℕ)
    (hthreshold : ∀ k : ℕ,
      kappa * p * (N : ℝ≥0) < (k : ℝ≥0) → R ≤ k) :
    pairBadMass kappa p N ≤ (Nat.choose N R : ℝ≥0) * p ^ R := by
  calc
    pairBadMass kappa p N =
        ∑ bits : List.Vector Bool N,
          if kappa * p * (N : ℝ≥0) <
              (bits.toList.count true : ℝ≥0)
          then vectorWeight p bits else 0 := by
      unfold pairBadMass
      apply Fintype.sum_equiv (answerPathVectorEquiv N)
      intro bits
      rw [vectorWeight_answerPathVectorEquiv,
        answerPathVectorEquiv_apply_toList]
      rfl
    _ ≤ (Nat.choose N R : ℝ≥0) * p ^ R := by
      apply nnreal_vector_event_mass_le_choose_mul_pow p hp N R
        (fun bits ↦ kappa * p * (N : ℝ≥0) <
          (bits.toList.count true : ℝ≥0))
      intro bits hbits
      exact hthreshold (bits.toList.count true) hbits

/-- The least natural number which is strictly larger than `κ p N`. -/
def pairThreshold (kappa p : ℝ≥0) (N : ℕ) : ℕ :=
  ⌊kappa * p * (N : ℝ≥0)⌋₊ + 1

theorem pairThreshold_pos (kappa p : ℝ≥0) (N : ℕ) :
    0 < pairThreshold kappa p N := by
  simp [pairThreshold]

theorem lt_pairThreshold (kappa p : ℝ≥0) (N : ℕ) :
    kappa * p * (N : ℝ≥0) < (pairThreshold kappa p N : ℝ≥0) := by
  simpa [pairThreshold] using
    (Nat.lt_floor_add_one (kappa * p * (N : ℝ≥0)))

theorem pairThreshold_le_of_lt (kappa p : ℝ≥0) (N k : ℕ)
    (h : kappa * p * (N : ℝ≥0) < (k : ℝ≥0)) :
    pairThreshold kappa p N ≤ k := by
  rw [pairThreshold, Nat.add_one_le_iff]
  exact (Nat.floor_lt
    (show 0 ≤ kappa * p * (N : ℝ≥0) by positivity)).mpr h

/-- The strict real threshold defining the pair bad event is exactly the
natural upper-tail cutoff `floor (κpN) + 1`. -/
theorem pairThreshold_le_iff_lt (kappa p : ℝ≥0) (N k : ℕ) :
    pairThreshold kappa p N ≤ k ↔
      kappa * p * (N : ℝ≥0) < (k : ℝ≥0) := by
  constructor
  · intro hk
    exact (lt_pairThreshold kappa p N).trans_le (by exact_mod_cast hk)
  · exact pairThreshold_le_of_lt kappa p N k

/-- Exact identification of `pairBadMass` with the `NNReal` binomial upper
tail at its canonical integer threshold. -/
theorem pairBadMass_eq_nnrealVectorUpperTail (kappa p : ℝ≥0) (N : ℕ) :
    pairBadMass kappa p N =
      nnrealVectorUpperTail p N (pairThreshold kappa p N) := by
  calc
    pairBadMass kappa p N =
        ∑ bits : List.Vector Bool N,
          if kappa * p * (N : ℝ≥0) <
              (bits.toList.count true : ℝ≥0)
          then vectorWeight p bits else 0 := by
      unfold pairBadMass
      apply Fintype.sum_equiv (answerPathVectorEquiv N)
      intro bits
      rw [vectorWeight_answerPathVectorEquiv,
        answerPathVectorEquiv_apply_toList]
      rfl
    _ = nnrealVectorUpperTail p N (pairThreshold kappa p N) := by
      unfold nnrealVectorUpperTail
      apply Finset.sum_congr rfl
      intro bits _
      rw [vectorWeight_eq_count]
      by_cases h : kappa * p * (N : ℝ≥0) <
          (bits.toList.count true : ℝ≥0)
      · have ht : pairThreshold kappa p N ≤ bits.toList.count true :=
          (pairThreshold_le_iff_lt kappa p N _).2 h
        simp [h, ht]
      · have ht : ¬pairThreshold kappa p N ≤ bits.toList.count true := by
          simpa [pairThreshold_le_iff_lt] using h
        simp [h, ht]

/-- `ENNReal` form of the preceding exact identification. -/
theorem coe_pairBadMass_eq_bernoulliUpperTail (kappa p : ℝ≥0) (N : ℕ) :
    (pairBadMass kappa p N : ℝ≥0∞) =
      OnlineRamsey.bernoulliUpperTail (p : ℝ≥0∞) N
        (pairThreshold kappa p N) := by
  rw [pairBadMass_eq_nnrealVectorUpperTail,
    coe_nnrealVectorUpperTail]

/-- Increasing the required number of positive answers can only decrease the
finite Bernoulli upper-tail mass. -/
theorem bernoulliUpperTail_mono_threshold (p : ℝ≥0∞) (N R S : ℕ)
    (hRS : R ≤ S) :
    OnlineRamsey.bernoulliUpperTail p N S ≤
      OnlineRamsey.bernoulliUpperTail p N R := by
  rw [← OnlineRamsey.sum_support_bernoulli_eq_upperTail,
    ← OnlineRamsey.sum_support_bernoulli_eq_upperTail]
  apply Finset.sum_le_sum
  intro support _
  by_cases hS : S ≤ support.card
  · simp [hS, hRS.trans hS]
  · simp [hS]

/-- A cutoff above the canonical pair threshold is controlled by the exact
pair bad mass. -/
theorem bernoulliUpperTail_le_coe_pairBadMass
    (kappa p : ℝ≥0) (N R : ℕ)
    (hR : pairThreshold kappa p N ≤ R) :
    OnlineRamsey.bernoulliUpperTail (p : ℝ≥0∞) N R ≤
      (pairBadMass kappa p N : ℝ≥0∞) := by
  rw [coe_pairBadMass_eq_bernoulliUpperTail]
  exact bernoulliUpperTail_mono_threshold _ _ _ _ hR

/-- Euler's number, packaged as an `NNReal`. -/
def expOneNNReal : ℝ≥0 := ⟨Real.exp 1, (Real.exp_pos 1).le⟩

/-- The standard finite estimate `choose(n,k) ≤ (e n / k)^k`, transported
to `NNReal`. -/
theorem choose_nnreal_le_exp_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (Nat.choose n k : ℝ≥0) ≤
      (expOneNNReal * (n : ℝ≥0) / (k : ℝ≥0)) ^ k := by
  apply NNReal.coe_le_coe.mp
  change (Nat.choose n k : ℝ) ≤
    (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    calc
      (1 : ℝ) ^ 2 ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * (k : ℝ) := by
        gcongr
        exact Real.pi_gt_three.le
  have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
    calc
      ((k : ℝ) / Real.exp 1) ^ k ≤
          Real.sqrt (2 * Real.pi * (k : ℝ)) *
            ((k : ℝ) / Real.exp 1) ^ k := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ (k.factorial : ℝ) := Stirling.le_factorial_stirling k
  have hchoose := Nat.choose_le_pow_div (α := ℝ) k n
  have hfacpos : 0 < (k.factorial : ℝ) := by positivity
  have hbase : 0 ≤ (n : ℝ) ^ k := by positivity
  calc
    (Nat.choose n k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := hchoose
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / Real.exp 1) ^ k) := by
      exact div_le_div_of_nonneg_left hbase (by positivity) hfac
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
      rw [div_pow, div_pow]
      field_simp [ne_of_gt hkR, ne_of_gt (Real.exp_pos 1)]
      <;> ring

/-- Concrete Chernoff-style bound for the pair bad mass. -/
theorem pairBadMass_le_exp_div_pow
    (kappa p : ℝ≥0) (hkappa : 0 < kappa) (hp : p ≤ 1) (N : ℕ) :
    pairBadMass kappa p N ≤
      (expOneNNReal / kappa) ^ pairThreshold kappa p N := by
  let R := pairThreshold kappa p N
  have hR : 0 < R := pairThreshold_pos kappa p N
  have hRcast : 0 < (R : ℝ≥0) := by exact_mod_cast hR
  have hthreshold : kappa * p * (N : ℝ≥0) < (R : ℝ≥0) := by
    exact lt_pairThreshold kappa p N
  calc
    pairBadMass kappa p N ≤ (Nat.choose N R : ℝ≥0) * p ^ R := by
      apply pairBadMass_le_choose_mul_pow kappa p hp N R
      intro k hk
      exact pairThreshold_le_of_lt kappa p N k hk
    _ ≤ (expOneNNReal * (N : ℝ≥0) / (R : ℝ≥0)) ^ R * p ^ R := by
      gcongr
      exact choose_nnreal_le_exp_mul_div_pow N R hR
    _ = (expOneNNReal * p * (N : ℝ≥0) / (R : ℝ≥0)) ^ R := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ (expOneNNReal / kappa) ^ R := by
      apply pow_le_pow_left₀ (zero_le _) _ R
      apply (div_le_div_iff₀ hRcast hkappa).2
      calc
        (expOneNNReal * p * (N : ℝ≥0)) * kappa =
            expOneNNReal * (kappa * p * (N : ℝ≥0)) := by ring
        _ ≤ expOneNNReal * (R : ℝ≥0) :=
          mul_le_mul_left' hthreshold.le _

theorem expOneNNReal_div_eight_le_half :
    expOneNNReal / 8 ≤ (2 : ℝ≥0)⁻¹ := by
  apply NNReal.coe_le_coe.mp
  change Real.exp 1 / 8 ≤ (2 : ℝ)⁻¹
  have hexp : Real.exp 1 < 4 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  norm_num at hexp ⊢
  linarith

/-- With the concrete slack `κ = 8`, the bad mass decays by at least one
factor of two per threshold success. -/
theorem pairBadMass_eight_le_half_pow (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ) :
    pairBadMass 8 p N ≤ (2 : ℝ≥0)⁻¹ ^ pairThreshold 8 p N := by
  exact (pairBadMass_le_exp_div_pow 8 p (by norm_num) hp N).trans
    (pow_le_pow_left₀ (zero_le _) expOneNNReal_div_eight_le_half _)

/-- Explicit exceptional contribution used in the pair recurrence. -/
def pairTail (kappa p : ℝ≥0) (N : ℕ) (H : K6FinitePattern) : ℝ≥0 :=
  ((2 * N : ℕ) ^ 6 : ℝ≥0) * pairBadMass kappa p N

/-- Explicit exponentially decaying bound for the pair tail at slack eight. -/
theorem pairTail_eight_le_half_pow (p : ℝ≥0) (hp : p ≤ 1) (N : ℕ)
    (H : K6FinitePattern) :
    pairTail 8 p N H ≤
      ((2 * N : ℕ) ^ 6 : ℝ≥0) *
        (2 : ℝ≥0)⁻¹ ^ pairThreshold 8 p N := by
  exact mul_le_mul_left' (pairBadMass_eight_le_half_pow p hp N) _

/-- A fixed polynomial cannot offset the geometric factor `2⁻ᴿ`.  This is
the elementary asymptotic estimate used below to dispose of every accumulated
pair-recurrence error. -/
theorem polynomial_mul_half_pow_tendsto_zero (d : ℕ) :
    Tendsto (fun R : ℕ ↦ (R : ℝ≥0) ^ d * (2 : ℝ≥0)⁻¹ ^ R)
      atTop (𝓝 0) := by
  rw [← NNReal.tendsto_coe]
  simpa using
    (tendsto_pow_const_mul_const_pow_of_lt_one d
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity) (by norm_num : (2 : ℝ)⁻¹ < 1))

/-- The concrete pair tail tends to zero whenever its threshold tends to
infinity and the query budget is eventually at most the square of that
threshold. -/
theorem pairTail_eight_tendsto_zero_of_threshold
    {ι : Type*} {l : Filter ι}
    (p : ι → ℝ≥0) (N : ι → ℕ) (H : K6FinitePattern)
    (hp : ∀ i, p i ≤ 1)
    (hthreshold : Tendsto
      (fun i ↦ pairThreshold 8 (p i) (N i)) l atTop)
    (hN : ∀ᶠ i in l,
      (N i : ℝ≥0) ≤
        (pairThreshold 8 (p i) (N i) : ℝ≥0) ^ 2) :
    Tendsto (fun i ↦ pairTail 8 (p i) (N i) H) l (𝓝 0) := by
  let R : ι → ℕ := fun i ↦ pairThreshold 8 (p i) (N i)
  have hdecay : Tendsto
      (fun i ↦ (64 : ℝ≥0) *
        ((R i : ℝ≥0) ^ 12 * (2 : ℝ≥0)⁻¹ ^ R i)) l (𝓝 0) := by
    simpa [Function.comp_def] using
      (polynomial_mul_half_pow_tendsto_zero 12).comp hthreshold
        |>.const_mul (64 : ℝ≥0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0)) l (𝓝 0))
      hdecay
  · exact Filter.Eventually.of_forall (fun _ ↦ zero_le _)
  · filter_upwards [hN] with i hi
    calc
      pairTail 8 (p i) (N i) H ≤
          ((2 * N i : ℕ) ^ 6 : ℝ≥0) * (2 : ℝ≥0)⁻¹ ^ R i :=
        pairTail_eight_le_half_pow (p i) (hp i) (N i) H
      _ = (64 : ℝ≥0) * (N i : ℝ≥0) ^ 6 *
          (2 : ℝ≥0)⁻¹ ^ R i := by
        push_cast
        ring
      _ ≤ (64 : ℝ≥0) * (R i : ℝ≥0) ^ 12 *
          (2 : ℝ≥0)⁻¹ ^ R i := by
        have hpow : (N i : ℝ≥0) ^ 6 ≤ (R i : ℝ≥0) ^ 12 := by
          calc
            (N i : ℝ≥0) ^ 6 ≤ ((R i : ℝ≥0) ^ 2) ^ 6 :=
              pow_le_pow_left₀ (zero_le _) hi 6
            _ = (R i : ℝ≥0) ^ 12 := by ring
        exact mul_le_mul_right' (mul_le_mul_left' hpow 64) _
      _ = (64 : ℝ≥0) * ((R i : ℝ≥0) ^ 12 *
          (2 : ℝ≥0)⁻¹ ^ R i) := by ring

/-- The mild condition `64 p²N ≥ 1` makes the query budget at most the
square of the concrete threshold `⌊8pN⌋ + 1`. -/
theorem le_pairThreshold_eight_sq_of_density
    (p : ℝ≥0) (N : ℕ)
    (hdensity : 1 ≤ 64 * p ^ 2 * (N : ℝ≥0)) :
    (N : ℝ≥0) ≤ (pairThreshold 8 p N : ℝ≥0) ^ 2 := by
  have hbase : 8 * p * (N : ℝ≥0) <
      (pairThreshold 8 p N : ℝ≥0) := lt_pairThreshold 8 p N
  calc
    (N : ℝ≥0) ≤ (N : ℝ≥0) * (64 * p ^ 2 * (N : ℝ≥0)) := by
      simpa using mul_le_mul_left' hdensity (N : ℝ≥0)
    _ = (8 * p * (N : ℝ≥0)) ^ 2 := by ring
    _ ≤ (pairThreshold 8 p N : ℝ≥0) ^ 2 :=
      pow_le_pow_left₀ (zero_le _) hbase.le 2

/-- If `pN` tends to infinity, so does the explicit natural threshold
`⌊8pN⌋ + 1`. -/
theorem pairThreshold_eight_tendsto_atTop
    {ι : Type*} {l : Filter ι} (p : ι → ℝ≥0) (N : ι → ℕ)
    (hdensity : Tendsto (fun i ↦ p i * (N i : ℝ≥0)) l atTop) :
    Tendsto (fun i ↦ pairThreshold 8 (p i) (N i)) l atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ≥0)).mp
  apply Filter.tendsto_atTop_mono
      (fun i ↦ (lt_pairThreshold 8 (p i) (N i)).le)
  simpa only [mul_assoc] using
    hdensity.const_mul_atTop (by norm_num : (0 : ℝ≥0) < 8)

/-- Direct scale-free negligibility theorem for one local pair tail.  The
conditions `pN → ∞` and `p²N → ∞` are exactly what the target
`N≈p⁻¹⁰⁄³` scale supplies. -/
theorem pairTail_eight_tendsto_zero_of_density
    {ι : Type*} {l : Filter ι}
    (p : ι → ℝ≥0) (N : ι → ℕ) (H : K6FinitePattern)
    (hp : ∀ i, p i ≤ 1)
    (hlinear : Tendsto (fun i ↦ p i * (N i : ℝ≥0)) l atTop)
    (hquadratic : Tendsto (fun i ↦ p i ^ 2 * (N i : ℝ≥0)) l atTop) :
    Tendsto (fun i ↦ pairTail 8 (p i) (N i) H) l (𝓝 0) := by
  apply pairTail_eight_tendsto_zero_of_threshold p N H hp
    (pairThreshold_eight_tendsto_atTop p N hlinear)
  have hlarge : ∀ᶠ i in l, 1 ≤ p i ^ 2 * (N i : ℝ≥0) :=
    (tendsto_atTop.1 hquadratic) 1
  filter_upwards [hlarge] with i hi
  apply le_pairThreshold_eight_sq_of_density
  calc
    1 ≤ p i ^ 2 * (N i : ℝ≥0) := hi
    _ ≤ 64 * p i ^ 2 * (N i : ℝ≥0) := by
      have hsixfour : (1 : ℝ≥0) ≤ 64 := by norm_num
      calc
        p i ^ 2 * (N i : ℝ≥0) =
            (p i ^ 2 * (N i : ℝ≥0)) * 1 := by simp
        _ ≤ (p i ^ 2 * (N i : ℝ≥0)) * 64 :=
          mul_le_mul_left' hsixfour _
        _ = 64 * p i ^ 2 * (N i : ℝ≥0) := by ring

/-- The cubic substitution underlying the exponent `10/3`.  If `q → 0⁺`
and the normalized query budget `q¹⁰N` stays bounded below by a positive
constant, then, for Bernoulli density `p=q³`, both quantities needed by the
tail criterion diverge: `pN=q³N → ∞` and `p²N=q⁶N → ∞`. -/
theorem cubic_query_scales_tendsto_atTop
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (N : ι → ℕ) (c : ℝ≥0) (hc : 0 < c)
    (hq : Tendsto q l (𝓝[>] 0))
    (hscale : ∀ᶠ i in l, c ≤ q i ^ 10 * (N i : ℝ≥0)) :
    Tendsto (fun i ↦ q i ^ 3 * (N i : ℝ≥0)) l atTop ∧
      Tendsto (fun i ↦ q i ^ 6 * (N i : ℝ≥0)) l atTop := by
  have hqpos : ∀ᶠ i in l, 0 < q i := by
    exact hq.eventually (by
      simpa using
        (self_mem_nhdsWithin : Set.Ioi (0 : ℝ≥0) ∈ 𝓝[>] 0))
  have hinv : Tendsto (fun i ↦ (q i)⁻¹) l atTop :=
    hq.inv_tendsto_nhdsGT_zero
  constructor
  · refine Filter.tendsto_atTop_mono' l
      (f₁ := fun i ↦ c * (q i)⁻¹ ^ 7) ?_ ?_
    · filter_upwards [hqpos, hscale] with i hqi hsi
      calc
        c * (q i)⁻¹ ^ 7 ≤
            (q i ^ 10 * (N i : ℝ≥0)) * (q i)⁻¹ ^ 7 :=
          mul_le_mul_right' hsi _
        _ = q i ^ 3 * (N i : ℝ≥0) := by
          field_simp [ne_of_gt hqi]
    · exact ((tendsto_pow_atTop (by norm_num : 7 ≠ 0)).comp hinv)
        |>.const_mul_atTop hc
  · refine Filter.tendsto_atTop_mono' l
      (f₁ := fun i ↦ c * (q i)⁻¹ ^ 4) ?_ ?_
    · filter_upwards [hqpos, hscale] with i hqi hsi
      calc
        c * (q i)⁻¹ ^ 4 ≤
            (q i ^ 10 * (N i : ℝ≥0)) * (q i)⁻¹ ^ 4 :=
          mul_le_mul_right' hsi _
        _ = q i ^ 6 * (N i : ℝ≥0) := by
          field_simp [ne_of_gt hqi]
    · exact ((tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp hinv)
        |>.const_mul_atTop hc

/-- `NNReal` wrapper for the actual floored budget `⌊ell/q¹⁰⌋` used by the
finite scale module. -/
def nnrealQueryBudget (q ell : ℝ≥0) : ℕ :=
  AsymptoticScale.queryBudget (q : ℝ) (ell : ℝ)

/-- The exact half-to-one normalized bounds for the actual floored query
budget, transported from `Real` to `NNReal`. -/
theorem nnreal_normalized_queryBudget_bounds_half
    {q ell : ℝ≥0} (hq : 0 < q) (hsmall : 2 * q ^ 10 ≤ ell) :
    ell / 2 < q ^ 10 * (nnrealQueryBudget q ell : ℝ≥0) ∧
      q ^ 10 * (nnrealQueryBudget q ell : ℝ≥0) ≤ ell := by
  have h := AsymptoticScale.normalized_queryBudget_bounds_half
    (q := (q : ℝ)) (ell := (ell : ℝ))
    (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hsmall)
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- Under the same smallness condition, the floored budget is nonzero. -/
theorem nnrealQueryBudget_pos {q ell : ℝ≥0}
    (hq : 0 < q) (hsmall : 2 * q ^ 10 ≤ ell) :
    0 < nnrealQueryBudget q ell := by
  have hlower := (nnreal_normalized_queryBudget_bounds_half hq hsmall).1
  by_contra hzero
  have hz : nnrealQueryBudget q ell = 0 := Nat.eq_zero_of_not_pos hzero
  simp [hz] at hlower

private theorem prefixCopyCount_le_sixthPower {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (h : Transcript (Query N)) :
    prefixCopyCount hN H h ≤ (2 * N) ^ 6 := by
  calc
    prefixCopyCount hN H h ≤
        (Finset.univ : Finset (Fin 6 → Vertex N)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (2 * N) ^ 6 := by simp

/-- Fixed-strategy good/bad pair recurrence, with no asymptotic notation. -/
theorem strategyExpectedPrefixCopies_pair_le
    (kappa p : ℝ≥0) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (H : K6FinitePattern)
    (e : K6Edge) (he : e ∈ H.edges) :
    strategyExpectedPrefixCopies p hN strategy H ≤
      2 * kappa * p * N *
          strategyExpectedPrefixCopies p hN strategy (eraseFinitePair H e) +
        pairTail kappa p N H := by
  let child := eraseFinitePair H e
  let crude : ℝ≥0 := ((2 * N : ℕ) ^ 6 : ℝ≥0)
  let goodTerm : AnswerPath N → ℝ≥0 := fun bits ↦
    if (answerPathTrueCount bits : ℝ≥0) ≤ kappa * p * N then
      answerPathWeight p bits *
        (prefixCopyCount hN H (replay strategy (answerList bits)) : ℝ≥0)
    else 0
  let badTerm : AnswerPath N → ℝ≥0 := fun bits ↦
    if kappa * p * N < (answerPathTrueCount bits : ℝ≥0) then
      answerPathWeight p bits *
        (prefixCopyCount hN H (replay strategy (answerList bits)) : ℝ≥0)
    else 0
  have hsplit : strategyExpectedPrefixCopies p hN strategy H =
      (∑ bits, goodTerm bits) + ∑ bits, badTerm bits := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro bits _
    by_cases hgood : (answerPathTrueCount bits : ℝ≥0) ≤ kappa * p * N
    · have hnotbad : ¬kappa * p * N < (answerPathTrueCount bits : ℝ≥0) :=
        not_lt.mpr hgood
      simp [strategyExpectedPrefixCopies, goodTerm, badTerm, hgood, hnotbad]
    · have hbad : kappa * p * N < (answerPathTrueCount bits : ℝ≥0) :=
        lt_of_not_ge hgood
      simp [strategyExpectedPrefixCopies, goodTerm, badTerm, hgood, hbad]
  have hgoodSum : (∑ bits, goodTerm bits) ≤
      2 * kappa * p * N * strategyExpectedPrefixCopies p hN strategy child := by
    calc
      (∑ bits, goodTerm bits) ≤
          ∑ bits : AnswerPath N,
            2 * kappa * p * N *
              (answerPathWeight p bits *
                (prefixCopyCount hN child
                  (replay strategy (answerList bits)) : ℝ≥0)) := by
        apply Finset.sum_le_sum
        intro bits _
        by_cases hgood : (answerPathTrueCount bits : ℝ≥0) ≤ kappa * p * N
        · rw [show goodTerm bits = answerPathWeight p bits *
              (prefixCopyCount hN H
                (replay strategy (answerList bits)) : ℝ≥0) by
              simp [goodTerm, hgood]]
          have hcountNat := prefixCopyCount_pair_le_trueCount hN H
            (replay strategy (answerList bits)) e he
          have hcount :
              (prefixCopyCount hN H
                (replay strategy (answerList bits)) : ℝ≥0) ≤
                2 * (answerPathTrueCount bits : ℝ≥0) *
                  (prefixCopyCount hN child
                    (replay strategy (answerList bits)) : ℝ≥0) := by
            simpa [child, answerPathTrueCount, answers_replay] using
              (show
                (prefixCopyCount hN H
                    (replay strategy (answerList bits)) : ℝ≥0) ≤
                  ((2 * (answers (replay strategy (answerList bits))).count true *
                    prefixCopyCount hN child
                      (replay strategy (answerList bits)) : ℕ) : ℝ≥0) by
                    exact_mod_cast hcountNat)
          calc
            answerPathWeight p bits *
                (prefixCopyCount hN H
                  (replay strategy (answerList bits)) : ℝ≥0) ≤
              answerPathWeight p bits *
                (2 * (answerPathTrueCount bits : ℝ≥0) *
                  (prefixCopyCount hN child
                    (replay strategy (answerList bits)) : ℝ≥0)) :=
                mul_le_mul_left' hcount _
            _ ≤ answerPathWeight p bits *
                (2 * (kappa * p * N) *
                  (prefixCopyCount hN child
                    (replay strategy (answerList bits)) : ℝ≥0)) := by
                gcongr
            _ = 2 * kappa * p * N *
                (answerPathWeight p bits *
                  (prefixCopyCount hN child
                    (replay strategy (answerList bits)) : ℝ≥0)) := by ring
        · simp [goodTerm, hgood]
      _ = 2 * kappa * p * N * strategyExpectedPrefixCopies p hN strategy child := by
        change (∑ bits : AnswerPath N,
            2 * kappa * p * N * (answerPathWeight p bits *
              (prefixCopyCount hN child
                (replay strategy (answerList bits)) : ℝ≥0))) =
          2 * kappa * p * N * (∑ bits : AnswerPath N,
            answerPathWeight p bits *
              (prefixCopyCount hN child
                (replay strategy (answerList bits)) : ℝ≥0))
        exact (Finset.mul_sum Finset.univ _ _).symm
  have hbadSum : (∑ bits, badTerm bits) ≤ crude * pairBadMass kappa p N := by
    calc
      (∑ bits, badTerm bits) ≤
          ∑ bits : AnswerPath N,
            if kappa * p * N < (answerPathTrueCount bits : ℝ≥0) then
              answerPathWeight p bits * crude else 0 := by
        apply Finset.sum_le_sum
        intro bits _
        by_cases hbad : kappa * p * N < (answerPathTrueCount bits : ℝ≥0)
        · simp only [badTerm, hbad, if_true]
          have hcrude :
              (prefixCopyCount hN H
                (replay strategy (answerList bits)) : ℝ≥0) ≤ crude := by
            dsimp [crude]
            exact_mod_cast prefixCopyCount_le_sixthPower hN H
              (replay strategy (answerList bits))
          exact mul_le_mul_left' hcrude _
        · simp [badTerm, hbad]
      _ = crude * pairBadMass kappa p N := by
        change (∑ bits : AnswerPath N,
            if kappa * p * N < (answerPathTrueCount bits : ℝ≥0) then
              answerPathWeight p bits * crude else 0) =
          crude * (∑ bits : AnswerPath N,
            if kappa * p * N < (answerPathTrueCount bits : ℝ≥0) then
              answerPathWeight p bits else 0)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro bits _
        by_cases hbad : kappa * p * N < (answerPathTrueCount bits : ℝ≥0)
        · simp [hbad, mul_comm]
        · simp [hbad]
  rw [hsplit]
  simpa [child, pairTail, crude] using add_le_add hgoodSum hbadSum

/-- The genuine extremal expected prefix count, as a supremum over fresh
adaptive strategies on the canonical `2N`-vertex board. -/
def extremalExpectedPrefixCopies (p : ℝ≥0) {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) : ℝ≥0 :=
  sSup {x : ℝ≥0 | ∃ strategy : K6Strategy N,
    FreshForBudget strategy ∧ x = strategyExpectedPrefixCopies p hN strategy H}

/-! A canonical fresh strategy, used only to witness that the extremal set is
nonempty.  It queries distinct diagonal coordinates.  Diagonal queries cannot
create graph edges, but freshness is the sole property needed here. -/

def diagonalQuery {N : ℕ} (hN : 0 < N) (k : Fin N) : Query N :=
  Sym2.diag ⟨k.1, by omega⟩

theorem diagonalQuery_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (diagonalQuery hN) := by
  intro i j hij
  have hv : (⟨i.1, by omega⟩ : Vertex N) = ⟨j.1, by omega⟩ :=
    Sym2.diag_injective hij
  apply Fin.ext
  exact congrArg (fun x : Vertex N ↦ x.1) hv

def canonicalFreshStrategy {N : ℕ} (hN : 0 < N) : K6Strategy N :=
  fun h ↦
    if hk : h.length < N then diagonalQuery hN ⟨h.length, hk⟩
    else diagonalQuery hN ⟨0, hN⟩

private theorem mem_queries_replay_canonicalFresh {N : ℕ} (hN : 0 < N)
    (bits : List Bool) (hlen : bits.length ≤ N) (q : Query N)
    (hq : q ∈ queries (replay (canonicalFreshStrategy hN) bits)) :
    ∃ k : Fin N, k.1 < bits.length ∧ q = diagonalQuery hN k := by
  induction bits generalizing q with
  | nil => simp [queries] at hq
  | cons bit bits ih =>
      have htail : bits.length < N := by simpa using hlen
      simp only [replay_cons, queries, List.map_cons, List.mem_cons] at hq
      rcases hq with hq | hq
      · refine ⟨⟨bits.length, htail⟩, Nat.lt_succ_self _, ?_⟩
        simpa [canonicalFreshStrategy, htail] using hq
      · rcases ih (Nat.le_of_lt htail) q hq with ⟨k, hk, rfl⟩
        exact ⟨k, hk.trans (Nat.lt_succ_self _), rfl⟩

private theorem canonicalFreshStrategy_fresh_aux {N : ℕ} (hN : 0 < N)
    (bits : List Bool) (hlen : bits.length ≤ N) :
    FreshPath (canonicalFreshStrategy hN) bits := by
  unfold FreshPath
  induction bits with
  | nil => simp [queries]
  | cons bit tail ih =>
      have htail : tail.length < N := by simpa using hlen
      simp only [replay_cons, queries, List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases mem_queries_replay_canonicalFresh hN tail
            (Nat.le_of_lt htail) _ hmem with ⟨k, hk, heq⟩
        have hhead :
            canonicalFreshStrategy hN (replay (canonicalFreshStrategy hN) tail) =
              diagonalQuery hN ⟨tail.length, htail⟩ := by
          simp [canonicalFreshStrategy, htail]
        have heqd : diagonalQuery hN ⟨tail.length, htail⟩ =
            diagonalQuery hN k := hhead.symm.trans heq
        have hki := diagonalQuery_injective hN heqd
        have hv : tail.length = k.1 := congrArg Fin.val hki
        exact (Nat.ne_of_lt hk) hv.symm
      · exact ih (by simpa using Nat.le_of_lt htail)

theorem canonicalFreshStrategy_fresh {N : ℕ} (hN : 0 < N) :
    FreshForBudget (canonicalFreshStrategy hN) := by
  intro bits
  apply canonicalFreshStrategy_fresh_aux hN bits.toList
  simp

/-! ## A finite base bound -/

/-- Restriction of a canonical total map to its active labels. -/
def restrictCanonical {N : ℕ} {hN : 0 < N} {H : K6FinitePattern} :
    {f : Fin 6 → Vertex N // CanonicalMap hN H f} →
      ({v : Fin 6 // v ∈ activeLabels H} → Vertex N) :=
  fun f v ↦ f.1 v.1

theorem restrictCanonical_injective {N : ℕ} {hN : 0 < N}
    {H : K6FinitePattern} :
    Function.Injective (restrictCanonical (N := N) (hN := hN) (H := H)) := by
  intro f g hfg
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ activeLabels H
  · have := congrFun hfg ⟨v, hv⟩
    exact this
  · exact (f.2 v hv).trans (g.2 v hv).symm

theorem card_canonicalMap_le {N : ℕ} {hN : 0 < N}
    (H : K6FinitePattern) :
    Fintype.card {f : Fin 6 → Vertex N // CanonicalMap hN H f} ≤
      (2 * N) ^ (activeLabels H).card := by
  calc
    Fintype.card {f : Fin 6 → Vertex N // CanonicalMap hN H f} ≤
        Fintype.card ({v : Fin 6 // v ∈ activeLabels H} → Vertex N) :=
      Fintype.card_le_of_injective restrictCanonical restrictCanonical_injective
    _ = (2 * N) ^ (activeLabels H).card := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

theorem prefixCopyCount_le {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (h : Transcript (Query N)) :
    prefixCopyCount hN H h ≤ (2 * N) ^ (activeLabels H).card := by
  let embSubtype := {f : Fin 6 → Vertex N //
    f ∈ prefixEmbeddingFinset hN H h}
  let canonicalSubtype := {f : Fin 6 → Vertex N // CanonicalMap hN H f}
  let forget : embSubtype → canonicalSubtype := fun f ↦
    ⟨f.1, (Finset.mem_filter.mp f.2).2.2.1⟩
  have hinj : Function.Injective forget := by
    intro f g hfg
    apply Subtype.ext
    exact congrArg (fun x : canonicalSubtype ↦ x.1) hfg
  calc
    prefixCopyCount hN H h = Fintype.card embSubtype := by
      simp [prefixCopyCount, embSubtype]
    _ ≤ Fintype.card canonicalSubtype :=
      Fintype.card_le_of_injective forget hinj
    _ ≤ (2 * N) ^ (activeLabels H).card := card_canonicalMap_le H

theorem strategyExpectedPrefixCopies_le (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) (strategy : K6Strategy N)
    (H : K6FinitePattern) :
    strategyExpectedPrefixCopies p hN strategy H ≤
      ((2 * N : ℕ) ^ (activeLabels H).card : ℝ≥0) := by
  calc
    strategyExpectedPrefixCopies p hN strategy H ≤
        ∑ bits : AnswerPath N,
          answerPathWeight p bits *
            (((2 * N : ℕ) ^ (activeLabels H).card : ℕ) : ℝ≥0) := by
      apply Finset.sum_le_sum
      intro bits _
      have hcount :
          (prefixCopyCount hN H (replay strategy (answerList bits)) : ℝ≥0) ≤
            (((2 * N) ^ (activeLabels H).card : ℕ) : ℝ≥0) := by
        exact_mod_cast
          prefixCopyCount_le hN H (replay strategy (answerList bits))
      exact mul_le_mul_left'
        hcount _
    _ = ((2 * N : ℕ) ^ (activeLabels H).card : ℝ≥0) := by
      rw [← Finset.sum_mul, sum_answerPathWeight p hp, one_mul]
      norm_cast

theorem extremalExpectedPrefixCopies_le (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) (H : K6FinitePattern) :
    extremalExpectedPrefixCopies p hN H ≤
      ((2 * N : ℕ) ^ (activeLabels H).card : ℝ≥0) := by
  apply csSup_le
  · exact ⟨strategyExpectedPrefixCopies p hN (canonicalFreshStrategy hN) H,
      canonicalFreshStrategy hN, canonicalFreshStrategy_fresh hN, rfl⟩
  intro x hx
  rcases hx with ⟨strategy, _hfresh, rfl⟩
  exact strategyExpectedPrefixCopies_le p hp hN strategy H

/-- The empty-pattern estimate in exactly the form used by
`RecurrenceSemantics`. -/
theorem extremal_empty_bound (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ}
    (hN : 0 < N) (H : K6FinitePattern) :
    extremalExpectedPrefixCopies p hN H ≤
      (2 * (N : ℝ≥0)) ^ k6FinitePrefixSystem.vertexCount H := by
  rw [← card_activeLabels H]
  simpa [Nat.cast_mul, Nat.cast_ofNat] using
    extremalExpectedPrefixCopies_le p hp hN H

theorem strategyExpectedPrefixCopies_le_extremal
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (H : K6FinitePattern) :
    strategyExpectedPrefixCopies p hN strategy H ≤
      extremalExpectedPrefixCopies p hN H := by
  apply le_csSup
  · refine ⟨((2 * N : ℕ) ^ (activeLabels H).card : ℝ≥0), ?_⟩
    intro x hx
    rcases hx with ⟨other, _hother, rfl⟩
    exact strategyExpectedPrefixCopies_le p hp hN other H
  · exact ⟨strategy, hfresh, rfl⟩

/-- Supremum-level last-positive-exposure recurrence for the actual finite
adaptive prefix expectation.  There is no edge exceptional term. -/
theorem extremalExpectedPrefixCopies_edge_le
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (hNonempty : H.edges.Nonempty) :
    extremalExpectedPrefixCopies p hN H ≤
      p * ∑ e : PresentEdge k6FinitePrefixSystem H,
        extremalExpectedPrefixCopies p hN
          (k6FinitePrefixSystem.eraseEdge H e.1) := by
  apply csSup_le
  · exact ⟨strategyExpectedPrefixCopies p hN (canonicalFreshStrategy hN) H,
      canonicalFreshStrategy hN, canonicalFreshStrategy_fresh hN, rfl⟩
  · intro x hx
    rcases hx with ⟨strategy, hfresh, rfl⟩
    calc
      strategyExpectedPrefixCopies p hN strategy H ≤
          p * ∑ e ∈ H.edges,
            strategyExpectedPrefixCopies p hN strategy (eraseFiniteEdge H e) :=
        strategyExpectedPrefixCopies_edge_le
          p hp hN strategy hfresh H hNonempty
      _ ≤ p * ∑ e ∈ H.edges,
            extremalExpectedPrefixCopies p hN (eraseFiniteEdge H e) := by
        gcongr with e he
        exact strategyExpectedPrefixCopies_le_extremal
          p hp hN strategy hfresh _
      _ = p * ∑ e : PresentEdge k6FinitePrefixSystem H,
            extremalExpectedPrefixCopies p hN
              (k6FinitePrefixSystem.eraseEdge H e.1) := by
        congr 1
        rw [Finset.sum_subtype H.edges]
        · rfl
        · intro e
          rfl

/-- Supremum-level pair recurrence for the actual finite adaptive prefix
expectation.  This is the analytic pair field required by
`PrefixSoundness.RecurrenceSemantics`, with an explicit finite bad-tail sum. -/
theorem extremalExpectedPrefixCopies_pair_le
    (kappa p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) (e : K6Edge) (he : e ∈ H.edges) :
    extremalExpectedPrefixCopies p hN H ≤
      2 * kappa * p * N *
          extremalExpectedPrefixCopies p hN (eraseFinitePair H e) +
        pairTail kappa p N H := by
  apply csSup_le
  · exact ⟨strategyExpectedPrefixCopies p hN (canonicalFreshStrategy hN) H,
      canonicalFreshStrategy hN, canonicalFreshStrategy_fresh hN, rfl⟩
  · intro x hx
    rcases hx with ⟨strategy, hfresh, rfl⟩
    calc
      strategyExpectedPrefixCopies p hN strategy H ≤
          2 * kappa * p * N *
              strategyExpectedPrefixCopies p hN strategy (eraseFinitePair H e) +
            pairTail kappa p N H :=
        strategyExpectedPrefixCopies_pair_le kappa p hN strategy H e he
      _ ≤ 2 * kappa * p * N *
              extremalExpectedPrefixCopies p hN (eraseFinitePair H e) +
            pairTail kappa p N H := by
        gcongr
        exact strategyExpectedPrefixCopies_le_extremal p hp hN strategy hfresh _

/-! ## Uniform propagation of pair tails through a derivation -/

universe u v

/-- A structural coefficient controlling the propagation of a uniform pair
tail through a recurrence derivation. -/
noncomputable def derivationTailComplexity
    {Pattern : Type u} {Edge : Type v} [DecidableEq Edge]
    (S : PrefixSystem Pattern Edge) :
    {b : ℕ} → {H : Pattern} → {a : ℕ} → Derivation S b H a → ℕ
  | _, _, _, .empty _ _ => 0
  | _, _, _, .edge _ _ _ children =>
      ∑ e, derivationTailComplexity S (children e)
  | _, _, _, .pair _ _ _ child =>
      1 + 2 * derivationTailComplexity S child

/-- A uniform local pair-tail bound propagates through any derivation with at
most the displayed structural coefficient and `b` powers of `1 + N`. -/
theorem derivationTail_le_complexity
    {Pattern : Type u} {Edge : Type v} [DecidableEq Edge]
    (S : PrefixSystem Pattern Edge) (M : RecurrenceSemantics S) (T : ℝ≥0)
    (hedge : ∀ H, M.edgeTail H = 0)
    (hpair : ∀ H e, M.pairTail H e ≤ T)
    {b : ℕ} {H : Pattern} {a : ℕ} (D : Derivation S b H a) :
    Derivation.tail (S := S) (M := M) D ≤
      (derivationTailComplexity S D : ℝ≥0) * (1 + M.N) ^ b * T := by
  induction D with
  | @empty b₀ H₀ hEmpty hVertices =>
      simp [Derivation.tail, derivationTailComplexity]
  | @edge b₀ H₀ a₀ hNonempty childExponent hExponent children ih =>
      rw [Derivation.tail, hedge, zero_add]
      calc
        M.p * ∑ e, Derivation.tail (S := S) (M := M) (children e) ≤
            M.p * ∑ e, (derivationTailComplexity S (children e) : ℝ≥0) *
              (1 + M.N) ^ b₀ * T := by
          gcongr with e
          exact ih e
        _ ≤ 1 * ∑ e, (derivationTailComplexity S (children e) : ℝ≥0) *
              (1 + M.N) ^ b₀ * T := by
          gcongr
          exact M.p_le_one
        _ = (derivationTailComplexity S
              (Derivation.edge hNonempty childExponent hExponent children) : ℝ≥0) *
              (1 + M.N) ^ b₀ * T := by
          simp only [one_mul, derivationTailComplexity, Nat.cast_sum]
          rw [Finset.sum_mul, Finset.sum_mul]
  | @pair b₀ H₀ a₀ e childExponent hExponent child ih =>
      rw [Derivation.tail]
      let B : ℝ≥0 := 1 + M.N
      let c : ℝ≥0 := derivationTailComplexity S child
      have hB : 1 ≤ B := by simp [B]
      have hpow : 1 ≤ B ^ (b₀ + 1) := one_le_pow₀ hB
      have hpN : M.p * M.N ≤ B := by
        calc
          M.p * M.N ≤ 1 * M.N := mul_le_mul_right' M.p_le_one _
          _ = M.N := one_mul _
          _ ≤ 1 + M.N := le_add_self
          _ = B := rfl
      have hfirst : M.pairTail H₀ e.1 ≤ B ^ (b₀ + 1) * T := by
        exact (hpair H₀ e.1).trans
          (by simpa using mul_le_mul_right' hpow T)
      have hsecond :
          2 * M.p * M.N * Derivation.tail (S := S) (M := M) child ≤
            2 * c * B ^ (b₀ + 1) * T := by
        calc
          2 * M.p * M.N * Derivation.tail (S := S) (M := M) child ≤
              2 * M.p * M.N * (c * B ^ b₀ * T) := by
            exact mul_le_mul_left' (by simpa [B, c] using ih) _
          _ = 2 * c * (M.p * M.N) * B ^ b₀ * T := by ring
          _ ≤ 2 * c * B * B ^ b₀ * T := by gcongr
          _ = 2 * c * B ^ (b₀ + 1) * T := by
            rw [pow_succ]
            ring
      calc
        M.pairTail H₀ e.1 +
            2 * M.p * M.N * Derivation.tail (S := S) (M := M) child ≤
          B ^ (b₀ + 1) * T + 2 * c * B ^ (b₀ + 1) * T :=
            add_le_add hfirst hsecond
        _ = (derivationTailComplexity S
              (Derivation.pair e childExponent hExponent child) : ℝ≥0) *
              (1 + M.N) ^ (b₀ + 1) * T := by
          simp only [derivationTailComplexity, Nat.cast_add, Nat.cast_one,
            Nat.cast_mul, Nat.cast_ofNat]
          change B ^ (b₀ + 1) * T + 2 * c * B ^ (b₀ + 1) * T =
            (1 + 2 * c) * B ^ (b₀ + 1) * T
          ring

/-- The formal residual of the edge recurrence. -/
def edgeResidual (p : ℝ≥0) {N : ℕ} (hN : 0 < N)
    (H : K6FinitePattern) : ℝ≥0 :=
  extremalExpectedPrefixCopies p hN H -
    p * ∑ e : PresentEdge k6FinitePrefixSystem H,
      extremalExpectedPrefixCopies p hN
        (k6FinitePrefixSystem.eraseEdge H e.1)

theorem edgeResidual_eq_zero (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) (H : K6FinitePattern)
    (hNonempty : H.edges.Nonempty) :
    edgeResidual p hN H = 0 := by
  exact tsub_eq_zero_iff_le.mpr
    (extremalExpectedPrefixCopies_edge_le p hp hN H hNonempty)

/-- A completely instantiated recurrence semantics.  Its edge tail is
identically zero; its pair tail is the explicit finite bad-event sum. -/
def finitePrefixSemantics (kappa p : ℝ≥0) (hkappa : 1 ≤ kappa)
    (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) :
    RecurrenceSemantics k6FinitePrefixSystem where
  p := p
  N := kappa * N
  p_le_one := hp
  one_le_N := by
    calc
      1 ≤ kappa := hkappa
      _ ≤ kappa * (N : ℝ≥0) := by
        simpa using mul_le_mul_left' (show (1 : ℝ≥0) ≤ N by exact_mod_cast hN) kappa
  value := extremalExpectedPrefixCopies p hN
  edgeTail := fun _ ↦ 0
  pairTail := fun H _ ↦ pairTail kappa p N H
  empty_bound := by
    intro H _hEmpty
    calc
      extremalExpectedPrefixCopies p hN H ≤
          (2 * (N : ℝ≥0)) ^ k6FinitePrefixSystem.vertexCount H :=
        extremal_empty_bound p hp hN H
      _ ≤ (2 * (kappa * (N : ℝ≥0))) ^
          k6FinitePrefixSystem.vertexCount H := by
        gcongr
        exact le_mul_of_one_le_left (zero_le _) hkappa
  edge_bound := by
    intro H hNonempty
    simpa using extremalExpectedPrefixCopies_edge_le p hp hN H hNonempty
  pair_bound := by
    intro H e
    have hpair := extremalExpectedPrefixCopies_pair_le
      kappa p hp hN H e.1 e.2
    calc
      extremalExpectedPrefixCopies p hN H ≤
          2 * kappa * p * (N : ℝ≥0) *
              extremalExpectedPrefixCopies p hN
                (k6FinitePrefixSystem.erasePair H e.1) +
            pairTail kappa p N H := hpair
      _ = 2 * p * (kappa * (N : ℝ≥0)) *
              extremalExpectedPrefixCopies p hN
                (k6FinitePrefixSystem.erasePair H e.1) +
            pairTail kappa p N H := by ring

/-- At slack eight, every accumulated derivation tail is bounded by a
structural constant, a degree-`b+6` polynomial factor, and the explicit
half-power exponential. -/
theorem finitePrefixSemantics_eight_tail_le
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    {b : ℕ} {H : K6FinitePattern} {a : ℕ}
    (D : Derivation k6FinitePrefixSystem b H a) :
    Derivation.tail (S := k6FinitePrefixSystem)
        (M := finitePrefixSemantics 8 p (by norm_num) hp hN) D ≤
      (derivationTailComplexity k6FinitePrefixSystem D : ℝ≥0) *
        (1 + 8 * (N : ℝ≥0)) ^ b *
          (((2 * N : ℕ) ^ 6 : ℝ≥0) *
            (2 : ℝ≥0)⁻¹ ^ pairThreshold 8 p N) := by
  apply derivationTail_le_complexity k6FinitePrefixSystem
    (finitePrefixSemantics 8 p (by norm_num) hp hN)
    (((2 * N : ℕ) ^ 6 : ℝ≥0) *
      (2 : ℝ≥0)⁻¹ ^ pairThreshold 8 p N)
  · intro H
    rfl
  · intro H e
    exact pairTail_eight_le_half_pow p hp N H

/-- Along any scale where the threshold tends to infinity and `N` is
eventually at most its square, the complete tail propagated through a fixed
derivation tends to zero.  The proof exposes the dominating sequence
`C R^(2b+12) 2⁻ᴿ`. -/
theorem finitePrefixSemantics_eight_tail_tendsto_zero_of_threshold
    {ι : Type*} {l : Filter ι}
    (p : ι → ℝ≥0) (N : ι → ℕ)
    (hp : ∀ i, p i ≤ 1) (hNpos : ∀ i, 0 < N i)
    {b : ℕ} {H : K6FinitePattern} {a : ℕ}
    (D : Derivation k6FinitePrefixSystem b H a)
    (hthreshold : Tendsto
      (fun i ↦ pairThreshold 8 (p i) (N i)) l atTop)
    (hN : ∀ᶠ i in l,
      (N i : ℝ≥0) ≤
        (pairThreshold 8 (p i) (N i) : ℝ≥0) ^ 2) :
    Tendsto (fun i ↦
      Derivation.tail (S := k6FinitePrefixSystem)
        (M := finitePrefixSemantics 8 (p i) (by norm_num)
          (hp i) (hNpos i)) D) l (𝓝 0) := by
  let R : ι → ℕ := fun i ↦ pairThreshold 8 (p i) (N i)
  let C : ℝ≥0 :=
    (derivationTailComplexity k6FinitePrefixSystem D : ℝ≥0) *
      9 ^ b * 64
  have hdecay : Tendsto
      (fun i ↦ C * ((R i : ℝ≥0) ^ (2 * b + 12) *
        (2 : ℝ≥0)⁻¹ ^ R i)) l (𝓝 0) := by
    simpa [Function.comp_def] using
      (polynomial_mul_half_pow_tendsto_zero (2 * b + 12)).comp hthreshold
        |>.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0)) l (𝓝 0))
      hdecay
  · exact Filter.Eventually.of_forall (fun _ ↦ zero_le _)
  · filter_upwards [hN] with i hi
    have hRone : (1 : ℝ≥0) ≤ (R i : ℝ≥0) := by
      exact_mod_cast pairThreshold_pos 8 (p i) (N i)
    have hlinear : 1 + 8 * (N i : ℝ≥0) ≤
        9 * (R i : ℝ≥0) ^ 2 := by
      calc
        1 + 8 * (N i : ℝ≥0) ≤
            (R i : ℝ≥0) ^ 2 + 8 * (R i : ℝ≥0) ^ 2 := by
          exact add_le_add (one_le_pow₀ hRone)
            (mul_le_mul_left' hi 8)
        _ = 9 * (R i : ℝ≥0) ^ 2 := by ring
    have hcrude : ((2 * N i : ℕ) ^ 6 : ℝ≥0) ≤
        64 * (R i : ℝ≥0) ^ 12 := by
      rw [show ((2 * N i : ℕ) ^ 6 : ℝ≥0) =
          64 * (N i : ℝ≥0) ^ 6 by
        push_cast
        ring]
      apply mul_le_mul_left'
      calc
        (N i : ℝ≥0) ^ 6 ≤ ((R i : ℝ≥0) ^ 2) ^ 6 :=
          pow_le_pow_left₀ (zero_le _) hi 6
        _ = (R i : ℝ≥0) ^ 12 := by ring
    calc
      Derivation.tail (S := k6FinitePrefixSystem)
          (M := finitePrefixSemantics 8 (p i) (by norm_num)
            (hp i) (hNpos i)) D ≤
        (derivationTailComplexity k6FinitePrefixSystem D : ℝ≥0) *
          (1 + 8 * (N i : ℝ≥0)) ^ b *
            (((2 * N i : ℕ) ^ 6 : ℝ≥0) *
              (2 : ℝ≥0)⁻¹ ^ R i) :=
        finitePrefixSemantics_eight_tail_le (p i) (hp i) (hNpos i) D
      _ ≤ (derivationTailComplexity k6FinitePrefixSystem D : ℝ≥0) *
          (9 * (R i : ℝ≥0) ^ 2) ^ b *
            ((64 * (R i : ℝ≥0) ^ 12) *
              (2 : ℝ≥0)⁻¹ ^ R i) := by
        gcongr
      _ = C * ((R i : ℝ≥0) ^ (2 * b + 12) *
          (2 : ℝ≥0)⁻¹ ^ R i) := by
        simp only [C]
        rw [mul_pow, ← pow_mul]
        ring

/-- A scale-free negligibility criterion tailored to the query problem.
If `pN → ∞` and `p²N → ∞`, then every accumulated pair tail tends to zero.
For the target substitution `p=q³`, `N≈q⁻¹⁰`, these quantities have orders
`q⁻⁷` and `q⁻⁴`, respectively. -/
theorem finitePrefixSemantics_eight_tail_tendsto_zero_of_density
    {ι : Type*} {l : Filter ι}
    (p : ι → ℝ≥0) (N : ι → ℕ)
    (hp : ∀ i, p i ≤ 1) (hNpos : ∀ i, 0 < N i)
    {b : ℕ} {H : K6FinitePattern} {a : ℕ}
    (D : Derivation k6FinitePrefixSystem b H a)
    (hlinear : Tendsto (fun i ↦ p i * (N i : ℝ≥0)) l atTop)
    (hquadratic : Tendsto (fun i ↦ p i ^ 2 * (N i : ℝ≥0)) l atTop) :
    Tendsto (fun i ↦
      Derivation.tail (S := k6FinitePrefixSystem)
        (M := finitePrefixSemantics 8 (p i) (by norm_num)
          (hp i) (hNpos i)) D) l (𝓝 0) := by
  apply finitePrefixSemantics_eight_tail_tendsto_zero_of_threshold
    p N hp hNpos D (pairThreshold_eight_tendsto_atTop p N hlinear)
  have hlarge : ∀ᶠ i in l, 1 ≤ p i ^ 2 * (N i : ℝ≥0) :=
    (tendsto_atTop.1 hquadratic) 1
  filter_upwards [hlarge] with i hi
  apply le_pairThreshold_eight_sq_of_density
  calc
    1 ≤ p i ^ 2 * (N i : ℝ≥0) := hi
    _ ≤ 64 * p i ^ 2 * (N i : ℝ≥0) := by
      have hsixfour : (1 : ℝ≥0) ≤ 64 := by norm_num
      calc
        p i ^ 2 * (N i : ℝ≥0) =
            (p i ^ 2 * (N i : ℝ≥0)) * 1 := by simp
        _ ≤ (p i ^ 2 * (N i : ℝ≥0)) * 64 :=
          mul_le_mul_left' hsixfour _
        _ = 64 * p i ^ 2 * (N i : ℝ≥0) := by ring

/-- Unconditional application of the checked ordinary-prefix certificate to
the finite adaptive semantics.  Its pair tails are the explicit binomial
bad-event sums above; every edge tail is zero. -/
theorem ordinaryNineEdge_finiteSemantic_bound
    (kappa p : ℝ≥0) (hkappa : 1 ≤ kappa) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N)
    (g : Fin K6Prefix.graphCount)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      4 ≤ a ∧
      extremalExpectedPrefixCopies p hN
          (finitePatternOfMasks fullVertexMask g) ≤
        Derivation.coefficient (S := k6FinitePrefixSystem) D *
            p ^ 4 * (kappa * (N : ℝ≥0)) ^ 3 +
          Derivation.tail (S := k6FinitePrefixSystem)
            (M := finitePrefixSemantics kappa p hkappa hp hN) D :=
  ordinaryNineEdge_sound (finitePrefixSemantics kappa p hkappa hp hN)
    g hNine hOrdinary

/-- Ordinary nine-edge bound with no opaque semantic tail: the entire error
is an explicit polynomial times `2^(-floor(8pN)-1)`. -/
theorem ordinaryNineEdge_finiteSemantic_eight_bound
    (p : ℝ≥0) (hp : p ≤ 1) {N : ℕ} (hN : 0 < N)
    (g : Fin K6Prefix.graphCount)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      4 ≤ a ∧
      extremalExpectedPrefixCopies p hN
          (finitePatternOfMasks fullVertexMask g) ≤
        Derivation.coefficient (S := k6FinitePrefixSystem) D *
            p ^ 4 * (8 * (N : ℝ≥0)) ^ 3 +
          (derivationTailComplexity k6FinitePrefixSystem D : ℝ≥0) *
            (1 + 8 * (N : ℝ≥0)) ^ 3 *
              (((2 * N : ℕ) ^ 6 : ℝ≥0) *
                (2 : ℝ≥0)⁻¹ ^ pairThreshold 8 p N) := by
  rcases ordinaryNineEdge_finiteSemantic_bound
      8 p (by norm_num) hp hN g hNine hOrdinary with ⟨a, D, hFour, hvalue⟩
  refine ⟨a, D, hFour, hvalue.trans ?_⟩
  gcongr
  exact finitePrefixSemantics_eight_tail_le p hp hN D

/-- The ordinary-mask certificate can be chosen once and for all, independently
of the probability and query budget subsequently used to interpret it. -/
theorem ordinaryNineEdge_has_fixedDerivation
    (g : Fin K6Prefix.graphCount)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      4 ≤ a := by
  rcases ordinaryNineEdge_finiteSemantic_bound
      8 0 (by norm_num) (by norm_num) (by norm_num : 0 < (1 : ℕ))
      g hNine hOrdinary with ⟨a, D, hFour, _⟩
  exact ⟨a, D, hFour⟩

/-- A fixed ordinary-mask derivation bounds every finite semantic
interpretation.  This separates the finite certificate from all subsequent
limit arguments. -/
theorem ordinaryNineEdge_fixedDerivation_bound
    {g : Fin K6Prefix.graphCount} {a : ℕ}
    (D : Derivation k6FinitePrefixSystem 3
      (finitePatternOfMasks fullVertexMask g) a)
    (hFour : 4 ≤ a) (p : ℝ≥0) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N) :
    extremalExpectedPrefixCopies p hN
        (finitePatternOfMasks fullVertexMask g) ≤
      Derivation.coefficient (S := k6FinitePrefixSystem) D *
          p ^ 4 * (8 * (N : ℝ≥0)) ^ 3 +
        Derivation.tail (S := k6FinitePrefixSystem)
          (M := finitePrefixSemantics 8 p (by norm_num) hp hN) D := by
  have hsound := Derivation.sound (S := k6FinitePrefixSystem)
    (M := finitePrefixSemantics 8 p (by norm_num) hp hN) D
  refine hsound.trans ?_
  exact add_le_add_right
    (mul_le_mul_right'
      (mul_le_mul_left'
        (pow_le_pow_of_le_one (zero_le p) hp hFour)
        (Derivation.coefficient (S := k6FinitePrefixSystem) D))
      ((8 * (N : ℝ≥0)) ^ 3)) _

/-- Full cubic-scale closure for an ordinary nine-edge prefix.

Here `p=q³`, so `N≈q⁻¹⁰` is exactly `N≈p⁻¹⁰⁄³`.  The same fixed checked
derivation works at every scale.  Its complete additive tail tends to zero,
while multiplication by the six still-unexposed clique edges turns the main
term into the uniform constant
`512 * coefficient(D) * C³` whenever `q¹⁰N ≤ C`.
-/
theorem ordinaryNineEdge_cubicScale_bound
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (N : ι → ℕ) (c C : ℝ≥0) (hc : 0 < c)
    (hq : Tendsto q l (𝓝[>] 0))
    (hq1 : ∀ i, q i ≤ 1) (hNpos : ∀ i, 0 < N i)
    (hscaleLower : ∀ᶠ i in l,
      c ≤ q i ^ 10 * (N i : ℝ≥0))
    (hscaleUpper : ∀ i, q i ^ 10 * (N i : ℝ≥0) ≤ C)
    (g : Fin K6Prefix.graphCount)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      4 ≤ a ∧
      Tendsto (fun i ↦
        Derivation.tail (S := k6FinitePrefixSystem)
          (M := finitePrefixSemantics 8 (q i ^ 3) (by norm_num)
            (pow_le_one₀ (zero_le _) (hq1 i)) (hNpos i)) D) l (𝓝 0) ∧
      ∀ i,
        q i ^ 18 * extremalExpectedPrefixCopies (q i ^ 3) (hNpos i)
            (finitePatternOfMasks fullVertexMask g) ≤
          512 * Derivation.coefficient (S := k6FinitePrefixSystem) D * C ^ 3 +
            Derivation.tail (S := k6FinitePrefixSystem)
              (M := finitePrefixSemantics 8 (q i ^ 3) (by norm_num)
                (pow_le_one₀ (zero_le _) (hq1 i)) (hNpos i)) D := by
  rcases ordinaryNineEdge_has_fixedDerivation g hNine hOrdinary with
    ⟨a, D, hFour⟩
  refine ⟨a, D, hFour, ?_, ?_⟩
  · rcases cubic_query_scales_tendsto_atTop q N c hc hq hscaleLower with
      ⟨hlinear, hquadratic⟩
    apply finitePrefixSemantics_eight_tail_tendsto_zero_of_density
      (fun i ↦ q i ^ 3) N
      (fun i ↦ pow_le_one₀ (zero_le _) (hq1 i)) hNpos D hlinear
    convert hquadratic using 1 <;> funext i <;> ring
  · intro i
    let tail : ℝ≥0 := Derivation.tail (S := k6FinitePrefixSystem)
      (M := finitePrefixSemantics 8 (q i ^ 3) (by norm_num)
        (pow_le_one₀ (zero_le _) (hq1 i)) (hNpos i)) D
    have hprefix := ordinaryNineEdge_fixedDerivation_bound D hFour
      (q i ^ 3) (pow_le_one₀ (zero_le _) (hq1 i)) (hNpos i)
    have hscalePow :
        (q i ^ 10 * (N i : ℝ≥0)) ^ 3 ≤ C ^ 3 :=
      pow_le_pow_left₀ (zero_le _) (hscaleUpper i) 3
    have hq18 : q i ^ 18 ≤ (1 : ℝ≥0) :=
      pow_le_one₀ (zero_le _) (hq1 i)
    calc
      q i ^ 18 * extremalExpectedPrefixCopies (q i ^ 3) (hNpos i)
          (finitePatternOfMasks fullVertexMask g) ≤
        q i ^ 18 *
          (Derivation.coefficient (S := k6FinitePrefixSystem) D *
              (q i ^ 3) ^ 4 * (8 * (N i : ℝ≥0)) ^ 3 + tail) :=
        mul_le_mul_left' hprefix _
      _ = 512 * Derivation.coefficient (S := k6FinitePrefixSystem) D *
          (q i ^ 10 * (N i : ℝ≥0)) ^ 3 + q i ^ 18 * tail := by
        dsimp [tail]
        ring
      _ ≤ 512 * Derivation.coefficient (S := k6FinitePrefixSystem) D *
          C ^ 3 + tail := by
        exact add_le_add
          (mul_le_mul_left' hscalePow
            (512 * Derivation.coefficient (S := k6FinitePrefixSystem) D))
          (by
            calc
              q i ^ 18 * tail ≤ 1 * tail :=
                mul_le_mul_right' hq18 tail
              _ = tail := one_mul _)

/-- Specialization of `ordinaryNineEdge_cubicScale_bound` to the actual
natural budget `N=⌊ell/q¹⁰⌋`.  The normalized budget lies in
`(ell/2, ell]`, so the ordinary-prefix contribution after exposing the six
remaining clique edges is bounded by the concrete main constant
`512 * coefficient(D) * ell³` plus a tail tending to zero. -/
theorem ordinaryNineEdge_queryBudget_cubicScale_bound
    {ι : Type*} {l : Filter ι}
    (q : ι → ℝ≥0) (ell : ℝ≥0) (hell : 0 < ell)
    (hq : Tendsto q l (𝓝[>] 0))
    (hqpos : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1)
    (hsmall : ∀ i, 2 * q i ^ 10 ≤ ell)
    (g : Fin K6Prefix.graphCount)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      4 ≤ a ∧
      Tendsto (fun i ↦
        Derivation.tail (S := k6FinitePrefixSystem)
          (M := finitePrefixSemantics 8 (q i ^ 3) (by norm_num)
            (pow_le_one₀ (zero_le _) (hq1 i))
            (nnrealQueryBudget_pos (hqpos i) (hsmall i))) D) l (𝓝 0) ∧
      ∀ i,
        q i ^ 18 * extremalExpectedPrefixCopies (q i ^ 3)
            (nnrealQueryBudget_pos (hqpos i) (hsmall i))
            (finitePatternOfMasks fullVertexMask g) ≤
          512 * Derivation.coefficient (S := k6FinitePrefixSystem) D * ell ^ 3 +
            Derivation.tail (S := k6FinitePrefixSystem)
              (M := finitePrefixSemantics 8 (q i ^ 3) (by norm_num)
                (pow_le_one₀ (zero_le _) (hq1 i))
                (nnrealQueryBudget_pos (hqpos i) (hsmall i))) D := by
  apply ordinaryNineEdge_cubicScale_bound q
    (fun i ↦ nnrealQueryBudget (q i) ell) (ell / 2) ell
    (by positivity) hq hq1
    (fun i ↦ nnrealQueryBudget_pos (hqpos i) (hsmall i))
  · exact Filter.Eventually.of_forall fun i ↦
      (nnreal_normalized_queryBudget_bounds_half
        (hqpos i) (hsmall i)).1.le
  · exact fun i ↦
      (nnreal_normalized_queryBudget_bounds_half
        (hqpos i) (hsmall i)).2
  · exact hNine
  · exact hOrdinary

end

end OnlineRamsey.RecurrenceInstantiation
