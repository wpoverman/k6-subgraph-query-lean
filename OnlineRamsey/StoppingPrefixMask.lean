import OnlineRamsey.StoppingPrefixCount

/-!
# Canonical executable masks for ordered stopping prefixes

This file converts the first `r` edges of an abstract relative edge order
into the exact fifteen-bit mask consumed by the checked recurrence.  The
construction goes through an equivalence between the fixed executable edge
coordinates and the unordered nonloop source edges; no choice of vertex
relabeling or orbit representative is hidden.
-/

open scoped BigOperators ENNReal NNReal

namespace OnlineRamsey
namespace StoppingPrefixCount

open QueryComplexity LowerAssembly StoppingHistory StoppingCoverage
  PrefixSoundness RecurrenceInstantiation

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem edgeCoord_not_diag (d : PrefixSoundness.K6Edge) :
    ¬(edgeCoord d).IsDiag := by
  simpa [edgeCoord, Sym2.mk_isDiag_iff] using
    (ne_of_lt (edgeLo_lt_edgeHi d))

def edgeCoordSubtype (d : PrefixSoundness.K6Edge) :
    StoppingHistory.K6Edge :=
  ⟨edgeCoord d, edgeCoord_not_diag d⟩

theorem edgeCoordSubtype_injective : Function.Injective edgeCoordSubtype := by
  intro d e hde
  apply edgeCoord_injective
  exact congrArg Subtype.val hde

theorem card_prefixEdge_eq_card_stoppingEdge :
    Fintype.card PrefixSoundness.K6Edge =
      Fintype.card StoppingHistory.K6Edge := by
  rw [StoppingHistory.card_k6Edge]
  rfl

def prefixEdgeEquivStoppingEdge :
    PrefixSoundness.K6Edge ≃ StoppingHistory.K6Edge :=
  Equiv.ofBijective edgeCoordSubtype
    ((Fintype.bijective_iff_injective_and_card edgeCoordSubtype).mpr
      ⟨edgeCoordSubtype_injective, card_prefixEdge_eq_card_stoppingEdge⟩)

@[simp] theorem prefixEdgeEquivStoppingEdge_apply_val
    (d : PrefixSoundness.K6Edge) :
    (prefixEdgeEquivStoppingEdge d).1 = edgeCoord d := rfl

def sourceEdgeIndex (i : Fin 15) : PrefixSoundness.K6Edge :=
  prefixEdgeEquivStoppingEdge.symm (StoppingHistory.edgeEquiv i)

theorem sourceEdgeIndex_injective : Function.Injective sourceEdgeIndex :=
  prefixEdgeEquivStoppingEdge.symm.injective.comp
    StoppingHistory.edgeEquiv.injective

@[simp] theorem edgeCoord_sourceEdgeIndex (i : Fin 15) :
    edgeCoord (sourceEdgeIndex i) = (StoppingHistory.edgeEquiv i).1 := by
  have h := congrArg Subtype.val
    (prefixEdgeEquivStoppingEdge.apply_symm_apply
      (StoppingHistory.edgeEquiv i))
  exact h

def orderPrefixEdgeSet (π : K6EdgeOrder) (r : K6PrefixLength) :
    Finset PrefixSoundness.K6Edge :=
  Finset.univ.image fun j : Fin r.val ↦
    sourceEdgeIndex (π (prefixIndex r j))

theorem orderPrefixEdgeSet_card (π : K6EdgeOrder) (r : K6PrefixLength) :
    (orderPrefixEdgeSet π r).card = r.val := by
  unfold orderPrefixEdgeSet
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have hindex := sourceEdgeIndex_injective hij
    have hp := π.injective hindex
    apply Fin.ext
    exact congrArg (fun k : Fin 15 ↦ k.val) hp

theorem edgeFinsetOfMask_injective :
    Function.Injective PrefixSoundness.edgeFinsetOfMask := by
  intro g h hgh
  apply Fin.ext
  have hm := congrArg PrefixSoundness.edgeFinsetMask hgh
  simpa [PrefixSoundness.edgeMask_roundtrip] using hm

theorem card_graphMask_eq_card_edgeFinset :
    Fintype.card (Fin K6Prefix.graphCount) =
      Fintype.card (Finset PrefixSoundness.K6Edge) := by
  simp [K6Prefix.graphCount, K6Prefix.edgeCount]

def graphMaskEquivEdgeFinset :
    Fin K6Prefix.graphCount ≃ Finset PrefixSoundness.K6Edge :=
  Equiv.ofBijective PrefixSoundness.edgeFinsetOfMask
    ((Fintype.bijective_iff_injective_and_card
      PrefixSoundness.edgeFinsetOfMask).mpr
      ⟨edgeFinsetOfMask_injective, card_graphMask_eq_card_edgeFinset⟩)

def orderPrefixMask (π : K6EdgeOrder) (r : K6PrefixLength) :
    Fin K6Prefix.graphCount :=
  graphMaskEquivEdgeFinset.symm (orderPrefixEdgeSet π r)

@[simp] theorem edgeFinsetOfMask_orderPrefixMask
    (π : K6EdgeOrder) (r : K6PrefixLength) :
    edgeFinsetOfMask (orderPrefixMask π r) = orderPrefixEdgeSet π r := by
  exact graphMaskEquivEdgeFinset.apply_symm_apply (orderPrefixEdgeSet π r)

theorem orderPrefixPattern_matches (π : K6EdgeOrder)
    (r : K6PrefixLength) :
    PatternMatchesOrderPrefix
      (finitePatternOfMasks fullVertexMask (orderPrefixMask π r)) π r := by
  constructor
  · rfl
  · intro d
    rw [show (finitePatternOfMasks fullVertexMask
        (orderPrefixMask π r)).edges = orderPrefixEdgeSet π r by
      exact edgeFinsetOfMask_orderPrefixMask π r]
    constructor
    · intro hd
      rw [orderPrefixEdgeSet, Finset.mem_image] at hd
      rcases hd with ⟨j, _hj, rfl⟩
      exact ⟨j, edgeCoord_sourceEdgeIndex _⟩
    · rintro ⟨j, hd⟩
      rw [orderPrefixEdgeSet, Finset.mem_image]
      refine ⟨j, Finset.mem_univ _, ?_⟩
      apply edgeCoord_injective
      exact (edgeCoord_sourceEdgeIndex _).trans hd.symm

private theorem card_edgeFinsetOfMask_aux :
    ∀ g : Fin K6Prefix.graphCount,
      (edgeFinsetOfMask g).card =
        K6Prefix.countBits K6Prefix.edgeCount g.1 := by
  native_decide

theorem countBits_orderPrefixMask (π : K6EdgeOrder)
    (r : K6PrefixLength) :
    K6Prefix.countBits K6Prefix.edgeCount (orderPrefixMask π r).1 =
      r.val := by
  rw [← card_edgeFinsetOfMask_aux, edgeFinsetOfMask_orderPrefixMask,
    orderPrefixEdgeSet_card]

def ninePrefixLength : K6PrefixLength := ⟨9, by omega⟩

def tenPrefixLength : K6PrefixLength := ⟨10, by omega⟩

@[simp] theorem ninePrefixLength_val : ninePrefixLength.val = 9 := rfl

@[simp] theorem tenPrefixLength_val : tenPrefixLength.val = 10 := rfl

/-- The checked nine-edge classification applies to the canonical prefix of
every relative order.  The statement deliberately retains the three
exceptional orbit tags separately, since they select three different
counting arguments downstream. -/
theorem orderNinePrefix_classification (π : K6EdgeOrder) :
    K6Prefix.inExceptionalOrbit
          (orderPrefixMask π ninePrefixLength).1 = false ∨
      K6Prefix.h3Orbit[(orderPrefixMask π ninePrefixLength).1]! = true ∨
      K6Prefix.k5MinusEdgePlusIsolateOrbit[
          (orderPrefixMask π ninePrefixLength).1]! = true ∨
      K6Prefix.b4Orbit[(orderPrefixMask π ninePrefixLength).1]! = true := by
  let g := orderPrefixMask π ninePrefixLength
  by_cases hordinary : K6Prefix.inExceptionalOrbit g.1 = false
  · exact Or.inl (by simpa [g] using hordinary)
  · right
    have hexceptional : K6Prefix.inExceptionalOrbit g.1 = true :=
      Bool.eq_true_of_not_eq_false hordinary
    unfold K6Prefix.inExceptionalOrbit at hexceptional
    simp only [Bool.or_eq_true] at hexceptional
    rcases hexceptional with (h3 | hk5) | hb4
    · exact Or.inl (by simpa [g] using h3)
    · exact Or.inr (Or.inl (by simpa [g] using hk5))
    · exact Or.inr (Or.inr (by simpa [g] using hb4))

/-- The ordinary branch for the canonical nine-edge mask, with no mask or
pattern-matching hypotheses left for a caller to manufacture. -/
theorem ordinary_orderNinePrefixHistoryMass_finiteSemantic_bound
    (kappa p : ℝ≥0) (hkappa : 1 ≤ kappa) (hp : p ≤ 1)
    {N : ℕ} (hN : 0 < N)
    (strategy : K6Strategy N) (hfresh : FreshForBudget strategy)
    (π : K6EdgeOrder)
    (hOrdinary : K6Prefix.inExceptionalOrbit
      (orderPrefixMask π ninePrefixLength).1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask
          (orderPrefixMask π ninePrefixLength)) a,
      4 ≤ a ∧
      orderPrefixHistoryMass (p : ℝ≥0∞) strategy π ninePrefixLength ≤
        (Derivation.coefficient (S := k6FinitePrefixSystem) D : ℝ≥0∞) *
            (p : ℝ≥0∞) ^ 4 *
              (kappa * (N : ℝ≥0) : ℝ≥0∞) ^ 3 +
          (Derivation.tail (S := k6FinitePrefixSystem)
            (M := finitePrefixSemantics kappa p hkappa hp hN) D : ℝ≥0∞) := by
  apply ordinary_orderPrefixHistoryMass_finiteSemantic_bound
    kappa p hkappa hp hN strategy hfresh π
      (orderPrefixMask π ninePrefixLength)
  · exact orderPrefixPattern_matches π ninePrefixLength
  · simpa using countBits_orderPrefixMask π ninePrefixLength
  · exact hOrdinary

end
end StoppingPrefixCount
end OnlineRamsey
