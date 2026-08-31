import OnlineRamsey.Assembly
import OnlineRamsey.OrderedPrefix
import OnlineRamsey.PrefixSoundness
import OnlineRamsey.QueryComplexity

/-!
# Lower-bound assembly for the `K₆` query problem

This file isolates two pieces of bookkeeping which are easy to blur in a
paper proof.

First, it proves an exact finite-product stopping-history lemma.  If an event
does not inspect a finite set `remaining` of board coordinates, intersecting
it with the requirement that all those coordinates are positive multiplies
its mass by exactly `p ^ remaining.card`.  Thus adaptively choosing *when* to
query the remaining edges costs no independence assumption: the only semantic
obligation is the explicit non-anticipation statement `EventIgnores`.

Second, it gives a finite non-asymptotic assembly theorem for the four cases in
the nine-edge classification.  Its hypotheses expose precisely the semantic
copy-count estimates which are not supplied by the executable prefix table.
The conclusion has the target main term `p ^ 10 * N ^ 3`, retains all error
terms, sums over the `15!` relative edge orders, and finishes with Markov.
-/

open scoped BigOperators ENNReal NNReal

namespace OnlineRamsey
namespace LowerAssembly

universe u v

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

section StoppingHistory

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Two boards agree on every coordinate outside `remaining`. -/
def AgreeOutside (remaining : Finset Q) (b b' : Board Q) : Prop :=
  ∀ q, q ∉ remaining → b q = b' q

/-- Membership in `event` is determined without reading `remaining`. -/
def EventIgnores (event : Set (Board Q)) (remaining : Finset Q) : Prop :=
  ∀ b b', AgreeOutside remaining b b' → (b ∈ event ↔ b' ∈ event)

/-- Every coordinate in `remaining` carries a positive answer. -/
def allPositiveOn (remaining : Finset Q) : Set (Board Q) :=
  {b | ∀ q ∈ remaining, b q = true}

private def IsInside (remaining : Finset Q) (q : Q) : Prop := q ∈ remaining
private abbrev Inside (remaining : Finset Q) := {q : Q // IsInside remaining q}
private abbrev Outside (remaining : Finset Q) := {q : Q // ¬IsInside remaining q}

private def boardSplit (remaining : Finset Q) :
    Board Q ≃ (Inside remaining → Bool) × (Outside remaining → Bool) :=
  Equiv.piEquivPiSubtypeProd (IsInside remaining) (fun _ => Bool)

private theorem boardWeight_split (weight : Bool → ℝ≥0∞)
    (remaining : Finset Q)
    (inside : Inside remaining → Bool)
    (outside : Outside remaining → Bool) :
    boardWeight weight ((boardSplit remaining).symm (inside, outside)) =
      (∏ q, weight (inside q)) * ∏ q, weight (outside q) := by
  let b : Board Q := (boardSplit remaining).symm (inside, outside)
  change (∏ q : Q, weight (b q)) = _
  calc
    (∏ q : Q, weight (b q)) =
        (∏ q : Inside remaining, weight (b q)) *
          ∏ q : Outside remaining, weight (b q) :=
      (Fintype.prod_subtype_mul_prod_subtype
        (IsInside remaining) (fun q => weight (b q))).symm
    _ = (∏ q, weight (inside q)) * ∏ q, weight (outside q) := by
      congr 1
      · apply Fintype.prod_congr
        intro q
        dsimp [b, boardSplit]
        simp [q.property]
      · apply Fintype.prod_congr
        intro q
        dsimp [b, boardSplit]
        simp [q.property]

private theorem split_agreeOutside (remaining : Finset Q)
    (inside inside' : Inside remaining → Bool)
    (outside : Outside remaining → Bool) :
    AgreeOutside remaining
      ((boardSplit remaining).symm (inside, outside))
      ((boardSplit remaining).symm (inside', outside)) := by
  intro q hq
  dsimp [boardSplit]
  simp [IsInside, hq]

private theorem allPositiveOn_split_iff (remaining : Finset Q)
    (inside : Inside remaining → Bool)
    (outside : Outside remaining → Bool) :
    (boardSplit remaining).symm (inside, outside) ∈ allPositiveOn remaining ↔
      inside = fun _ => true := by
  constructor
  · intro h
    funext q
    have hq := h q (by simpa [IsInside] using q.property)
    dsimp [boardSplit] at hq
    simpa [q.property] using hq
  · rintro rfl q hq
    dsimp [boardSplit]
    simp [IsInside, hq]

private theorem event_split_iff_fixedInside
    (event : Set (Board Q)) (remaining : Finset Q)
    (hignore : EventIgnores event remaining)
    (inside : Inside remaining → Bool)
    (outside : Outside remaining → Bool) :
    (boardSplit remaining).symm (inside, outside) ∈ event ↔
      (boardSplit remaining).symm ((fun _ => false), outside) ∈ event :=
  hignore _ _ (split_agreeOutside remaining inside (fun _ => false) outside)

private theorem sum_inside_weights
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (remaining : Finset Q) :
    (∑ inside : Inside remaining → Bool,
      ∏ q, weight (inside q)) = 1 := by
  simpa [boardWeight] using
    (sum_boardWeight (Q := Inside remaining) weight hnormalized)

private theorem sum_inside_allPositive_weights
    (weight : Bool → ℝ≥0∞) (remaining : Finset Q) :
    (∑ inside : Inside remaining → Bool,
      if inside = (fun _ => true) then (∏ q, weight (inside q)) else 0) =
      weight true ^ remaining.card := by
  rw [Fintype.sum_eq_single (fun _ => true)]
  · simp only [if_true, Finset.prod_const, Finset.card_univ]
    congr 1
    rw [Fintype.card_subtype]
    congr 1
    ext q
    simp [IsInside]
  · intro inside hne
    simp [hne]

private theorem finiteBoardMass_eq_split_sum
    (weight : Bool → ℝ≥0∞) (event : Set (Board Q))
    (remaining : Finset Q) :
    finiteBoardMass weight event =
      ∑ pair : (Inside remaining → Bool) × (Outside remaining → Bool),
        if (boardSplit remaining).symm pair ∈ event then
          boardWeight weight ((boardSplit remaining).symm pair) else 0 := by
  unfold finiteBoardMass
  apply Fintype.sum_equiv (boardSplit remaining)
  intro board
  simp

/--
Exact finite-product non-anticipation identity.

This is the stopping-history calculation needed in the ordered-prefix proof:
`event` may encode the complete adaptive history up to the instant a prefix
is finished, provided changing still-unqueried coordinates in `remaining`
cannot alter whether that history occurred.
-/
theorem finiteBoardMass_inter_allPositiveOn
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (event : Set (Board Q)) (remaining : Finset Q)
    (hignore : EventIgnores event remaining) :
    finiteBoardMass weight (event ∩ allPositiveOn remaining) =
      weight true ^ remaining.card * finiteBoardMass weight event := by
  let fixedEvent : (Outside remaining → Bool) → Prop :=
    fun outside => (boardSplit remaining).symm ((fun _ => false), outside) ∈ event
  have hleft : finiteBoardMass weight (event ∩ allPositiveOn remaining) =
      ∑ outside : Outside remaining → Bool,
        (if fixedEvent outside then
          weight true ^ remaining.card * (∏ q, weight (outside q)) else 0) := by
    rw [finiteBoardMass_eq_split_sum weight (event ∩ allPositiveOn remaining)
      remaining, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro outside _houtside
    by_cases hevent : fixedEvent outside
    · simp only [hevent, if_true]
      trans ∑ inside : Inside remaining → Bool,
          if inside = (fun _ => true) then
            (∏ q, weight (inside q)) * ∏ q, weight (outside q) else 0
      · apply Finset.sum_congr rfl
        intro inside _hinside
        by_cases hi : inside = (fun _ => true)
        · subst inside
          have hmemEvent :
              (boardSplit remaining).symm ((fun _ => true), outside) ∈ event :=
            (event_split_iff_fixedInside event remaining hignore
              (fun _ => true) outside).mpr hevent
          have hmemPositive :
              (boardSplit remaining).symm ((fun _ => true), outside) ∈
                allPositiveOn remaining :=
            (allPositiveOn_split_iff remaining (fun _ => true) outside).mpr rfl
          simp only [hmemEvent, hmemPositive, Set.mem_inter_iff, and_self,
            if_true]
          rw [boardWeight_split]
        · have hnotPositive :
              (boardSplit remaining).symm (inside, outside) ∉
                allPositiveOn remaining :=
            fun h => hi ((allPositiveOn_split_iff remaining inside outside).mp h)
          simp [hnotPositive, hi]
      · rw [show (∑ inside : Inside remaining → Bool,
            if inside = (fun _ => true) then
              (∏ q, weight (inside q)) * ∏ q, weight (outside q) else 0) =
            (∑ inside : Inside remaining → Bool,
              if inside = (fun _ => true) then ∏ q, weight (inside q) else 0) *
              ∏ q, weight (outside q) by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro inside _hinside
                by_cases hi : inside = (fun _ => true) <;> simp [hi]]
        rw [sum_inside_allPositive_weights weight remaining]
    · simp only [hevent, if_false]
      apply Finset.sum_eq_zero
      intro inside _hinside
      have hnotEvent : (boardSplit remaining).symm (inside, outside) ∉ event := by
        intro hmem
        apply hevent
        exact (event_split_iff_fixedInside event remaining hignore inside outside).mp hmem
      simp [hnotEvent]
  have hright : finiteBoardMass weight event =
      ∑ outside : Outside remaining → Bool,
        (if fixedEvent outside then ∏ q, weight (outside q) else 0) := by
    rw [finiteBoardMass_eq_split_sum weight event remaining,
      Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro outside _houtside
    by_cases hevent : fixedEvent outside
    · simp only [hevent, if_true]
      trans (∑ inside : Inside remaining → Bool,
          ∏ q, weight (inside q)) * ∏ q, weight (outside q)
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro inside _hinside
        have hmem : (boardSplit remaining).symm (inside, outside) ∈ event :=
          (event_split_iff_fixedInside event remaining hignore inside outside).mpr
            hevent
        simp only [hmem, if_true]
        rw [boardWeight_split]
      · rw [sum_inside_weights weight hnormalized remaining, one_mul]
    · simp only [hevent, if_false]
      apply Finset.sum_eq_zero
      intro inside _hinside
      have hnotEvent : (boardSplit remaining).symm (inside, outside) ∉ event := by
        intro hmem
        apply hevent
        exact (event_split_iff_fixedInside event remaining hignore inside outside).mp hmem
      simp [hnotEvent]
  rw [hleft, hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outside _houtside
  by_cases hevent : fixedEvent outside <;> simp [hevent]

/-- Bernoulli specialization of the exact stopping-history identity. -/
theorem bernoulli_inter_allPositiveOn
    (p : ℝ≥0∞) (hp : p ≤ 1) (event : Set (Board Q))
    (remaining : Finset Q) (hignore : EventIgnores event remaining) :
    finiteBoardMass (bernoulliWeight p) (event ∩ allPositiveOn remaining) =
      p ^ remaining.card * finiteBoardMass (bernoulliWeight p) event := by
  simpa [bernoulliWeight] using
    finiteBoardMass_inter_allPositiveOn (Q := Q) (bernoulliWeight p)
      (sum_bernoulliWeight p hp) event remaining hignore

/--
One completed-object event is bounded by its viable prefix event times the
cost of its still-unqueried positive coordinates.
-/
theorem stoppingPrefix_event_mass_le
    (p : ℝ≥0∞) (hp : p ≤ 1)
    (completion prefixEvent : Set (Board Q)) (remaining : Finset Q)
    (hcompletion : completion ⊆ prefixEvent ∩ allPositiveOn remaining)
    (hignore : EventIgnores prefixEvent remaining) :
    finiteBoardMass (bernoulliWeight p) completion ≤
      p ^ remaining.card * finiteBoardMass (bernoulliWeight p) prefixEvent := by
  calc
    finiteBoardMass (bernoulliWeight p) completion ≤
        finiteBoardMass (bernoulliWeight p)
          (prefixEvent ∩ allPositiveOn remaining) := by
      unfold finiteBoardMass
      apply Finset.sum_le_sum
      intro board _hboard
      by_cases hc : board ∈ completion
      · have ht := hcompletion hc
        simp [hc, ht]
      · simp [hc]
    _ = p ^ remaining.card *
        finiteBoardMass (bernoulliWeight p) prefixEvent :=
      bernoulli_inter_allPositiveOn p hp prefixEvent remaining hignore

/-- Finite weighted stopping-history composition.  The indices may represent
labelled prefix embeddings at their unique completion histories. -/
theorem stoppingPrefix_weighted_family_mass_le
    {I : Type v} [DecidableEq I]
    (p : ℝ≥0∞) (hp : p ≤ 1) (indices : Finset I)
    (coefficient : I → ℝ≥0∞)
    (completion prefixEvent : I → Set (Board Q))
    (remaining : I → Finset Q) (k : ℕ)
    (hcompletion : ∀ i ∈ indices,
      completion i ⊆ prefixEvent i ∩ allPositiveOn (remaining i))
    (hignore : ∀ i ∈ indices, EventIgnores (prefixEvent i) (remaining i))
    (hcard : ∀ i ∈ indices, (remaining i).card = k) :
    (∑ i ∈ indices, coefficient i *
        finiteBoardMass (bernoulliWeight p) (completion i)) ≤
      p ^ k * ∑ i ∈ indices, coefficient i *
        finiteBoardMass (bernoulliWeight p) (prefixEvent i) := by
  calc
    (∑ i ∈ indices, coefficient i *
        finiteBoardMass (bernoulliWeight p) (completion i)) ≤
        ∑ i ∈ indices, coefficient i *
          (p ^ k * finiteBoardMass (bernoulliWeight p) (prefixEvent i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_left'
      simpa [hcard i hi] using
        stoppingPrefix_event_mass_le p hp (completion i) (prefixEvent i)
          (remaining i) (hcompletion i hi) (hignore i hi)
    _ = p ^ k * ∑ i ∈ indices, coefficient i *
        finiteBoardMass (bernoulliWeight p) (prefixEvent i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ac_rfl

end StoppingHistory

section FourCaseAssembly

/-!
The finite classifier leaves three exceptional nine-edge prefixes.  The
`shiftedBipartite` case is stopped after ten edges and therefore has five,
rather than six, positive completion edges.  Its prefix estimate gains the
corresponding fifth power of `p`.
-/

inductive PrefixCase
  | ordinary
  | halfGraph
  | almostCompleteFive
  | shiftedBipartite
  deriving DecidableEq

/-- Number of positive answers still required after the selected prefix. -/
def completionExponent : PrefixCase → ℕ
  | .ordinary | .halfGraph | .almostCompleteFive => 6
  | .shiftedBipartite => 5

/-- Power of `p` supplied by the semantic prefix-copy estimate. -/
def prefixExponent : PrefixCase → ℕ
  | .ordinary | .halfGraph | .almostCompleteFive => 4
  | .shiftedBipartite => 5

@[simp] theorem completionExponent_add_prefixExponent (kind : PrefixCase) :
    completionExponent kind + prefixExponent kind = 10 := by
  cases kind <;> rfl

/--
Direct connection from the exhaustive nine-edge table to the ordered-copy
scale for every ordinary prefix.  The only new premise, `hstop`, is the
semantic ordered-prefix estimate.  The recurrence coefficient and its full
accumulated exceptional tail are returned explicitly.
-/
theorem ordinaryOrder_from_checkedTable
    (M : PrefixSoundness.RecurrenceSemantics
      PrefixSoundness.k6FinitePrefixSystem)
    (g : Fin K6Prefix.graphCount)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false)
    (orderedMass : ℝ≥0)
    (hstop : orderedMass ≤ M.p ^ 6 *
      M.value (PrefixSoundness.finitePatternOfMasks
        PrefixSoundness.fullVertexMask g)) :
    ∃ a, ∃ D : PrefixSoundness.Derivation
        PrefixSoundness.k6FinitePrefixSystem 3
        (PrefixSoundness.finitePatternOfMasks
          PrefixSoundness.fullVertexMask g) a,
      4 ≤ a ∧
      orderedMass ≤
        PrefixSoundness.Derivation.coefficient
            (S := PrefixSoundness.k6FinitePrefixSystem) D *
            M.p ^ 10 * M.N ^ 3 +
          M.p ^ 6 * PrefixSoundness.Derivation.tail
            (S := PrefixSoundness.k6FinitePrefixSystem) (M := M) D := by
  rcases PrefixSoundness.ordinaryNineEdge_sound M g hNine hOrdinary with
    ⟨a, D, hFour, hvalue⟩
  refine ⟨a, D, hFour, hstop.trans ?_⟩
  calc
    M.p ^ 6 * M.value (PrefixSoundness.finitePatternOfMasks
        PrefixSoundness.fullVertexMask g) ≤
        M.p ^ 6 *
          (PrefixSoundness.Derivation.coefficient
              (S := PrefixSoundness.k6FinitePrefixSystem) D *
              M.p ^ 4 * M.N ^ 3 +
            PrefixSoundness.Derivation.tail
              (S := PrefixSoundness.k6FinitePrefixSystem) (M := M) D) :=
      mul_le_mul_left' hvalue _
    _ = PrefixSoundness.Derivation.coefficient
          (S := PrefixSoundness.k6FinitePrefixSystem) D *
          M.p ^ 10 * M.N ^ 3 +
        M.p ^ 6 * PrefixSoundness.Derivation.tail
          (S := PrefixSoundness.k6FinitePrefixSystem) (M := M) D := by
      ring

/-- One order contributes the target `p^10 N^3` main term.  The two
hypotheses are deliberately separate: `hstop` is the ordered stopping-history
obligation, while `hcount` is the recurrence/host-counting obligation. -/
theorem oneOrder_target_scale
    (p N C orderedMass prefixMass error : ℝ≥0∞) (kind : PrefixCase)
    (hstop : orderedMass ≤ p ^ completionExponent kind * prefixMass)
    (hcount : prefixMass ≤
      C * p ^ prefixExponent kind * N ^ 3 + error) :
    orderedMass ≤ C * p ^ 10 * N ^ 3 +
      p ^ completionExponent kind * error := by
  have hpows : p ^ completionExponent kind * p ^ prefixExponent kind =
      p ^ 10 := by
    rw [← pow_add, completionExponent_add_prefixExponent]
  calc
    orderedMass ≤ p ^ completionExponent kind * prefixMass := hstop
    _ ≤ p ^ completionExponent kind *
        (C * p ^ prefixExponent kind * N ^ 3 + error) :=
      mul_le_mul_left' hcount _
    _ = C * p ^ 10 * N ^ 3 + p ^ completionExponent kind * error := by
      rw [mul_add]
      rw [show p ^ completionExponent kind *
          (C * p ^ prefixExponent kind * N ^ 3) =
          C * (p ^ completionExponent kind * p ^ prefixExponent kind) * N ^ 3 by
        ac_rfl]
      rw [hpows]

/--
Finite non-asymptotic lower-bound assembly over all relative edge orders.

There are no hidden probability or graph assumptions.  The caller supplies:

* `hpartition`, assigning every completed copy to an edge order;
* `hstop`, the ordered-prefix/non-anticipation estimate;
* `hcount`, the ordinary recurrence or exceptional host estimate.

Every exceptional error remains visible in the conclusion.
-/
theorem allOrders_target_scale
    {Order : Type v} [Fintype Order]
    (hcard : Fintype.card Order = Nat.factorial 15)
    (p N C totalMass : ℝ≥0∞)
    (kind : Order → PrefixCase)
    (orderedMass prefixMass error : Order → ℝ≥0∞)
    (hpartition : totalMass ≤ ∑ order, orderedMass order)
    (hstop : ∀ order, orderedMass order ≤
      p ^ completionExponent (kind order) * prefixMass order)
    (hcount : ∀ order, prefixMass order ≤
      C * p ^ prefixExponent (kind order) * N ^ 3 + error order) :
    totalMass ≤
      (Nat.factorial 15 : ℝ≥0∞) * (C * p ^ 10 * N ^ 3) +
        ∑ order, p ^ completionExponent (kind order) * error order := by
  calc
    totalMass ≤ ∑ order, orderedMass order := hpartition
    _ ≤ ∑ order, (C * p ^ 10 * N ^ 3 +
        p ^ completionExponent (kind order) * error order) :=
      Finset.sum_le_sum fun order _horder =>
        oneOrder_target_scale p N C (orderedMass order) (prefixMass order)
          (error order) (kind order) (hstop order) (hcount order)
    _ = (Fintype.card Order : ℝ≥0∞) * (C * p ^ 10 * N ^ 3) +
        ∑ order, p ^ completionExponent (kind order) * error order := by
      rw [Finset.sum_add_distrib]
      simp
    _ = (Nat.factorial 15 : ℝ≥0∞) * (C * p ^ 10 * N ^ 3) +
        ∑ order, p ^ completionExponent (kind order) * error order := by
      rw [hcard]

/-- Markov/partition payoff of the finite four-case assembly. -/
theorem success_lt_half_of_allOrders
    {Order : Type v} [Fintype Order]
    (hcard : Fintype.card Order = Nat.factorial 15)
    (p N C totalMass successMass : ℝ≥0∞)
    (kind : Order → PrefixCase)
    (orderedMass prefixMass error : Order → ℝ≥0∞)
    (hsuccess : successMass ≤ totalMass)
    (hpartition : totalMass ≤ ∑ order, orderedMass order)
    (hstop : ∀ order, orderedMass order ≤
      p ^ completionExponent (kind order) * prefixMass order)
    (hcount : ∀ order, prefixMass order ≤
      C * p ^ prefixExponent (kind order) * N ^ 3 + error order)
    (hsmall :
      (Nat.factorial 15 : ℝ≥0∞) * (C * p ^ 10 * N ^ 3) +
        ∑ order, p ^ completionExponent (kind order) * error order <
          (2 : ℝ≥0∞)⁻¹) :
    successMass < (2 : ℝ≥0∞)⁻¹ := by
  exact hsuccess.trans
    (allOrders_target_scale hcard p N C totalMass kind orderedMass prefixMass
      error hpartition hstop hcount) |>.trans_lt hsmall

end FourCaseAssembly

end
end LowerAssembly
end OnlineRamsey
