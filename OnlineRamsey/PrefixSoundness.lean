import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
import K6Prefix

/-!
# Soundness of the finite prefix recurrence

`K6Prefix.lean` evaluates the integer recurrence used in the finite
nine-edge classification.  This file gives that computation a separate
semantic meaning.  It deliberately does not identify bit masks with
`SimpleGraph` objects: the final section records, as an explicit structure,
the finite representation obligations still needed for that identification.

There are three layers.

* `PrefixSystem` is an abstract finite graph-like deletion system.
* `Derivation` is a proof tree built from the empty, edge-deletion, and
  endpoint-pair-deletion rules.
* `RecurrenceSemantics` says that a nonnegative quantity satisfies the two
  analytic recurrences.  Its pair rule has the labelled-copy factor `2` and
  an explicit tail term.

The main theorem `finite_recurrence_sound` turns a locally checked finite
table into a monomial bound.  The proof first reconstructs a derivation by
induction on the number of edges and then proves the derivation sound.  No
asymptotic notation occurs: every exceptional-event contribution is retained
in `Derivation.tail`.
-/

open scoped BigOperators NNReal

namespace OnlineRamsey.PrefixSoundness

universe u v

/-! ## Abstract deletion systems -/

/--
The information about a finite pattern which is used by the two recurrences.

Both deletion operations are required to decrease the edge count.  For
`erasePair H e`, this follows in an ordinary simple graph because the selected
edge `e` itself disappears when its two endpoints are removed.  These strict
inequalities are exactly what makes edge-count induction possible, even
though the pair rule also decreases the monomial's `N` exponent.
-/
structure PrefixSystem (Pattern : Type u) (Edge : Type v) [DecidableEq Edge] where
  edges : Pattern → Finset Edge
  vertexCount : Pattern → ℕ
  eraseEdge : Pattern → Edge → Pattern
  erasePair : Pattern → Edge → Pattern
  eraseEdge_card_lt : ∀ H e, e ∈ edges H →
    (edges (eraseEdge H e)).card < (edges H).card
  erasePair_card_lt : ∀ H e, e ∈ edges H →
    (edges (erasePair H e)).card < (edges H).card

variable {Pattern : Type u} {Edge : Type v} [DecidableEq Edge]
variable (S : PrefixSystem Pattern Edge)

/-- An edge together with the proof that it belongs to the current pattern. -/
abbrev PresentEdge (H : Pattern) := {e : Edge // e ∈ S.edges H}

/-! ## Syntactic certificates -/

/--
A derivation of the monomial exponent `a` at `N` exponent `b`.

The children of an edge step may have different (stronger) exponents.  The
hypothesis `a ≤ childExponent e` says that, for `0 ≤ p ≤ 1`, every child
can be weakened to the common exponent `a` before multiplying by one further
factor of `p`.  The pair constructor is indexed by `b + 1`, so it cannot be
used at `b = 0`.
-/
inductive Derivation : ℕ → Pattern → ℕ → Type (max u v)
  | empty {b H} (hEmpty : S.edges H = ∅)
      (hVertices : S.vertexCount H ≤ b) : Derivation b H 0
  | edge {b H a} (hNonempty : (S.edges H).Nonempty)
      (childExponent : PresentEdge S H → ℕ)
      (hExponent : ∀ e, a ≤ childExponent e)
      (children : ∀ e, Derivation b (S.eraseEdge H e.1) (childExponent e)) :
      Derivation b H (a + 1)
  | pair {b H a} (e : PresentEdge S H) (childExponent : ℕ)
      (hExponent : a ≤ childExponent)
      (child : Derivation b (S.erasePair H e.1) childExponent) :
      Derivation (b + 1) H (a + 1)

/-! ## Analytic semantics, with an explicit pair tail -/

/--
Nonnegative semantics for the recurrence at fixed `p` and `N`.

The intended `value H` is an expected labelled-copy count.  The empty bound
uses the crude ambient-vertex estimate `(2N)^v`.  `edgeTail` is normally zero,
but is retained because it costs nothing and makes the composition theorem
reusable.  `pairTail H e` is the contribution of the exceptional event in
the pair recurrence.  In particular, no `o(1)` is hidden in this structure.

The coefficient in `pair_bound` is **exactly `2 * p * N`**.  The factor `2`
is necessary for injective labelled copies: an unordered positive query has
two possible orientations for the ordered images of the selected endpoints.
-/
structure RecurrenceSemantics where
  p : ℝ≥0
  N : ℝ≥0
  p_le_one : p ≤ 1
  one_le_N : 1 ≤ N
  value : Pattern → ℝ≥0
  edgeTail : Pattern → ℝ≥0
  pairTail : Pattern → Edge → ℝ≥0
  empty_bound : ∀ H, S.edges H = ∅ →
    value H ≤ (2 * N) ^ S.vertexCount H
  edge_bound : ∀ H, (S.edges H).Nonempty →
    value H ≤
      p * (∑ e : PresentEdge S H, value (S.eraseEdge H e.1)) + edgeTail H
  pair_bound : ∀ H (e : PresentEdge S H),
    value H ≤
      2 * p * N * value (S.erasePair H e.1) + pairTail H e.1

variable (M : RecurrenceSemantics S)

/-- The good/bad-event remainder in a pair recurrence. -/
def pairTailCost (badMass crudeCount : ℝ≥0) : ℝ≥0 :=
  badMass * crudeCount

/--
Elementary good/bad decomposition producing the exact pair recurrence used
above.  A probabilistic application takes `badMass` to be the probability of
the upper-tail event and `crudeCount` to be a deterministic bound on the
number of copies on that event.
-/
theorem pair_bound_of_good_bad
    {p N value childValue goodPart badPart badMass crudeCount : ℝ≥0}
    (hSplit : value ≤ goodPart + badPart)
    (hGood : goodPart ≤ 2 * p * N * childValue)
    (hBad : badPart ≤ pairTailCost badMass crudeCount) :
    value ≤ 2 * p * N * childValue + pairTailCost badMass crudeCount := by
  exact hSplit.trans (add_le_add hGood hBad)

/-! ## The coefficient and the accumulated tail of a derivation -/

/-- The constant multiplying the certified monomial. -/
noncomputable def Derivation.coefficient :
    {b : ℕ} → {H : Pattern} → {a : ℕ} → Derivation S b H a → ℝ≥0
  | _, H, _, .empty _ _ => 2 ^ S.vertexCount H
  | _, _, _, .edge _ _ _ children =>
      ∑ e, Derivation.coefficient (children e)
  | _, _, _, .pair _ _ _ child =>
      2 * Derivation.coefficient child

/--
The exact additive error accumulated along a derivation.  Notice that a pair
step transports its child's error with the full multiplier `2 * p * N`.
-/
noncomputable def Derivation.tail :
    {b : ℕ} → {H : Pattern} → {a : ℕ} → Derivation S b H a → ℝ≥0
  | _, _, _, .empty _ _ => 0
  | _, H, _, .edge _ _ _ children =>
      M.edgeTail H + M.p *
        ∑ e, Derivation.tail (children e)
  | _, H, _, .pair e _ _ child =>
      M.pairTail H e.1 + 2 * M.p * M.N *
        Derivation.tail child

/-- The normalized monomial bound represented by a derivation. -/
noncomputable def Derivation.bound {b : ℕ} {H : Pattern} {a : ℕ}
    (D : Derivation S b H a) : ℝ≥0 :=
  Derivation.coefficient (S := S) D * M.p ^ a * M.N ^ b +
    Derivation.tail (S := S) (M := M) D

/-! ## Soundness of a proof tree -/

theorem Derivation.sound {b : ℕ} {H : Pattern} {a : ℕ}
    (D : Derivation S b H a) :
    M.value H ≤ Derivation.bound (S := S) (M := M) D := by
  induction D with
  | @empty b₀ H₀ hEmpty hVertices =>
      have hPower : M.N ^ S.vertexCount H₀ ≤ M.N ^ b₀ :=
        pow_le_pow_right₀ M.one_le_N hVertices
      calc
        M.value H₀ ≤ (2 * M.N) ^ S.vertexCount H₀ :=
          M.empty_bound H₀ hEmpty
        _ = 2 ^ S.vertexCount H₀ * M.N ^ S.vertexCount H₀ := by
          rw [mul_pow]
        _ ≤ 2 ^ S.vertexCount H₀ * M.N ^ b₀ :=
          mul_le_mul_left' hPower _
        _ = Derivation.bound (S := S) (M := M)
            (Derivation.empty hEmpty hVertices) := by
          simp [Derivation.bound, Derivation.coefficient, Derivation.tail]
  | @edge b₀ H₀ a₀ hNonempty childExponent hExponent children ih =>
      have hChildren :
          (∑ e : PresentEdge S H₀, M.value (S.eraseEdge H₀ e.1)) ≤
            ∑ e : PresentEdge S H₀, (
              Derivation.coefficient (S := S) (children e) *
                  M.p ^ a₀ * M.N ^ b₀ +
                Derivation.tail (S := S) (M := M) (children e)) := by
        apply Finset.sum_le_sum
        intro e he
        have hp : M.p ^ childExponent e ≤ M.p ^ a₀ :=
          pow_le_pow_of_le_one (zero_le M.p) M.p_le_one (hExponent e)
        refine (ih e).trans ?_
        exact add_le_add_right
          (mul_le_mul_right'
            (mul_le_mul_left' hp
              (Derivation.coefficient (S := S) (children e)))
            (M.N ^ b₀)) _
      have hMulSum (f : PresentEdge S H₀ → ℝ≥0) :
          M.p * (∑ e, f e) = ∑ e, M.p * f e :=
        Finset.mul_sum Finset.univ f M.p
      have hCoeffSum :
          (∑ e : PresentEdge S H₀,
              M.p * (Derivation.coefficient (S := S) (children e) *
                M.p ^ a₀ * M.N ^ b₀)) =
            ∑ e : PresentEdge S H₀,
              Derivation.coefficient (S := S) (children e) *
                (M.p ^ a₀ * M.p) * M.N ^ b₀ := by
        apply Finset.sum_congr rfl
        intro e he
        ring
      calc
        M.value H₀ ≤
            M.p * (∑ e : PresentEdge S H₀,
              M.value (S.eraseEdge H₀ e.1)) +
              M.edgeTail H₀ := M.edge_bound H₀ hNonempty
        _ ≤ M.p *
              (∑ e : PresentEdge S H₀, (
                Derivation.coefficient (S := S) (children e) *
                    M.p ^ a₀ * M.N ^ b₀ +
                  Derivation.tail (S := S) (M := M) (children e))) +
                M.edgeTail H₀ :=
            add_le_add_right (mul_le_mul_left' hChildren M.p) _
        _ = Derivation.bound (S := S) (M := M)
            (Derivation.edge hNonempty childExponent hExponent children) := by
          simp only [Derivation.bound, Derivation.coefficient, Derivation.tail,
            Finset.sum_add_distrib, Finset.sum_mul, pow_succ, mul_add]
          rw [hMulSum, hMulSum]
          rw [hCoeffSum]
          ac_rfl
  | @pair b₀ H₀ a₀ e childExponent hExponent child ih =>
      have hp : M.p ^ childExponent ≤ M.p ^ a₀ :=
        pow_le_pow_of_le_one (zero_le M.p) M.p_le_one hExponent
      have hChild :
          M.value (S.erasePair H₀ e.1) ≤
            Derivation.coefficient (S := S) child * M.p ^ a₀ * M.N ^ b₀ +
              Derivation.tail (S := S) (M := M) child := by
        refine ih.trans ?_
        exact add_le_add_right
          (mul_le_mul_right'
            (mul_le_mul_left' hp (Derivation.coefficient (S := S) child))
            (M.N ^ b₀)) _
      calc
        M.value H₀ ≤
            2 * M.p * M.N * M.value (S.erasePair H₀ e.1) +
              M.pairTail H₀ e.1 := M.pair_bound H₀ e
        _ ≤ 2 * M.p * M.N *
              (Derivation.coefficient (S := S) child * M.p ^ a₀ * M.N ^ b₀ +
                Derivation.tail (S := S) (M := M) child) +
                M.pairTail H₀ e.1 :=
            add_le_add_right (mul_le_mul_left' hChild (2 * M.p * M.N)) _
        _ = Derivation.bound (S := S) (M := M)
            (Derivation.pair e childExponent hExponent child) := by
          simp only [Derivation.bound, Derivation.coefficient, Derivation.tail,
            pow_succ]
          ring

/-! ## Local finite tables and edge-count induction -/

/--
The local obligations checked by a finite recurrence table.

`A b H = none` represents `-∞`.  A finite nonempty entry must be one plus
an exponent supported either by every edge-deletion child or by one
pair-deletion child.  This is the proposition-level counterpart of the
`max(min(...), max(...))` computation in `K6Prefix.buildTable`.
-/
structure LocalWitness (A : ℕ → Pattern → Option ℕ) : Prop where
  empty_value : ∀ b H, S.edges H = ∅ →
    A b H = if S.vertexCount H ≤ b then some 0 else none
  nonempty_value : ∀ b H a, S.edges H ≠ ∅ → A b H = some a →
    ∃ k, a = k + 1 ∧
      ((∀ e : PresentEdge S H, ∃ ae,
          A b (S.eraseEdge H e.1) = some ae ∧ k ≤ ae) ∨
       (∃ b', b = b' + 1 ∧ ∃ e : PresentEdge S H, ∃ ae,
          A b' (S.erasePair H e.1) = some ae ∧ k ≤ ae))

/--
Reconstruct a proof tree from local table entries.  The natural-number
parameter is an upper bound on the current number of edges; recursive calls
use `eraseEdge_card_lt` or `erasePair_card_lt`, so this is a literal
edge-count induction rather than trust in an evaluator.
-/
theorem LocalWitness.toDerivation_le {A : ℕ → Pattern → Option ℕ}
    (W : LocalWitness S A) (n : ℕ) {b : ℕ} {H : Pattern} {a : ℕ}
    (hCard : (S.edges H).card ≤ n) (hA : A b H = some a) :
    Nonempty (Derivation S b H a) := by
  classical
  induction n generalizing b H a with
  | zero =>
      have hEmpty : S.edges H = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hCard)
      by_cases hVertices : S.vertexCount H ≤ b
      · have hBase := W.empty_value b H hEmpty
        simp only [if_pos hVertices] at hBase
        rw [hBase] at hA
        injection hA with ha
        subst a
        exact ⟨Derivation.empty hEmpty hVertices⟩
      · have hBase := W.empty_value b H hEmpty
        simp only [if_neg hVertices] at hBase
        rw [hBase] at hA
        contradiction
  | succ n ih =>
      by_cases hEmpty : S.edges H = ∅
      · by_cases hVertices : S.vertexCount H ≤ b
        · have hBase := W.empty_value b H hEmpty
          simp only [if_pos hVertices] at hBase
          rw [hBase] at hA
          injection hA with ha
          subst a
          exact ⟨Derivation.empty hEmpty hVertices⟩
        · have hBase := W.empty_value b H hEmpty
          simp only [if_neg hVertices] at hBase
          rw [hBase] at hA
          contradiction
      · have hNonempty : (S.edges H).Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        rcases W.nonempty_value b H a hEmpty hA with ⟨k, rfl, hEdge | hPair⟩
        · let childExponent : PresentEdge S H → ℕ :=
            fun e => Classical.choose (hEdge e)
          have hChildA : ∀ e : PresentEdge S H,
              A b (S.eraseEdge H e.1) = some (childExponent e) := by
            intro e
            exact (Classical.choose_spec (hEdge e)).1
          have hExponent : ∀ e : PresentEdge S H, k ≤ childExponent e := by
            intro e
            exact (Classical.choose_spec (hEdge e)).2
          have hChildCard : ∀ e : PresentEdge S H,
              (S.edges (S.eraseEdge H e.1)).card ≤ n := by
            intro e
            apply Nat.lt_succ_iff.mp
            exact (S.eraseEdge_card_lt H e.1 e.2).trans_le hCard
          have hChild : ∀ e : PresentEdge S H,
              Nonempty (Derivation S b (S.eraseEdge H e.1) (childExponent e)) := by
            intro e
            exact ih (hChildCard e) (hChildA e)
          exact ⟨Derivation.edge hNonempty childExponent hExponent
            (fun e => Classical.choice (hChild e))⟩
        · rcases hPair with ⟨b', rfl, e, childExponent, hChildA, hExponent⟩
          have hChildCard : (S.edges (S.erasePair H e.1)).card ≤ n := by
            apply Nat.lt_succ_iff.mp
            exact (S.erasePair_card_lt H e.1 e.2).trans_le hCard
          have hChild : Nonempty
              (Derivation S b' (S.erasePair H e.1) childExponent) :=
            ih hChildCard hChildA
          exact ⟨Derivation.pair e childExponent hExponent
            (Classical.choice hChild)⟩

/-- Every finite table entry satisfying `LocalWitness` has a derivation. -/
theorem LocalWitness.toDerivation {A : ℕ → Pattern → Option ℕ}
    (W : LocalWitness S A) {b : ℕ} {H : Pattern} {a : ℕ}
    (hA : A b H = some a) : Nonempty (Derivation S b H a) :=
  LocalWitness.toDerivation_le (S := S) W (S.edges H).card le_rfl hA

/--
Semantic soundness of a locally checked finite recurrence, with an explicit
coefficient and accumulated tail returned as data.
-/
theorem finite_recurrence_sound {A : ℕ → Pattern → Option ℕ}
    (W : LocalWitness S A) {b : ℕ} {H : Pattern} {a : ℕ}
    (hA : A b H = some a) :
    ∃ D : Derivation S b H a,
      M.value H ≤ Derivation.coefficient (S := S) D * M.p ^ a * M.N ^ b +
        Derivation.tail (S := S) (M := M) D := by
  let D := Classical.choice (LocalWitness.toDerivation (S := S) W hA)
  exact ⟨D, Derivation.sound (S := S) (M := M) D⟩

/-! ### A bounded version for the four checked tables -/

/-- A decidable finite replacement for “this optional exponent is at least `k`”. -/
def exponentAtLeast : Option ℕ → ℕ → Bool
  | none, _ => false
  | some a, k => decide (k ≤ a)

@[simp] theorem exponentAtLeast_eq_true_iff (x : Option ℕ) (k : ℕ) :
    exponentAtLeast x k = true ↔ ∃ a, x = some a ∧ k ≤ a := by
  cases x with
  | none => simp [exponentAtLeast]
  | some a => simp [exponentAtLeast]

/--
The same local recurrence witness with the `N` exponent living in a finite
index type.  This is the form which can itself be discharged by
`native_decide`: for the K6 computation the index is `Fin 4`.
-/
structure BoundedLocalWitness {B : ℕ}
    (A : Fin (B + 1) → Pattern → Option ℕ) : Prop where
  empty_value : ∀ b H, S.edges H = ∅ →
    A b H = if S.vertexCount H ≤ b.1 then some 0 else none
  nonempty_value : ∀ b H, S.edges H ≠ ∅ →
    match A b H with
    | none => True
    | some 0 => False
    | some (k + 1) =>
        ((∀ e : PresentEdge S H,
            exponentAtLeast (A b (S.eraseEdge H e.1)) k = true) ∨
         (∃ b' : Fin (B + 1), b.1 = b'.1 + 1 ∧
            ∃ e : PresentEdge S H,
              exponentAtLeast (A b' (S.erasePair H e.1)) k = true))

/-- Edge-count induction for a bounded table. -/
theorem BoundedLocalWitness.toDerivation_le {B : ℕ}
    {A : Fin (B + 1) → Pattern → Option ℕ}
    (W : BoundedLocalWitness S A) (n : ℕ) {b : Fin (B + 1)}
    {H : Pattern} {a : ℕ}
    (hCard : (S.edges H).card ≤ n) (hA : A b H = some a) :
    Nonempty (Derivation S b.1 H a) := by
  classical
  induction n generalizing b H a with
  | zero =>
      have hEmpty : S.edges H = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hCard)
      by_cases hVertices : S.vertexCount H ≤ b.1
      · have hBase := W.empty_value b H hEmpty
        simp only [if_pos hVertices] at hBase
        rw [hBase] at hA
        injection hA with ha
        subst a
        exact ⟨Derivation.empty hEmpty hVertices⟩
      · have hBase := W.empty_value b H hEmpty
        simp only [if_neg hVertices] at hBase
        rw [hBase] at hA
        contradiction
  | succ n ih =>
      by_cases hEmpty : S.edges H = ∅
      · by_cases hVertices : S.vertexCount H ≤ b.1
        · have hBase := W.empty_value b H hEmpty
          simp only [if_pos hVertices] at hBase
          rw [hBase] at hA
          injection hA with ha
          subst a
          exact ⟨Derivation.empty hEmpty hVertices⟩
        · have hBase := W.empty_value b H hEmpty
          simp only [if_neg hVertices] at hBase
          rw [hBase] at hA
          contradiction
      · have hNonempty : (S.edges H).Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        have hStep := W.nonempty_value b H hEmpty
        rw [hA] at hStep
        cases a with
        | zero => contradiction
        | succ k =>
          rcases hStep with hEdge | hPair
          · have hEdge' : ∀ e : PresentEdge S H, ∃ ae,
                A b (S.eraseEdge H e.1) = some ae ∧ k ≤ ae := by
              intro e
              exact (exponentAtLeast_eq_true_iff _ _).mp (hEdge e)
            let childExponent : PresentEdge S H → ℕ :=
              fun e => Classical.choose (hEdge' e)
            have hChildA : ∀ e : PresentEdge S H,
                A b (S.eraseEdge H e.1) = some (childExponent e) := by
              intro e
              exact (Classical.choose_spec (hEdge' e)).1
            have hExponent : ∀ e : PresentEdge S H, k ≤ childExponent e := by
              intro e
              exact (Classical.choose_spec (hEdge' e)).2
            have hChildCard : ∀ e : PresentEdge S H,
                (S.edges (S.eraseEdge H e.1)).card ≤ n := by
              intro e
              apply Nat.lt_succ_iff.mp
              exact (S.eraseEdge_card_lt H e.1 e.2).trans_le hCard
            have hChild : ∀ e : PresentEdge S H,
                Nonempty (Derivation S b.1 (S.eraseEdge H e.1) (childExponent e)) := by
              intro e
              exact ih (hChildCard e) (hChildA e)
            exact ⟨Derivation.edge hNonempty childExponent hExponent
              (fun e => Classical.choice (hChild e))⟩
          · rcases hPair with ⟨b', hb, e, hAtLeast⟩
            rcases (exponentAtLeast_eq_true_iff _ _).mp hAtLeast with
              ⟨childExponent, hChildA, hExponent⟩
            have hChildCard : (S.edges (S.erasePair H e.1)).card ≤ n := by
              apply Nat.lt_succ_iff.mp
              exact (S.erasePair_card_lt H e.1 e.2).trans_le hCard
            have hChild : Nonempty
                (Derivation S b'.1 (S.erasePair H e.1) childExponent) :=
              ih hChildCard hChildA
            rw [hb]
            exact ⟨Derivation.pair e childExponent hExponent
              (Classical.choice hChild)⟩

/-- Every entry of a bounded table satisfying the local recurrence is sound. -/
theorem bounded_finite_recurrence_sound {B : ℕ}
    {A : Fin (B + 1) → Pattern → Option ℕ}
    (W : BoundedLocalWitness S A) {b : Fin (B + 1)}
    {H : Pattern} {a : ℕ} (hA : A b H = some a) :
    ∃ D : Derivation S b.1 H a,
      M.value H ≤ Derivation.coefficient (S := S) D * M.p ^ a * M.N ^ b.1 +
        Derivation.tail (S := S) (M := M) D := by
  let D := Classical.choice
    (BoundedLocalWitness.toDerivation_le (S := S) W
      (S.edges H).card le_rfl hA)
  exact ⟨D, Derivation.sound (S := S) (M := M) D⟩

/-! ## Reading the bit-mask tables -/

/-- The edge indices selected by a 15-bit graph mask. -/
def maskEdges (g : K6Prefix.GraphMask) : Finset ℕ :=
  (Finset.range K6Prefix.edgeCount).filter fun i => g.testBit i = true

/-- The vertices selected by a six-bit vertex mask. -/
def maskVertexCount (vertices : K6Prefix.VertexMask) : ℕ :=
  K6Prefix.countBits K6Prefix.vertexCount vertices

/-- The four tables which occur in the checked computation. -/
def checkedTable : Fin 4 → Array Int
  := fun b =>
    (#[K6Prefix.table0, K6Prefix.table1, K6Prefix.table2,
      K6Prefix.table3] : Array (Array Int))[b]

/-- Convert the finite table's sentinel convention to `Option Nat`. -/
def decodeExponent (z : Int) : Option ℕ :=
  if z = K6Prefix.negInf then none
  else if 0 ≤ z then some z.toNat else none

/-- Read one checked table cell.  Out-of-range cells are deliberately absent. -/
def checkedExponent (b : Fin 4) (vertices : K6Prefix.VertexMask)
    (g : K6Prefix.GraphMask) : Option ℕ :=
  ((checkedTable b)[K6Prefix.stateIndex vertices g]?).bind decodeExponent

/-- The validity predicate used by `K6Prefix.buildTable`. -/
def ValidMaskState (vertices : K6Prefix.VertexMask) (g : K6Prefix.GraphMask) : Prop :=
  vertices < K6Prefix.vertexSetCount ∧
    g < K6Prefix.graphCount ∧
    (g &&& K6Prefix.allowedEdgeMasks[vertices]!) = g

/-! ### A concrete finite deletion system for the checked masks -/

/-- One of the fifteen edge positions in the fixed `K6Prefix.edgePairs` array. -/
abbrev K6Edge := Fin K6Prefix.edgeCount

/--
A finite pattern keeps the six-bit vertex mask and the edge positions as an
actual `Finset`.  Using a `Finset` here makes strict decrease of both deletion
operations a theorem of the representation, rather than an unproved fact
about arithmetic bit subtraction.
-/
structure K6FinitePattern where
  vertices : Fin K6Prefix.vertexSetCount
  edges : Finset K6Edge
deriving DecidableEq

/-- Explicit finite enumeration, avoiding any metaprogram-generated instance. -/
instance : Fintype K6FinitePattern :=
  Fintype.ofEquiv
    (Fin K6Prefix.vertexSetCount × Finset K6Edge)
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun H => (H.vertices, H.edges)
      left_inv := by intro x; cases x; rfl
      right_inv := by intro H; cases H; rfl }

/-- Whether an edge position has both endpoints in a vertex mask. -/
def edgeAllowedBy (vertices : K6Prefix.VertexMask) (e : K6Edge) : Bool :=
  let uv := K6Prefix.edgePairs[e.1]!
  vertices.testBit uv.1 && vertices.testBit uv.2

/-- Vertex mask after deleting the endpoints of `e`. -/
def erasePairVertices (vertices : Fin K6Prefix.vertexSetCount) (e : K6Edge) :
    Fin K6Prefix.vertexSetCount :=
  let uv := K6Prefix.edgePairs[e.1]!
  let child := vertices.1 - K6Prefix.bit uv.1 - K6Prefix.bit uv.2
  ⟨child, by
    have hFirst : child ≤ vertices.1 - K6Prefix.bit uv.1 := Nat.sub_le _ _
    have hSecond : vertices.1 - K6Prefix.bit uv.1 ≤ vertices.1 := Nat.sub_le _ _
    exact hFirst.trans_lt (hSecond.trans_lt vertices.2)⟩

/-- Concrete one-edge deletion. -/
def eraseFiniteEdge (H : K6FinitePattern) (e : K6Edge) : K6FinitePattern :=
  ⟨H.vertices, H.edges.erase e⟩

/-- Concrete endpoint-pair deletion. -/
def eraseFinitePair (H : K6FinitePattern) (e : K6Edge) : K6FinitePattern :=
  let childVertices := erasePairVertices H.vertices e
  ⟨childVertices,
    (H.edges.erase e).filter fun f => edgeAllowedBy childVertices.1 f = true⟩

/-- The fully concrete deletion system used to interpret the four DP tables. -/
def k6FinitePrefixSystem : PrefixSystem K6FinitePattern K6Edge where
  edges := K6FinitePattern.edges
  vertexCount H := maskVertexCount H.vertices.1
  eraseEdge := eraseFiniteEdge
  erasePair := eraseFinitePair
  eraseEdge_card_lt := by
    intro H e he
    exact Finset.card_erase_lt_of_mem he
  erasePair_card_lt := by
    intro H e he
    exact (Finset.card_filter_le _ _).trans_lt
      (Finset.card_erase_lt_of_mem he)

/-- The present edges of a concrete mask have the evident executable enumeration. -/
instance k6PresentEdgeFintype (H : K6FinitePattern) :
    Fintype (PresentEdge k6FinitePrefixSystem H) :=
  Fintype.ofFinset H.edges (fun _ => by rfl)

/-- Encode a `Finset` of edge positions as the 15-bit mask read by the DP. -/
def edgeFinsetMask (s : Finset K6Edge) : K6Prefix.GraphMask :=
  ∑ e ∈ s, K6Prefix.bit e.1

/-- Decode a bounded graph mask into its set of edge positions. -/
def edgeFinsetOfMask (g : Fin K6Prefix.graphCount) : Finset K6Edge :=
  Finset.univ.filter fun e => g.1.testBit e.1 = true

/-- Decode the two raw masks into the concrete finite pattern. -/
def finitePatternOfMasks (vertices : Fin K6Prefix.vertexSetCount)
    (g : Fin K6Prefix.graphCount) : K6FinitePattern :=
  ⟨vertices, edgeFinsetOfMask g⟩

/-- Exact round trip between the finite edge-set and bit-mask representations. -/
theorem edgeMask_roundtrip :
    ∀ g : Fin K6Prefix.graphCount, edgeFinsetMask (edgeFinsetOfMask g) = g.1 := by
  native_decide

/-- The actual optional exponent returned by the checked table for a pattern. -/
def concreteCheckedExponent (b : Fin 4) (H : K6FinitePattern) : Option ℕ :=
  checkedExponent b H.vertices.1 (edgeFinsetMask H.edges)

/-- Reading a raw mask and reading its concrete pattern give the same DP cell. -/
theorem concreteCheckedExponent_ofMasks (b : Fin 4)
    (vertices : Fin K6Prefix.vertexSetCount) (g : Fin K6Prefix.graphCount) :
    concreteCheckedExponent b (finitePatternOfMasks vertices g) =
      checkedExponent b vertices.1 g.1 := by
  simp [concreteCheckedExponent, finitePatternOfMasks, edgeMask_roundtrip]

/-- The full six-vertex mask and the `b = 3` table index. -/
def fullVertexMask : Fin K6Prefix.vertexSetCount :=
  ⟨K6Prefix.vertexSetCount - 1, by native_decide⟩

def exponentIndexThree : Fin 4 := ⟨3, by decide⟩

/-- `checkedExponent` at the full mask is exactly the already-verified `A3`. -/
theorem checkedExponent_eq_A3 : ∀ g : Fin K6Prefix.graphCount,
    checkedExponent exponentIndexThree fullVertexMask.1 g.1 =
      decodeExponent (K6Prefix.A3 g.1) := by
  native_decide

/--
Finite Bellman obligation for the concrete table.  Unlike
`K6MaskTableBridge.tableEntry`, this proposition contains no semantic graph
objects and is decidable by exhaustive evaluation over four exponents, sixty
four vertex masks, and `2^15` edge sets.
-/
def ConcreteTableLocal : Prop :=
  BoundedLocalWitness k6FinitePrefixSystem concreteCheckedExponent

/-- The nonempty-state Bellman conclusion, with the table cell exposed as data. -/
def concreteStepCondition (b : Fin 4) (H : K6FinitePattern) : Option ℕ → Prop
  | none => True
  | some 0 => False
  | some (k + 1) =>
      ((∀ e : PresentEdge k6FinitePrefixSystem H,
          exponentAtLeast
            (concreteCheckedExponent b
              (k6FinitePrefixSystem.eraseEdge H e.1)) k = true) ∨
        (∃ b' : Fin 4, b.1 = b'.1 + 1 ∧
          ∃ e : PresentEdge k6FinitePrefixSystem H,
            exponentAtLeast
              (concreteCheckedExponent b'
                (k6FinitePrefixSystem.erasePair H e.1)) k = true))

/-- Executable Boolean form of `concreteStepCondition`.

The quantifiers use raw edges plus membership hypotheses so that the
decidability term remains small; `concreteStepCheck_eq_true_iff` below
transports it to the subtype formulation used by `BoundedLocalWitness`.
-/
def concreteStepCheck (b : Fin 4) (H : K6FinitePattern) : Option ℕ → Bool
  | none => true
  | some 0 => false
  | some (k + 1) =>
      decide (∀ e : K6Edge, e ∈ H.edges →
        exponentAtLeast
          (concreteCheckedExponent b
            (k6FinitePrefixSystem.eraseEdge H e)) k = true) ||
      decide (∃ b' : Fin 4, b.1 = b'.1 + 1 ∧
        ∃ e : K6Edge, e ∈ H.edges ∧
          exponentAtLeast
            (concreteCheckedExponent b'
              (k6FinitePrefixSystem.erasePair H e)) k = true)

/-- The executable and subtype formulations of a nonempty table step agree. -/
theorem concreteStepCheck_eq_true_iff (b : Fin 4) (H : K6FinitePattern)
    (x : Option ℕ) :
    concreteStepCheck b H x = true ↔ concreteStepCondition b H x := by
  cases x with
  | none => simp only [concreteStepCheck, concreteStepCondition]
  | some a =>
      cases a with
      | zero =>
          simp only [concreteStepCheck, concreteStepCondition, Bool.false_eq_true]
      | succ k =>
          simp only [concreteStepCheck, concreteStepCondition, Bool.or_eq_true,
            decide_eq_true_eq]
          constructor
          · intro h
            rcases h with hEdge | ⟨b', hb, e, he, hChild⟩
            · left
              intro e
              exact hEdge e.1 e.2
            · right
              exact ⟨b', hb, ⟨e, he⟩, hChild⟩
          · intro h
            rcases h with hEdge | ⟨b', hb, e, hChild⟩
            · left
              intro e he
              exact hEdge ⟨e, he⟩
            · right
              exact ⟨b', hb, e.1, e.2, hChild⟩

/-- Exhaustive Boolean check of every nonempty concrete table state. -/
theorem concreteTableNonemptyCheck : ∀ (b : Fin 4) (H : K6FinitePattern),
    k6FinitePrefixSystem.edges H ≠ ∅ →
      concreteStepCheck b H (concreteCheckedExponent b H) = true := by
  native_decide

/-- Exhaustive check of the base row on every concrete empty pattern. -/
theorem concreteTableEmptyCheck : ∀ (b : Fin 4) (H : K6FinitePattern),
    k6FinitePrefixSystem.edges H = ∅ →
      concreteCheckedExponent b H =
        if k6FinitePrefixSystem.vertexCount H ≤ b.1 then some 0 else none := by
  native_decide

/--
Executable discharge of the finite Bellman obligation.  This is separate
from the histogram theorem: it checks that every finite DP entry has the
children required by `BoundedLocalWitness`, including the `b-1` index in a
pair step.
-/
theorem concreteTableLocal : ConcreteTableLocal := by
  constructor
  · exact concreteTableEmptyCheck
  · intro b H hNonempty
    have hCheck := concreteTableNonemptyCheck b H hNonempty
    cases hA : concreteCheckedExponent b H with
    | none => trivial
    | some a =>
        cases a with
        | zero =>
            have hFalse : concreteStepCheck b H (some 0) = true := by
              rw [← hA]
              exact hCheck
            simp only [concreteStepCheck, Bool.false_eq_true] at hFalse
        | succ k =>
            have hStep : concreteStepCheck b H (some (k + 1)) = true := by
              rw [← hA]
              exact hCheck
            exact (concreteStepCheck_eq_true_iff b H (some (k + 1))).mp hStep

/--
End-to-end soundness of a checked table cell for the concrete finite deletion
system.  The only hypotheses left here are the analytic edge/pair recurrences
contained in `M`; the DP recurrence itself is discharged by
`concreteTableLocal`.
-/
theorem concrete_checked_entry_sound
    (M : RecurrenceSemantics k6FinitePrefixSystem)
    {b : Fin 4} {H : K6FinitePattern} {a : ℕ}
    (hA : concreteCheckedExponent b H = some a) :
    ∃ D : Derivation k6FinitePrefixSystem b.1 H a,
      M.value H ≤ Derivation.coefficient (S := k6FinitePrefixSystem) D *
          M.p ^ a * M.N ^ b.1 +
        Derivation.tail (S := k6FinitePrefixSystem) (M := M) D :=
  bounded_finite_recurrence_sound (S := k6FinitePrefixSystem) (M := M)
    concreteTableLocal hA

/--
Direct semantic interpretation of the `A3` value used by
`nineEdgePrefixClassification`.
-/
theorem A3_entry_sound (M : RecurrenceSemantics k6FinitePrefixSystem)
    {g : Fin K6Prefix.graphCount} {a : ℕ}
    (hA : decodeExponent (K6Prefix.A3 g.1) = some a) :
    ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      M.value (finitePatternOfMasks fullVertexMask g) ≤
        Derivation.coefficient (S := k6FinitePrefixSystem) D *
            M.p ^ a * M.N ^ 3 +
          Derivation.tail (S := k6FinitePrefixSystem) (M := M) D := by
  apply concrete_checked_entry_sound (b := exponentIndexThree)
    (H := finitePatternOfMasks fullVertexMask g) (a := a) M
  rw [concreteCheckedExponent_ofMasks, checkedExponent_eq_A3]
  exact hA

/-- The form consumed by the nine-edge argument: every `A3 ≥ 4` cell gives
an explicit `p^4 N^3` bound, with exactly the same accumulated tail. -/
theorem A3_atLeastFour_sound (M : RecurrenceSemantics k6FinitePrefixSystem)
    {g : Fin K6Prefix.graphCount} {a : ℕ}
    (hA : decodeExponent (K6Prefix.A3 g.1) = some a) (hFour : 4 ≤ a) :
    ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      M.value (finitePatternOfMasks fullVertexMask g) ≤
        Derivation.coefficient (S := k6FinitePrefixSystem) D *
            M.p ^ 4 * M.N ^ 3 +
          Derivation.tail (S := k6FinitePrefixSystem) (M := M) D := by
  rcases A3_entry_sound M hA with ⟨D, hD⟩
  refine ⟨D, hD.trans ?_⟩
  have hp : M.p ^ a ≤ M.p ^ 4 :=
    pow_le_pow_of_le_one (zero_le M.p) M.p_le_one hFour
  exact add_le_add_right
    (mul_le_mul_right'
      (mul_le_mul_left' hp (Derivation.coefficient (S := k6FinitePrefixSystem) D))
      (M.N ^ 3)) _

/--
Finite classification in exactly the proposition needed by the semantic
bridge: a nonexceptional nine-edge mask has a finite exponent at least four.
This is a consequence of the same executable data checked by
`nineEdgePrefixClassification`, stated without extracting information from a
histogram equality.
-/
theorem ordinaryNineEdge_hasExponent : ∀ g : Fin K6Prefix.graphCount,
    K6Prefix.countBits K6Prefix.edgeCount g.1 = 9 →
    K6Prefix.inExceptionalOrbit g.1 = false →
    exponentAtLeast (decodeExponent (K6Prefix.A3 g.1)) 4 = true := by
  native_decide

/-- Every ordinary nine-edge prefix has the explicit `p^4 N^3 + tail` bound. -/
theorem ordinaryNineEdge_sound (M : RecurrenceSemantics k6FinitePrefixSystem)
    (g : Fin K6Prefix.graphCount)
    (hNine : K6Prefix.countBits K6Prefix.edgeCount g.1 = 9)
    (hOrdinary : K6Prefix.inExceptionalOrbit g.1 = false) :
    ∃ a, ∃ D : Derivation k6FinitePrefixSystem 3
        (finitePatternOfMasks fullVertexMask g) a,
      4 ≤ a ∧
      M.value (finitePatternOfMasks fullVertexMask g) ≤
        Derivation.coefficient (S := k6FinitePrefixSystem) D *
            M.p ^ 4 * M.N ^ 3 +
          Derivation.tail (S := k6FinitePrefixSystem) (M := M) D := by
  have hAtLeast := ordinaryNineEdge_hasExponent g hNine hOrdinary
  rcases (exponentAtLeast_eq_true_iff _ _).mp hAtLeast with ⟨a, hA, hFour⟩
  rcases A3_atLeastFour_sound M hA hFour with ⟨D, hD⟩
  exact ⟨a, D, hFour, hD⟩

/-! ### Optional bridge to another graph representation -/

/--
The precise representation obligations between the executable certificate
and an independently supplied abstract deletion system.

The concrete `K6FinitePattern` interpretation above already discharges the
finite recurrence.  Filling this structure is needed only when transporting
the certificate to some other graph representation.  It is intentionally
separate from
`nineEdgePrefixClassification`: `native_decide` proves facts about arrays and
bit operations, while these fields prove that those operations denote the
mathematical empty, edge-deletion, and endpoint-pair-deletion rules.  The last
field is the local Bellman/table obligation; once it is supplied,
`k6_checked_entry_sound` below is immediate from the general theorem.
-/
structure K6MaskTableBridge where
  decode : K6Prefix.VertexMask → K6Prefix.GraphMask → Pattern
  edgeOfIndex : ℕ → Edge
  edges_decode : ∀ vertices g, ValidMaskState vertices g →
    S.edges (decode vertices g) = (maskEdges g).image edgeOfIndex
  vertexCount_decode : ∀ vertices g, ValidMaskState vertices g →
    S.vertexCount (decode vertices g) = maskVertexCount vertices
  eraseEdge_decode : ∀ vertices g i,
    ValidMaskState vertices g → i ∈ maskEdges g →
    S.eraseEdge (decode vertices g) (edgeOfIndex i) =
      decode vertices (g - K6Prefix.bit i)
  erasePair_decode : ∀ vertices g i,
    ValidMaskState vertices g → i ∈ maskEdges g →
    let uv := K6Prefix.edgePairs[i]!
    let childVertices := vertices - K6Prefix.bit uv.1 - K6Prefix.bit uv.2
    let childEdges := g &&& K6Prefix.allowedEdgeMasks[childVertices]!
    S.erasePair (decode vertices g) (edgeOfIndex i) =
      decode childVertices childEdges
  /--
  The remaining finite proof obligation: each finite entry of the executable
  table denotes a derivation in the abstract deletion system.  This field is
  intentionally visible.  It must ultimately be discharged from the three
  representation equations above and the defining equations of
  `K6Prefix.buildTable`.
  -/
  tableEntry : ∀ (b : Fin 4) vertices g a,
    ValidMaskState vertices g → checkedExponent b vertices g = some a →
    Nonempty (Derivation S b.1 (decode vertices g) a)

/-- The semantic payoff of one finite mask/table entry. -/
theorem k6_checked_entry_sound (B : K6MaskTableBridge S)
    (b : Fin 4) (vertices : K6Prefix.VertexMask)
    (g : K6Prefix.GraphMask) (a : ℕ)
    (hValid : ValidMaskState vertices g)
    (hA : checkedExponent b vertices g = some a) :
    ∃ D : Derivation S b.1 (B.decode vertices g) a,
      M.value (B.decode vertices g) ≤
        Derivation.coefficient (S := S) D * M.p ^ a * M.N ^ b.1 +
          Derivation.tail (S := S) (M := M) D := by
  let D := Classical.choice (B.tableEntry b vertices g a hValid hA)
  exact ⟨D, Derivation.sound (S := S) (M := M) D⟩

end OnlineRamsey.PrefixSoundness
