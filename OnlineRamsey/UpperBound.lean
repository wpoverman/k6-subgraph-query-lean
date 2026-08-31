import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The deterministic and moment cores of the `K₆` branch-and-fill upper bound

The upper bound in the subgraph-query problem uses the parameterization
`p = q³`.  If `a` represents `q⁻¹`, its three relevant integer scales are

* `a¹⁰` initial queries;
* `a²` branch trials, each scanning at most `a⁷` reservoir vertices;
* `a⁴` vertices in each filled set.

This file proves, with explicit constants, that these operations use only
`O(a¹⁰)` queries.  It also isolates the exact real-algebra step which turns
the first- and second-moment estimates for the number of `K₄`'s in one
filled set into a lower bound of order `a⁻²` for one trial.

The random-graph moment estimates and their connection to an adaptive query
tree belong in a probability module.  They are deliberately hypotheses of
`oneTrial_success_of_moment_bounds`, rather than axioms or unproved declarations.
-/

namespace OnlineRamsey

namespace K6Upper

section FiniteK4PairCount

variable {α : Type*} [DecidableEq α]

/-- The `r`-subsets of `U` meeting a fixed set `A` in exactly `k` points. -/
def fixedIntersectionFamily (U A : Finset α) (r k : ℕ) : Finset (Finset α) :=
  (U.powersetCard r).filter fun B => (A ∩ B).card = k

/-- Exact finite hypergeometric fiber count.

Every `r`-subset `B` of `U` with `|A ∩ B| = k` is uniquely the union of
the `k`-set `A ∩ B` and the `(r-k)`-set `B \ A`.  This is the combinatorial
identity needed to group the ordered pairs of `K₄` vertex sets in the
second-moment computation.
-/
theorem card_fixedIntersectionFamily
    (U A : Finset α) (r k : ℕ) (hAU : A ⊆ U) (hkr : k ≤ r) :
    (fixedIntersectionFamily U A r k).card =
      (A.card.choose k) * ((U \ A).card.choose (r - k)) := by
  let source : Finset (Finset α × Finset α) :=
    A.powersetCard k ×ˢ (U \ A).powersetCard (r - k)
  have hcard : source.card = (fixedIntersectionFamily U A r k).card := by
    refine Finset.card_bij (fun z _hz => z.1 ∪ z.2) ?_ ?_ ?_
    · intro z hz
      rcases Finset.mem_product.mp hz with ⟨hz₁, hz₂⟩
      rcases Finset.mem_powersetCard.mp hz₁ with ⟨hz₁A, hcard₁⟩
      rcases Finset.mem_powersetCard.mp hz₂ with ⟨hz₂UA, hcard₂⟩
      have hz₂U : z.2 ⊆ U := hz₂UA.trans Finset.sdiff_subset
      have hdisj : Disjoint z.1 z.2 := by
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        exact (Finset.mem_sdiff.mp (hz₂UA hx₂)).2 (hz₁A hx₁)
      have hinter : A ∩ (z.1 ∪ z.2) = z.1 := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_inter.mp hx with ⟨hxA, hxunion⟩
          rcases Finset.mem_union.mp hxunion with hx₁ | hx₂
          · exact hx₁
          · exact False.elim ((Finset.mem_sdiff.mp (hz₂UA hx₂)).2 hxA)
        · intro hx₁
          exact Finset.mem_inter.mpr
            ⟨hz₁A hx₁, Finset.mem_union_left _ hx₁⟩
      rw [fixedIntersectionFamily, Finset.mem_filter,
        Finset.mem_powersetCard]
      refine ⟨⟨Finset.union_subset (hz₁A.trans hAU) hz₂U, ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hcard₁, hcard₂,
          Nat.add_sub_of_le hkr]
      · rw [hinter, hcard₁]
    · intro z hz w hw hunion
      rcases Finset.mem_product.mp hz with ⟨hz₁, hz₂⟩
      rcases Finset.mem_product.mp hw with ⟨hw₁, hw₂⟩
      have hz₁A := (Finset.mem_powersetCard.mp hz₁).1
      have hz₂UA := (Finset.mem_powersetCard.mp hz₂).1
      have hw₁A := (Finset.mem_powersetCard.mp hw₁).1
      have hw₂UA := (Finset.mem_powersetCard.mp hw₂).1
      change z.1 ∪ z.2 = w.1 ∪ w.2 at hunion
      apply Prod.ext
      · ext x
        constructor
        · intro hxz₁
          have hxzw : x ∈ w.1 ∪ w.2 := by
            rw [← hunion]
            exact Finset.mem_union_left _ hxz₁
          rcases Finset.mem_union.mp hxzw with hxw₁ | hxw₂
          · exact hxw₁
          · exact False.elim
              ((Finset.mem_sdiff.mp (hw₂UA hxw₂)).2 (hz₁A hxz₁))
        · intro hxw₁
          have hxwz : x ∈ z.1 ∪ z.2 := by
            rw [hunion]
            exact Finset.mem_union_left _ hxw₁
          rcases Finset.mem_union.mp hxwz with hxz₁ | hxz₂
          · exact hxz₁
          · exact False.elim
              ((Finset.mem_sdiff.mp (hz₂UA hxz₂)).2 (hw₁A hxw₁))
      · ext x
        constructor
        · intro hxz₂
          have hxzw : x ∈ w.1 ∪ w.2 := by
            rw [← hunion]
            exact Finset.mem_union_right _ hxz₂
          rcases Finset.mem_union.mp hxzw with hxw₁ | hxw₂
          · exact False.elim
              ((Finset.mem_sdiff.mp (hz₂UA hxz₂)).2 (hw₁A hxw₁))
          · exact hxw₂
        · intro hxw₂
          have hxwz : x ∈ z.1 ∪ z.2 := by
            rw [hunion]
            exact Finset.mem_union_right _ hxw₂
          rcases Finset.mem_union.mp hxwz with hxz₁ | hxz₂
          · exact False.elim
              ((Finset.mem_sdiff.mp (hw₂UA hxw₂)).2 (hz₁A hxz₁))
          · exact hxz₂
    · intro B hB
      rw [fixedIntersectionFamily, Finset.mem_filter,
        Finset.mem_powersetCard] at hB
      rcases hB with ⟨⟨hBU, hcardB⟩, hintercard⟩
      refine ⟨(A ∩ B, B \ A), ?_, ?_⟩
      · rw [Finset.mem_product]
        constructor
        · exact Finset.mem_powersetCard.mpr
            ⟨Finset.inter_subset_left, hintercard⟩
        · apply Finset.mem_powersetCard.mpr
          constructor
          · intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxA⟩
            exact Finset.mem_sdiff.mpr ⟨hBU hxB, hxA⟩
          · rw [Finset.card_sdiff, hcardB, hintercard]
      · ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_inter.mp hx).2
          · exact (Finset.mem_sdiff.mp hx).1
        · intro hxB
          by_cases hxA : x ∈ A
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxA, hxB⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxB, hxA⟩)
  rw [← hcard]
  simp [source]

/-- For a fixed four-set `A`, the number of four-sets `B ⊆ U` meeting it
in exactly `k` vertices is
`choose 4 k * choose (|U|-4) (4-k)`.

This is the coefficient of the overlap-`k` summand in the exact `K₄`
second-moment identity.
-/
theorem card_k4Sets_with_intersection
    (U A : Finset α) (k : ℕ) (hAU : A ⊆ U) (hA : A.card = 4)
    (hk : k ≤ 4) :
    ((U.powersetCard 4).filter fun B => (A ∩ B).card = k).card =
      Nat.choose 4 k * Nat.choose (U.card - 4) (4 - k) := by
  simpa [fixedIntersectionFamily, hA, Finset.card_sdiff_of_subset hAU] using
    card_fixedIntersectionFamily U A 4 k hAU hk

/-- Exact count of ordered pairs of four-sets with a prescribed overlap.

This is the full combinatorial coefficient in the `K₄` second moment; the
remaining probabilistic input is only that the union of a pair with overlap
`k` requires `12 - choose k 2` independent positive edges.
-/
theorem card_orderedK4Pairs_with_intersection
    (U : Finset α) (k : ℕ) (hk : k ≤ 4) :
    (((U.powersetCard 4) ×ˢ (U.powersetCard 4)).filter fun AB =>
      (AB.1 ∩ AB.2).card = k).card =
      Nat.choose U.card 4 * Nat.choose 4 k *
        Nat.choose (U.card - 4) (4 - k) := by
  let S : Finset (Finset α) := U.powersetCard 4
  calc
    (((U.powersetCard 4) ×ˢ (U.powersetCard 4)).filter fun AB =>
        (AB.1 ∩ AB.2).card = k).card =
        ∑ A ∈ S, (S.filter fun B => (A ∩ B).card = k).card := by
      simp only [S, Finset.card_eq_sum_ones, Finset.sum_filter,
        Finset.sum_product]
    _ = ∑ _A ∈ S, Nat.choose 4 k *
          Nat.choose (U.card - 4) (4 - k) := by
      apply Finset.sum_congr rfl
      intro A hA
      rcases Finset.mem_powersetCard.mp hA with ⟨hAU, hAcard⟩
      exact card_k4Sets_with_intersection U A k hAU hAcard hk
    _ = Nat.choose U.card 4 * Nat.choose 4 k *
          Nat.choose (U.card - 4) (4 - k) := by
      simp [S, Nat.mul_assoc]

/-- Group an arbitrary real weight on ordered pairs of four-sets by their
intersection cardinality.  This is a purely finite identity; it is useful
for moments because the joint cylinder probability of two clique indicators
depends only on this intersection cardinality. -/
theorem sum_orderedK4Pairs_by_intersection
    (U : Finset α) (weight : ℕ → ℝ) :
    (∑ AB ∈ (U.powersetCard 4) ×ˢ (U.powersetCard 4),
        weight (AB.1 ∩ AB.2).card) =
      ∑ k ∈ Finset.range 5,
        ((Nat.choose U.card 4 * Nat.choose 4 k *
          Nat.choose (U.card - 4) (4 - k) : ℕ) : ℝ) * weight k := by
  let pairs : Finset (Finset α × Finset α) :=
    (U.powersetCard 4) ×ˢ (U.powersetCard 4)
  let overlap : Finset α × Finset α → ℕ := fun AB => (AB.1 ∩ AB.2).card
  have hoverlap : ∀ AB ∈ pairs, overlap AB ∈ Finset.range 5 := by
    intro AB hAB
    rcases Finset.mem_product.mp hAB with ⟨hA, _hB⟩
    have hAcard : AB.1.card = 4 := (Finset.mem_powersetCard.mp hA).2
    have hinter : (AB.1 ∩ AB.2).card ≤ AB.1.card :=
      Finset.card_le_card Finset.inter_subset_left
    rw [Finset.mem_range]
    change (AB.1 ∩ AB.2).card < 5
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hoverlap weight]
  apply Finset.sum_congr rfl
  intro k hk
  have hk4 : k ≤ 4 := by
    rw [Finset.mem_range] at hk
    omega
  rw [Finset.sum_const, nsmul_eq_mul]
  change
    (((((U.powersetCard 4) ×ˢ (U.powersetCard 4)).filter fun AB =>
      (AB.1 ∩ AB.2).card = k).card : ℕ) : ℝ) * weight k = _
  rw [card_orderedK4Pairs_with_intersection U k hk4]

/-- The exact finite overlap expansion for the edge-count weight appearing
in the `K₄` second moment.  Once a finite Bernoulli board proves that a pair
of clique indicators with overlap `k` has expectation
`p ^ (12 - choose k 2)`, this theorem turns the sum over ordered pairs into
the five standard overlap terms. -/
theorem k4PairEdgeWeight_identity (U : Finset α) (p : ℝ) :
    (∑ AB ∈ (U.powersetCard 4) ×ˢ (U.powersetCard 4),
        p ^ (12 - Nat.choose (AB.1 ∩ AB.2).card 2)) =
      ∑ k ∈ Finset.range 5,
        ((Nat.choose U.card 4 * Nat.choose 4 k *
          Nat.choose (U.card - 4) (4 - k) : ℕ) : ℝ) *
          p ^ (12 - Nat.choose k 2) := by
  simpa using sum_orderedK4Pairs_by_intersection U
    (fun k => p ^ (12 - Nat.choose k 2))

end FiniteK4PairCount

/-- Number of pairs queried when all pairs inside a set of size `s` are filled. -/
def fillCost (s : ℕ) : ℕ := s.choose 2

/-- The elementary bound used to budget a fill operation. -/
theorem fillCost_le_sq (s : ℕ) : fillCost s ≤ s ^ 2 := by
  rw [fillCost, Nat.choose_two_right]
  calc
    s * (s - 1) / 2 ≤ s * (s - 1) := Nat.div_le_self _ _
    _ ≤ s * s := Nat.mul_le_mul_left s (Nat.sub_le s 1)
    _ = s ^ 2 := by simp [pow_two]

/-- The number of queries in the three nonrecursive parts of branch-and-fill.

The terms are, respectively, the initial star, scans of the reservoir by all
branch roots, and complete fills of the selected sets.
-/
def branchFillQueries (initial trials reservoir fillSize : ℕ) : ℕ :=
  initial + trials * reservoir + trials * fillCost fillSize

/-- Integer scales for the `K₆` branch-and-fill construction when `p=q³` and
`a` represents `q⁻¹`.  `amplification` is an absolute constant multiplying the
number of trials. -/
def scaledBranchFillQueries (a amplification : ℕ) : ℕ :=
  branchFillQueries (a ^ 10) (amplification * a ^ 2) (a ^ 7) (a ^ 4)

/-- The branch-and-fill construction has the claimed `a¹⁰` query scale, with
an explicit coefficient. -/
theorem scaledBranchFillQueries_le (a amplification : ℕ) (ha : 1 ≤ a) :
    scaledBranchFillQueries a amplification ≤
      (2 * amplification + 1) * a ^ 10 := by
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hpow : a ^ 9 ≤ a ^ 10 :=
    Nat.pow_le_pow_right ha0 (by omega)
  have hscan : amplification * a ^ 2 * a ^ 7 ≤
      amplification * a ^ 10 := by
    calc
      amplification * a ^ 2 * a ^ 7 = amplification * a ^ 9 := by ring
      _ ≤ amplification * a ^ 10 := Nat.mul_le_mul_left amplification hpow
  have hfill : amplification * a ^ 2 * fillCost (a ^ 4) ≤
      amplification * a ^ 10 := by
    calc
      amplification * a ^ 2 * fillCost (a ^ 4)
          ≤ amplification * a ^ 2 * (a ^ 4) ^ 2 :=
            Nat.mul_le_mul_left (amplification * a ^ 2) (fillCost_le_sq (a ^ 4))
      _ = amplification * a ^ 10 := by ring
  unfold scaledBranchFillQueries branchFillQueries
  calc
    a ^ 10 + amplification * a ^ 2 * a ^ 7 +
          amplification * a ^ 2 * fillCost (a ^ 4)
        ≤ a ^ 10 + amplification * a ^ 10 + amplification * a ^ 10 :=
          Nat.add_le_add (Nat.add_le_add le_rfl hscan) hfill
    _ = (2 * amplification + 1) * a ^ 10 := by ring

/-- A convenient explicit amplification constant.  It is
`5 * 192²`, the denominator produced by the deliberately loose moment bounds
used below. -/
def momentAmplification : ℕ := 184320

/-- The resulting completely explicit deterministic query budget. -/
theorem scaledBranchFillQueries_explicit (a : ℕ) (ha : 1 ≤ a) :
    scaledBranchFillQueries a momentAmplification ≤ 368641 * a ^ 10 := by
  simpa [momentAmplification] using
    scaledBranchFillQueries_le a momentAmplification ha

section MomentCore

/-- Lower target for the expected number of `K₄` copies in one filled set
of size on the `a⁴` scale, when the edge probability is on the `a⁻³` scale. -/
noncomputable def k4FirstMomentLower (a : ℕ) : ℝ :=
  1 / (192 * (a : ℝ) ^ 2)

/-- Upper target for its second moment.  The terms from two `K₄`'s meeting
in two or three vertices are of smaller order; the loose constant `5` absorbs
all intersection types. -/
noncomputable def k4SecondMomentUpper (a : ℕ) : ℝ :=
  5 / (a : ℝ) ^ 2

/-- Success-probability target supplied by the second-moment argument. -/
noncomputable def oneTrialSuccessLower (a : ℕ) : ℝ :=
  1 / (momentAmplification * (a : ℝ) ^ 2)

theorem k4FirstMomentLower_nonneg (a : ℕ) : 0 ≤ k4FirstMomentLower a := by
  unfold k4FirstMomentLower
  positivity

theorem k4SecondMomentUpper_pos (a : ℕ) (ha : 0 < a) :
    0 < k4SecondMomentUpper a := by
  unfold k4SecondMomentUpper
  positivity

/-- The exact algebraic identity behind the constants in the moment bound. -/
theorem moment_constant_identity (a : ℕ) (ha : 0 < a) :
    oneTrialSuccessLower a * k4SecondMomentUpper a =
      k4FirstMomentLower a ^ 2 := by
  have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
  unfold oneTrialSuccessLower k4SecondMomentUpper k4FirstMomentLower
    momentAmplification
  field_simp [ne_of_gt haR]
  all_goals ring

/-- Reusable Paley--Zygmund algebra for one branch-and-fill trial.

In the intended application, `mu = E X`, `nu = E X²`, and `success` is the
probability that `X > 0`, where `X` counts `K₄` copies in the filled set.
The hypothesis `mu² ≤ success * nu` is precisely the Cauchy--Schwarz
second-moment inequality.  Thus this theorem contains no probabilistic axiom:
it only performs the exact final arithmetic once a probability module has
proved the three displayed hypotheses.
-/
theorem oneTrial_success_of_moment_bounds
    (a : ℕ) (ha : 0 < a) (mu nu success : ℝ)
    (hsuccess : 0 ≤ success)
    (hmu : k4FirstMomentLower a ≤ mu)
    (hnu : nu ≤ k4SecondMomentUpper a)
    (hsecond : mu ^ 2 ≤ success * nu) :
    oneTrialSuccessLower a ≤ success := by
  have hL0 : 0 ≤ k4FirstMomentLower a := k4FirstMomentLower_nonneg a
  have hmu0 : 0 ≤ mu := hL0.trans hmu
  have hsq : k4FirstMomentLower a ^ 2 ≤ mu ^ 2 := by
    nlinarith [sq_nonneg (mu - k4FirstMomentLower a)]
  have hprod : k4FirstMomentLower a ^ 2 ≤
      success * k4SecondMomentUpper a := by
    calc
      k4FirstMomentLower a ^ 2 ≤ mu ^ 2 := hsq
      _ ≤ success * nu := hsecond
      _ ≤ success * k4SecondMomentUpper a :=
        mul_le_mul_of_nonneg_left hnu hsuccess
  have hU : 0 < k4SecondMomentUpper a := k4SecondMomentUpper_pos a ha
  rw [← moment_constant_identity a ha] at hprod
  exact (mul_le_mul_iff_left₀ hU).mp hprod

end MomentCore

end K6Upper

end OnlineRamsey
