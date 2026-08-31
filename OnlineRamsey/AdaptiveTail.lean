import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import OnlineRamsey.AdaptiveQuery

/-!
# Finite upper tails for fresh adaptive Bernoulli queries

This file stays entirely in the explicit finite-board `ENNReal` model from
`OnlineRamsey.AdaptiveQuery`.  It packages the exact upper-tail law of the
number of positive answers seen by a deterministic adaptive strategy whose
queries are fresh on every answer path.

No moment-generating functions or measure-theoretic concentration theorem is
needed: the adaptive answer vector has the exact product Bernoulli law, and a
finite regrouping by its set of positive coordinates gives the binomial tail.
-/

namespace OnlineRamsey

open scoped ENNReal

universe u

section FiniteAdaptiveTail

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The event that at least `R` of the first `n` adaptive answers are true. -/
def adaptiveUpperTailEvent (strategy : Strategy Q) (n R : Nat) : Set (Board Q) :=
  {board | R ≤ trueAnswerCount strategy board n}

@[simp]
theorem mem_adaptiveUpperTailEvent (strategy : Strategy Q) (board : Board Q)
    (n R : Nat) :
    board ∈ adaptiveUpperTailEvent strategy n R ↔
      R ≤ trueAnswerCount strategy board n :=
  Iff.rfl

/-- In a Boolean vector of length `n`, the number of false coordinates is
`n` minus the number of true coordinates. -/
theorem vector_count_false_eq_sub_count_true {n : Nat}
    (bits : List.Vector Bool n) :
    bits.toList.count false = n - bits.toList.count true := by
  symm
  apply Nat.sub_eq_of_eq_add'
  have hsum := List.count_true_add_count_false bits.toList
  rw [List.Vector.toList_length] at hsum
  exact hsum.symm

/-- Direct answer-vector form of the exact adaptive Bernoulli upper tail. -/
theorem bernoulli_adaptiveUpperTail_mass_vector
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q) (n R : Nat)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight p) (adaptiveUpperTailEvent strategy n R) =
      ∑ bits : List.Vector Bool n,
        if R ≤ bits.toList.count true then
          p ^ bits.toList.count true *
            (1 - p) ^ (n - bits.toList.count true)
        else 0 := by
  rw [show adaptiveUpperTailEvent strategy n R =
      {board | R ≤ (answerVector strategy board n).toList.count true} by rfl]
  rw [finiteProduct_answerVector_event_mass (bernoulliWeight p)
    (sum_bernoulliWeight p hp) strategy n
    (fun bits ↦ R ≤ bits.toList.count true) hfresh]
  apply Finset.sum_congr rfl
  intro bits _hbits
  by_cases htail : R ≤ bits.toList.count true
  · simp [htail, prod_bernoulliWeight_eq_count,
      vector_count_false_eq_sub_count_true]
  · simp [htail]

/-- The same exact tail, indexed by the finite set of positive coordinates. -/
theorem bernoulli_adaptiveUpperTail_mass_support
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q) (n R : Nat)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight p) (adaptiveUpperTailEvent strategy n R) =
      ∑ support : Finset (Fin n),
        if R ≤ support.card then
          p ^ support.card * (1 - p) ^ (n - support.card)
        else 0 := by
  rw [bernoulli_adaptiveUpperTail_mass_vector p hp strategy n R hfresh]
  apply Fintype.sum_equiv (trueSupportEquiv n)
  intro bits
  change _ = if R ≤ (trueSupport bits).card then
    p ^ (trueSupport bits).card * (1 - p) ^ (n - (trueSupport bits).card) else 0
  rw [card_trueSupport]

/-- The finite binomial upper-tail expression. -/
noncomputable def bernoulliUpperTail (p : ℝ≥0∞) (n R : Nat) : ℝ≥0∞ :=
  ∑ k ∈ Finset.Icc R n,
    (Nat.choose n k : ℝ≥0∞) * p ^ k * (1 - p) ^ (n - k)

/-- Regrouping the support sum by cardinality gives the usual finite binomial
upper-tail formula. -/
theorem sum_support_bernoulli_eq_upperTail (p : ℝ≥0∞) (n R : Nat) :
    (∑ support : Finset (Fin n),
        if R ≤ support.card then
          p ^ support.card * (1 - p) ^ (n - support.card)
        else 0) = bernoulliUpperTail p n R := by
  classical
  let weight : Finset (Fin n) → ℝ≥0∞ := fun support ↦
    p ^ support.card * (1 - p) ^ (n - support.card)
  let selected : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter fun support ↦ R ≤ support.card
  have hselected : selected =
      (Finset.univ : Finset (Finset (Fin n))).filter
        fun support ↦ support.card ∈ Finset.Icc R n := by
    ext support
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Icc]
    exact (and_iff_left (by
      simpa using Finset.card_le_card (Finset.subset_univ support))).symm
  calc
    (∑ support : Finset (Fin n),
        if R ≤ support.card then
          p ^ support.card * (1 - p) ^ (n - support.card)
        else 0) = ∑ support ∈ selected, weight support := by
          simp [selected, weight, Finset.sum_filter]
    _ = ∑ support ∈ (Finset.univ : Finset (Finset (Fin n))) with
          support.card ∈ Finset.Icc R n, weight support := by
          rw [hselected]
    _ = ∑ k ∈ Finset.Icc R n,
          ∑ support ∈ (Finset.univ : Finset (Finset (Fin n))) with
            support.card = k, weight support := by
          exact (Finset.sum_fiberwise_eq_sum_filter
            (Finset.univ : Finset (Finset (Fin n))) (Finset.Icc R n)
            Finset.card weight).symm
    _ = ∑ k ∈ Finset.Icc R n,
          (Nat.choose n k : ℝ≥0∞) * p ^ k * (1 - p) ^ (n - k) := by
          apply Finset.sum_congr rfl
          intro k _hk
          let supportsOfCard : Finset (Finset (Fin n)) :=
            (Finset.univ : Finset (Finset (Fin n))).filter fun support ↦ support.card = k
          have hcard : supportsOfCard.card = Nat.choose n k := by
            calc
              supportsOfCard.card = Fintype.card
                  {support : Finset (Fin n) // support.card = k} := by
                    symm
                    apply Fintype.card_of_subtype supportsOfCard
                    intro support
                    simp [supportsOfCard]
              _ = Nat.choose n k := by
                    simpa using (Fintype.card_finset_len (Fin n) k)
          rw [show (∑ support ∈ (Finset.univ : Finset (Finset (Fin n))) with
              support.card = k, weight support) =
              ∑ _support ∈ supportsOfCard,
                p ^ k * (1 - p) ^ (n - k) by
                apply Finset.sum_congr
                · ext support
                  simp [supportsOfCard]
                · intro support hsupport
                  have hcount : support.card = k := by
                    simpa [supportsOfCard] using hsupport
                  simp [weight, hcount]]
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          simp [mul_assoc]
    _ = bernoulliUpperTail p n R := rfl

/-- Exact binomial upper tail for any fresh deterministic adaptive strategy. -/
theorem bernoulli_adaptiveUpperTail_mass
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q) (n R : Nat)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight p) (adaptiveUpperTailEvent strategy n R) =
      bernoulliUpperTail p n R := by
  rw [bernoulli_adaptiveUpperTail_mass_support p hp strategy n R hfresh]
  exact sum_support_bernoulli_eq_upperTail p n R

/-- A shifted binomial sum.  Combinatorially, after fixing `R` prescribed
positive positions, all remaining `n - R` coordinates are unrestricted. -/
theorem sum_Icc_choose_mul_bernoulli_eq_pow
    (p : ℝ≥0∞) (hp : p ≤ 1) {n R : Nat} (hRn : R ≤ n) :
    (∑ k ∈ Finset.Icc R n,
        (Nat.choose (n - R) (k - R) : ℝ≥0∞) *
          p ^ k * (1 - p) ^ (n - k)) = p ^ R := by
  classical
  have hIcc : Finset.Icc R n = Finset.Ico R (n + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hlength : n + 1 - R = n - R + 1 := by omega
  rw [hlength]
  calc
    (∑ k ∈ Finset.range (n - R + 1),
        (Nat.choose (n - R) (R + k - R) : ℝ≥0∞) *
          p ^ (R + k) * (1 - p) ^ (n - (R + k))) =
        p ^ R * ∑ k ∈ Finset.range (n - R + 1),
          p ^ k * (1 - p) ^ (n - R - k) *
            (Nat.choose (n - R) k : ℝ≥0∞) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ n - R := by
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hcomplement : n - (R + k) = n - R - k := by omega
      simp only [Nat.add_sub_cancel_left, hcomplement, pow_add]
      ac_rfl
    _ = p ^ R * (p + (1 - p)) ^ (n - R) := by
      rw [add_pow]
    _ = p ^ R := by
      rw [add_tsub_cancel_of_le hp]
      simp

/-- Finite witness (factorial-moment) bound for a binomial upper tail.  If at
least `R` coordinates are positive, one may choose an `R`-subset of them;
summing over those witnesses gives `choose n R * p^R`. -/
theorem bernoulliUpperTail_le_choose_mul_pow
    (p : ℝ≥0∞) (hp : p ≤ 1) (n R : Nat) :
    bernoulliUpperTail p n R ≤ (Nat.choose n R : ℝ≥0∞) * p ^ R := by
  classical
  by_cases hRn : R ≤ n
  · unfold bernoulliUpperTail
    calc
      (∑ k ∈ Finset.Icc R n,
          (Nat.choose n k : ℝ≥0∞) * p ^ k * (1 - p) ^ (n - k)) ≤
          ∑ k ∈ Finset.Icc R n,
            ((Nat.choose n R : ℝ≥0∞) *
                (Nat.choose (n - R) (k - R) : ℝ≥0∞)) *
              p ^ k * (1 - p) ^ (n - k) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hchooseNat :
            Nat.choose n k ≤ Nat.choose n R * Nat.choose (n - R) (k - R) := by
          calc
            Nat.choose n k ≤ Nat.choose n k * Nat.choose k R :=
              Nat.le_mul_of_pos_right _ (Nat.choose_pos hk'.1)
            _ = Nat.choose n R * Nat.choose (n - R) (k - R) :=
              Nat.choose_mul hk'.2 hk'.1
        have hchoose :
            (Nat.choose n k : ℝ≥0∞) ≤
              (Nat.choose n R : ℝ≥0∞) *
                (Nat.choose (n - R) (k - R) : ℝ≥0∞) := by
          exact_mod_cast hchooseNat
        gcongr
      _ = (Nat.choose n R : ℝ≥0∞) *
          (∑ k ∈ Finset.Icc R n,
            (Nat.choose (n - R) (k - R) : ℝ≥0∞) *
              p ^ k * (1 - p) ^ (n - k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ac_rfl
      _ = (Nat.choose n R : ℝ≥0∞) * p ^ R := by
        rw [sum_Icc_choose_mul_bernoulli_eq_pow p hp hRn]
  · have hlt : n < R := Nat.lt_of_not_ge hRn
    simp [bernoulliUpperTail, Finset.Icc_eq_empty hRn,
      Nat.choose_eq_zero_of_lt hlt]

/-- The adaptive form of the finite witness upper-tail bound. -/
theorem bernoulli_adaptiveUpperTail_mass_le_choose_mul_pow
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q) (n R : Nat)
    (hfresh : ∀ bits : List.Vector Bool n, FreshPath strategy bits.toList) :
    finiteBoardMass (bernoulliWeight p) (adaptiveUpperTailEvent strategy n R) ≤
      (Nat.choose n R : ℝ≥0∞) * p ^ R := by
  rw [bernoulli_adaptiveUpperTail_mass p hp strategy n R hfresh]
  exact bernoulliUpperTail_le_choose_mul_pow p hp n R

end FiniteAdaptiveTail

end OnlineRamsey
