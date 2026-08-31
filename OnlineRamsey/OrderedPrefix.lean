import OnlineRamsey.AdaptiveQuery

/-!
# Ordered-prefix exposure on a finite adaptive Bernoulli board

This file proves the probabilistic core of the ordered-prefix argument without
conditional probabilities or stopping-time machinery.  Histories in
`AdaptiveQuery` are newest first.  Consequently, if `prefix` records the
answers already exposed and `extension` records later answers, then the whole
path is `extension ++ prefix`.

For a fresh deterministic path, its cylinder mass is the product of its bit
weights.  Splitting that product at the list append gives an exact
factorization.  In particular, asking for `k` further positive answers costs
exactly `p ^ k`.  A finite weighted sum then gives the corresponding identity
for an expected weighted count of path indicators; no disjointness of the
path events is required.

The last section records the numerical `K₆` specialization `k = 15 - r`.
Turning it into the paper's full ordered-copy lemma still requires a finite
indexing of prefix embeddings at their completion histories.  The exact
boundary is documented in `OrderedPrefixStatus.md`.
-/

namespace OnlineRamsey

open scoped ENNReal

universe u v

section FreshSuffix

variable {Q : Type u}

/-- Freshness of a whole ordered extension implies freshness of its prefix. -/
theorem freshPath_of_append_left (strategy : Strategy Q)
    (extension pre : List Bool)
    (hfresh : FreshPath strategy (extension ++ pre)) :
    FreshPath strategy pre := by
  induction extension with
  | nil => simpa using hfresh
  | cons bit extension ih =>
      have htail : FreshPath strategy (extension ++ pre) :=
        ((freshPath_cons strategy bit (extension ++ pre)).mp hfresh).2
      exact ih htail

end FreshSuffix

section OrderedExtension

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-!
## One path

The next theorem is deliberately stated for arbitrary one-bit weights.  The
normalization assumption is used only to identify the explicit finite board
sum with the product probability law.
-/

/--
Exact ordered-extension factorization for a fresh adaptive path.

The strategy may choose every next query from the complete preceding
transcript.  Only freshness on the displayed path is assumed.
-/
theorem finiteProduct_orderedExtension_mass
    (weight : Bool → ℝ≥0∞) (hnormalized : (∑ bit : Bool, weight bit) = 1)
    (strategy : Strategy Q) (extension pre : List Bool)
    (hfresh : FreshPath strategy (extension ++ pre)) :
    finiteBoardMass weight (pathEvent strategy (extension ++ pre)) =
      (extension.map weight).prod *
        finiteBoardMass weight (pathEvent strategy pre) := by
  have hprefix : FreshPath strategy pre :=
    freshPath_of_append_left strategy extension pre hfresh
  rw [finiteProduct_adaptive_path_mass weight hnormalized strategy
      (extension ++ pre) hfresh,
    finiteProduct_adaptive_path_mass weight hnormalized strategy pre hprefix]
  simp

/-- A list of `k` later positive answers, prepended to a newest-first prefix. -/
def allPositiveExtension (k : ℕ) (pre : List Bool) : List Bool :=
  List.replicate k true ++ pre

@[simp] theorem length_allPositiveExtension (k : ℕ) (pre : List Bool) :
    (allPositiveExtension k pre).length = k + pre.length := by
  simp [allPositiveExtension]

/--
Every fresh ordered extension by `k` positive answers costs exactly `p ^ k`.
This exact identity is stronger than the ordered-prefix upper bound.
-/
theorem bernoulli_allPositiveExtension_mass
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q)
    (k : ℕ) (pre : List Bool)
    (hfresh : FreshPath strategy (allPositiveExtension k pre)) :
    finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy (allPositiveExtension k pre)) =
      p ^ k * finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy pre) := by
  rw [show allPositiveExtension k pre = List.replicate k true ++ pre by
    rfl]
  rw [finiteProduct_orderedExtension_mass (bernoulliWeight p)
    (sum_bernoulliWeight p hp) strategy (List.replicate k true) pre hfresh]
  simp [bernoulliWeight]

/-- The inequality form used in an ordered-prefix estimate. -/
theorem bernoulli_allPositiveExtension_mass_le
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q)
    (k : ℕ) (pre : List Bool)
    (hfresh : FreshPath strategy (allPositiveExtension k pre)) :
    finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy (allPositiveExtension k pre)) ≤
      p ^ k * finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy pre) :=
  (bernoulli_allPositiveExtension_mass p hp strategy k pre hfresh).le

/-!
## Finite weighted families

The quantity below is the finite sum of the masses of path indicators, with
arbitrary nonnegative weights.  By finite linearity it is exactly the
expectation of the corresponding weighted indicator count, even when the path
events overlap.
-/

/-- Weighted mass of a finite family of adaptive path events. -/
noncomputable def weightedPathMass {I : Type v} [DecidableEq I]
    (weight : Bool → ℝ≥0∞) (strategy : Strategy Q) (indices : Finset I)
    (coefficient : I → ℝ≥0∞) (bits : I → List Bool) : ℝ≥0∞ :=
  ∑ i ∈ indices,
    coefficient i * finiteBoardMass weight (pathEvent strategy (bits i))

/--
Exact factorization for a finite weighted family with a common number `k` of
later positive answers.  The prefixes may differ with the index.
-/
theorem bernoulli_weighted_allPositiveExtension_mass
    {I : Type v} [DecidableEq I]
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q)
    (indices : Finset I) (coefficient : I → ℝ≥0∞)
    (k : ℕ) (pre : I → List Bool)
    (hfresh : ∀ i ∈ indices,
      FreshPath strategy (allPositiveExtension k (pre i))) :
    weightedPathMass (bernoulliWeight p) strategy indices coefficient
        (fun i ↦ allPositiveExtension k (pre i)) =
      p ^ k * weightedPathMass (bernoulliWeight p) strategy indices
        coefficient pre := by
  unfold weightedPathMass
  calc
    (∑ i ∈ indices,
        coefficient i * finiteBoardMass (bernoulliWeight p)
          (pathEvent strategy (allPositiveExtension k (pre i)))) =
        ∑ i ∈ indices,
          coefficient i * (p ^ k * finiteBoardMass (bernoulliWeight p)
            (pathEvent strategy (pre i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [bernoulli_allPositiveExtension_mass p hp strategy k
                (pre i) (hfresh i hi)]
    _ = p ^ k * ∑ i ∈ indices,
          coefficient i * finiteBoardMass (bernoulliWeight p)
            (pathEvent strategy (pre i)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _hi
              ac_rfl

/-- Inequality form of the finite weighted ordered-prefix identity. -/
theorem bernoulli_weighted_allPositiveExtension_mass_le
    {I : Type v} [DecidableEq I]
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q)
    (indices : Finset I) (coefficient : I → ℝ≥0∞)
    (k : ℕ) (pre : I → List Bool)
    (hfresh : ∀ i ∈ indices,
      FreshPath strategy (allPositiveExtension k (pre i))) :
    weightedPathMass (bernoulliWeight p) strategy indices coefficient
        (fun i ↦ allPositiveExtension k (pre i)) ≤
      p ^ k * weightedPathMass (bernoulliWeight p) strategy indices
        coefficient pre :=
  (bernoulli_weighted_allPositiveExtension_mass p hp strategy indices
    coefficient k pre hfresh).le

end OrderedExtension

section K6Specialization

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- A legal prefix length for the fifteen-edge graph `K₆`. -/
abbrev K6PrefixLength := Fin 16

/--
The complete answer list obtained from an `r`-answer prefix by requiring all
of the remaining `15 - r` answers to be positive.
-/
def k6CompletionBits (r : K6PrefixLength)
    (pre : List.Vector Bool r.val) : List Bool :=
  allPositiveExtension (15 - r.val) pre.toList

@[simp] theorem length_k6CompletionBits (r : K6PrefixLength)
    (pre : List.Vector Bool r.val) :
    (k6CompletionBits r pre).length = 15 := by
  rw [k6CompletionBits, length_allPositiveExtension,
    List.Vector.toList_length]
  exact Nat.sub_add_cancel (Nat.le_of_lt_succ r.isLt)

/--
Finite `K₆` ordered-prefix cylinder bound.  Starting from an `r`-answer
prefix, a fresh completion of all remaining clique-edge answers has mass
exactly `p ^ (15 - r)` times the prefix mass.
-/
theorem bernoulli_k6_orderedPrefix_mass
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q)
    (r : K6PrefixLength) (pre : List.Vector Bool r.val)
    (hfresh : FreshPath strategy (k6CompletionBits r pre)) :
    finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy (k6CompletionBits r pre)) =
      p ^ (15 - r.val) * finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy pre.toList) := by
  exact bernoulli_allPositiveExtension_mass p hp strategy (15 - r.val)
    pre.toList hfresh

/-- Inequality form of the finite `K₆` ordered-prefix cylinder bound. -/
theorem bernoulli_k6_orderedPrefix_mass_le
    (p : ℝ≥0∞) (hp : p ≤ 1) (strategy : Strategy Q)
    (r : K6PrefixLength) (pre : List.Vector Bool r.val)
    (hfresh : FreshPath strategy (k6CompletionBits r pre)) :
    finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy (k6CompletionBits r pre)) ≤
      p ^ (15 - r.val) * finiteBoardMass (bernoulliWeight p)
        (pathEvent strategy pre.toList) :=
  (bernoulli_k6_orderedPrefix_mass p hp strategy r pre hfresh).le

end K6Specialization

end OnlineRamsey
