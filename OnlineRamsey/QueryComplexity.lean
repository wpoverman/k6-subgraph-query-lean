import OnlineRamsey.AdaptiveQuery
import OnlineRamsey.QueryGame
import Mathlib.Data.Sym.Card

/-!
# The finite `K₆` subgraph-query complexity

This file supplies the top-level definition that the analytic parts of the
formalization are intended to bound.  A board is sampled in advance on the
finite coordinate space `Sym2 (Fin (2 * N))`.  A deterministic adaptive
strategy queries exactly `N` coordinates; admissibility says that every
answer path uses distinct, non-diagonal coordinates.  Its positive transcript
then defines a simple graph, and success means that this graph contains a
labelled copy of `K₆`.

All probabilities below are the explicit finite Bernoulli sums from
`AdaptiveQuery.lean`; there is no measure-theoretic or independence axiom.
The final section isolates the lower- and upper-bound estimates as a reusable
interface.  Later modules instantiate both sides with the checked
graph-counting and concrete random-construction arguments and transport the
result to the countably infinite game.
-/

namespace OnlineRamsey
namespace QueryComplexity

open scoped ENNReal

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The canonical vertex set available to an `N`-query strategy. -/
abbrev Vertex (N : ℕ) := Fin (2 * N)

/-- Unordered board coordinates.  Admissible strategies never query the
diagonal coordinates that are present in `Sym2`. -/
abbrev Query (N : ℕ) := Sym2 (Vertex N)

/-- Deterministic adaptive strategies on the canonical finite board. -/
abbrev K6Strategy (N : ℕ) := Strategy (Query N)

/-- The positive-answer graph carried by a transcript of unordered pairs.
Diagonal positive answers are ignored, so looplessness is definitional. -/
def positiveGraph {N : ℕ} (h : Transcript (Query N)) : SimpleGraph (Vertex N) where
  Adj u v := u ≠ v ∧ (s(u, v), true) ∈ h
  symm := by
    intro u v huv
    exact ⟨huv.1.symm, by simpa only [Sym2.eq_swap] using huv.2⟩
  loopless := by
    intro u huv
    exact huv.1 rfl

@[simp] theorem positiveGraph_adj {N : ℕ} (h : Transcript (Query N))
    (u v : Vertex N) :
    (positiveGraph h).Adj u v ↔ u ≠ v ∧ (s(u, v), true) ∈ h := Iff.rfl

/-- The target `K₆`. -/
abbrev K6 : SimpleGraph (Fin 6) := SimpleGraph.completeGraph (Fin 6)

/-- A transcript succeeds exactly when its positive graph contains an
injectively labelled (not necessarily induced) copy of `K₆`. -/
def TranscriptSucceeds {N : ℕ} (h : Transcript (Query N)) : Prop :=
  Nonempty (SimpleGraph.Copy K6 (positiveGraph h))

/-- Membership enlargement of transcripts only adds positive edges. -/
theorem positiveGraph_mono_of_mem {N : ℕ} {h h' : Transcript (Query N)}
    (hsub : ∀ entry, entry ∈ h → entry ∈ h') :
    positiveGraph h ≤ positiveGraph h' := by
  intro u v huv
  exact ⟨huv.1, hsub _ huv.2⟩

/-- A successful transcript stays successful after arbitrary padding. -/
theorem transcriptSucceeds_mono_of_mem {N : ℕ} {h h' : Transcript (Query N)}
    (hsub : ∀ entry, entry ∈ h → entry ∈ h')
    (hsuccess : TranscriptSucceeds h) : TranscriptSucceeds h' := by
  rcases hsuccess with ⟨copy⟩
  exact ⟨(SimpleGraph.Copy.ofLE _ _ (positiveGraph_mono_of_mem hsub)).comp copy⟩

/-- Padding is newest-first, consistently with `FiniteQueryGame.pad`. -/
def pad {N : ℕ} (h padding : Transcript (Query N)) : Transcript (Query N) :=
  padding ++ h

theorem transcriptSucceeds_pad {N : ℕ} {h padding : Transcript (Query N)}
    (hsuccess : TranscriptSucceeds h) : TranscriptSucceeds (pad h padding) := by
  apply transcriptSucceeds_mono_of_mem (h := h) (h' := pad h padding) _ hsuccess
  intro entry hentry
  exact List.mem_append.mpr (Or.inr hentry)

/-- Every complete answer path consists of distinct queried coordinates. -/
def FreshForBudget {N : ℕ} (strategy : K6Strategy N) : Prop :=
  ∀ bits : List.Vector Bool N, FreshPath strategy bits.toList

/-- Every query made before the budget is exhausted is a genuine nonloop
pair.  Histories outside the reachable depth are immaterial. -/
def NonloopForBudget {N : ℕ} (strategy : K6Strategy N) : Prop :=
  ∀ h : Transcript (Query N), h.length < N → ¬(strategy h).IsDiag

/-- The complete pathwise legality condition on a strategy. -/
def Admissible {N : ℕ} (strategy : K6Strategy N) : Prop :=
  FreshForBudget strategy ∧ NonloopForBudget strategy

/-- Boards on which a fixed strategy finds a `K₆` in its first `N` queries. -/
def successEvent (N : ℕ) (strategy : K6Strategy N) : Set (Board (Query N)) :=
  {board | TranscriptSucceeds (run strategy board N)}

/-- Exact success probability under the finite Bernoulli(`p`) product board. -/
noncomputable def successProbability (p : ℝ≥0∞) (N : ℕ)
    (strategy : K6Strategy N) : ℝ≥0∞ :=
  finiteBoardMass (bernoulliWeight p) (successEvent N strategy)

/-- The success probability is literally a finite sum over all labelled
boards; this exposes the kernel-level meaning of the probability. -/
theorem successProbability_eq_board_sum (p : ℝ≥0∞) (N : ℕ)
    (strategy : K6Strategy N) :
    successProbability p N strategy =
      ∑ board : Board (Query N),
        if TranscriptSucceeds (run strategy board N) then
          boardWeight (bernoulliWeight p) board else 0 := by
  rfl

/-- Success can equivalently be decided from the length-`N` adaptive answer
vector by replaying it. -/
def answerVectorSucceeds {N : ℕ} (strategy : K6Strategy N)
    (bits : List.Vector Bool N) : Prop :=
  TranscriptSucceeds (replay strategy bits.toList)

theorem successEvent_eq_answerVector {N : ℕ} (strategy : K6Strategy N) :
    successEvent N strategy =
      {board | answerVectorSucceeds strategy (answerVector strategy board N)} := by
  ext board
  change TranscriptSucceeds (run strategy board N) ↔
    TranscriptSucceeds (replay strategy (answers (run strategy board N)))
  rw [replay_answers_run]

/-- Exact finite answer-vector formula for the success probability.  Freshness
is precisely what makes the adaptive answer vector have product mass. -/
theorem successProbability_eq_answer_sum (p : ℝ≥0∞) (hp : p ≤ 1)
    (N : ℕ) (strategy : K6Strategy N) (hfresh : FreshForBudget strategy) :
    successProbability p N strategy =
      ∑ bits : List.Vector Bool N,
        if answerVectorSucceeds strategy bits then
          (bits.toList.map (bernoulliWeight p)).prod else 0 := by
  rw [successProbability, successEvent_eq_answerVector]
  exact finiteProduct_answerVector_event_mass
    (bernoulliWeight p) (sum_bernoulliWeight p hp) strategy N
    (answerVectorSucceeds strategy) hfresh

/-- Monotonicity under pointwise inclusion of success events. -/
theorem successProbability_mono {p : ℝ≥0∞} {N : ℕ}
    {strategy strategy' : K6Strategy N}
    (hsub : successEvent N strategy ⊆ successEvent N strategy') :
    successProbability p N strategy ≤ successProbability p N strategy' := by
  classical
  unfold successProbability finiteBoardMass
  apply Finset.sum_le_sum
  intro board _
  by_cases hs : board ∈ successEvent N strategy
  · have hs' := hsub hs
    simp [hs, hs']
  · simp [hs]

/-- The standard fixed success threshold, one half. -/
def threshold : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹

/-- Budget `N` is sufficient at density `p` when an admissible deterministic
strategy succeeds with probability at least `1/2`. -/
def Achievable (p : ℝ≥0∞) (N : ℕ) : Prop :=
  p ≤ 1 ∧ ∃ strategy : K6Strategy N,
    Admissible strategy ∧ threshold ≤ successProbability p N strategy

/-- The minimum sufficient query budget, given existence of some sufficient
budget.  The existence proof is an explicit parameter so no global finiteness
claim is silently assumed. -/
noncomputable def queryComplexity (p : ℝ≥0∞)
    (hexists : ∃ N, Achievable p N) : ℕ :=
  Nat.find hexists

theorem queryComplexity_achievable (p : ℝ≥0∞)
    (hexists : ∃ N, Achievable p N) :
    Achievable p (queryComplexity p hexists) :=
  Nat.find_spec hexists

theorem queryComplexity_le (p : ℝ≥0∞)
    (hexists : ∃ N, Achievable p N) {N : ℕ} (hN : Achievable p N) :
    queryComplexity p hexists ≤ N :=
  Nat.find_min' hexists hN

/-! ## A finite, denominator-free `p^{-10/3}` statement

Writing `p = q^3`, the conjectured order `p^{-10/3}` becomes `q^{-10}`.
Thus multiplying the minimum budget by `q^10` gives a formulation that avoids
fractional powers and division at zero.
-/

/-- A predicate has finite cubic-scale power law between constants `c` and
`C` if its least valid budget, multiplied by `q^10`, lies between them for
every `0 < q ≤ 1`. -/
def FiniteCubicPowerLaw (P : ℝ≥0∞ → ℕ → Prop) (c C : ℝ≥0∞) : Prop :=
  ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
    ∃ hexists : ∃ N, P (q ^ 3) N,
      c ≤ (Nat.find hexists : ℝ≥0∞) * q ^ 10 ∧
        (Nat.find hexists : ℝ≥0∞) * q ^ 10 ≤ C

/-- Matching lower and upper estimates imply the finite cubic-scale power
law.  This theorem contains all minimization bookkeeping; its hypotheses are
exactly the two substantive estimates that the rest of the paper must supply.
-/
theorem matching_bounds_imply_finiteCubicPowerLaw
    (P : ℝ≥0∞ → ℕ → Prop) (c C : ℝ≥0∞)
    (hlower : ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∀ N, P (q ^ 3) N → c ≤ (N : ℝ≥0∞) * q ^ 10)
    (hupper : ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∃ N, P (q ^ 3) N ∧ (N : ℝ≥0∞) * q ^ 10 ≤ C) :
    FiniteCubicPowerLaw P c C := by
  intro q hq hq1
  obtain ⟨N, hPN, hNC⟩ := hupper q hq hq1
  let hexists : ∃ M, P (q ^ 3) M := ⟨N, hPN⟩
  refine ⟨hexists, hlower q hq hq1 (Nat.find hexists) (Nat.find_spec hexists), ?_⟩
  have hmin : Nat.find hexists ≤ N := Nat.find_min' hexists hPN
  have hmin' : (Nat.find hexists : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
    exact_mod_cast hmin
  exact (mul_le_mul_right' hmin' (q ^ 10)).trans hNC

/-- Specialized assembly theorem for the `K₆` subgraph-query definition.
No analytic estimate is assumed globally: both estimates are visible theorem
hypotheses. -/
theorem k6_powerLaw_of_matching_bounds (c C : ℝ≥0∞)
    (hlower : ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∀ N, Achievable (q ^ 3) N → c ≤ (N : ℝ≥0∞) * q ^ 10)
    (hupper : ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∃ N, Achievable (q ^ 3) N ∧ (N : ℝ≥0∞) * q ^ 10 ≤ C) :
    FiniteCubicPowerLaw Achievable c C :=
  matching_bounds_imply_finiteCubicPowerLaw Achievable c C hlower hupper

end
end QueryComplexity
end OnlineRamsey
