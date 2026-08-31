import OnlineRamsey.Amplification
import OnlineRamsey.QueryComplexity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# An unconditional finite baseline strategy

This file closes a small but important endpoint issue in the definition of
`QueryComplexity.queryComplexity`: at every fixed density `0 < p ≤ 1`, some
finite budget is genuinely achievable.

The strategy is completely static.  It places `T` vertex-disjoint labelled
copies of `K₆`, queries their fifteen edges, and ignores all answers when
choosing later queries.  The answer-vector law therefore gives the exact
independent-trial failure probability `(1 - p¹⁵)^T`.  Taking `T` large enough
makes this at most one half.

Besides pointwise existence, the final theorem gives one common budget and
one family of strategies for every density in a compact interval
`p₀ ≤ p ≤ 1`.
-/

namespace OnlineRamsey
namespace BaselineStrategy

open scoped BigOperators ENNReal
open QueryComplexity

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## A generic static schedule -/

/-- Follow an injective schedule until time `N`; arbitrary unreachable or
post-budget histories receive `fallback`.  The schedule is read in reverse
order so that the newest-first answer vector has coordinate `i` attached to
`schedule i`. -/
def reverseScheduleStrategy {Q : Type*} (N : ℕ) (schedule : Fin N → Q)
    (fallback : Q) : Strategy Q := fun h ↦
  if hlen : h.length < N then schedule (Fin.rev ⟨h.length, hlen⟩) else fallback

@[simp] theorem reverseScheduleStrategy_of_length_lt {Q : Type*} (N : ℕ)
    (schedule : Fin N → Q) (fallback : Q) (h : Transcript Q)
    (hlen : h.length < N) :
    reverseScheduleStrategy N schedule fallback h =
      schedule (Fin.rev ⟨h.length, hlen⟩) := by
  simp [reverseScheduleStrategy, hlen]

/-- Every query in the replay of a short answer list comes from a schedule
index whose reverse chronological position is before the list length. -/
private theorem mem_queries_replay_reverseSchedule {Q : Type*} (N : ℕ)
    (schedule : Fin N → Q) (fallback : Q) (bits : List Bool)
    (hlen : bits.length ≤ N) {q : Q}
    (hq : q ∈ queries (replay (reverseScheduleStrategy N schedule fallback) bits)) :
    ∃ i : Fin N, N - 1 - i.val < bits.length ∧ q = schedule i := by
  induction bits with
  | nil => simp [queries, replay] at hq
  | cons bit bits ih =>
      simp only [replay_cons, queries, List.map_cons, List.mem_cons] at hq
      have htail : bits.length < N := by simpa using hlen
      rcases hq with hhead | htailmem
      · refine ⟨Fin.rev ⟨bits.length, htail⟩, ?_, ?_⟩
        · simp
          omega
        · simpa [reverseScheduleStrategy, htail] using hhead
      · obtain ⟨i, hi, hischedule⟩ := ih (Nat.le_of_lt htail) htailmem
        exact ⟨i, hi.trans (Nat.lt_succ_self _), hischedule⟩

/-- An injective static schedule is fresh on every complete answer path. -/
theorem reverseScheduleStrategy_fresh {Q : Type*} (N : ℕ)
    (schedule : Fin N → Q) (fallback : Q)
    (hinj : Function.Injective schedule) :
    ∀ bits : List.Vector Bool N,
      FreshPath (reverseScheduleStrategy N schedule fallback) bits.toList := by
  intro bits
  unfold FreshPath
  have hlen : bits.toList.length ≤ N := by simp
  generalize hbits : bits.toList = list
  rw [hbits] at hlen
  clear bits hbits
  induction list with
  | nil => simp [queries, replay]
  | cons bit tail ih =>
      simp only [replay_cons, queries, List.map_cons, List.nodup_cons]
      have htail : tail.length < N := by simpa using hlen
      constructor
      · intro hmem
        obtain ⟨i, hi, heq⟩ :=
          mem_queries_replay_reverseSchedule N schedule fallback tail
            (Nat.le_of_lt htail) hmem
        have heqIndex : i = Fin.rev ⟨tail.length, htail⟩ := by
          apply hinj
          simpa [reverseScheduleStrategy, htail] using heq.symm
        subst i
        simp at hi
        omega
      · exact ih (Nat.le_of_lt htail)

/-- Replaying two policies which agree on every history shorter than the
given answer list gives the same transcript. -/
private theorem replay_eq_of_eq_on_short {Q : Type*}
    (left right : Strategy Q) (bits : List Bool)
    (heq : ∀ h : Transcript Q, h.length < bits.length → left h = right h) :
    replay left bits = replay right bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      have htail : replay left bits = replay right bits := by
        apply ih
        intro h hh
        exact heq h (hh.trans (Nat.lt_succ_self _))
      rw [replay_cons, replay_cons, htail]
      rw [heq (replay right bits) (by simp)]

/-- Exact replay formula for the reverse schedule. -/
theorem replay_reverseSchedule_ofFn {Q : Type*} (N : ℕ)
    (schedule : Fin N → Q) (fallback : Q) (bits : Fin N → Bool) :
    replay (reverseScheduleStrategy N schedule fallback) (List.ofFn bits) =
      List.ofFn (fun i ↦ (schedule i, bits i)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      let tailSchedule : Fin N → Q := fun i ↦ schedule i.succ
      let tailBits : Fin N → Bool := fun i ↦ bits i.succ
      have hpolicies :
          replay (reverseScheduleStrategy (N + 1) schedule fallback)
              (List.ofFn tailBits) =
            replay (reverseScheduleStrategy N tailSchedule fallback)
              (List.ofFn tailBits) := by
        apply replay_eq_of_eq_on_short
        intro h hlen
        have hlenN : h.length < N := by simpa using hlen
        simp only [reverseScheduleStrategy, hlenN, dif_pos]
        have hlenSucc : h.length < N + 1 := hlenN.trans (Nat.lt_succ_self _)
        rw [dif_pos hlenSucc]
        apply congrArg schedule
        apply Fin.ext
        simp
        omega
      rw [List.ofFn_succ, replay_cons, hpolicies, ih]
      have htailLength :
          (List.ofFn (fun i : Fin N ↦ (tailSchedule i, tailBits i))).length = N := by
        simp
      rw [reverseScheduleStrategy_of_length_lt]
      · have hrev : Fin.rev (⟨N, by omega⟩ : Fin (N + 1)) = 0 := by
          apply Fin.ext
          simp
        simp only [List.length_ofFn]
        rw [hrev]
        simp [List.ofFn_succ, tailSchedule, tailBits]
      · simp [htailLength]

/-- Coordinate `i` in a complete newest-first answer vector is attached to
exactly `schedule i`. -/
theorem schedule_get_mem_replay {Q : Type*} (N : ℕ)
    (schedule : Fin N → Q) (fallback : Q) (bits : List.Vector Bool N)
    (i : Fin N) :
    (schedule i, bits.get i) ∈
      replay (reverseScheduleStrategy N schedule fallback) bits.toList := by
  have hlist : bits.toList = List.ofFn bits.get := by
    calc
      bits.toList = (List.Vector.ofFn bits.get).toList :=
        congrArg List.Vector.toList (List.Vector.ofFn_get bits).symm
      _ = List.ofFn bits.get := List.Vector.toList_ofFn _
  rw [hlist, replay_reverseSchedule_ofFn]
  exact (List.mem_ofFn' _ _).2 ⟨i, rfl⟩

/-! ## The disjoint `K₆` schedule -/

/-- The fifteen non-diagonal unordered pairs of six vertices. -/
abbrev K6Edge := {e : Sym2 (Fin 6) // ¬ e.IsDiag}

theorem card_k6Edge : Fintype.card K6Edge = 15 := by
  rw [Sym2.card_subtype_not_diag]
  norm_num [Nat.choose]

/-- A fixed enumeration of the source edges. -/
def edgeEquiv : Fin 15 ≃ K6Edge :=
  Fintype.equivOfCardEq card_k6Edge.symm

/-- Image of source edge `e` under a vertex embedding. -/
def embeddedEdge {N : ℕ} (f : Fin 6 ↪ Vertex N) (e : Fin 15) : Query N :=
  f.sym2Map (edgeEquiv e).1

theorem embeddedEdge_injective {N : ℕ} (f : Fin 6 ↪ Vertex N) :
    Function.Injective (embeddedEdge f) := by
  intro i j hij
  apply edgeEquiv.injective
  apply Subtype.ext
  exact f.sym2Map.injective hij

theorem embeddedEdge_not_diag {N : ℕ} (f : Fin 6 ↪ Vertex N) (e : Fin 15) :
    ¬(embeddedEdge f e).IsDiag := by
  rw [embeddedEdge, Function.Embedding.sym2Map_apply,
    Sym2.isDiag_map f.injective]
  exact (edgeEquiv e).2

/-- Query budget for `T` disjoint fixed copies. -/
def baselineBudget (T : ℕ) : ℕ := T * 15

theorem six_mul_le_twice_budget (T : ℕ) : T * 6 ≤ 2 * baselineBudget T := by
  simp [baselineBudget]
  omega

/-- Vertex `v` in trial block `r`, embedded into the canonical board. -/
def blockVertex (T : ℕ) (r : Fin T) (v : Fin 6) : Vertex (baselineBudget T) :=
  Fin.castLE (six_mul_le_twice_budget T) (finProdFinEquiv (r, v))

theorem blockVertex_pair_injective (T : ℕ) :
    Function.Injective (fun rv : Fin T × Fin 6 ↦ blockVertex T rv.1 rv.2) := by
  exact (Fin.castLE_injective (six_mul_le_twice_budget T)).comp
    finProdFinEquiv.injective

/-- Vertex embedding of one block. -/
def blockEmbedding (T : ℕ) (r : Fin T) : Fin 6 ↪ Vertex (baselineBudget T) where
  toFun := blockVertex T r
  inj' := by
    intro u v huv
    have hpairs := blockVertex_pair_injective T
      (a₁ := (r, u)) (a₂ := (r, v)) huv
    exact congrArg Prod.snd hpairs

/-- Scheduled edge `e` of trial block `r`. -/
def blockQuery (T : ℕ) (r : Fin T) (e : Fin 15) : Query (baselineBudget T) :=
  embeddedEdge (blockEmbedding T r) e

/-- The same source edge with its trial label attached to both endpoints. -/
def taggedEdge (T : ℕ) (r : Fin T) (e : Fin 15) : Sym2 (Fin T × Fin 6) :=
  Sym2.map (fun v ↦ (r, v)) (edgeEquiv e).1

private theorem sym2_map_const {A B : Type*} (z : Sym2 A) (b : B) :
    Sym2.map (fun _ ↦ b) z = s(b, b) := by
  induction z using Sym2.inductionOn with
  | _ x y => rfl

theorem blockQuery_eq_map_taggedEdge (T : ℕ) (r : Fin T) (e : Fin 15) :
    blockQuery T r e =
      Sym2.map (fun rv : Fin T × Fin 6 ↦ blockVertex T rv.1 rv.2)
        (taggedEdge T r e) := by
  simp [blockQuery, embeddedEdge, taggedEdge, Sym2.map_map, blockEmbedding]

theorem taggedEdge_pair_injective (T : ℕ) :
    Function.Injective (fun re : Fin T × Fin 15 ↦ taggedEdge T re.1 re.2) := by
  intro re re' htag
  have hr := congrArg (Sym2.map Prod.fst) htag
  have he := congrArg (Sym2.map Prod.snd) htag
  have hr' : re.1 = re'.1 := by
    simpa [taggedEdge, Sym2.map_map, Function.comp_def, sym2_map_const,
      Sym2.eq_iff] using hr
  have he' : re.2 = re'.2 := by
    apply edgeEquiv.injective
    apply Subtype.ext
    simpa [taggedEdge, Sym2.map_map, Function.comp_def] using he
  exact Prod.ext hr' he'

theorem blockQuery_pair_injective (T : ℕ) :
    Function.Injective (fun re : Fin T × Fin 15 ↦ blockQuery T re.1 re.2) := by
  intro re re' hquery
  apply taggedEdge_pair_injective T
  apply Sym2.map.injective (blockVertex_pair_injective T)
  simpa [blockQuery_eq_map_taggedEdge] using hquery

/-- The schedule indexed by `Fin (T * 15)`. -/
def blockSchedule (T : ℕ) : Fin (baselineBudget T) → Query (baselineBudget T) :=
  fun i ↦
    let re := finProdFinEquiv.symm i
    blockQuery T re.1 re.2

theorem blockSchedule_injective (T : ℕ) : Function.Injective (blockSchedule T) := by
  exact (blockQuery_pair_injective T).comp finProdFinEquiv.symm.injective

theorem blockSchedule_not_diag (T : ℕ) (i : Fin (baselineBudget T)) :
    ¬(blockSchedule T i).IsDiag := by
  let re := finProdFinEquiv.symm i
  exact embeddedEdge_not_diag (blockEmbedding T re.1) re.2

theorem blockSchedule_apply_pair (T : ℕ) (r : Fin T) (e : Fin 15) :
    blockSchedule T (finProdFinEquiv (r, e)) = blockQuery T r e := by
  simp [blockSchedule]

/-- A fallback query, needed only to make the strategy total outside the
reachable pre-budget histories. -/
def fallbackQuery (T : ℕ) (hT : 0 < T) : Query (baselineBudget T) :=
  s(blockVertex T ⟨0, hT⟩ 0, blockVertex T ⟨0, hT⟩ 1)

/-- The static `T`-block strategy. -/
def strategy (T : ℕ) (hT : 0 < T) : K6Strategy (baselineBudget T) :=
  reverseScheduleStrategy (baselineBudget T) (blockSchedule T) (fallbackQuery T hT)

theorem strategy_fresh (T : ℕ) (hT : 0 < T) :
    FreshForBudget (strategy T hT) := by
  exact reverseScheduleStrategy_fresh (baselineBudget T) (blockSchedule T)
    (fallbackQuery T hT) (blockSchedule_injective T)

theorem strategy_nonloop (T : ℕ) (hT : 0 < T) :
    NonloopForBudget (strategy T hT) := by
  intro h hlen
  rw [strategy, reverseScheduleStrategy_of_length_lt _ _ _ h hlen]
  exact blockSchedule_not_diag T _

theorem strategy_admissible (T : ℕ) (hT : 0 < T) :
    Admissible (strategy T hT) :=
  ⟨strategy_fresh T hT, strategy_nonloop T hT⟩

/-! ## A completed block is a `K₆` -/

/-- All fifteen answer coordinates of one trial block are positive. -/
def BlockCompleted {T : ℕ} (bits : List.Vector Bool (baselineBudget T))
    (r : Fin T) : Prop :=
  ∀ e : Fin 15, bits.get (finProdFinEquiv (r, e)) = true

theorem answerVectorSucceeds_of_blockCompleted (T : ℕ) (hT : 0 < T)
    (bits : List.Vector Bool (baselineBudget T)) (r : Fin T)
    (hcomplete : BlockCompleted bits r) :
    answerVectorSucceeds (strategy T hT) bits := by
  let h := replay (strategy T hT) bits.toList
  let emb := blockEmbedding T r
  let hom : K6 →g positiveGraph h :=
    { toFun := emb
      map_rel' := by
        intro u v huv
        have huvne : u ≠ v := by
          simpa [K6, SimpleGraph.completeGraph_eq_top] using huv
        let source : K6Edge := ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff]⟩
        let e : Fin 15 := edgeEquiv.symm source
        have hedge : blockQuery T r e = s(emb u, emb v) := by
          simp [blockQuery, embeddedEdge, emb, e, source, blockEmbedding]
        have hmem := schedule_get_mem_replay (baselineBudget T)
          (blockSchedule T) (fallbackQuery T hT) bits
          (finProdFinEquiv (r, e))
        rw [blockSchedule_apply_pair] at hmem
        rw [hcomplete e] at hmem
        exact ⟨emb.injective.ne huvne, by simpa [strategy, h, hedge] using hmem⟩ }
  exact ⟨⟨hom, emb.injective⟩⟩

/-! ## Exact independent-block probability -/

/-- The fifteen Boolean edge answers in one fixed block. -/
abbrev TrialOutcome := Fin 15 → Bool

/-- Product Bernoulli point mass of one block outcome. -/
def trialOutcomeWeight (p : ℝ≥0∞) (outcome : TrialOutcome) : ℝ≥0∞ :=
  ∏ e, bernoulliWeight p (outcome e)

/-- A block outcome is successful when all fifteen edges are positive. -/
def trialOutcomeSucceeds (outcome : TrialOutcome) : Prop :=
  ∀ e, outcome e = true

theorem sum_trialOutcomeWeight (p : ℝ≥0∞) (hp : p ≤ 1) :
    (∑ outcome : TrialOutcome, trialOutcomeWeight p outcome) = 1 := by
  calc
    (∑ outcome : TrialOutcome, trialOutcomeWeight p outcome) =
        ∏ _e : Fin 15, ∑ bit : Bool, bernoulliWeight p bit := by
      simpa [trialOutcomeWeight] using
        (Fintype.prod_sum
          (fun _e : Fin 15 ↦ fun bit : Bool ↦ bernoulliWeight p bit)).symm
    _ = 1 := by
      rw [show (∑ bit : Bool, bernoulliWeight p bit) = 1 from
        sum_bernoulliWeight p hp]
      simp

/-- One fixed block succeeds with exact probability `p¹⁵`. -/
theorem oneTrialSuccessMass_eq_pow (p : ℝ≥0∞) :
    Amplification.oneTrialSuccessMass (trialOutcomeWeight p)
      trialOutcomeSucceeds = p ^ 15 := by
  classical
  unfold Amplification.oneTrialSuccessMass
  rw [Fintype.sum_eq_single (fun _e : Fin 15 ↦ true)]
  · simp [trialOutcomeSucceeds, trialOutcomeWeight, bernoulliWeight]
  · intro outcome houtcome
    have hfail : ¬trialOutcomeSucceeds outcome := by
      intro hsuccess
      apply houtcome
      funext e
      exact hsuccess e
    simp [hfail]

/-- Reindex a length-`15T` Boolean vector as `T` block outcomes. -/
def answerOutcomeEquiv (T : ℕ) :
    List.Vector Bool (baselineBudget T) ≃ (Fin T → TrialOutcome) :=
  (Equiv.vectorEquivFin Bool (baselineBudget T)).trans
    { toFun := fun bits r e ↦ bits (finProdFinEquiv (r, e))
      invFun := fun outcomes i ↦
        let re := finProdFinEquiv.symm i
        outcomes re.1 re.2
      left_inv := by
        intro bits
        funext i
        change bits (finProdFinEquiv (finProdFinEquiv.symm i)) = bits i
        rw [Equiv.apply_symm_apply]
      right_inv := by
        intro outcomes
        funext r e
        simp }

@[simp] theorem answerOutcomeEquiv_apply (T : ℕ)
    (bits : List.Vector Bool (baselineBudget T)) (r : Fin T) (e : Fin 15) :
    answerOutcomeEquiv T bits r e = bits.get (finProdFinEquiv (r, e)) := rfl

/-- A complete answer vector contains a successful scheduled block. -/
def SomeBlockCompleted {T : ℕ}
    (bits : List.Vector Bool (baselineBudget T)) : Prop :=
  ∃ r : Fin T, BlockCompleted bits r

theorem someBlockCompleted_iff_outcomeSuccess {T : ℕ}
    (bits : List.Vector Bool (baselineBudget T)) :
    SomeBlockCompleted bits ↔
      ∃ r : Fin T, trialOutcomeSucceeds (answerOutcomeEquiv T bits r) := by
  rfl

/-- Regrouping coordinates into blocks preserves point mass. -/
theorem vectorWeight_eq_outcomeVectorWeight (p : ℝ≥0∞) (T : ℕ)
    (bits : List.Vector Bool (baselineBudget T)) :
    (bits.toList.map (bernoulliWeight p)).prod =
      Amplification.outcomeVectorWeight (trialOutcomeWeight p)
        (answerOutcomeEquiv T bits) := by
  have hlist : bits.toList = List.ofFn bits.get := by
    calc
      bits.toList = (List.Vector.ofFn bits.get).toList :=
        congrArg List.Vector.toList (List.Vector.ofFn_get bits).symm
      _ = List.ofFn bits.get := List.Vector.toList_ofFn _
  rw [hlist, List.map_ofFn, List.prod_ofFn]
  unfold Amplification.outcomeVectorWeight trialOutcomeWeight
  calc
    (∏ i : Fin (baselineBudget T), bernoulliWeight p (bits.get i)) =
        ∏ re : Fin T × Fin 15,
          bernoulliWeight p (bits.get (finProdFinEquiv re)) := by
      exact Fintype.prod_equiv finProdFinEquiv.symm _ _ (fun i ↦ by
        rw [Equiv.apply_symm_apply])
    _ = ∏ r : Fin T, ∏ e : Fin 15,
          bernoulliWeight p (bits.get (finProdFinEquiv (r, e))) := by
      rw [Fintype.prod_prod_type]
    _ = ∏ r : Fin T, ∏ e : Fin 15,
          bernoulliWeight p (answerOutcomeEquiv T bits r e) := by
      simp

/-- Product-space mass that at least one block succeeds. -/
def repeatedSuccessMass (p : ℝ≥0∞) (T : ℕ) : ℝ≥0∞ :=
  Amplification.finiteOutcomeProductMass (trialOutcomeWeight p) T
    {outcomes | ∃ r, trialOutcomeSucceeds (outcomes r)}

/-- Product-space mass that all blocks fail. -/
def repeatedFailureMass (p : ℝ≥0∞) (T : ℕ) : ℝ≥0∞ :=
  Amplification.finiteOutcomeProductMass (trialOutcomeWeight p) T
    (Amplification.allTrialsFailEvent trialOutcomeSucceeds T)

theorem repeatedFailureMass_eq (p : ℝ≥0∞) (hp : p ≤ 1) (T : ℕ) :
    repeatedFailureMass p T = (1 - p ^ 15) ^ T := by
  unfold repeatedFailureMass
  rw [Amplification.finiteOutcomeProductMass_allTrialsFail_eq_one_sub_pow
    (trialOutcomeWeight p) trialOutcomeSucceeds T (sum_trialOutcomeWeight p hp)]
  rw [oneTrialSuccessMass_eq_pow]

theorem sum_outcomeVectorWeight (p : ℝ≥0∞) (hp : p ≤ 1) (T : ℕ) :
    (∑ outcomes : Fin T → TrialOutcome,
      Amplification.outcomeVectorWeight (trialOutcomeWeight p) outcomes) = 1 := by
  unfold Amplification.outcomeVectorWeight
  calc
    (∑ outcomes : Fin T → TrialOutcome,
        ∏ r, trialOutcomeWeight p (outcomes r)) =
        ∏ _r : Fin T, ∑ outcome, trialOutcomeWeight p outcome := by
      simpa using
        (Fintype.prod_sum
          (fun _r : Fin T ↦ fun outcome : TrialOutcome ↦
            trialOutcomeWeight p outcome)).symm
    _ = 1 := by simp [sum_trialOutcomeWeight p hp]

/-- Success and failure partition the repeated product space. -/
theorem repeatedSuccessMass_add_failureMass
    (p : ℝ≥0∞) (hp : p ≤ 1) (T : ℕ) :
    repeatedSuccessMass p T + repeatedFailureMass p T = 1 := by
  classical
  unfold repeatedSuccessMass repeatedFailureMass
    Amplification.finiteOutcomeProductMass Amplification.allTrialsFailEvent
  rw [← Finset.sum_add_distrib]
  simp only [Set.mem_setOf_eq]
  calc
    _ = ∑ outcomes : Fin T → TrialOutcome,
          Amplification.outcomeVectorWeight (trialOutcomeWeight p) outcomes := by
      apply Finset.sum_congr rfl
      intro outcomes _
      by_cases hsuccess : ∃ r, trialOutcomeSucceeds (outcomes r)
      · have hnotfail : ¬∀ r, ¬trialOutcomeSucceeds (outcomes r) := by
          intro hfail
          obtain ⟨r, hr⟩ := hsuccess
          exact hfail r hr
        simp [hsuccess, hnotfail]
      · have hfail : ∀ r, ¬trialOutcomeSucceeds (outcomes r) := by
          simpa only [not_exists] using hsuccess
        simp [hfail]
    _ = 1 := sum_outcomeVectorWeight p hp T

/-- The success mass is one minus the exact repeated failure mass. -/
theorem repeatedSuccessMass_eq_one_sub
    (p : ℝ≥0∞) (hp : p ≤ 1) (T : ℕ) :
    repeatedSuccessMass p T = 1 - repeatedFailureMass p T := by
  apply ENNReal.eq_sub_of_add_eq
  · have hle : repeatedFailureMass p T ≤ 1 := by
      rw [← repeatedSuccessMass_add_failureMass p hp T]
      exact le_add_of_nonneg_left bot_le
    exact (lt_top_iff_ne_top.mp (hle.trans_lt ENNReal.one_lt_top))
  · simpa [add_comm] using repeatedSuccessMass_add_failureMass p hp T

/-- The answer-vector mass of completed scheduled blocks is exactly the
independent product-space success mass. -/
theorem someBlockAnswerMass_eq_repeatedSuccessMass
    (p : ℝ≥0∞) (T : ℕ) :
    (∑ bits : List.Vector Bool (baselineBudget T),
      if SomeBlockCompleted bits then
        (bits.toList.map (bernoulliWeight p)).prod else 0) =
      repeatedSuccessMass p T := by
  classical
  unfold repeatedSuccessMass Amplification.finiteOutcomeProductMass
  apply Fintype.sum_equiv (answerOutcomeEquiv T)
  intro bits
  rw [vectorWeight_eq_outcomeVectorWeight]
  rfl

/-- The actual query-game success probability dominates the exact probability
that one scheduled block is wholly positive. -/
theorem repeatedSuccessMass_le_successProbability
    (p : ℝ≥0∞) (hp : p ≤ 1) (T : ℕ) (hT : 0 < T) :
    repeatedSuccessMass p T ≤
      successProbability p (baselineBudget T) (strategy T hT) := by
  rw [successProbability_eq_answer_sum p hp (baselineBudget T) (strategy T hT)
    (strategy_fresh T hT)]
  rw [← someBlockAnswerMass_eq_repeatedSuccessMass p T]
  apply Finset.sum_le_sum
  intro bits _
  by_cases hcompleted : SomeBlockCompleted bits
  · obtain ⟨r, hr⟩ := hcompleted
    have hsuccess := answerVectorSucceeds_of_blockCompleted T hT bits r hr
    have hcompleted' : SomeBlockCompleted bits := ⟨r, hr⟩
    simp [hcompleted', hsuccess]
  · simp [hcompleted]

/-! ## Reaching the one-half threshold -/

theorem repeatedFailureMass_toReal
    (p : ℝ≥0∞) (hp : p ≤ 1) (T : ℕ) :
    (repeatedFailureMass p T).toReal = (1 - p.toReal ^ 15) ^ T := by
  rw [repeatedFailureMass_eq p hp T, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le]
  · rw [ENNReal.toReal_one, ENNReal.toReal_pow]
  · exact pow_le_one₀ bot_le hp
  · simp

/-- At every positive density, finitely many disjoint blocks make the exact
failure mass at most one half. -/
theorem exists_trialCount_failure_le_threshold
    (p : ℝ≥0∞) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ T : ℕ, 0 < T ∧ repeatedFailureMass p T ≤ threshold := by
  have hptop : p ≠ ∞ := (hp1.trans_lt ENNReal.one_lt_top).ne
  have hpR0 : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hptop
  have hpR1 : p.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp) hp1
  have hs0 : 0 < p.toReal ^ 15 := pow_pos hpR0 _
  have hs1 : p.toReal ^ 15 ≤ 1 := pow_le_one₀ hpR0.le hpR1
  have hbase0 : 0 ≤ 1 - p.toReal ^ 15 := sub_nonneg.mpr hs1
  have hbase1 : 1 - p.toReal ^ 15 < 1 := by linarith
  obtain ⟨T, hTfail⟩ := exists_pow_lt_of_lt_one
    (by norm_num : (0 : ℝ) < 1 / 2) hbase1
  have hT : 0 < T := by
    by_contra hnot
    have hzero : T = 0 := Nat.eq_zero_of_not_pos hnot
    subst T
    norm_num at hTfail
  refine ⟨T, hT, ?_⟩
  have hfailureTop : repeatedFailureMass p T ≠ ∞ := by
    rw [repeatedFailureMass_eq p hp1 T]
    finiteness
  apply (ENNReal.toReal_le_toReal hfailureTop (by simp [threshold])).mp
  rw [repeatedFailureMass_toReal p hp1 T]
  simpa [threshold] using hTfail.le

/-- A failure bound on the scheduled blocks implies query-game
achievability, using the actual static strategy. -/
theorem achievable_of_repeatedFailureMass_le
    (p : ℝ≥0∞) (hp : p ≤ 1) (T : ℕ) (hT : 0 < T)
    (hfailure : repeatedFailureMass p T ≤ threshold) :
    Achievable p (baselineBudget T) := by
  have hsuccess : threshold ≤ repeatedSuccessMass p T := by
    rw [repeatedSuccessMass_eq_one_sub p hp T]
    have hsub := tsub_le_tsub_left hfailure 1
    simpa [threshold, ENNReal.one_sub_inv_two] using hsub
  exact ⟨hp, strategy T hT, strategy_admissible T hT,
    hsuccess.trans (repeatedSuccessMass_le_successProbability p hp T hT)⟩

/-- Unconditional existence of a sufficient finite query budget at every
positive density. -/
theorem exists_achievable (p : ℝ≥0∞) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ N, Achievable p N := by
  obtain ⟨T, hT, hfailure⟩ :=
    exists_trialCount_failure_le_threshold p hp0 hp1
  exact ⟨baselineBudget T,
    achievable_of_repeatedFailureMass_le p hp1 T hT hfailure⟩

/-- Increasing the Bernoulli parameter can only decrease the explicit
failure formula for the static disjoint-block strategy.  No monotonicity
claim for arbitrary adaptive policies is used here. -/
theorem repeatedFailureMass_antitone_density
    {p₀ p : ℝ≥0∞} (hp₀p : p₀ ≤ p) (hp : p ≤ 1) (T : ℕ) :
    repeatedFailureMass p T ≤ repeatedFailureMass p₀ T := by
  have hp₀1 : p₀ ≤ 1 := hp₀p.trans hp
  rw [repeatedFailureMass_eq p hp T, repeatedFailureMass_eq p₀ hp₀1 T]
  exact pow_le_pow_left' (tsub_le_tsub_left (pow_le_pow_left' hp₀p 15) 1) T

/-- One common static budget works uniformly throughout every interval
`[p₀,1]` with `p₀>0`. -/
theorem exists_uniform_achievable_above
    (p₀ : ℝ≥0∞) (hp₀0 : 0 < p₀) (hp₀1 : p₀ ≤ 1) :
    ∃ N : ℕ, ∀ p : ℝ≥0∞, p₀ ≤ p → p ≤ 1 → Achievable p N := by
  obtain ⟨T, hT, hfailure⟩ :=
    exists_trialCount_failure_le_threshold p₀ hp₀0 hp₀1
  refine ⟨baselineBudget T, ?_⟩
  intro p hp₀p hp1
  apply achievable_of_repeatedFailureMass_le p hp1 T hT
  exact (repeatedFailureMass_antitone_density hp₀p hp1 T).trans hfailure

/-! ## Bounded-density glue in the cubic parameter -/

/-- For every fixed `q₀>0`, one budget works throughout `q₀ ≤ q ≤ 1`,
and its normalized cost is bounded by the same natural number. -/
theorem exists_uniform_cubic_achievable_above
    (q₀ : ℝ≥0∞) (hq₀0 : 0 < q₀) (hq₀1 : q₀ ≤ 1) :
    ∃ N : ℕ, ∀ q : ℝ≥0∞, q₀ ≤ q → q ≤ 1 →
      Achievable (q ^ 3) N ∧ (N : ℝ≥0∞) * q ^ 10 ≤ (N : ℝ≥0∞) := by
  have hp₀0 : 0 < q₀ ^ 3 := by positivity
  have hp₀1 : q₀ ^ 3 ≤ 1 := pow_le_one₀ bot_le hq₀1
  obtain ⟨N, hN⟩ := exists_uniform_achievable_above (q₀ ^ 3) hp₀0 hp₀1
  refine ⟨N, ?_⟩
  intro q hq₀q hq1
  have hpLower : q₀ ^ 3 ≤ q ^ 3 := pow_le_pow_left' hq₀q 3
  have hpUpper : q ^ 3 ≤ 1 := pow_le_one₀ bot_le hq1
  refine ⟨hN (q ^ 3) hpLower hpUpper, ?_⟩
  calc
    (N : ℝ≥0∞) * q ^ 10 ≤ (N : ℝ≥0∞) * 1 :=
      mul_le_mul_left' (pow_le_one₀ bot_le hq1) _
    _ = (N : ℝ≥0∞) := mul_one _

/-- The bounded-density upper hypothesis in the exact shape used by
`FiniteCubicPowerLaw`. -/
theorem exists_boundedDensity_upperConstant
    (q₀ : ℝ≥0∞) (hq₀0 : 0 < q₀) (hq₀1 : q₀ ≤ 1) :
    ∃ C₀ : ℝ≥0∞, ∀ q : ℝ≥0∞, q₀ ≤ q → q ≤ 1 →
      ∃ N, Achievable (q ^ 3) N ∧ (N : ℝ≥0∞) * q ^ 10 ≤ C₀ := by
  obtain ⟨N, hN⟩ := exists_uniform_cubic_achievable_above q₀ hq₀0 hq₀1
  refine ⟨(N : ℝ≥0∞), ?_⟩
  intro q hq₀q hq1
  exact ⟨N, hN q hq₀q hq1⟩

/-- Glue a uniform small-density construction to the unconditional static
baseline on the compact interval `q₀ ≤ q ≤ 1`.  The output is the full
upper hypothesis, with no separate bounded-density assumption left over. -/
theorem extend_smallDensity_upperHypothesis
    (q₀ C : ℝ≥0∞) (hq₀0 : 0 < q₀) (hq₀1 : q₀ ≤ 1)
    (hsmall : ∀ q : ℝ≥0∞, 0 < q → q < q₀ →
      ∃ N, Achievable (q ^ 3) N ∧ (N : ℝ≥0∞) * q ^ 10 ≤ C) :
    ∃ C' : ℝ≥0∞, ∀ q : ℝ≥0∞, 0 < q → q ≤ 1 →
      ∃ N, Achievable (q ^ 3) N ∧ (N : ℝ≥0∞) * q ^ 10 ≤ C' := by
  obtain ⟨N₀, hN₀⟩ := exists_uniform_cubic_achievable_above q₀ hq₀0 hq₀1
  refine ⟨max C (N₀ : ℝ≥0∞), ?_⟩
  intro q hq hq1
  by_cases hsmallq : q < q₀
  · obtain ⟨N, hach, hnorm⟩ := hsmall q hq hsmallq
    exact ⟨N, hach, hnorm.trans (le_max_left _ _)⟩
  · have hq₀q : q₀ ≤ q := le_of_not_gt hsmallq
    obtain ⟨hach, hnorm⟩ := hN₀ q hq₀q hq1
    exact ⟨N₀, hach, hnorm.trans (le_max_right _ _)⟩

end
end BaselineStrategy
end OnlineRamsey
