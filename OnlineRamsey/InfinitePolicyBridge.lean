import OnlineRamsey.QueryComplexity
import Mathlib.Data.List.GetD

/-!
# The countably infinite query game and coherent first-appearance relabeling

The original subgraph-query game is normally played on a countably infinite
set of vertices.  A strategy makes only `N` queries, however, and hence every
answer path touches at most `2 * N` vertices.  This file formalizes the
policy-level reduction to the canonical board `Fin (2 * N)` used in
`QueryComplexity.lean`.

The key point is coherence.  We do not choose a new embedding separately at
each leaf.  Along every answer path, a vertex receives the index of its first
appearance, and the index is unchanged at every descendant of that node.  A
single canonical strategy can therefore simulate the complete infinite
policy tree.  Its replay transcript is exactly the pointwise relabeling of the
infinite replay transcript, so answer vectors, freshness, and graph success
are preserved pathwise.

No infinite product measure is required.  The probability of a finite-horizon
infinite-board policy is defined by the same finite Bernoulli answer-vector
sum that `QueryComplexity.successProbability_eq_answer_sum` derives from its
finite product board.
-/

namespace OnlineRamsey

open scoped ENNReal

namespace InfinitePolicyBridge

open QueryComplexity

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## The standard countably infinite finite-horizon game -/

/-- The standard vertex set. -/
abbrev InfiniteVertex := ℕ

/-- Unordered query coordinates on the countably infinite vertex set. -/
abbrev InfiniteQuery := Sym2 InfiniteVertex

/-- Infinite-board deterministic policies. -/
abbrev InfiniteStrategy := Strategy InfiniteQuery

/-- The positive graph of an infinite-board transcript. -/
def infinitePositiveGraph (h : Transcript InfiniteQuery) :
    SimpleGraph InfiniteVertex where
  Adj u v := u ≠ v ∧ (s(u, v), true) ∈ h
  symm := by
    intro u v huv
    exact ⟨huv.1.symm, by simpa only [Sym2.eq_swap] using huv.2⟩
  loopless := by
    intro u huv
    exact huv.1 rfl

@[simp] theorem infinitePositiveGraph_adj (h : Transcript InfiniteQuery)
    (u v : InfiniteVertex) :
    (infinitePositiveGraph h).Adj u v ↔
      u ≠ v ∧ (s(u, v), true) ∈ h := Iff.rfl

/-- Success in the countably infinite game means finding a labelled `K₆`. -/
def InfiniteTranscriptSucceeds (h : Transcript InfiniteQuery) : Prop :=
  Nonempty (SimpleGraph.Copy K6 (infinitePositiveGraph h))

/-- Every length-`N` answer path uses distinct unordered coordinates. -/
def InfiniteFreshForBudget (N : ℕ) (strategy : InfiniteStrategy) : Prop :=
  ∀ bits : List.Vector Bool N, FreshPath strategy bits.toList

/-- Every query made before the horizon is a nonloop coordinate. -/
def InfiniteNonloopForBudget (N : ℕ) (strategy : InfiniteStrategy) : Prop :=
  ∀ h : Transcript InfiniteQuery, h.length < N → ¬(strategy h).IsDiag

/-- Pathwise legality in the countably infinite game. -/
def InfiniteAdmissible (N : ℕ) (strategy : InfiniteStrategy) : Prop :=
  InfiniteFreshForBudget N strategy ∧ InfiniteNonloopForBudget N strategy

/-- Success on a prescribed finite answer vector. -/
def infiniteAnswerVectorSucceeds {N : ℕ} (strategy : InfiniteStrategy)
    (bits : List.Vector Bool N) : Prop :=
  InfiniteTranscriptSucceeds (replay strategy bits.toList)

/-- The exact Bernoulli(`p`) law of an `N`-step infinite-board policy,
expressed as a finite sum over its possible answer vectors. -/
def infiniteSuccessProbability (p : ℝ≥0∞) (N : ℕ)
    (strategy : InfiniteStrategy) : ℝ≥0∞ :=
  ∑ bits : List.Vector Bool N,
    if infiniteAnswerVectorSucceeds strategy bits then
      (bits.toList.map (bernoulliWeight p)).prod else 0

/-- The standard positive-horizon deterministic countably infinite
formulation at fixed horizon `N`. -/
def InfiniteAchievable (p : ℝ≥0∞) (N : ℕ) : Prop :=
  0 < N ∧ p ≤ 1 ∧ ∃ strategy : InfiniteStrategy,
    InfiniteAdmissible N strategy ∧
      threshold ≤ infiniteSuccessProbability p N strategy

/-! ## First-appearance names -/

/-- Endpoints in chronological order.  Transcripts themselves are newest
first, so a new query appends its two endpoints to this list. -/
def chronologicalEndpoints : Transcript InfiniteQuery → List InfiniteVertex
  | [] => []
  | (q, _) :: h => chronologicalEndpoints h ++ [q.out.1, q.out.2]

@[simp] theorem chronologicalEndpoints_nil :
    chronologicalEndpoints [] = [] := rfl

@[simp] theorem chronologicalEndpoints_cons (q : InfiniteQuery) (answer : Bool)
    (h : Transcript InfiniteQuery) :
    chronologicalEndpoints ((q, answer) :: h) =
      chronologicalEndpoints h ++ [q.out.1, q.out.2] := rfl

@[simp] theorem length_chronologicalEndpoints
    (h : Transcript InfiniteQuery) :
    (chronologicalEndpoints h).length = 2 * h.length := by
  induction h with
  | nil => simp
  | cons entry h ih =>
      rcases entry with ⟨q, answer⟩
      simp [chronologicalEndpoints, ih, Nat.mul_succ]

theorem out_fst_mem_chronologicalEndpoints
    {h : Transcript InfiniteQuery} {q : InfiniteQuery} {answer : Bool}
    (hq : (q, answer) ∈ h) : q.out.1 ∈ chronologicalEndpoints h := by
  induction h with
  | nil => simp at hq
  | cons entry h ih =>
      rcases entry with ⟨q', answer'⟩
      simp only [List.mem_cons] at hq
      rcases hq with hhead | htail
      · cases hhead
        simp
      · simp [chronologicalEndpoints, ih htail]

theorem out_snd_mem_chronologicalEndpoints
    {h : Transcript InfiniteQuery} {q : InfiniteQuery} {answer : Bool}
    (hq : (q, answer) ∈ h) : q.out.2 ∈ chronologicalEndpoints h := by
  induction h with
  | nil => simp at hq
  | cons entry h ih =>
      rcases entry with ⟨q', answer'⟩
      simp only [List.mem_cons] at hq
      rcases hq with hhead | htail
      · cases hhead
        simp
      · simp [chronologicalEndpoints, ih htail]

/-- A vertex receives the position of its first chronological occurrence.
The irrelevant value on untouched vertices makes this a total function. -/
def firstName (N : ℕ) (hN : 0 < N) (h : Transcript InfiniteQuery)
    (hlen : h.length ≤ N) (x : InfiniteVertex) : Fin (2 * N) :=
  if hx : x ∈ chronologicalEndpoints h then
    ⟨(chronologicalEndpoints h).idxOf x, by
      have hidx : (chronologicalEndpoints h).idxOf x <
          (chronologicalEndpoints h).length :=
        List.idxOf_lt_length_iff.mpr hx
      rw [length_chronologicalEndpoints] at hidx
      omega⟩
  else
    ⟨0, by omega⟩

@[simp] theorem firstName_of_mem (N : ℕ) (hN : 0 < N)
    (h : Transcript InfiniteQuery) (hlen : h.length ≤ N)
    (x : InfiniteVertex) (hx : x ∈ chronologicalEndpoints h) :
    (firstName N hN h hlen x : ℕ) =
      (chronologicalEndpoints h).idxOf x := by
  simp [firstName, hx]

/-- First-appearance naming is injective on the vertices actually touched by
the path. -/
theorem firstName_injective_on (N : ℕ) (hN : 0 < N)
    (h : Transcript InfiniteQuery) (hlen : h.length ≤ N)
    {x y : InfiniteVertex}
    (hx : x ∈ chronologicalEndpoints h)
    (hy : y ∈ chronologicalEndpoints h)
    (heq : firstName N hN h hlen x = firstName N hN h hlen y) :
    x = y := by
  have hidxX : (chronologicalEndpoints h).idxOf x <
      (chronologicalEndpoints h).length :=
    List.idxOf_lt_length_iff.mpr hx
  have hidxY : (chronologicalEndpoints h).idxOf y <
      (chronologicalEndpoints h).length :=
    List.idxOf_lt_length_iff.mpr hy
  have hidx : (chronologicalEndpoints h).idxOf x =
      (chronologicalEndpoints h).idxOf y := by
    have := congrArg Fin.val heq
    simpa [firstName, hx, hy] using this
  have hxget := List.idxOf_get hidxX
  have hyget := List.idxOf_get hidxY
  let ix : Fin (chronologicalEndpoints h).length :=
    ⟨(chronologicalEndpoints h).idxOf x, hidxX⟩
  let iy : Fin (chronologicalEndpoints h).length :=
    ⟨(chronologicalEndpoints h).idxOf y, hidxY⟩
  have hfin : ix = iy := Fin.ext hidx
  calc
    x = (chronologicalEndpoints h).get ix := hxget.symm
    _ = (chronologicalEndpoints h).get iy := congrArg _ hfin
    _ = y := hyget

/-- Once a touched vertex is named, appending a later query does not change
its name. -/
theorem firstName_cons_of_mem (N : ℕ) (hN : 0 < N)
    (q : InfiniteQuery) (answer : Bool) (h : Transcript InfiniteQuery)
    (hlen : h.length ≤ N) (hfull : ((q, answer) :: h).length ≤ N)
    (x : InfiniteVertex) (hx : x ∈ chronologicalEndpoints h) :
    firstName N hN ((q, answer) :: h) hfull x =
      firstName N hN h hlen x := by
  apply Fin.ext
  simp [firstName, hx, List.idxOf_append_of_mem hx]

/-- Every old unordered coordinate is unchanged when a later query extends
the path. -/
theorem map_firstName_cons_of_mem (N : ℕ) (hN : 0 < N)
    (q : InfiniteQuery) (answer : Bool) (h : Transcript InfiniteQuery)
    (hlen : h.length ≤ N) (hfull : ((q, answer) :: h).length ≤ N)
    {q' : InfiniteQuery} {answer' : Bool} (hq' : (q', answer') ∈ h) :
    Sym2.map (firstName N hN ((q, answer) :: h) hfull) q' =
      Sym2.map (firstName N hN h hlen) q' := by
  rw [← q'.out_eq]
  apply Sym2.eq_iff.mpr
  left
  exact ⟨
    firstName_cons_of_mem N hN q answer h hlen hfull q'.out.1
      (out_fst_mem_chronologicalEndpoints hq'),
    firstName_cons_of_mem N hN q answer h hlen hfull q'.out.2
      (out_snd_mem_chronologicalEndpoints hq')⟩

/-- Relabel every coordinate in a completed path using that path's coherent
first-appearance names. -/
def relabelCompletedTranscript (N : ℕ) (hN : 0 < N)
    (h : Transcript InfiniteQuery) (hlen : h.length ≤ N) :
    Transcript (Query N) :=
  h.map fun entry =>
    (Sym2.map (firstName N hN h hlen) entry.1, entry.2)

@[simp] theorem length_relabelCompletedTranscript (N : ℕ) (hN : 0 < N)
    (h : Transcript InfiniteQuery) (hlen : h.length ≤ N) :
    (relabelCompletedTranscript N hN h hlen).length = h.length := by
  simp [relabelCompletedTranscript]

@[simp] theorem answers_relabelCompletedTranscript (N : ℕ) (hN : 0 < N)
    (h : Transcript InfiniteQuery) (hlen : h.length ≤ N) :
    answers (relabelCompletedTranscript N hN h hlen) = answers h := by
  simp [relabelCompletedTranscript, answers, Function.comp_def]

/-- The explicit canonical transcript associated with an answer path.  The
recursive definition makes the online nature of the naming construction
visible: the new coordinate is named using only the preceding path and the
new query. -/
def canonicalPath (N : ℕ) (hN : 0 < N) (strategy : InfiniteStrategy) :
    (bits : List Bool) → bits.length ≤ N → Transcript (Query N)
  | [], _ => []
  | bit :: bits, hlen =>
      let rawTail := replay strategy bits
      let q := strategy rawTail
      let rawFull := (q, bit) :: rawTail
      let htail : bits.length ≤ N := by
        have hlen' : bits.length + 1 ≤ N := by
          simpa only [List.length_cons] using hlen
        omega
      let hfull : rawFull.length ≤ N := by
        simpa [rawFull, rawTail] using hlen
      (Sym2.map (firstName N hN rawFull hfull) q, bit) ::
        canonicalPath N hN strategy bits htail

@[simp] theorem length_canonicalPath (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) (bits : List Bool) (hlen : bits.length ≤ N) :
    (canonicalPath N hN strategy bits hlen).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [canonicalPath, List.length_cons]
      rw [ih]

@[simp] theorem answers_canonicalPath (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) (bits : List Bool) (hlen : bits.length ≤ N) :
    answers (canonicalPath N hN strategy bits hlen) = bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [canonicalPath, answers, List.map_cons]
      change bit :: answers (canonicalPath N hN strategy bits _) = bit :: bits
      rw [ih]

/-- The recursive online construction equals the one-shot relabeling by the
final first-appearance map.  This is the central coherence lemma. -/
theorem canonicalPath_eq_relabelCompletedTranscript
    (N : ℕ) (hN : 0 < N) (strategy : InfiniteStrategy)
    (bits : List Bool) (hlen : bits.length ≤ N) :
    canonicalPath N hN strategy bits hlen =
      relabelCompletedTranscript N hN (replay strategy bits)
        (by simpa using hlen) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      let rawTail := replay strategy bits
      let q := strategy rawTail
      have htail : bits.length ≤ N := by
        have hlen' : bits.length + 1 ≤ N := by
          simpa only [List.length_cons] using hlen
        omega
      have hrawTail : rawTail.length ≤ N := by simpa [rawTail] using htail
      have hfull : ((q, bit) :: rawTail).length ≤ N := by
        simpa [rawTail] using hlen
      simp only [canonicalPath, replay_cons, relabelCompletedTranscript,
        List.map_cons]
      congr 1
      rw [ih htail]
      unfold relabelCompletedTranscript
      apply List.map_congr_left
      intro entry hentry
      rcases entry with ⟨q', answer'⟩
      congr 1
      exact (map_firstName_cons_of_mem N hN q bit rawTail hrawTail hfull
        hentry).symm

/-! ## One coherent canonical policy -/

/-- A harmless off-horizon coordinate.  It is consulted only on histories
of length at least `N`. -/
def fallbackQuery (N : ℕ) (hN : 0 < N) : Query N :=
  s(⟨0, by omega⟩, ⟨1, by omega⟩)

/-- The canonical policy determined by an infinite policy.  At every
reachable pre-horizon transcript it recovers the raw answer path, asks the
raw policy for its next coordinate, and assigns any newly seen endpoints
their first-appearance names. -/
def canonicalPolicy (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) : K6Strategy N :=
  fun h =>
    if hlt : h.length < N then
      let bits := answers h
      let rawTail := replay strategy bits
      let q := strategy rawTail
      let rawFull := (q, false) :: rawTail
      let hfull : rawFull.length ≤ N := by
        simpa [rawFull, rawTail, bits] using hlt
      Sym2.map (firstName N hN rawFull hfull) q
    else fallbackQuery N hN

/-- Replaying the one canonical policy gives exactly the coherent canonical
path, for every answer vector up to the horizon. -/
theorem replay_canonicalPolicy (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) (bits : List Bool)
    (hlen : bits.length ≤ N) :
    replay (canonicalPolicy N hN strategy) bits =
      canonicalPath N hN strategy bits hlen := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      have hlen' : bits.length + 1 ≤ N := by
        simpa only [List.length_cons] using hlen
      have htail : bits.length ≤ N := by omega
      have hlt : bits.length < N := by omega
      rw [replay_cons, ih htail]
      simp only [canonicalPath]
      have hans : answers (canonicalPath N hN strategy bits htail) = bits :=
        answers_canonicalPath N hN strategy bits htail
      simp only [canonicalPolicy, length_canonicalPath, hlt, dite_true, hans]
      congr 2

/-! ## Pathwise legality of the canonical policy -/

theorem exists_answer_of_mem_queries {h : Transcript InfiniteQuery}
    {q : InfiniteQuery} (hq : q ∈ queries h) :
  ∃ answer : Bool, (q, answer) ∈ h := by
  rcases List.mem_map.mp hq with ⟨entry, hentry, heq⟩
  rcases entry with ⟨q', answer⟩
  simp only at heq
  subst q'
  exact ⟨answer, hentry⟩

theorem out_fst_mem_chronologicalEndpoints_of_mem_queries
    {h : Transcript InfiniteQuery} {q : InfiniteQuery}
    (hq : q ∈ queries h) : q.out.1 ∈ chronologicalEndpoints h := by
  rcases exists_answer_of_mem_queries hq with ⟨answer, hentry⟩
  exact out_fst_mem_chronologicalEndpoints hentry

theorem out_snd_mem_chronologicalEndpoints_of_mem_queries
    {h : Transcript InfiniteQuery} {q : InfiniteQuery}
    (hq : q ∈ queries h) : q.out.2 ∈ chronologicalEndpoints h := by
  rcases exists_answer_of_mem_queries hq with ⟨answer, hentry⟩
  exact out_snd_mem_chronologicalEndpoints hentry

/-- On the coordinates occurring in a completed path, the induced map on
unordered pairs is injective. -/
theorem map_firstName_injective_on_queries (N : ℕ) (hN : 0 < N)
    (h : Transcript InfiniteQuery) (hlen : h.length ≤ N)
    {q q' : InfiniteQuery} (hq : q ∈ queries h) (hq' : q' ∈ queries h)
    (heq : Sym2.map (firstName N hN h hlen) q =
      Sym2.map (firstName N hN h hlen) q') : q = q' := by
  have hq1 := out_fst_mem_chronologicalEndpoints_of_mem_queries hq
  have hq2 := out_snd_mem_chronologicalEndpoints_of_mem_queries hq
  have hq1' := out_fst_mem_chronologicalEndpoints_of_mem_queries hq'
  have hq2' := out_snd_mem_chronologicalEndpoints_of_mem_queries hq'
  have heq' :
      s(firstName N hN h hlen q.out.1, firstName N hN h hlen q.out.2) =
        s(firstName N hN h hlen q'.out.1,
          firstName N hN h hlen q'.out.2) := by
    calc
      s(firstName N hN h hlen q.out.1,
          firstName N hN h hlen q.out.2) =
          Sym2.map (firstName N hN h hlen) (Sym2.mk q.out) := by
            rw [Sym2.map_pair_eq]
      _ = Sym2.map (firstName N hN h hlen) q :=
        congrArg _ q.out_eq
      _ = Sym2.map (firstName N hN h hlen) q' := heq
      _ = Sym2.map (firstName N hN h hlen) (Sym2.mk q'.out) :=
        congrArg _ q'.out_eq.symm
      _ = s(firstName N hN h hlen q'.out.1,
          firstName N hN h hlen q'.out.2) := by
            rw [Sym2.map_pair_eq]
  have hout : Sym2.mk q.out = Sym2.mk q'.out := by
    rw [Sym2.eq_iff] at heq' ⊢
    rcases heq' with heq' | heq'
    · left
      exact ⟨
        firstName_injective_on N hN h hlen hq1 hq1' heq'.1,
        firstName_injective_on N hN h hlen hq2 hq2' heq'.2⟩
    · right
      exact ⟨
        firstName_injective_on N hN h hlen hq1 hq2' heq'.1,
        firstName_injective_on N hN h hlen hq2 hq1' heq'.2⟩
  exact q.out_eq.symm.trans (hout.trans q'.out_eq)

theorem queries_canonicalPath (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) (bits : List Bool)
    (hlen : bits.length ≤ N) :
    queries (canonicalPath N hN strategy bits hlen) =
      (queries (replay strategy bits)).map
        (Sym2.map (firstName N hN (replay strategy bits) (by simpa using hlen))) := by
  rw [canonicalPath_eq_relabelCompletedTranscript]
  simp [queries, relabelCompletedTranscript, Function.comp_def]

/-- Mapping a fresh infinite path by first appearances preserves freshness. -/
theorem freshPath_canonicalPolicy (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) (bits : List Bool)
    (hlen : bits.length ≤ N) (hfresh : FreshPath strategy bits) :
    FreshPath (canonicalPolicy N hN strategy) bits := by
  unfold FreshPath at hfresh ⊢
  rw [replay_canonicalPolicy N hN strategy bits hlen,
    queries_canonicalPath]
  apply hfresh.map_on
  intro q hq q' hq' heq
  exact map_firstName_injective_on_queries N hN (replay strategy bits)
    (by simpa using hlen) hq hq' heq

/-- A nonloop raw coordinate remains nonloop under its current
first-appearance names. -/
theorem not_isDiag_map_firstName_head (N : ℕ) (hN : 0 < N)
    (q : InfiniteQuery) (answer : Bool) (h : Transcript InfiniteQuery)
    (hfull : ((q, answer) :: h).length ≤ N) (hq : ¬q.IsDiag) :
    ¬(Sym2.map (firstName N hN ((q, answer) :: h) hfull) q).IsDiag := by
  intro hdiag
  have hqfst : q.out.1 ∈ chronologicalEndpoints ((q, answer) :: h) := by simp
  have hqsnd : q.out.2 ∈ chronologicalEndpoints ((q, answer) :: h) := by simp
  have hnames : firstName N hN ((q, answer) :: h) hfull q.out.1 =
      firstName N hN ((q, answer) :: h) hfull q.out.2 := by
    have hdiag' :
        (Sym2.map (firstName N hN ((q, answer) :: h) hfull)
          (Sym2.mk q.out)).IsDiag := by
      simpa only [q.out_eq] using hdiag
    simpa only [Sym2.map_pair_eq, Sym2.mk_isDiag_iff] using hdiag'
  have hout : q.out.1 = q.out.2 :=
    firstName_injective_on N hN ((q, answer) :: h) hfull
      hqfst hqsnd hnames
  apply hq
  have : (Sym2.mk q.out).IsDiag := by
    rw [Sym2.mk_isDiag_iff]
    exact hout
  simpa only [q.out_eq] using this

/-- The coherent canonical policy is admissible whenever the infinite policy
is admissible. -/
theorem canonicalPolicy_admissible (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) (hadm : InfiniteAdmissible N strategy) :
    Admissible (canonicalPolicy N hN strategy) := by
  constructor
  · intro bits
    apply freshPath_canonicalPolicy N hN strategy bits.toList (by simp)
    exact hadm.1 bits
  · intro h hlen
    have hrawLen : (replay strategy (answers h)).length < N := by
      simpa using hlen
    have hrawNonloop := hadm.2 (replay strategy (answers h)) hrawLen
    simp only [canonicalPolicy, hlen, dite_true]
    exact not_isDiag_map_firstName_head N hN
      (strategy (replay strategy (answers h))) false
      (replay strategy (answers h)) _ hrawNonloop

/-! ## Preservation of graph success -/

/-- Both vertices of a queried unordered pair occur in the chronological
endpoint list, independently of the representative chosen by `Sym2.out`. -/
theorem pair_vertices_mem_chronologicalEndpoints
    {h : Transcript InfiniteQuery} {u v : InfiniteVertex} {answer : Bool}
    (hmem : (s(u, v), answer) ∈ h) :
    u ∈ chronologicalEndpoints h ∧ v ∈ chronologicalEndpoints h := by
  let q : InfiniteQuery := s(u, v)
  have hentry : (q, answer) ∈ h := hmem
  have hfst := out_fst_mem_chronologicalEndpoints hentry
  have hsnd := out_snd_mem_chronologicalEndpoints hentry
  have hout : Sym2.mk q.out = s(u, v) := q.out_eq
  rw [Sym2.eq_iff] at hout
  rcases hout with hout | hout
  · exact ⟨by simpa [hout.1] using hfst, by simpa [hout.2] using hsnd⟩
  · exact ⟨by simpa [hout.2] using hsnd, by simpa [hout.1] using hfst⟩

/-- Every vertex in a `K₆` copy lies on a positive edge and therefore has a
first-appearance name. -/
theorem copy_vertex_mem_chronologicalEndpoints
    {h : Transcript InfiniteQuery}
    (copy : SimpleGraph.Copy K6 (infinitePositiveGraph h)) (i : Fin 6) :
    copy i ∈ chronologicalEndpoints h := by
  obtain ⟨j, hji⟩ := exists_ne i
  have hij : i ≠ j := hji.symm
  have hK6 : K6.Adj i j := by simp [K6, hij]
  have hadj := copy.toHom.map_rel hK6
  exact (pair_vertices_mem_chronologicalEndpoints hadj.2).1

/-- A raw positive entry is carried to the corresponding positive entry of
the completed canonical transcript. -/
theorem positive_pair_mem_relabelCompletedTranscript
    (N : ℕ) (hN : 0 < N) (h : Transcript InfiniteQuery)
    (hlen : h.length ≤ N) {u v : InfiniteVertex}
    (hmem : (s(u, v), true) ∈ h) :
    (s(firstName N hN h hlen u, firstName N hN h hlen v), true) ∈
      relabelCompletedTranscript N hN h hlen := by
  unfold relabelCompletedTranscript
  apply List.mem_map.mpr
  refine ⟨(s(u, v), true), hmem, ?_⟩
  simp only [Sym2.map_pair_eq]

/-- Any `K₆` found on an infinite answer path is found on the coherently
relabelled finite answer path. -/
noncomputable def canonicalCopyOfInfiniteCopy
    (N : ℕ) (hN : 0 < N) (strategy : InfiniteStrategy)
    (bits : List Bool) (hlen : bits.length ≤ N)
    (copy : SimpleGraph.Copy K6
      (infinitePositiveGraph (replay strategy bits))) :
    SimpleGraph.Copy K6
      (positiveGraph (canonicalPath N hN strategy bits hlen)) where
  toHom :=
    { toFun := fun i =>
        firstName N hN (replay strategy bits) (by simpa using hlen) (copy i)
      map_rel' := by
        intro i j hij
        have hadj := copy.toHom.map_rel hij
        have hi := copy_vertex_mem_chronologicalEndpoints copy i
        have hj := copy_vertex_mem_chronologicalEndpoints copy j
        constructor
        · intro heq
          have hcij : copy i = copy j :=
            firstName_injective_on N hN (replay strategy bits)
              (by simpa using hlen) hi hj heq
          exact hadj.1 hcij
        · rw [canonicalPath_eq_relabelCompletedTranscript]
          exact positive_pair_mem_relabelCompletedTranscript N hN
            (replay strategy bits) (by simpa using hlen) hadj.2 }
  injective' := by
    intro i j heq
    have hi := copy_vertex_mem_chronologicalEndpoints copy i
    have hj := copy_vertex_mem_chronologicalEndpoints copy j
    apply copy.injective
    exact firstName_injective_on N hN (replay strategy bits)
      (by simpa using hlen) hi hj heq

theorem infiniteSucceeds_implies_canonicalPathSucceeds
    (N : ℕ) (hN : 0 < N) (strategy : InfiniteStrategy)
    (bits : List Bool) (hlen : bits.length ≤ N)
    (hsuccess : InfiniteTranscriptSucceeds (replay strategy bits)) :
    TranscriptSucceeds (canonicalPath N hN strategy bits hlen) := by
  rcases hsuccess with ⟨copy⟩
  exact ⟨canonicalCopyOfInfiniteCopy N hN strategy bits hlen copy⟩

theorem infiniteAnswerVectorSucceeds_implies_canonical
    (N : ℕ) (hN : 0 < N) (strategy : InfiniteStrategy)
    (bits : List.Vector Bool N)
    (hsuccess : infiniteAnswerVectorSucceeds strategy bits) :
    answerVectorSucceeds (canonicalPolicy N hN strategy) bits := by
  unfold infiniteAnswerVectorSucceeds at hsuccess
  unfold answerVectorSucceeds
  rw [replay_canonicalPolicy N hN strategy bits.toList (by simp)]
  exact infiniteSucceeds_implies_canonicalPathSucceeds N hN strategy
    bits.toList (by simp) hsuccess

/-- The canonical finite policy has at least the success probability of the
infinite policy it simulates.  Both sides are compared term by term under the
same Bernoulli answer-vector law. -/
theorem infiniteSuccessProbability_le_canonical
    (p : ℝ≥0∞) (hp : p ≤ 1) (N : ℕ) (hN : 0 < N)
    (strategy : InfiniteStrategy) (hadm : InfiniteAdmissible N strategy) :
    infiniteSuccessProbability p N strategy ≤
      successProbability p N (canonicalPolicy N hN strategy) := by
  rw [successProbability_eq_answer_sum p hp N
    (canonicalPolicy N hN strategy)
    (canonicalPolicy_admissible N hN strategy hadm).1]
  unfold infiniteSuccessProbability
  apply Finset.sum_le_sum
  intro bits _
  by_cases hs : infiniteAnswerVectorSucceeds strategy bits
  · have hcan := infiniteAnswerVectorSucceeds_implies_canonical
      N hN strategy bits hs
    simp [hs, hcan]
  · simp [hs]

/-- Every winning infinite-board policy has one coherent winning policy on
the canonical `Fin (2 * N)` board. -/
theorem achievable_of_infiniteAchievable {p : ℝ≥0∞} {N : ℕ}
    (h : InfiniteAchievable p N) : Achievable p N := by
  rcases h with ⟨hN, hp, strategy, hadm, hprob⟩
  refine ⟨hp, canonicalPolicy N hN strategy,
    canonicalPolicy_admissible N hN strategy hadm, ?_⟩
  exact hprob.trans (infiniteSuccessProbability_le_canonical
    p hp N hN strategy hadm)

/-! ## Lifting a canonical finite policy back to `ℕ` -/

/-- The fixed inclusion of canonical vertices into the natural numbers. -/
def vertexInclusion (N : ℕ) : Vertex N ↪ InfiniteVertex :=
  ⟨Fin.val, Fin.val_injective⟩

/-- Relabel a canonical finite coordinate along the fixed inclusion. -/
def includeQuery (N : ℕ) : Query N → InfiniteQuery :=
  Sym2.map (vertexInclusion N)

theorem includeQuery_injective (N : ℕ) :
    Function.Injective (includeQuery N) :=
  Sym2.map.injective (vertexInclusion N).injective

/-- Relabel a finite transcript into the countably infinite vertex set. -/
def includeTranscript {N : ℕ} (h : Transcript (Query N)) :
    Transcript InfiniteQuery :=
  h.map fun entry => (includeQuery N entry.1, entry.2)

@[simp] theorem length_includeTranscript {N : ℕ}
    (h : Transcript (Query N)) :
    (includeTranscript h).length = h.length := by
  simp [includeTranscript]

@[simp] theorem answers_includeTranscript {N : ℕ}
    (h : Transcript (Query N)) :
    answers (includeTranscript h) = answers h := by
  simp [includeTranscript, answers, Function.comp_def]

theorem queries_includeTranscript {N : ℕ} (h : Transcript (Query N)) :
    queries (includeTranscript h) = (queries h).map (includeQuery N) := by
  simp [includeTranscript, queries, Function.comp_def]

/-- The lifted policy reconstructs the finite history from its answer vector,
then includes the next finite coordinate into `ℕ`.  Thus irrelevant
off-tree coordinate names cannot affect the simulation. -/
def includedPolicy (N : ℕ) (strategy : K6Strategy N) : InfiniteStrategy :=
  fun h => includeQuery N (strategy (replay strategy (answers h)))

/-- One fixed included policy commutes with replay on every answer path. -/
theorem replay_includedPolicy (N : ℕ) (strategy : K6Strategy N)
    (bits : List Bool) :
    replay (includedPolicy N strategy) bits =
      includeTranscript (replay strategy bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [replay_cons, ih]
      have hnext :
          includedPolicy N strategy (includeTranscript (replay strategy bits)) =
            includeQuery N (strategy (replay strategy bits)) := by
        simp [includedPolicy]
      rw [hnext]
      rfl

theorem freshPath_includedPolicy_iff (N : ℕ) (strategy : K6Strategy N)
    (bits : List Bool) :
    FreshPath (includedPolicy N strategy) bits ↔ FreshPath strategy bits := by
  unfold FreshPath
  rw [replay_includedPolicy, queries_includeTranscript]
  exact List.nodup_map_iff (includeQuery_injective N)

theorem includedPolicy_admissible (N : ℕ) (strategy : K6Strategy N)
    (hadm : Admissible strategy) :
    InfiniteAdmissible N (includedPolicy N strategy) := by
  constructor
  · intro bits
    exact (freshPath_includedPolicy_iff N strategy bits.toList).mpr
      (hadm.1 bits)
  · intro h hlen
    have hfiniteLen : (replay strategy (answers h)).length < N := by
      simpa using hlen
    have hfinite := hadm.2 (replay strategy (answers h)) hfiniteLen
    unfold includedPolicy
    simpa [includeQuery, Sym2.isDiag_map (vertexInclusion N).injective]
      using hfinite

/-- A positive finite edge remains positive after the fixed inclusion. -/
theorem positive_pair_mem_includeTranscript {N : ℕ}
    (h : Transcript (Query N)) {u v : Vertex N}
    (hmem : (s(u, v), true) ∈ h) :
    (s((vertexInclusion N) u, (vertexInclusion N) v), true) ∈
      includeTranscript h := by
  unfold includeTranscript
  apply List.mem_map.mpr
  refine ⟨(s(u, v), true), hmem, ?_⟩
  simp [includeQuery, Sym2.map_pair_eq]

/-- A finite `K₆` copy embeds into the lifted infinite transcript. -/
def infiniteCopyOfFiniteCopy {N : ℕ} (h : Transcript (Query N))
    (copy : SimpleGraph.Copy K6 (positiveGraph h)) :
    SimpleGraph.Copy K6 (infinitePositiveGraph (includeTranscript h)) where
  toHom :=
    { toFun := fun i => (vertexInclusion N) (copy i)
      map_rel' := by
        intro i j hij
        have hadj := copy.toHom.map_rel hij
        exact ⟨
          fun heq => hadj.1 ((vertexInclusion N).injective heq),
          positive_pair_mem_includeTranscript h hadj.2⟩ }
  injective' := fun i j heq =>
    copy.injective ((vertexInclusion N).injective heq)

theorem finiteSucceeds_implies_includedSucceeds {N : ℕ}
    (strategy : K6Strategy N) (bits : List Bool)
    (hsuccess : TranscriptSucceeds (replay strategy bits)) :
    InfiniteTranscriptSucceeds (replay (includedPolicy N strategy) bits) := by
  rw [replay_includedPolicy]
  rcases hsuccess with ⟨copy⟩
  exact ⟨infiniteCopyOfFiniteCopy (replay strategy bits) copy⟩

theorem finiteAnswerVectorSucceeds_implies_included {N : ℕ}
    (strategy : K6Strategy N) (bits : List.Vector Bool N)
    (hsuccess : answerVectorSucceeds strategy bits) :
    infiniteAnswerVectorSucceeds (includedPolicy N strategy) bits := by
  exact finiteSucceeds_implies_includedSucceeds strategy bits.toList hsuccess

theorem successProbability_le_included
    (p : ℝ≥0∞) (hp : p ≤ 1) (N : ℕ) (strategy : K6Strategy N)
    (hadm : Admissible strategy) :
    successProbability p N strategy ≤
      infiniteSuccessProbability p N (includedPolicy N strategy) := by
  rw [successProbability_eq_answer_sum p hp N strategy hadm.1]
  unfold infiniteSuccessProbability
  apply Finset.sum_le_sum
  intro bits _
  by_cases hs : answerVectorSucceeds strategy bits
  · have hinf := finiteAnswerVectorSucceeds_implies_included strategy bits hs
    simp [hs, hinf]
  · simp [hs]

/-- A zero-query canonical game has no strategy at all, since its query type
is `Sym2 (Fin 0)`. -/
theorem not_achievable_zero (p : ℝ≥0∞) : ¬ Achievable p 0 := by
  rintro ⟨_, strategy, _⟩
  exact Fin.elim0 (strategy []).out.1

/-- Every winning canonical finite policy lifts to a winning policy in the
countably infinite formulation. -/
theorem infiniteAchievable_of_achievable {p : ℝ≥0∞} {N : ℕ}
    (h : Achievable p N) : InfiniteAchievable p N := by
  have hN : 0 < N := by
    by_contra hzero
    have : N = 0 := Nat.eq_zero_of_not_pos hzero
    subst N
    exact not_achievable_zero p h
  rcases h with ⟨hp, strategy, hadm, hprob⟩
  refine ⟨hN, hp, includedPolicy N strategy,
    includedPolicy_admissible N strategy hadm, ?_⟩
  exact hprob.trans (successProbability_le_included p hp N strategy hadm)

/-- Exact equivalence of the standard countably infinite formulation and the
canonical `Fin (2 * N)` formulation, at every density and every horizon. -/
theorem infiniteAchievable_iff_achievable (p : ℝ≥0∞) (N : ℕ) :
    InfiniteAchievable p N ↔ Achievable p N :=
  ⟨achievable_of_infiniteAchievable, infiniteAchievable_of_achievable⟩

end
end InfinitePolicyBridge
end OnlineRamsey
