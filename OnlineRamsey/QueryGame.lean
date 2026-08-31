import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-!
# A finite graph-specific interface for the subgraph-query game

An `N`-query play touches at most `2N` vertices, so this module works on the
canonical ambient type `Fin (2 * N)`.  Queries are represented canonically by
their smaller and larger endpoints; loops are therefore unrepresentable.

The module is deterministic.  A separate probability layer may run a policy
against a pre-sampled board, but all legality, freshness, positive-graph, and
padding facts below are pathwise.
-/

namespace OnlineRamsey

namespace FiniteQueryGame

/-- A canonical unordered, nonloop pair of vertices of `Fin n`. -/
structure PairQuery (n : ℕ) where
  lo : Fin n
  hi : Fin n
  isLt : lo < hi
  deriving DecidableEq

namespace PairQuery

variable {n : ℕ}

/-- The two possible orientations in which a query can connect vertices. -/
def Connects (q : PairQuery n) (u v : Fin n) : Prop :=
  (q.lo = u ∧ q.hi = v) ∨ (q.lo = v ∧ q.hi = u)

theorem connects_symm (q : PairQuery n) (u v : Fin n) :
    q.Connects u v ↔ q.Connects v u := by
  constructor <;> intro h <;> rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

theorem not_connects_self (q : PairQuery n) (u : Fin n) :
    ¬ q.Connects u u := by
  intro h
  rcases h with h | h
  · exact (ne_of_lt q.isLt) (h.1.trans h.2.symm)
  · exact (ne_of_lt q.isLt) (h.1.trans h.2.symm)

end PairQuery

/-- Canonical vertex type for a game with query budget `N`. -/
abbrev Vertex (N : ℕ) := Fin (2 * N)

/-- Legal unordered pair queries for a game with query budget `N`. -/
abbrev Query (N : ℕ) := PairQuery (2 * N)

/-- A transcript is stored newest first, matching the adaptive-query module. -/
abbrev GameTranscript (N : ℕ) := List (Query N × Bool)

/-- The query coordinates in a transcript. -/
def transcriptQueries {N : ℕ} (h : GameTranscript N) : List (Query N) :=
  h.map Prod.fst

/-- A deterministic graph-specific policy. -/
abbrev Policy (N : ℕ) := GameTranscript N → Query N

/-- No query coordinate occurs twice in the transcript. -/
def FreshTranscript {N : ℕ} (h : GameTranscript N) : Prop :=
  (transcriptQueries h).Nodup

/-- The next query selected by a policy has not previously occurred. -/
def FreshAt {N : ℕ} (policy : Policy N) (h : GameTranscript N) : Prop :=
  policy h ∉ transcriptQueries h

/-- The positive-answer graph represented by a transcript. -/
def positiveGraph {N : ℕ} (h : GameTranscript N) : SimpleGraph (Vertex N) where
  Adj u v := ∃ q : Query N, (q, true) ∈ h ∧ q.Connects u v
  symm := by
    intro u v huv
    rcases huv with ⟨q, hq, hconn⟩
    exact ⟨q, hq, (q.connects_symm u v).mp hconn⟩
  loopless := by
    intro u huu
    rcases huu with ⟨q, _, hconn⟩
    exact q.not_connects_self u hconn

@[simp] theorem positiveGraph_adj {N : ℕ} (h : GameTranscript N)
    (u v : Vertex N) :
    (positiveGraph h).Adj u v ↔
      ∃ q : Query N, (q, true) ∈ h ∧ q.Connects u v := Iff.rfl

/-- Adding transcript entries cannot remove a positive edge. -/
theorem positiveGraph_mono_of_mem {N : ℕ} {h h' : GameTranscript N}
    (hsub : ∀ entry, entry ∈ h → entry ∈ h') :
    positiveGraph h ≤ positiveGraph h' := by
  intro u v huv
  rcases huv with ⟨q, hq, hconn⟩
  exact ⟨q, hsub (q, true) hq, hconn⟩

/-- Padding is placed before a newest-first transcript. -/
def pad {N : ℕ} (h padding : GameTranscript N) : GameTranscript N :=
  padding ++ h

@[simp] theorem transcriptQueries_pad {N : ℕ} (h padding : GameTranscript N) :
    transcriptQueries (pad h padding) =
      transcriptQueries padding ++ transcriptQueries h := by
  simp [transcriptQueries, pad]

@[simp] theorem length_pad {N : ℕ} (h padding : GameTranscript N) :
    (pad h padding).length = padding.length + h.length := by
  simp [pad]

/-- A padding transcript is fresh relative to an existing transcript. -/
def FreshPadding {N : ℕ} (h padding : GameTranscript N) : Prop :=
  FreshTranscript padding ∧
    (transcriptQueries padding).Disjoint (transcriptQueries h)

/-- Fresh padding preserves the no-repeated-query invariant. -/
theorem freshTranscript_pad {N : ℕ} {h padding : GameTranscript N}
    (hh : FreshTranscript h) (hp : FreshPadding h padding) :
    FreshTranscript (pad h padding) := by
  unfold FreshPadding at hp
  unfold FreshTranscript at hh ⊢
  rw [transcriptQueries_pad]
  exact hp.1.append hh hp.2

/-- Padding never removes a positive edge, irrespective of its answers. -/
theorem positiveGraph_le_pad {N : ℕ} (h padding : GameTranscript N) :
    positiveGraph h ≤ positiveGraph (pad h padding) := by
  apply positiveGraph_mono_of_mem
  intro entry hentry
  exact List.mem_append.mpr (Or.inr hentry)

/-- Consequently every non-induced graph property monotone under graph
inclusion may be proved after padding to the full query budget. -/
theorem positiveGraph_le_of_padding {N : ℕ} {h h' padding : GameTranscript N}
    (heq : h' = pad h padding) : positiveGraph h ≤ positiveGraph h' := by
  subst h'
  exact positiveGraph_le_pad h padding

end FiniteQueryGame

namespace CanonicalRelabeling

/-!
## Canonical relabeling of an auxiliary oriented transcript

This section deliberately works with an arbitrary vertex type and with a pair
whose two endpoints are stored in a chosen order.  It proves a finite
transcript-level embedding lemma useful for graph counting.  It is not the
standard unordered query space: reversing the stored endpoints gives a
different `RawPairQuery` value.  The actual game uses `Sym2`, and the coherent
whole-policy first-appearance reduction is in `InfinitePolicyBridge.lean`.
-/

universe u w

/-- An auxiliary oriented representative of a nonloop pair.

`left` and `right` are structural fields, so swapping them changes the value.
`Connects` below deliberately forgets that orientation when forming a graph.
The standard unordered game is instead formulated with `Sym2`. -/
structure RawPairQuery (V : Type u) where
  left : V
  right : V
  ne : left ≠ right

namespace RawPairQuery

variable {V : Type u}

def Connects (q : RawPairQuery V) (u v : V) : Prop :=
  (q.left = u ∧ q.right = v) ∨ (q.left = v ∧ q.right = u)

theorem connects_symm (q : RawPairQuery V) (u v : V) :
    q.Connects u v ↔ q.Connects v u := by
  constructor <;> intro h <;> rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

theorem not_connects_self (q : RawPairQuery V) (u : V) :
    ¬ q.Connects u u := by
  intro h
  rcases h with h | h
  · exact q.ne (h.1.trans h.2.symm)
  · exact q.ne (h.1.trans h.2.symm)

end RawPairQuery

abbrev RawTranscript (V : Type u) := List (RawPairQuery V × Bool)

/-- Vertices appearing as endpoints of at least one query. -/
def touched [DecidableEq V] : RawTranscript V → Finset V
  | [] => ∅
  | (q, _) :: h => insert q.left (insert q.right (touched h))

theorem left_mem_touched [DecidableEq V] {h : RawTranscript V}
    {q : RawPairQuery V} {answer : Bool} (hq : (q, answer) ∈ h) :
    q.left ∈ touched h := by
  induction h with
  | nil => simp at hq
  | cons head tail ih =>
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp [touched]
      · simp [touched, ih hq]

theorem right_mem_touched [DecidableEq V] {h : RawTranscript V}
    {q : RawPairQuery V} {answer : Bool} (hq : (q, answer) ∈ h) :
    q.right ∈ touched h := by
  induction h with
  | nil => simp at hq
  | cons head tail ih =>
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp [touched]
      · simp [touched, ih hq]

/-- Two endpoints per query is the only cardinality estimate required for
canonical finite relabeling. -/
theorem card_touched_le [DecidableEq V] (h : RawTranscript V) :
    (touched h).card ≤ 2 * h.length := by
  induction h with
  | nil => simp [touched]
  | cons head tail ih =>
      have hleft := Finset.card_insert_le head.1.left
        (insert head.1.right (touched tail))
      have hright := Finset.card_insert_le head.1.right (touched tail)
      simp only [touched, List.length_cons]
      omega

/-- The positive graph of a raw transcript. -/
def rawPositiveGraph [DecidableEq V] (h : RawTranscript V) : SimpleGraph V where
  Adj u v := ∃ q : RawPairQuery V, (q, true) ∈ h ∧ q.Connects u v
  symm := by
    intro u v huv
    rcases huv with ⟨q, hq, hconn⟩
    exact ⟨q, hq, (q.connects_symm u v).mp hconn⟩
  loopless := by
    intro u huu
    rcases huu with ⟨q, _, hconn⟩
    exact q.not_connects_self u hconn

/-- The positive graph restricted to the touched-vertex subtype. -/
abbrev touchedPositiveGraph [DecidableEq V] (h : RawTranscript V) :
    SimpleGraph {v : V // v ∈ touched h} :=
  (rawPositiveGraph h).induce {v | v ∈ touched h}

/-- A transcript of length at most `N` has enough canonical names in
`Fin (2 * N)` for all of its touched vertices. -/
theorem touched_card_le_budget [DecidableEq V] {h : RawTranscript V} {N : ℕ}
    (hlen : h.length ≤ N) :
    Fintype.card {v : V // v ∈ touched h} ≤ Fintype.card (Fin (2 * N)) := by
  simpa using (card_touched_le h).trans (Nat.mul_le_mul_left 2 hlen)

/-- A canonical injection of all touched vertices into `Fin (2 * N)`.

The choice of injection is intentionally noncomputable: the theorem needs
only existence, and the online first-appearance construction may later choose
a particular computable representative.
-/
noncomputable def vertexEmbedding [DecidableEq V]
    (h : RawTranscript V) (N : ℕ) (hlen : h.length ≤ N) :
    {v : V // v ∈ touched h} ↪ Fin (2 * N) :=
  Classical.choice <|
    (Function.Embedding.nonempty_iff_card_le.mpr
      (touched_card_le_budget hlen))

/-- The exact positive graph after canonical finite relabeling.  Vertices not
in the image of `vertexEmbedding` are isolated. -/
noncomputable def canonicalPositiveGraph [DecidableEq V]
    (h : RawTranscript V) (N : ℕ) (hlen : h.length ≤ N) :
    SimpleGraph (Fin (2 * N)) :=
  (touchedPositiveGraph h).map (vertexEmbedding h N hlen)

/-- Canonical relabeling preserves adjacency and nonadjacency on all touched
vertices, expressed as a graph embedding. -/
noncomputable def graphEmbedding [DecidableEq V]
    (h : RawTranscript V) (N : ℕ) (hlen : h.length ≤ N) :
    touchedPositiveGraph h ↪g canonicalPositiveGraph h N hlen :=
  SimpleGraph.Embedding.map (vertexEmbedding h N hlen) (touchedPositiveGraph h)

theorem graphEmbedding_apply [DecidableEq V]
    (h : RawTranscript V) (N : ℕ) (hlen : h.length ≤ N)
    (v : {v : V // v ∈ touched h}) :
    graphEmbedding h N hlen v = vertexEmbedding h N hlen v := rfl

/-- Composition with a fixed copy injects labelled copies into the larger
ambient graph.  This generic finite lemma is useful beyond relabeling. -/
theorem labelledCopyCount_le_of_copy
    {A : Type u} {B : Type w} {W : Type*}
    [Fintype A] [Fintype B] [Fintype W]
    {G : SimpleGraph A} {G' : SimpleGraph B} (f : SimpleGraph.Copy G G')
    (H : SimpleGraph W) :
    G.labelledCopyCount H ≤ G'.labelledCopyCount H := by
  classical
  unfold SimpleGraph.labelledCopyCount
  apply Fintype.card_le_of_injective (fun c => f.comp c)
  intro c d hcd
  apply SimpleGraph.Copy.ext
  intro v
  apply f.injective
  have hv := congrArg (fun z : SimpleGraph.Copy H G' => z v) hcd
  simpa using hv

/-- In particular, canonical relabeling cannot decrease the number of
labelled non-induced copies of any finite pattern. -/
theorem labelledCopyCount_le_canonical [DecidableEq V]
    (h : RawTranscript V) (N : ℕ) (hlen : h.length ≤ N)
    {W : Type*} [Fintype W] (H : SimpleGraph W) :
    (touchedPositiveGraph h).labelledCopyCount H ≤
      (canonicalPositiveGraph h N hlen).labelledCopyCount H :=
  labelledCopyCount_le_of_copy (graphEmbedding h N hlen).toCopy H

/-- Existential packaging of the canonical-relabeling core. -/
theorem exists_finite_relabeling [DecidableEq V]
    (h : RawTranscript V) (N : ℕ) (hlen : h.length ≤ N) :
    ∃ f : {v : V // v ∈ touched h} ↪ Fin (2 * N),
      Nonempty
        (touchedPositiveGraph h ↪g
          (touchedPositiveGraph h).map f) := by
  let f := vertexEmbedding h N hlen
  exact ⟨f, ⟨SimpleGraph.Embedding.map f (touchedPositiveGraph h)⟩⟩

end CanonicalRelabeling

end OnlineRamsey
