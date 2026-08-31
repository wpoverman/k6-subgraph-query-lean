import OnlineRamsey.AdaptiveQuery
import OnlineRamsey.QueryGame

/-!
# Coherent equivalence relabeling of auxiliary oriented policies

This file supplies the policy-level counterpart of the transcript-level
canonicalization in `QueryGame.lean`.  An equivalence of vertex types induces
equivalences of the auxiliary `RawPairQuery` values, transcripts,
deterministic policies, and pre-sampled boards.  `RawPairQuery` stores an
orientation, even though its graph interpretation is symmetric.  Transporting
both a policy and a board commutes exactly with `run` and `replay`, not merely
up to distribution.

Consequently freshness, answer vectors, positive graphs, and success by
containing a fixed finite graph are invariant under relabeling.  For a finite
vertex type, specializing to `Fintype.equivFin` gives a canonical policy on
`Fin (Fintype.card V)` within this auxiliary model.  The standard unordered
`Sym2 ℕ` game and its coherent first-appearance reduction to `Fin (2 * N)`
are treated in `InfinitePolicyBridge.lean`.
-/

namespace OnlineRamsey

namespace PolicyRelabeling

open CanonicalRelabeling
open scoped SimpleGraph

universe u v w

/-- Relabel both stored endpoints of an auxiliary oriented nonloop query. -/
def relabelQuery {V : Type u} {W : Type v} (e : V ≃ W) :
    RawPairQuery V → RawPairQuery W :=
  fun q =>
    { left := e q.left
      right := e q.right
      ne := fun h => q.ne (e.injective h) }

@[simp] theorem relabelQuery_left {V : Type u} {W : Type v} (e : V ≃ W)
    (q : RawPairQuery V) : (relabelQuery e q).left = e q.left := rfl

@[simp] theorem relabelQuery_right {V : Type u} {W : Type v} (e : V ≃ W)
    (q : RawPairQuery V) : (relabelQuery e q).right = e q.right := rfl

@[ext] theorem RawPairQuery.ext {V : Type u} {q q' : RawPairQuery V}
    (hleft : q.left = q'.left) (hright : q.right = q'.right) : q = q' := by
  cases q
  cases q'
  simp_all

@[simp] theorem relabelQuery_symm_apply {V : Type u} {W : Type v}
    (e : V ≃ W) (q : RawPairQuery V) :
    relabelQuery e.symm (relabelQuery e q) = q := by
  ext <;> simp [relabelQuery]

@[simp] theorem relabelQuery_apply_symm {V : Type u} {W : Type v}
    (e : V ≃ W) (q : RawPairQuery W) :
    relabelQuery e (relabelQuery e.symm q) = q := by
  ext <;> simp [relabelQuery]

/-- Vertex relabeling is an equivalence on legal query coordinates. -/
def queryEquiv {V : Type u} {W : Type v} (e : V ≃ W) :
    RawPairQuery V ≃ RawPairQuery W where
  toFun := relabelQuery e
  invFun := relabelQuery e.symm
  left_inv := relabelQuery_symm_apply e
  right_inv := relabelQuery_apply_symm e

@[simp] theorem queryEquiv_apply {V : Type u} {W : Type v} (e : V ≃ W)
    (q : RawPairQuery V) : queryEquiv e q = relabelQuery e q := rfl

@[simp] theorem queryEquiv_symm_apply {V : Type u} {W : Type v} (e : V ≃ W)
    (q : RawPairQuery W) : (queryEquiv e).symm q = relabelQuery e.symm q := rfl

/-- Relabel every query coordinate in a newest-first transcript. -/
def relabelTranscript {V : Type u} {W : Type v} (e : V ≃ W)
    (h : RawTranscript V) : RawTranscript W :=
  h.map fun entry => (relabelQuery e entry.1, entry.2)

@[simp] theorem relabelTranscript_nil {V : Type u} {W : Type v} (e : V ≃ W) :
    relabelTranscript e ([] : RawTranscript V) = [] := rfl

@[simp] theorem relabelTranscript_cons {V : Type u} {W : Type v} (e : V ≃ W)
    (q : RawPairQuery V) (answer : Bool) (h : RawTranscript V) :
    relabelTranscript e ((q, answer) :: h) =
      (relabelQuery e q, answer) :: relabelTranscript e h := rfl

@[simp] theorem length_relabelTranscript {V : Type u} {W : Type v}
    (e : V ≃ W) (h : RawTranscript V) :
    (relabelTranscript e h).length = h.length := by
  simp [relabelTranscript]

@[simp] theorem relabelTranscript_symm_apply {V : Type u} {W : Type v}
    (e : V ≃ W) (h : RawTranscript V) :
    relabelTranscript e.symm (relabelTranscript e h) = h := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
      rcases entry with ⟨q, answer⟩
      simp [ih]

@[simp] theorem relabelTranscript_apply_symm {V : Type u} {W : Type v}
    (e : V ≃ W) (h : RawTranscript W) :
    relabelTranscript e (relabelTranscript e.symm h) = h := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
      rcases entry with ⟨q, answer⟩
      simp [ih]

/-- Relabeling is an equivalence of complete transcript spaces. -/
def transcriptEquiv {V : Type u} {W : Type v} (e : V ≃ W) :
    RawTranscript V ≃ RawTranscript W where
  toFun := relabelTranscript e
  invFun := relabelTranscript e.symm
  left_inv := relabelTranscript_symm_apply e
  right_inv := relabelTranscript_apply_symm e

abbrev RawPolicy (V : Type u) := Strategy (RawPairQuery V)
abbrev RawBoard (V : Type u) := Board (RawPairQuery V)

/-- Conjugate a deterministic policy by a vertex equivalence. -/
def relabelPolicy {V : Type u} {W : Type v} (e : V ≃ W)
    (policy : RawPolicy V) : RawPolicy W :=
  fun h => relabelQuery e (policy (relabelTranscript e.symm h))

/-- Transport a pre-sampled board along the same vertex equivalence. -/
def relabelBoard {V : Type u} {W : Type v} (e : V ≃ W)
    (board : RawBoard V) : RawBoard W :=
  fun q => board (relabelQuery e.symm q)

@[simp] theorem relabelPolicy_symm_apply {V : Type u} {W : Type v}
    (e : V ≃ W) (policy : RawPolicy V) :
    relabelPolicy e.symm (relabelPolicy e policy) = policy := by
  funext h
  simp [relabelPolicy]

@[simp] theorem relabelPolicy_apply_symm {V : Type u} {W : Type v}
    (e : V ≃ W) (policy : RawPolicy W) :
    relabelPolicy e (relabelPolicy e.symm policy) = policy := by
  funext h
  simp [relabelPolicy]

@[simp] theorem relabelBoard_symm_apply {V : Type u} {W : Type v}
    (e : V ≃ W) (board : RawBoard V) :
    relabelBoard e.symm (relabelBoard e board) = board := by
  funext q
  simp [relabelBoard]

@[simp] theorem relabelBoard_apply_symm {V : Type u} {W : Type v}
    (e : V ≃ W) (board : RawBoard W) :
    relabelBoard e (relabelBoard e.symm board) = board := by
  funext q
  simp [relabelBoard]

/-- Relabeling is a bijection on complete deterministic policies. -/
def policyEquiv {V : Type u} {W : Type v} (e : V ≃ W) :
    RawPolicy V ≃ RawPolicy W where
  toFun := relabelPolicy e
  invFun := relabelPolicy e.symm
  left_inv := relabelPolicy_symm_apply e
  right_inv := relabelPolicy_apply_symm e

/-- Relabeling is likewise a bijection on pre-sampled boards. -/
def boardEquiv {V : Type u} {W : Type v} (e : V ≃ W) :
    RawBoard V ≃ RawBoard W where
  toFun := relabelBoard e
  invFun := relabelBoard e.symm
  left_inv := relabelBoard_symm_apply e
  right_inv := relabelBoard_apply_symm e

@[simp] theorem relabelPolicy_on_relabelTranscript {V : Type u} {W : Type v}
    (e : V ≃ W) (policy : RawPolicy V) (h : RawTranscript V) :
    relabelPolicy e policy (relabelTranscript e h) =
      relabelQuery e (policy h) := by
  simp [relabelPolicy]

@[simp] theorem relabelBoard_on_relabelQuery {V : Type u} {W : Type v}
    (e : V ≃ W) (board : RawBoard V) (q : RawPairQuery V) :
    relabelBoard e board (relabelQuery e q) = board q := by
  simp [relabelBoard]

/-- Within the auxiliary oriented model, relabeling an entire policy and board
commutes exactly with every finite run. -/
theorem relabel_run {V : Type u} {W : Type v} (e : V ≃ W)
    (policy : RawPolicy V) (board : RawBoard V) (n : ℕ) :
    relabelTranscript e (run policy board n) =
      run (relabelPolicy e policy) (relabelBoard e board) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run_succ, relabelTranscript_cons]
      rw [← ih]
      simp

/-- The same conjugation commutes with prescribed answer-path replay. -/
theorem relabel_replay {V : Type u} {W : Type v} (e : V ≃ W)
    (policy : RawPolicy V) (bits : List Bool) :
    relabelTranscript e (replay policy bits) =
      replay (relabelPolicy e policy) bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [replay_cons, relabelTranscript_cons]
      rw [← ih]
      simp

theorem answers_relabelTranscript {V : Type u} {W : Type v} (e : V ≃ W)
    (h : RawTranscript V) : answers (relabelTranscript e h) = answers h := by
  simp [answers, relabelTranscript, Function.comp_def]

/-- Hence the complete adaptive answer vector, and in particular the query
count, are unchanged. -/
theorem answers_relabel_run {V : Type u} {W : Type v} (e : V ≃ W)
    (policy : RawPolicy V) (board : RawBoard V) (n : ℕ) :
    answers (run (relabelPolicy e policy) (relabelBoard e board) n) =
      answers (run policy board n) := by
  rw [← relabel_run]
  exact answers_relabelTranscript e _

theorem length_relabel_run {V : Type u} {W : Type v} (e : V ≃ W)
    (policy : RawPolicy V) (board : RawBoard V) (n : ℕ) :
    (run (relabelPolicy e policy) (relabelBoard e board) n).length =
      (run policy board n).length := by
  simp

/-- Query-coordinate lists are mapped pointwise by the induced equivalence. -/
theorem queries_relabelTranscript {V : Type u} {W : Type v} (e : V ≃ W)
    (h : RawTranscript V) :
    queries (relabelTranscript e h) = (queries h).map (relabelQuery e) := by
  simp [queries, relabelTranscript, Function.comp_def]

/-- Freshness of the next choice is invariant under coherent policy
transport. -/
theorem freshAt_relabel_iff {V : Type u} {W : Type v} (e : V ≃ W)
    (policy : RawPolicy V) (h : RawTranscript V) :
    FreshAt (relabelPolicy e policy) (relabelTranscript e h) ↔
      FreshAt policy h := by
  simp only [FreshAt, relabelPolicy_on_relabelTranscript,
    queries_relabelTranscript]
  constructor
  · contrapose!
    intro hmem
    exact List.mem_map.mpr ⟨policy h, hmem, rfl⟩
  · contrapose!
    intro hmem
    rcases List.mem_map.mp hmem with ⟨q, hq, heq⟩
    have hqp : q = policy h := (queryEquiv e).injective heq
    simpa [hqp] using hq

theorem freshPath_relabel_iff {V : Type u} {W : Type v} (e : V ≃ W)
    (policy : RawPolicy V) (bits : List Bool) :
    FreshPath (relabelPolicy e policy) bits ↔ FreshPath policy bits := by
  unfold FreshPath
  rw [← relabel_replay, queries_relabelTranscript]
  exact List.nodup_map_iff (queryEquiv e).injective

/-- Connectivity of a relabeled query is exactly connectivity of the source
query. -/
theorem connects_relabelQuery_iff {V : Type u} {W : Type v} (e : V ≃ W)
    (q : RawPairQuery V) (x y : V) :
    (relabelQuery e q).Connects (e x) (e y) ↔ q.Connects x y := by
  simp only [RawPairQuery.Connects, relabelQuery_left, relabelQuery_right]
  aesop

/-- The positive-answer graphs at corresponding policy-tree nodes are
isomorphic by the original vertex equivalence. -/
def positiveGraphIso {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (h : RawTranscript V) :
    rawPositiveGraph h ≃g rawPositiveGraph (relabelTranscript e h) where
  toEquiv := e
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨q', hq', hconn⟩
      have hqmem :
          (relabelQuery e.symm q', true) ∈ h := by
        rcases List.mem_map.mp hq' with ⟨entry, hentry, heq⟩
        rcases entry with ⟨q, answer⟩
        have hqeq : relabelQuery e q = q' := congrArg Prod.fst heq
        have haeq : answer = true := congrArg Prod.snd heq
        subst answer
        have hback : relabelQuery e.symm q' = q := by
          rw [← hqeq]
          simp
        simpa [hback] using hentry
      refine ⟨relabelQuery e.symm q', hqmem, ?_⟩
      have hc := (connects_relabelQuery_iff e
        (relabelQuery e.symm q') x y).mp ?_
      · exact hc
      · simpa using hconn
    · rintro ⟨q, hq, hconn⟩
      refine ⟨relabelQuery e q, ?_, (connects_relabelQuery_iff e q x y).mpr hconn⟩
      exact List.mem_map.mpr ⟨(q, true), hq, rfl⟩

/-- Success defined by containing any fixed pattern is preserved exactly. -/
theorem isContained_positiveGraph_relabel_iff
    {V : Type u} {W : Type v} {A : Type w}
    [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (h : RawTranscript V) (H : SimpleGraph A) :
    H ⊑ rawPositiveGraph (relabelTranscript e h) ↔
      H ⊑ rawPositiveGraph h := by
  exact (SimpleGraph.isContained_congr_right (positiveGraphIso e h).symm)

/-- In particular, graph-containment success is preserved at every fixed
query horizon of the transported policy. -/
theorem isContained_relabel_run_iff
    {V : Type u} {W : Type v} {A : Type w}
    [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (policy : RawPolicy V) (board : RawBoard V)
    (n : ℕ) (H : SimpleGraph A) :
    H ⊑ rawPositiveGraph
        (run (relabelPolicy e policy) (relabelBoard e board) n) ↔
      H ⊑ rawPositiveGraph (run policy board n) := by
  rw [← relabel_run]
  exact isContained_positiveGraph_relabel_iff e _ H

/-! ## Canonical finite vertex set -/

section Finite

variable {V : Type u} [Fintype V]

/-- The canonical renaming of a finite vertex type. -/
noncomputable def finVertexEquiv : V ≃ Fin (Fintype.card V) :=
  Fintype.equivFin V

/-- A policy on an arbitrary finite vertex type, transported coherently to
the canonical type `Fin (Fintype.card V)`. -/
noncomputable def finPolicy (policy : RawPolicy V) :
    RawPolicy (Fin (Fintype.card V)) :=
  relabelPolicy finVertexEquiv policy

/-- The corresponding canonical finite board. -/
noncomputable def finBoard (board : RawBoard V) :
    RawBoard (Fin (Fintype.card V)) :=
  relabelBoard finVertexEquiv board

/-- Complete finite-board canonicalization: for every board and every query
count, one fixed transported policy has exactly the relabeled transcript. -/
theorem finPolicy_run (policy : RawPolicy V) (board : RawBoard V) (n : ℕ) :
    run (finPolicy policy) (finBoard board) n =
      relabelTranscript finVertexEquiv (run policy board n) := by
  exact (relabel_run finVertexEquiv policy board n).symm

theorem finPolicy_answers (policy : RawPolicy V) (board : RawBoard V) (n : ℕ) :
    answers (run (finPolicy policy) (finBoard board) n) =
      answers (run policy board n) :=
  answers_relabel_run finVertexEquiv policy board n

theorem finPolicy_freshPath_iff (policy : RawPolicy V) (bits : List Bool) :
    FreshPath (finPolicy policy) bits ↔ FreshPath policy bits :=
  freshPath_relabel_iff finVertexEquiv policy bits

theorem finPolicy_success_iff [DecidableEq V]
    {A : Type w} (policy : RawPolicy V) (board : RawBoard V)
    (n : ℕ) (H : SimpleGraph A) :
    H ⊑ rawPositiveGraph (run (finPolicy policy) (finBoard board) n) ↔
      H ⊑ rawPositiveGraph (run policy board n) := by
  rw [finPolicy_run]
  exact isContained_positiveGraph_relabel_iff finVertexEquiv _ H

end Finite

end PolicyRelabeling

end OnlineRamsey
