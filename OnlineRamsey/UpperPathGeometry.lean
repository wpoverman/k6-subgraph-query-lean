import OnlineRamsey.UpperStrategy

/-!
# Concrete path geometry for the slack upper strategy

This module isolates the deterministic bookkeeping needed to turn a ready
pre-fill transcript into a `SlackQueryGeometry`.  It deliberately lives
outside `UpperStrategy.lean`, so the probability and strategy work can
continue independently.
-/

namespace OnlineRamsey
namespace UpperPathGeometry

open QueryComplexity UpperStrategy

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Filtering a duplicate-free list away from an arbitrary used list loses
at most the length of the used list. -/
theorem length_sub_le_filter_not_mem
    {V : Type*} [DecidableEq V] (xs used : List V) (hxs : xs.Nodup) :
    xs.length - used.length ≤ (xs.filter fun v ↦ v ∉ used).length := by
  let removed := xs.filter fun v ↦ v ∈ used
  have hremovedNodup : removed.Nodup := hxs.filter _
  have hremovedSubset : removed.toFinset ⊆ used.toFinset := by
    intro v hv
    have hv' : v ∈ removed := by simpa [removed] using hv
    have hvused : v ∈ used :=
      of_decide_eq_true (List.mem_filter.mp hv').2
    simpa using hvused
  have hremovedLength : removed.length ≤ used.length := by
    calc
      removed.length = removed.toFinset.card :=
        (List.toFinset_card_of_nodup hremovedNodup).symm
      _ ≤ used.toFinset.card := Finset.card_le_card hremovedSubset
      _ ≤ used.length := List.toFinset_card_le used
  have hpartition := List.length_eq_length_filter_add
    (l := xs) (fun v ↦ decide (v ∈ used))
  have hpartition' : xs.length = removed.length +
      (xs.filter fun v ↦ v ∉ used).length := by
    simpa only [removed, ← decide_not] using hpartition
  omega

/-- Every attempted retained fill contains at most the target number of
vertices, so the first `n` attempts consume at most `n * fillSize` vertices. -/
theorem selectedBranchFills_flatten_length_le
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) (n : ℕ) :
    (selectedBranchFills a ha h n).flatten.length ≤
      n * slackFillSize a := by
  induction n with
  | zero => simp [selectedBranchFills]
  | succ n ih =>
      let prior := selectedBranchFills a ha h n
      let candidates :=
        (availableBranchPool a ha h prior.flatten).take (slackBranchScan a)
      let root := selectedRoot a ha h n
      let positives := candidates.filter fun v ↦ (s(root, v), true) ∈ h
      let chosen := if slackFillSize a ≤ positives.length then
        positives.take (slackFillSize a) else []
      have hchosen : chosen.length ≤ slackFillSize a := by
        by_cases hsize : slackFillSize a ≤ positives.length
        · simp [chosen, hsize]
        · simp [chosen, hsize]
      have hstep : selectedBranchFills a ha h (n + 1) =
          prior ++ [chosen] := by
        simp only [selectedBranchFills]
        rfl
      rw [hstep, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
        List.length_append]
      change prior.flatten.length + chosen.length ≤
        (n + 1) * slackFillSize a
      have ih' : prior.flatten.length ≤ n * slackFillSize a := ih
      calc
        prior.flatten.length + chosen.length ≤
            n * slackFillSize a + slackFillSize a :=
          Nat.add_le_add ih' hchosen
        _ = (n + 1) * slackFillSize a := by ring

/-- Reservoir capacity makes every branch candidate list have the full
scheduled length, independently of the branch answers. -/
theorem selectedBranchCandidates_length_of_reservoir_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : ℕ) (hi : i < slackAttemptCount a) :
    (selectedBranchCandidates a ha h i).length = slackBranchScan a := by
  let reservoir := selectedReservoir a ha h
  let used := (selectedBranchFills a ha h i).flatten
  let tail := reservoir.drop (slackAttemptCount a)
  let pool := tail.filter fun v ↦ v ∉ used
  have hresLen : reservoir.length = slackReservoirSize a :=
    selectedReservoir_length_of_ready a ha h hres
  have hused : used.length ≤ i * slackFillSize a := by
    exact selectedBranchFills_flatten_length_le a ha h i
  have hiLe : i ≤ slackAttemptCount a := Nat.le_of_lt hi
  have hused' : used.length ≤ slackAttemptCount a * slackFillSize a := by
    exact hused.trans (Nat.mul_le_mul_right (slackFillSize a) hiLe)
  have htailNodup : tail.Nodup := (selectedReservoir_nodup a ha h).drop
  have hpoolLower : tail.length - used.length ≤ pool.length := by
    exact length_sub_le_filter_not_mem tail used htailNodup
  have htailLen : tail.length =
      slackReservoirSize a - slackAttemptCount a := by
    simp [tail, hresLen]
  have hscanPool : slackBranchScan a ≤ pool.length := by
    rw [htailLen] at hpoolLower
    have hcapEq : slackBranchScan a +
          slackAttemptCount a * slackFillSize a + slackAttemptCount a =
        slackReservoirSize a := by
      unfold slackReservoirSize
      ring
    have hsum : slackBranchScan a + used.length + slackAttemptCount a ≤
        slackReservoirSize a := by
      calc
        slackBranchScan a + used.length + slackAttemptCount a ≤
            slackBranchScan a +
                slackAttemptCount a * slackFillSize a + slackAttemptCount a :=
          Nat.add_le_add_right
            (Nat.add_le_add_left hused' (slackBranchScan a)) _
        _ = slackReservoirSize a := hcapEq
    have hscanUsed : slackBranchScan a + used.length ≤
        slackReservoirSize a - slackAttemptCount a :=
      Nat.le_sub_of_add_le hsum
    have hscanSub : slackBranchScan a ≤
        (slackReservoirSize a - slackAttemptCount a) - used.length :=
      Nat.le_sub_of_add_le hscanUsed
    exact hscanSub.trans hpoolLower
  unfold selectedBranchCandidates availableBranchPool
  change (pool.take (slackBranchScan a)).length = slackBranchScan a
  simp [List.length_take, Nat.min_eq_left hscanPool]

/-- Every scheduled branch candidate is a genuine entry of the reservoir
tail (and hence not one of the reserved roots). -/
theorem selectedBranchCandidate_mem_reservoirDrop_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : Fin (slackAttemptCount a)) (k : Fin (slackBranchScan a)) :
    (selectedBranchCandidates a ha h i.1).getD k.1 (slackCenter a ha) ∈
      (selectedReservoir a ha h).drop (slackAttemptCount a) := by
  have hlen := selectedBranchCandidates_length_of_reservoir_ready
    a ha h hres i.1 i.2
  have hk : k.1 < (selectedBranchCandidates a ha h i.1).length := by
    simpa [hlen] using k.2
  rw [List.getD_eq_getElem _ _ hk]
  have hmem : (selectedBranchCandidates a ha h i.1)[k.1] ∈
      selectedBranchCandidates a ha h i.1 := List.getElem_mem hk
  have havail : (selectedBranchCandidates a ha h i.1)[k.1] ∈
      availableBranchPool a ha h
        (selectedBranchFills a ha h i.1).flatten := by
    exact List.mem_of_mem_take hmem
  have hdrop : (selectedBranchCandidates a ha h i.1)[k.1] ∈
        (selectedReservoir a ha h).drop (slackAttemptCount a) ∧
      (selectedBranchCandidates a ha h i.1)[k.1] ∉
        (selectedBranchFills a ha h i.1).flatten := by
    simpa [availableBranchPool] using havail
  exact hdrop.1

/-- Candidate positions inside one full branch scan are distinct. -/
theorem selectedBranchCandidate_injective_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : Fin (slackAttemptCount a)) :
    Function.Injective (fun k : Fin (slackBranchScan a) ↦
      (selectedBranchCandidates a ha h i.1).getD k.1
        (slackCenter a ha)) := by
  intro k l hkl
  have hlen := selectedBranchCandidates_length_of_reservoir_ready
    a ha h hres i.1 i.2
  have hk : k.1 < (selectedBranchCandidates a ha h i.1).length := by
    simpa [hlen] using k.2
  have hl : l.1 < (selectedBranchCandidates a ha h i.1).length := by
    simpa [hlen] using l.2
  change (selectedBranchCandidates a ha h i.1).getD k.1
      (slackCenter a ha) =
    (selectedBranchCandidates a ha h i.1).getD l.1
      (slackCenter a ha) at hkl
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl] at hkl
  apply Fin.ext
  have hnodup : (selectedBranchCandidates a ha h i.1).Nodup := by
    unfold selectedBranchCandidates
    exact (availableBranchPool_nodup a ha h
      (selectedBranchFills a ha h i.1).flatten).take
  exact hnodup.getElem_inj_iff.mp hkl

/-- The reserved roots are distinct whenever the star reservoir is ready. -/
theorem selectedRoot_injective_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length) :
    Function.Injective (fun i : Fin (slackAttemptCount a) ↦
      selectedRoot a ha h i.1) := by
  intro i j hij
  have hlen := selectedReservoir_length_of_ready a ha h hres
  have hiR : i.1 < (selectedReservoir a ha h).length := by
    rw [hlen]
    exact i.2.trans_le (slackAttemptCount_le_reservoirSize a)
  have hjR : j.1 < (selectedReservoir a ha h).length := by
    rw [hlen]
    exact j.2.trans_le (slackAttemptCount_le_reservoirSize a)
  unfold selectedRoot at hij
  change (selectedReservoir a ha h).getD i.1 (slackCenter a ha) =
    (selectedReservoir a ha h).getD j.1 (slackCenter a ha) at hij
  rw [List.getD_eq_getElem _ _ hiR, List.getD_eq_getElem _ _ hjR] at hij
  apply Fin.ext
  exact (selectedReservoir_nodup a ha h).getElem_inj_iff.mp hij

/-- A selected branch candidate cannot be one of the reserved roots. -/
theorem selectedBranchCandidate_ne_root_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : Fin (slackAttemptCount a)) (k : Fin (slackBranchScan a))
    (j : Fin (slackAttemptCount a)) :
    (selectedBranchCandidates a ha h i.1).getD k.1 (slackCenter a ha) ≠
      selectedRoot a ha h j.1 := by
  have hlen := selectedReservoir_length_of_ready a ha h hres
  have hjR : j.1 < (selectedReservoir a ha h).length := by
    rw [hlen]
    exact j.2.trans_le (slackAttemptCount_le_reservoirSize a)
  have hjTake : selectedRoot a ha h j.1 ∈
      (selectedReservoir a ha h).take (slackAttemptCount a) := by
    rw [selectedRoot, List.getD_eq_getElem _ _ hjR]
    have hjTakeLen : j.1 <
        ((selectedReservoir a ha h).take (slackAttemptCount a)).length := by
      simp only [List.length_take]
      rw [Nat.min_eq_left]
      · exact j.2
      · rw [hlen]
        exact slackAttemptCount_le_reservoirSize a
    have hm := List.getElem_mem hjTakeLen
    simpa using hm
  have hikDrop := selectedBranchCandidate_mem_reservoirDrop_of_ready
    a ha h hres i k
  have hdisjoint : List.Disjoint
      ((selectedReservoir a ha h).take (slackAttemptCount a))
      ((selectedReservoir a ha h).drop (slackAttemptCount a)) :=
    List.disjoint_of_nodup_append (by
      simpa using selectedReservoir_nodup a ha h)
  rw [List.disjoint_left] at hdisjoint
  intro heq
  rw [heq] at hikDrop
  exact hdisjoint hjTake hikDrop

/-- A ready pre-fill transcript canonically instantiates all deterministic
fields of `SlackQueryGeometry`. -/
noncomputable def readySlackQueryGeometry
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (hbranch : slackTrialCount a ≤
      (successfulBranchFills a ha h).length) :
    SlackQueryGeometry a (Vertex (slackQueryBudget a)) where
  center := slackCenter a ha
  starVertex := slackStarVertex a ha
  starVertex_injective := slackStarVertex_injective a ha
  root i := selectedRoot a ha h i.1
  root_injective := selectedRoot_injective_of_ready a ha h hres
  branchVertex i k :=
    (selectedBranchCandidates a ha h i.1).getD k.1 (slackCenter a ha)
  branchVertex_injective i :=
    selectedBranchCandidate_injective_of_ready a ha h hres i
  fillVertex := selectedFillVertex a ha h
  fillVertex_pair_injective :=
    selectedFillVertex_pair_injective a ha h hbranch
  center_ne_star := slackCenter_ne_starVertex a ha
  center_ne_root i := selectedRoot_center_ne_of_ready
    a ha h hres i.1 i.2
  center_ne_branch i k := mem_selectedReservoir_center_ne a ha h
    ((List.drop_sublist _ _).subset
      (selectedBranchCandidate_mem_reservoirDrop_of_ready
        a ha h hres i k))
  center_ne_fill := selectedFillVertex_center_ne_of_ready a ha h hbranch
  branch_ne_root i k j :=
    selectedBranchCandidate_ne_root_of_ready a ha h hres i k j
  fill_ne_root i x j :=
    (selectedRoot_ne_selectedFillVertex_of_ready
      a ha h hres hbranch j.1 j.2 i x).symm

/-! ## Stability of the star-selected reservoir -/

/-- Adding an answer on a coordinate distinct from every centre-star
coordinate does not change the selected positive star indices. -/
theorem positiveStarIndices_cons_eq_of_query_ne
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (q : Query (slackQueryBudget a)) (bit : Bool)
    (hne : ∀ i : Fin (slackStarQueries a),
      q ≠ s(slackCenter a ha, slackStarVertex a ha i)) :
    positiveStarIndices a ha ((q, bit) :: h) =
      positiveStarIndices a ha h := by
  unfold positiveStarIndices
  apply congrArg Finset.toList
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
  by_cases hold : (s(slackCenter a ha, slackStarVertex a ha i), true) ∈ h
  · simp [hold]
  · have hhead :
        (s(slackCenter a ha, slackStarVertex a ha i), true) ≠ (q, bit) := by
      intro heq
      exact hne i (congrArg Prod.fst heq).symm
    simp [hold, hhead]

/-- Consequently the truncated reservoir itself is unchanged. -/
theorem selectedReservoir_cons_eq_of_query_ne
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (q : Query (slackQueryBudget a)) (bit : Bool)
    (hne : ∀ i : Fin (slackStarQueries a),
      q ≠ s(slackCenter a ha, slackStarVertex a ha i)) :
    selectedReservoir a ha ((q, bit) :: h) =
      selectedReservoir a ha h := by
  unfold selectedReservoir
  rw [positiveStarIndices_cons_eq_of_query_ne a ha h q bit hne]

/-- The branch query attached to a ready transcript cannot collide with any
centre-star coordinate. -/
theorem readyBranchQuery_ne_star
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : Fin (slackAttemptCount a)) (k : Fin (slackBranchScan a))
    (j : Fin (slackStarQueries a)) :
    s(selectedRoot a ha h i.1,
        (selectedBranchCandidates a ha h i.1).getD k.1 (slackCenter a ha)) ≠
      s(slackCenter a ha, slackStarVertex a ha j) := by
  intro heq
  have hrootCenter := selectedRoot_center_ne_of_ready
    a ha h hres i.1 i.2
  have hcandMem := selectedBranchCandidate_mem_reservoirDrop_of_ready
    a ha h hres i k
  have hcenterCand : slackCenter a ha ≠
      (selectedBranchCandidates a ha h i.1).getD k.1
        (slackCenter a ha) :=
    mem_selectedReservoir_center_ne a ha h
      ((List.drop_sublist _ _).subset hcandMem)
  simp only [Sym2.eq_iff] at heq
  rcases heq with hsame | hswap
  · exact hrootCenter hsame.1.symm
  · exact hcenterCand hswap.2.symm

/-- One ready branch answer leaves the positive-star reservoir unchanged. -/
theorem selectedReservoir_cons_readyBranchQuery
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (i : Fin (slackAttemptCount a)) (k : Fin (slackBranchScan a))
    (bit : Bool) :
    let q := s(selectedRoot a ha h i.1,
      (selectedBranchCandidates a ha h i.1).getD k.1 (slackCenter a ha))
    selectedReservoir a ha ((q, bit) :: h) = selectedReservoir a ha h := by
  dsimp only
  apply selectedReservoir_cons_eq_of_query_ne
  exact readyBranchQuery_ne_star a ha h hres i k

/-- Adding a query which is new relative to the first `n` complete branch
scans does not change the fills selected from those scans.  This is the
selector-stability induction needed when a later branch answer is prepended
to a transcript. -/
theorem selectedBranchFills_cons_eq_of_query_ne
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (q : Query (slackQueryBudget a)) (bit : Bool)
    (hstar : ∀ j : Fin (slackStarQueries a),
      q ≠ s(slackCenter a ha, slackStarVertex a ha j)) :
    ∀ n : ℕ, n ≤ slackAttemptCount a →
      (∀ j : ℕ, j < n → ∀ k : Fin (slackBranchScan a),
        q ≠ s(selectedRoot a ha h j,
          (selectedBranchCandidates a ha h j).getD k.1
            (slackCenter a ha))) →
      selectedBranchFills a ha ((q, bit) :: h) n =
        selectedBranchFills a ha h n := by
  intro n hn hbranch
  induction n with
  | zero => simp [selectedBranchFills]
  | succ n ih =>
      have hnlt : n < slackAttemptCount a := by omega
      have hprior : selectedBranchFills a ha ((q, bit) :: h) n =
          selectedBranchFills a ha h n := by
        apply ih (Nat.le_of_lt hnlt)
        intro j hj k
        exact hbranch j (hj.trans (Nat.lt_succ_self n)) k
      have hreservoir : selectedReservoir a ha ((q, bit) :: h) =
          selectedReservoir a ha h :=
        selectedReservoir_cons_eq_of_query_ne a ha h q bit hstar
      have hroot : selectedRoot a ha ((q, bit) :: h) n =
          selectedRoot a ha h n := by
        unfold selectedRoot
        rw [hreservoir]
      have havailable :
          availableBranchPool a ha ((q, bit) :: h)
              (selectedBranchFills a ha ((q, bit) :: h) n).flatten =
            availableBranchPool a ha h
              (selectedBranchFills a ha h n).flatten := by
        unfold availableBranchPool
        rw [hprior, hreservoir]
      have hcandidates :
          selectedBranchCandidates a ha ((q, bit) :: h) n =
            selectedBranchCandidates a ha h n := by
        unfold selectedBranchCandidates
        rw [havailable]
      let candidates := selectedBranchCandidates a ha h n
      let root := selectedRoot a ha h n
      have hcandidatesLen : candidates.length = slackBranchScan a := by
        exact selectedBranchCandidates_length_of_reservoir_ready
          a ha h hres n hnlt
      have hpositives :
          (selectedBranchCandidates a ha ((q, bit) :: h) n).filter
              (fun v ↦ (s(selectedRoot a ha ((q, bit) :: h) n, v), true) ∈
                ((q, bit) :: h)) =
            (selectedBranchCandidates a ha h n).filter
              (fun v ↦ (s(selectedRoot a ha h n, v), true) ∈ h) := by
        rw [hcandidates, hroot]
        apply List.filter_congr
        intro v hv
        have hqne : q ≠ s(root, v) := by
          obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
          have hkScan : k < slackBranchScan a := by
            simpa [candidates, hcandidatesLen] using hk
          let kFin : Fin (slackBranchScan a) := ⟨k, hkScan⟩
          have hne := hbranch n (Nat.lt_succ_self n) kFin
          change q ≠ s(root,
            candidates.getD k (slackCenter a ha)) at hne
          rw [List.getD_eq_getElem _ _ hk, hkv] at hne
          exact hne
        have hpairNe : (s(root, v), true) ≠ (q, bit) := by
          intro heq
          exact hqne (congrArg Prod.fst heq).symm
        have hpairNe' :
            (s(selectedRoot a ha h n, v), true) ≠ (q, bit) := by
          simpa [root] using hpairNe
        apply decide_eq_decide.mpr
        constructor
        · intro hm
          exact (List.mem_cons.mp hm).resolve_left hpairNe'
        · intro hm
          exact List.mem_cons_of_mem _ hm
      have havailableOld :
          availableBranchPool a ha ((q, bit) :: h)
              (selectedBranchFills a ha h n).flatten =
            availableBranchPool a ha h
              (selectedBranchFills a ha h n).flatten := by
        simpa only [hprior] using havailable
      have hpositivesOld :
          (List.take (slackBranchScan a)
              (availableBranchPool a ha ((q, bit) :: h)
                (selectedBranchFills a ha h n).flatten)).filter
              (fun v ↦ (s(selectedRoot a ha h n, v), true) ∈
                ((q, bit) :: h)) =
            (List.take (slackBranchScan a)
              (availableBranchPool a ha h
                (selectedBranchFills a ha h n).flatten)).filter
              (fun v ↦ (s(selectedRoot a ha h n, v), true) ∈ h) := by
        simpa only [selectedBranchCandidates, hprior, hroot] using hpositives
      simp only [selectedBranchFills]
      rw [hprior, hroot, hpositivesOld]

/-! ## A canonical chronological branch schedule -/

/-- Branch query at a row-major attempt/candidate coordinate, evaluated in
the supplied transcript. -/
def readyBranchQuery
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (ik : Fin (slackAttemptCount a) × Fin (slackBranchScan a)) :
    Query (slackQueryBudget a) :=
  s(selectedRoot a ha h ik.1.1,
    (selectedBranchCandidates a ha h ik.1.1).getD ik.2.1
      (slackCenter a ha))

/-- Ready branch coordinates are pairwise distinct. -/
theorem readyBranchQuery_injective_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length) :
    Function.Injective (readyBranchQuery a ha h) := by
  intro ik jl heq
  simp only [readyBranchQuery, Sym2.eq_iff] at heq
  rcases heq with hsame | hswap
  · have hi : ik.1 = jl.1 :=
      selectedRoot_injective_of_ready a ha h hres hsame.1
    have hk : ik.2 = jl.2 := by
      apply selectedBranchCandidate_injective_of_ready a ha h hres ik.1
      simpa [hi] using hsame.2
    exact Prod.ext hi hk
  · exact False.elim
      (selectedBranchCandidate_ne_root_of_ready
        a ha h hres ik.1 ik.2 jl.1 hswap.2)

/-- Chronological row-major branch schedule. -/
def readyBranchSchedule
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a))) :
    Fin (slackBranchPhaseQueries a) → Query (slackQueryBudget a) :=
  fun z ↦ readyBranchQuery a ha h (finProdFinEquiv.symm z)

theorem readyBranchSchedule_injective_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length) :
    Function.Injective (readyBranchSchedule a ha h) :=
  (readyBranchQuery_injective_of_ready a ha h hres).comp
    finProdFinEquiv.symm.injective

/-- Every ready branch schedule coordinate is a nonloop. -/
theorem readyBranchSchedule_nonloop_of_ready
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (z : Fin (slackBranchPhaseQueries a)) :
    ¬(readyBranchSchedule a ha h z).IsDiag := by
  let ik := finProdFinEquiv.symm z
  have hne := selectedBranchCandidate_ne_root_of_ready
    a ha h hres ik.1 ik.2 ik.1
  simpa [readyBranchSchedule, readyBranchQuery, Sym2.mk_isDiag_iff, ik]
    using hne.symm

/-- At a transcript whose length lies in the branch phase, the implemented
proposed rule is exactly the corresponding chronological ready schedule. -/
theorem proposedSlackStrategy_eq_readyBranchSchedule
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (m : ℕ) (hlen : h.length = slackStarQueries a + m)
    (hm : m < slackBranchPhaseQueries a) :
    proposedSlackStrategy a ha h =
      readyBranchSchedule a ha h ⟨m, hm⟩ := by
  have hnotStar : ¬ h.length < slackStarQueries a := by omega
  have hinBranch : h.length <
      slackStarQueries a + slackAttemptCount a * slackBranchScan a := by
    unfold slackBranchPhaseQueries at hm
    omega
  unfold proposedSlackStrategy
  rw [dif_neg hnotStar, dif_pos hinBranch]
  simp [hlen, readyBranchSchedule, readyBranchQuery,
    slackBranchPhaseQueries]

/-- Prepending the next chronological branch answer leaves every branch
schedule coordinate up to and including that coordinate unchanged.  The
proof combines reservoir stability with the recursive fill-selector
stability above. -/
theorem readyBranchSchedule_cons_next_eq
    (a : ℕ) (ha : 1 ≤ a)
    (h : Transcript (Query (slackQueryBudget a)))
    (hres : slackReservoirSize a ≤ (positiveStarIndices a ha h).length)
    (m : ℕ) (hm : m < slackBranchPhaseQueries a)
    (bit : Bool) (z : Fin (slackBranchPhaseQueries a))
    (hz : z.1 ≤ m) :
    let current : Fin (slackBranchPhaseQueries a) := ⟨m, hm⟩
    let q := readyBranchSchedule a ha h current
    readyBranchSchedule a ha ((q, bit) :: h) z =
      readyBranchSchedule a ha h z := by
  dsimp only
  let current : Fin (slackBranchPhaseQueries a) := ⟨m, hm⟩
  let currentPair : Fin (slackAttemptCount a) × Fin (slackBranchScan a) :=
    finProdFinEquiv.symm current
  let oldPair : Fin (slackAttemptCount a) × Fin (slackBranchScan a) :=
    finProdFinEquiv.symm z
  let q := readyBranchSchedule a ha h current
  have hstar : ∀ j : Fin (slackStarQueries a),
      q ≠ s(slackCenter a ha, slackStarVertex a ha j) := by
    intro j
    simpa [q, currentPair, readyBranchSchedule, readyBranchQuery] using
      readyBranchQuery_ne_star a ha h hres currentPair.1 currentPair.2 j
  have hbranch : ∀ r : ℕ, r < oldPair.1.1 →
      ∀ k : Fin (slackBranchScan a),
        q ≠ s(selectedRoot a ha h r,
          (selectedBranchCandidates a ha h r).getD k.1
            (slackCenter a ha)) := by
    intro r hr k
    let rFin : Fin (slackAttemptCount a) := ⟨r, hr.trans oldPair.1.2⟩
    let earlierPair : Fin (slackAttemptCount a) × Fin (slackBranchScan a) :=
      (rFin, k)
    have hlinear :
        k.1 + slackBranchScan a * r <
          oldPair.2.1 + slackBranchScan a * oldPair.1.1 := by
      calc
        k.1 + slackBranchScan a * r <
            slackBranchScan a + slackBranchScan a * r :=
          Nat.add_lt_add_right k.2 _
        _ = slackBranchScan a * (r + 1) := by ring
        _ ≤ slackBranchScan a * oldPair.1.1 :=
          Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hr)
        _ ≤ oldPair.2.1 + slackBranchScan a * oldPair.1.1 :=
          Nat.le_add_left _ _
    have hearlierOld : (finProdFinEquiv earlierPair).1 < z.1 := by
      rw [← Equiv.apply_symm_apply finProdFinEquiv z]
      simpa [finProdFinEquiv, earlierPair, rFin] using hlinear
    have hearlierCurrent : (finProdFinEquiv earlierPair).1 < current.1 := by
      exact hearlierOld.trans_le hz
    have hpairsNe : currentPair ≠ earlierPair := by
      intro heq
      have hfin : current = finProdFinEquiv earlierPair := by
        calc
          current = finProdFinEquiv currentPair := by
            symm
            exact Equiv.apply_symm_apply finProdFinEquiv current
          _ = finProdFinEquiv earlierPair := congrArg finProdFinEquiv heq
      have hval := congrArg Fin.val hfin
      exact (Nat.ne_of_gt hearlierCurrent) hval
    have hinj := readyBranchQuery_injective_of_ready a ha h hres
    have hne := hinj.ne hpairsNe
    simpa [q, currentPair, earlierPair, rFin,
      readyBranchSchedule, readyBranchQuery] using hne
  have hfill : selectedBranchFills a ha ((q, bit) :: h) oldPair.1.1 =
      selectedBranchFills a ha h oldPair.1.1 := by
    apply selectedBranchFills_cons_eq_of_query_ne
      a ha h hres q bit hstar oldPair.1.1 oldPair.1.2.le
    exact hbranch
  have hreservoir : selectedReservoir a ha ((q, bit) :: h) =
      selectedReservoir a ha h :=
    selectedReservoir_cons_eq_of_query_ne a ha h q bit hstar
  have hroot : selectedRoot a ha ((q, bit) :: h) oldPair.1.1 =
      selectedRoot a ha h oldPair.1.1 := by
    unfold selectedRoot
    rw [hreservoir]
  have hcandidates :
      selectedBranchCandidates a ha ((q, bit) :: h) oldPair.1.1 =
        selectedBranchCandidates a ha h oldPair.1.1 := by
    unfold selectedBranchCandidates availableBranchPool
    rw [hfill, hreservoir]
  change readyBranchQuery a ha ((q, bit) :: h) oldPair =
    readyBranchQuery a ha h oldPair
  simp only [readyBranchQuery]
  rw [hroot, hcandidates]

/-! ## Legality of the complete raw branch prefix -/

/-- Simultaneous branch induction: the star/branch prefix is legal, and
every query already made is represented either by a centre-star coordinate
or by an earlier coordinate of the ready branch schedule evaluated in the
current transcript. -/
theorem branchStar_legal_and_query_representation
    (a : ℕ) (ha : 1 ≤ a)
    (star : List.Vector Bool (slackStarQueries a))
    (hstar : slackReservoirSize a ≤ star.toList.count true) :
    ∀ (branch : List Bool), branch.length ≤ slackBranchPhaseQueries a →
      let h := replay (proposedSlackStrategy a ha)
        (branch ++ star.toList)
      ProposedPathLegal (proposedSlackStrategy a ha)
          (branch ++ star.toList) ∧
        ∀ r ∈ queries h,
          (∃ j : Fin (slackStarQueries a),
              r = s(slackCenter a ha, slackStarVertex a ha j)) ∨
            ∃ z : Fin (slackBranchPhaseQueries a),
              z.1 < branch.length ∧
                r = readyBranchSchedule a ha h z := by
  intro branch hbranchLen
  induction branch with
  | nil =>
      dsimp only [List.nil_append]
      constructor
      · exact proposedPathLegal_star a ha star
      · intro r hr
        left
        rw [replay_proposedSlackStrategy_star_eq
          a ha star.toList (by simp)] at hr
        have hstarList : star.toList = List.ofFn star.get := by
          rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
        rw [hstarList] at hr
        unfold slackStarContinuation at hr
        rw [BaselineStrategy.replay_reverseSchedule_ofFn] at hr
        simp only [queries, List.map_ofFn, Function.comp_apply] at hr
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hr
        exact ⟨Fin.rev j, by simp [slackStarFinalSchedule]⟩
  | cons bit tail ih =>
      have htailLen : tail.length < slackBranchPhaseQueries a := by
        simpa using hbranchLen
      have ih' := ih (Nat.le_of_lt htailLen)
      let htail := replay (proposedSlackStrategy a ha)
        (tail ++ star.toList)
      have htailLength : htail.length = slackStarQueries a + tail.length := by
        simp [htail, Nat.add_comm]
      have hresTail : slackReservoirSize a ≤
          (positiveStarIndices a ha htail).length := by
        exact hstar.trans (trueStarCount_le_positiveStarIndices_length
          a ha tail star)
      let current : Fin (slackBranchPhaseQueries a) :=
        ⟨tail.length, htailLen⟩
      let q := readyBranchSchedule a ha htail current
      have hpolicy : proposedSlackStrategy a ha htail = q := by
        simpa [q, current] using
          proposedSlackStrategy_eq_readyBranchSchedule
            a ha htail tail.length htailLength htailLen
      have hnonloop : ¬q.IsDiag := by
        exact readyBranchSchedule_nonloop_of_ready
          a ha htail hresTail current
      have hfresh : q ∉ queries htail := by
        intro hmem
        rcases ih'.2 q hmem with hstarQuery | hbranchQuery
        · obtain ⟨j, hqj⟩ := hstarQuery
          let currentPair := finProdFinEquiv.symm current
          have hne := readyBranchQuery_ne_star
            a ha htail hresTail currentPair.1 currentPair.2 j
          exact hne (by
            simpa [q, currentPair, readyBranchSchedule, readyBranchQuery]
              using hqj)
        · obtain ⟨z, hz, hqz⟩ := hbranchQuery
          have hcz : current ≠ z := by
            intro heq
            have hval := congrArg Fin.val heq
            change tail.length = z.1 at hval
            omega
          have hinj := readyBranchSchedule_injective_of_ready
            a ha htail hresTail
          exact (hinj.ne hcz) (by simpa [q] using hqz)
      have hreplay : replay (proposedSlackStrategy a ha)
          ((bit :: tail) ++ star.toList) = (q, bit) :: htail := by
        simp only [List.cons_append, replay_cons]
        rw [hpolicy]
      have hreplay' : replay (proposedSlackStrategy a ha)
          (bit :: (tail ++ star.toList)) = (q, bit) :: htail := by
        simpa only [List.cons_append] using hreplay
      have hstable (z : Fin (slackBranchPhaseQueries a))
          (hz : z.1 ≤ tail.length) :
          readyBranchSchedule a ha ((q, bit) :: htail) z =
            readyBranchSchedule a ha htail z := by
        exact readyBranchSchedule_cons_next_eq
          a ha htail hresTail tail.length htailLen bit z hz
      dsimp only [List.cons_append]
      constructor
      · rw [ProposedPathLegal]
        refine ⟨⟨?_, ?_⟩, ih'.1⟩
        · change ¬(proposedSlackStrategy a ha htail).IsDiag
          rw [hpolicy]
          exact hnonloop
        · change proposedSlackStrategy a ha htail ∉ queries htail
          rw [hpolicy]
          exact hfresh
      · intro r hr
        rw [hreplay'] at hr ⊢
        simp only [queries, List.map_cons, List.mem_cons] at hr
        rcases hr with rfl | hr
        · right
          refine ⟨current, by simp [current], ?_⟩
          exact (hstable current (by simp [current])).symm
        · rcases ih'.2 r hr with hstarQuery | hbranchQuery
          · exact Or.inl hstarQuery
          · right
            obtain ⟨z, hz, hrz⟩ := hbranchQuery
            refine ⟨z, hz.trans (Nat.lt_succ_self _), ?_⟩
            rw [hstable z hz.le]
            exact hrz

/-- Coordinatewise version of the branch replay invariant.  At every
chronological branch coordinate already exposed, the answer paired with the
final (history-dependent) ready schedule is the corresponding newest-first
raw branch bit. -/
theorem branchStar_readySchedule_getD_mem
    (a : ℕ) (ha : 1 ≤ a)
    (star : List.Vector Bool (slackStarQueries a))
    (hstar : slackReservoirSize a ≤ star.toList.count true) :
    ∀ (branch : List Bool), branch.length ≤ slackBranchPhaseQueries a →
      let h := replay (proposedSlackStrategy a ha)
        (branch ++ star.toList)
      ∀ (z : Fin (slackBranchPhaseQueries a)), z.1 < branch.length →
        (readyBranchSchedule a ha h z,
          branch.getD (branch.length - 1 - z.1) false) ∈ h := by
  intro branch hbranchLen
  induction branch with
  | nil =>
      dsimp only [List.nil_append]
      intro z hz
      exact (Nat.not_lt_zero z.1 (by simpa only [List.length_nil] using hz)).elim
  | cons bit tail ih =>
      have htailLen : tail.length < slackBranchPhaseQueries a := by
        simpa using hbranchLen
      have ih' := ih (Nat.le_of_lt htailLen)
      let htail := replay (proposedSlackStrategy a ha)
        (tail ++ star.toList)
      have htailLength : htail.length = slackStarQueries a + tail.length := by
        simp [htail, Nat.add_comm]
      have hresTail : slackReservoirSize a ≤
          (positiveStarIndices a ha htail).length := by
        exact hstar.trans (trueStarCount_le_positiveStarIndices_length
          a ha tail star)
      let current : Fin (slackBranchPhaseQueries a) :=
        ⟨tail.length, htailLen⟩
      let q := readyBranchSchedule a ha htail current
      have hpolicy : proposedSlackStrategy a ha htail = q := by
        simpa [q, current] using
          proposedSlackStrategy_eq_readyBranchSchedule
            a ha htail tail.length htailLength htailLen
      have hreplay : replay (proposedSlackStrategy a ha)
          (bit :: (tail ++ star.toList)) = (q, bit) :: htail := by
        simp only [List.cons_append, replay_cons]
        rw [hpolicy]
      have hstable (z : Fin (slackBranchPhaseQueries a))
          (hz : z.1 ≤ tail.length) :
          readyBranchSchedule a ha ((q, bit) :: htail) z =
            readyBranchSchedule a ha htail z := by
        exact readyBranchSchedule_cons_next_eq
          a ha htail hresTail tail.length htailLen bit z hz
      dsimp only [List.cons_append]
      intro z hz
      simp only [List.length_cons] at hz
      rw [hreplay]
      by_cases hcurrent : z.1 = tail.length
      · have hzCurrent : z = current := Fin.ext hcurrent
        subst z
        have hindex : (bit :: tail).length - 1 - current.1 = 0 := by
          simp [current]
        rw [hindex, List.getD_cons_zero]
        rw [hstable current (by simp [current])]
        change (q, bit) ∈ (q, bit) :: htail
        exact List.mem_cons_self
      · have hzTail : z.1 < tail.length := by omega
        have hmem := ih' z hzTail
        have hindex : (bit :: tail).length - 1 - z.1 =
            (tail.length - 1 - z.1) + 1 := by
          simp only [List.length_cons]
          omega
        rw [hindex, List.getD_cons_succ]
        rw [hstable z hzTail.le]
        exact List.mem_cons_of_mem _ hmem

/-- Every raw newest-first branch answer occurs in the completed pre-fill
replay at the same coordinate of the final stable ready schedule. -/
theorem slackBaseBranch_get_mem_readySchedule
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true)
    (j : Fin (slackBranchPhaseQueries a)) :
    (readyBranchSchedule a ha
        (replay (proposedSlackStrategy a ha) base.toList) (Fin.rev j),
      (slackBaseBranchAnswerVector a base).get j) ∈
      replay (proposedSlackStrategy a ha) base.toList := by
  let branch := (slackBaseBranchAnswerVector a base).toList
  let star := slackBaseStarAnswerVector a base
  have hdecomp : branch ++ star.toList = base.toList := by
    exact slackBase_branch_star_decomposition a base
  have hjBranch : (Fin.rev j).1 < branch.length := by
    simpa [branch] using (Fin.rev j).2
  have hmem := branchStar_readySchedule_getD_mem
    a ha star hstar branch (by simp [branch]) (Fin.rev j) hjBranch
  rw [hdecomp] at hmem
  have hindex : branch.length - 1 - (Fin.rev j).1 = j.1 := by
    have hrev : (Fin.rev j).1 =
        slackBranchPhaseQueries a - (j.1 + 1) := rfl
    simp only [branch, List.Vector.toList_length]
    rw [hrev]
    omega
  rw [hindex] at hmem
  have hj : j.1 < branch.length := by simp [branch]
  rw [List.getD_eq_getElem _ _ hj] at hmem
  exact hmem

/-- Raw star supply alone makes the entire centre-star plus branch scan path
legal.  No semantic legality or selector-readiness premise remains. -/
theorem proposedPathLegal_branchStar_of_starSupply
    (a : ℕ) (ha : 1 ≤ a)
    (base : List.Vector Bool (slackFillStart a))
    (hstar : slackReservoirSize a ≤
      (slackBaseStarAnswerVector a base).toList.count true) :
    ProposedPathLegal (proposedSlackStrategy a ha) base.toList := by
  rw [← slackBase_branch_star_decomposition a base]
  exact (branchStar_legal_and_query_representation
    a ha (slackBaseStarAnswerVector a base) hstar
    (slackBaseBranchAnswerVector a base).toList (by simp)).1

end
end UpperPathGeometry
end OnlineRamsey
