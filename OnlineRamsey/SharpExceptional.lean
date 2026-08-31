import OnlineRamsey.CentralK4Bridge
import OnlineRamsey.ExceptionalLabelled

/-!
# Sharp labelled bounds for the exceptional prefixes

This file composes the exact labelled-copy encodings with the deterministic
host charges.  The statements are deliberately about labelled copies, which
is the convention used by the executable prefix recurrence.
-/

namespace OnlineRamsey

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical labelled half-graph has the paper-scale bound on every
queried subgraph of a certified host. -/
theorem HostGood.subgraphLabelledH3_sharp_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    labelledCopies F H3Graph ≤
      2 * ((6 * c₂ * (2 * L) * M) * edgeCount F) := by
  calc
    labelledCopies F H3Graph ≤ 2 * h3Charge F :=
      labelledCopies_H3_le_two_mul_charge F
    _ ≤ 2 * ((6 * c₂ * (2 * L) * M) * edgeCount F) :=
      Nat.mul_le_mul_left 2
        (HostGood.subgraphH3Charge_sharp_le hD h hFG hE)

/-- The isolated sixth label costs exactly one ambient-vertex factor after
the sharp five-vertex estimate. -/
theorem HostGood.subgraphLabelledK5MinusEdgeIsolated_sharp_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    labelledCopies F K5MinusEdgeIsolatedGraph ≤
      ((24 * c₃ * (2 * L * L)) * edgeCount F) * Fintype.card V := by
  calc
    labelledCopies F K5MinusEdgeIsolatedGraph ≤
        labelledCopies F K5MinusEdgeGraph * Fintype.card V :=
      labelledCopies_K5MinusEdgeIsolated_le F
    _ ≤ ((24 * c₃ * (2 * L * L)) * edgeCount F) * Fintype.card V :=
      Nat.mul_le_mul_right _
        (HostGood.subgraphLabelledK5MinusEdge_sharp_le hD h hFG hE)

/-- The ten-edge `Q` completion is controlled directly by the pair-codegree
charge.  This is the deterministic estimate needed after exposing the tenth
edge of the shifted `B₄` prefix. -/
theorem HostGood.subgraphLabelledQ_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) :
    labelledCopies F QGraph ≤
      (c₂ * c₂ * (2 * c₂ * c₂)) * edgeCount F := by
  exact (labelledCopies_Q_le_qCharge F).trans
    (HostGood.subgraphQCharge_le h hFG)

/-- Paper-scale `Q` estimate.  Rather than bounding the common-neighborhood
edge incidence once more by a pair-codegree square, retain its exact rooted
`K₄` interpretation and apply the linear labelled-`K₄` bound.  This saves
two powers of the pair-codegree cutoff and is the estimate needed for the
shifted `B₄` branch. -/
theorem HostGood.subgraphLabelledQ_sharp_le
    {F G : SimpleGraph V} {M D L c₂ c₃ : ℕ}
    (hD : 0 < D)
    (h : RandomBoard.HostGood G M D L c₂ c₃)
    (hFG : F ≤ G) (hE : edgeCount F ≤ M) :
    labelledCopies F QGraph ≤
      (c₂ * c₂ * (24 * (2 * L * L))) * edgeCount F := by
  calc
    labelledCopies F QGraph ≤ qCharge F :=
      labelledCopies_Q_le_qCharge F
    _ ≤ (c₂ * c₂) * centralK4Mass F :=
      qCharge_le F (HostGood.subgraphPairCodegreeLE h hFG)
    _ ≤ (c₂ * c₂) * labelledCopies F K4Graph :=
      Nat.mul_le_mul_left _ (centralK4Mass_le_labelledCopies_k4 F)
    _ ≤ (c₂ * c₂) *
        ((24 * (2 * L * L)) * edgeCount F) :=
      Nat.mul_le_mul_left _
        (HostGood.subgraphLabelledK4_sharp_le hD h hFG hE)
    _ = (c₂ * c₂ * (24 * (2 * L * L))) * edgeCount F := by
      ring

end OnlineRamsey
