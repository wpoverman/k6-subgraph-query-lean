import Std

namespace K6Prefix

/-!
# The finite nine-edge prefix certificate for the K6 subgraph-query argument

This file formalizes the exact finite computation in Lemma 4.1 and Appendix A
of `k6_subgraph_query_proof.pdf`. A six-vertex graph is a 15-bit natural number.
The dynamic program evaluates the recurrence A_b on every relevant state, then
checks all 5005 labeled graphs with nine edges.
-/

abbrev GraphMask := Nat
abbrev VertexMask := Nat

def vertexCount : Nat := 6
def edgeCount : Nat := 15
def graphCount : Nat := 32768       -- 2^15
def vertexSetCount : Nat := 64      -- 2^6
def stateCount : Nat := vertexSetCount * graphCount
def negInf : Int := -1000000

/-- The fixed ordering of the 15 edges of K6. -/
def edgePairs : Array (Nat × Nat) := #[
  (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
  (1, 2), (1, 3), (1, 4), (1, 5),
  (2, 3), (2, 4), (2, 5),
  (3, 4), (3, 5),
  (4, 5)
]

def bit (i : Nat) : Nat := Nat.shiftLeft 1 i

def countBits (width n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in [0:width] do
    if n.testBit i then
      total := total + 1
  return total

def allowedEdgeMasks : Array GraphMask := Id.run do
  let mut result := Array.replicate vertexSetCount 0
  for vertices in [0:vertexSetCount] do
    let mut edges := 0
    for i in [0:edgeCount] do
      let (u, v) := edgePairs[i]!
      if vertices.testBit u && vertices.testBit v then
        edges := edges ||| bit i
    result := result.set! vertices edges
  return result

def stateIndex (vertices : VertexMask) (edges : GraphMask) : Nat :=
  vertices * graphCount + edges

def addOne (a : Int) : Int :=
  if a = negInf then negInf else a + 1

/--
Build the table for A_b from the already-computed table for A_(b-1).

The table is filled in increasing `(vertices, edges)` order. Every edge-deletion
child has a smaller edge mask. Every pair-deletion child is read from the table
for `b-1`. Thus this is a terminating bottom-up implementation of recurrence
(4.1), with no untrusted memoization or external certificate.
-/
def buildTable (b : Nat) (previous : Array Int) : Array Int := Id.run do
  let mut table := Array.replicate stateCount negInf
  for vertices in [0:vertexSetCount] do
    let allowed := allowedEdgeMasks[vertices]!
    for edges in [0:graphCount] do
      if (edges &&& allowed) = edges then
        let index := stateIndex vertices edges
        if edges = 0 then
          let base := if countBits vertexCount vertices ≤ b then 0 else negInf
          table := table.set! index base
        else
          let mut deletion := (1000000 : Int)
          let mut pairDeletion := negInf
          for i in [0:edgeCount] do
            if edges.testBit i then
              let deletionChild := table[stateIndex vertices (edges - bit i)]!
              deletion := min deletion (addOne deletionChild)
              if b > 0 then
                let (u, v) := edgePairs[i]!
                let childVertices := vertices - bit u - bit v
                let childEdges := edges &&& allowedEdgeMasks[childVertices]!
                let pairChild := previous[stateIndex childVertices childEdges]!
                pairDeletion := max pairDeletion (addOne pairChild)
          table := table.set! index (max deletion pairDeletion)
  return table

def table0 : Array Int := buildTable 0 #[]
def table1 : Array Int := buildTable 1 table0
def table2 : Array Int := buildTable 2 table1
def table3 : Array Int := buildTable 3 table2

def A3 (edges : GraphMask) : Int :=
  table3[stateIndex (vertexSetCount - 1) edges]!

def findEdgeIndex (u v : Nat) : Nat := Id.run do
  let a := min u v
  let b := max u v
  for i in [0:edgeCount] do
    if edgePairs[i]! = (a, b) then
      return i
  return edgeCount

def maskOfPairs (pairs : Array (Nat × Nat)) : GraphMask := Id.run do
  let mut result := 0
  for pair in pairs do
    result := result ||| bit (findEdgeIndex pair.1 pair.2)
  return result

def h3 : GraphMask := maskOfPairs #[
  (0, 1), (0, 2), (1, 2),
  (0, 3), (0, 4), (0, 5),
  (1, 4), (1, 5), (2, 5)
]

def k5MinusEdgePlusIsolate : GraphMask := maskOfPairs #[
  (0, 2), (0, 3), (0, 4),
  (1, 2), (1, 3), (1, 4),
  (2, 3), (2, 4), (3, 4)
]

def b4 : GraphMask := maskOfPairs #[
  (0, 1),
  (0, 2), (0, 3), (0, 4), (0, 5),
  (1, 2), (1, 3), (1, 4), (1, 5)
]

def permutations6 : Array (Array Nat) := Id.run do
  let mut result := #[]
  for a in [0:vertexCount] do
    for b in [0:vertexCount] do
      for c in [0:vertexCount] do
        for d in [0:vertexCount] do
          for e in [0:vertexCount] do
            for f in [0:vertexCount] do
              if a != b && a != c && a != d && a != e && a != f &&
                 b != c && b != d && b != e && b != f &&
                 c != d && c != e && c != f &&
                 d != e && d != f && e != f then
                result := result.push #[a, b, c, d, e, f]
  return result

def relabel (edges : GraphMask) (permutation : Array Nat) : GraphMask := Id.run do
  let mut result := 0
  for i in [0:edgeCount] do
    if edges.testBit i then
      let (u, v) := edgePairs[i]!
      let newIndex := findEdgeIndex permutation[u]! permutation[v]!
      result := result ||| bit newIndex
  return result

def orbit (representative : GraphMask) : Array Bool := Id.run do
  let mut result := Array.replicate graphCount false
  for permutation in permutations6 do
    result := result.set! (relabel representative permutation) true
  return result

def h3Orbit : Array Bool := orbit h3
def k5MinusEdgePlusIsolateOrbit : Array Bool := orbit k5MinusEdgePlusIsolate
def b4Orbit : Array Bool := orbit b4

def inExceptionalOrbit (edges : GraphMask) : Bool :=
  h3Orbit[edges]! ||
  k5MinusEdgePlusIsolateOrbit[edges]! ||
  b4Orbit[edges]!

def countTrue (values : Array Bool) : Nat := Id.run do
  let mut total := 0
  for value in values do
    if value then total := total + 1
  return total

/-- Categories are -infinity, 3, 4, 5, and 6, in that order. -/
def exponentCategory (value : Int) : Nat :=
  if value = negInf then 0
  else if value = 3 then 1
  else if value = 4 then 2
  else if value = 5 then 3
  else if value = 6 then 4
  else 5

def labeledHistogram : Array Nat := Id.run do
  let mut result := Array.replicate 6 0
  for edges in [0:graphCount] do
    if countBits edgeCount edges = 9 then
      let category := exponentCategory (A3 edges)
      result := result.set! category (result[category]! + 1)
  return result

def canonicalRelabeling (edges : GraphMask) : GraphMask := Id.run do
  let mut best := edges
  for permutation in permutations6 do
    best := min best (relabel edges permutation)
  return best

def unlabeledHistogram : Array Nat := Id.run do
  let mut result := Array.replicate 6 0
  for edges in [0:graphCount] do
    if countBits edgeCount edges = 9 && canonicalRelabeling edges = edges then
      let category := exponentCategory (A3 edges)
      result := result.set! category (result[category]! + 1)
  return result

def nineEdgeCount : Nat := Id.run do
  let mut total := 0
  for edges in [0:graphCount] do
    if countBits edgeCount edges = 9 then total := total + 1
  return total

def exceptionAgreement : Bool := Id.run do
  for edges in [0:graphCount] do
    if countBits edgeCount edges = 9 then
      let belowFour := decide (A3 edges < 4)
      if belowFour != inExceptionalOrbit edges then
        return false
  return true

def degreeHistogram (edges : GraphMask) : Array Nat := Id.run do
  let mut degrees := Array.replicate vertexCount 0
  for i in [0:edgeCount] do
    if edges.testBit i then
      let (u, v) := edgePairs[i]!
      degrees := degrees.set! u (degrees[u]! + 1)
      degrees := degrees.set! v (degrees[v]! + 1)
  let mut result := Array.replicate vertexCount 0
  for degree in degrees do
    result := result.set! degree (result[degree]! + 1)
  return result

/--
The complete executable certificate for Lemma 4.1. Besides the labeled and
unlabeled histograms, it checks the exact exceptional-orbit equality, all three
orbit sizes, all three degree multisets, and the count C(15,9) = 5005.
-/
def classificationCheck : Bool :=
  labeledHistogram = #[75, 360, 3180, 1380, 10, 0] &&
  unlabeledHistogram = #[2, 1, 10, 7, 1, 0] &&
  nineEdgeCount = 5005 &&
  permutations6.size = 720 &&
  countTrue h3Orbit = 360 &&
  countTrue k5MinusEdgePlusIsolateOrbit = 60 &&
  countTrue b4Orbit = 15 &&
  degreeHistogram h3 = #[0, 1, 1, 2, 1, 1] &&
  degreeHistogram k5MinusEdgePlusIsolate = #[1, 0, 0, 2, 3, 0] &&
  degreeHistogram b4 = #[0, 0, 4, 0, 0, 2] &&
  exceptionAgreement

/-- Lean-checked finite classification from Lemma 4.1 and Appendix A. -/
theorem nineEdgePrefixClassification : classificationCheck = true := by
  native_decide

end K6Prefix
