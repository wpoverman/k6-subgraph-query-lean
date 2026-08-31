import K6Prefix

def main : IO Unit := do
  IO.println "K6 finite-prefix certificate"
  IO.println s!"  Lean theorem: {K6Prefix.classificationCheck}"
  IO.println s!"  nine-edge labeled graphs: {K6Prefix.nineEdgeCount}"
  IO.println s!"  labeled A3 histogram [-inf,3,4,5,6,other]: {K6Prefix.labeledHistogram}"
  IO.println s!"  unlabeled A3 histogram [-inf,3,4,5,6,other]: {K6Prefix.unlabeledHistogram}"
  IO.println (s!"  exceptional orbit sizes [H3,K5-e+I,B4]: " ++
    s!"[{K6Prefix.countTrue K6Prefix.h3Orbit}, " ++
    s!"{K6Prefix.countTrue K6Prefix.k5MinusEdgePlusIsolateOrbit}, " ++
    s!"{K6Prefix.countTrue K6Prefix.b4Orbit}]")
