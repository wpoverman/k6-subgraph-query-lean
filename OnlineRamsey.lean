import OnlineRamsey.AdaptiveQuery
import OnlineRamsey.AdaptiveTail
import OnlineRamsey.Amplification
import OnlineRamsey.Assembly
import OnlineRamsey.AsymptoticScale
import OnlineRamsey.Deterministic
import OnlineRamsey.HostCounting
import OnlineRamsey.InfiniteUnconditional
import OnlineRamsey.K4MomentBounds
import OnlineRamsey.K4Moments
import OnlineRamsey.K4OneTrial
import OnlineRamsey.LabelledCharges
import OnlineRamsey.LowerAssembly
import OnlineRamsey.OrderedPrefix
import OnlineRamsey.PolicyRelabeling
import OnlineRamsey.PrefixSoundness
import OnlineRamsey.QueryComplexity
import OnlineRamsey.QueryGame
import OnlineRamsey.RandomBoard
import OnlineRamsey.UnconditionalUpper
import OnlineRamsey.UpperBound

/-!
# Formalization of the `K₆` subgraph-query argument

This root module collects the Mathlib development surrounding the independently
verified finite prefix certificate in `K6Prefix.lean`.  In particular it
imports the unconditional end-to-end theorem in both the canonical finite
form and the standard countably infinite form,
`InfiniteUnconditional.exists_infiniteCubicPowerLaw`; see
`FORMALIZATION_STATUS.md` for its exact finite, denominator-free statement.
-/
