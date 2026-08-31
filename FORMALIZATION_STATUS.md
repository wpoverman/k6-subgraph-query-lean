# Formalization status for the `K₆` subgraph-query result

## Headline

The cubic-scale `K₆` subgraph-query theorem is now proved end to end in Lean
for the standard countably infinite vertex game. The final theorem is

```lean
OnlineRamsey.InfiniteUnconditional.exists_infiniteCubicPowerLaw
```

with type

```lean
∃ c : ℝ≥0∞, 0 < c ∧
    QueryComplexity.FiniteCubicPowerLaw
    InfinitePolicyBridge.InfiniteAchievable c
    (((UpperBudgetUniversal.slackUniversalUpperConstant * 2 ^ 10 : ℕ) : ℝ≥0∞))
```

There are no theorem hypotheses. Since

```lean
UpperBudgetUniversal.slackUniversalUpperConstant
  = 16384 + 769 * K6Upper.momentAmplification
```

and `K6Upper.momentAmplification = 184320`, the displayed upper constant is
`145160667136`.

## Exact meaning

`InfinitePolicyBridge.InfiniteAchievable p N` is the game in which:

- vertices are the natural numbers;
- queries are unordered pairs represented by `Sym2 ℕ`;
- a deterministic adaptive strategy makes exactly `N` queries;
- admissibility requires distinct, non-diagonal queries on every answer path;
- probability is the exact finite Bernoulli sum over length-`N` answer
  vectors; and
- success means that the positive transcript contains an injectively labelled
  copy of `K₆`, with probability at least `1/2`.

This is a positive-horizon, deterministic, exact-`N` formulation.  Its answer
sum is the finite-horizon operational Bernoulli law obtained from `G(ℕ,p)`;
no infinite product measure is constructed.  Exact `N` is equivalent to the
paper's at-most-`N` convention by fresh padding, formalized canonically by
`BudgetMonotonicity.achievable_mono_budget` and transferred through the
bridge.  Deterministic policies are without loss for the existential
threshold after conditioning on a private random seed and fixing one seed
with at least the average success probability.

The theorem `InfinitePolicyBridge.infiniteAchievable_iff_achievable` proves
that this is equivalent, for every density and horizon, to the canonical
finite game `QueryComplexity.Achievable p N`, in which:

- the available vertices are `Fin (2*N)`;
- a deterministic adaptive strategy makes exactly `N` unordered-pair queries;
- admissibility requires distinct, non-diagonal queries on every answer path;
- the board has the explicit finite Bernoulli(`p`) product mass; and
- success means that the positive transcript contains an injectively labelled
  copy of `K₆`, with required probability at least `1/2`.

For every `0 < q ≤ 1`,
`FiniteCubicPowerLaw InfiniteAchievable c C` chooses the least `N` for which
`InfiniteAchievable (q^3) N` and proves

```text
c ≤ N q^10 ≤ C.
```

Thus it is the denominator-free `p=q³` formulation of
`f(K₆,p)=Θ(p^(-10/3))`. The theorem is not merely a conditional implication
from assumed lower and upper estimates: both estimates are instantiated in the
dependency chain below.

## Final proof chain

| Layer | Principal theorem/module | Checked conclusion |
| --- | --- | --- |
| Finite classification | `K6Prefix.nineEdgePrefixClassification` | All 5,005 labelled nine-edge graphs, all 21 unlabelled types, and the three exceptional orbits. |
| Lower graph counting | `UnifiedAllCasesHCount` | One checked bound covering every ordinary and exceptional prefix case. |
| Lower analytic limit | `SmallEllMainCoefficient`, `SmallEllErrorTendsToZero` | A fixed positive small parameter makes the main term and all error terms fall below the threshold margin. |
| Unconditional lower bound | `UnconditionalLower.exists_global_queryBudget_lower_constant` | `∃ c>0`, every achievable budget satisfies `c ≤ N q^10`. |
| Concrete upper strategy | `UpperStrategy` | A total legalized star/reservoir/branch/fill policy and a pathwise `K₆` success certificate. |
| Branch replay geometry | `UpperPathGeometry.slackBaseBranch_get_mem_readySchedule` | Raw branch answers use the same stable coordinates as the completed adaptive allocator. |
| Allocator readiness | `SlackBranchReady.branch_ready_of_rawReady_of_dominates` | Raw scan supply yields enough successful retained fills. |
| Deterministic upper assembly | `UpperDeterministicAssembly` | Supply implies full-path legality and a concrete coupled success path, with no replay premise left unproved. |
| Upper probability | `UpperProbabilityAssembly.achievable_slack_of_supplySuccess_implies_concrete` | Exact finite Bernoulli estimates give success probability at least `1/2`. |
| Density and budget | `UpperHypothesisPackaging` | Every `0<q≤1` gets an achievable `O(q^-10)` budget. |
| Final minimization | `UnconditionalUpper.exists_finiteCubicPowerLaw` | The least achievable budget lies between the fixed positive lower constant and explicit finite upper constant. |
| Infinite-policy bridge | `InfinitePolicyBridge.infiniteAchievable_iff_achievable` | Coherent first-appearance naming gives success-preserving transformations in both directions and exact equivalence of achievable budgets. |
| Infinite final theorem | `InfiniteUnconditional.exists_infiniteCubicPowerLaw` | The same least-budget power law holds in the standard countably infinite formulation. |

## The infinite-policy bridge

The reduction is policy-level rather than a separate relabeling chosen at
each terminal transcript.  For a newest-first transcript, Lean builds the
endpoint list in chronological order and names each vertex by the index of
its first occurrence.  Appending a new query cannot change an old index.  The
central coherence statements are

```lean
InfinitePolicyBridge.canonicalPath_eq_relabelCompletedTranscript
InfinitePolicyBridge.replay_canonicalPolicy
```

They say that one deterministic policy on `Fin (2*N)` reproduces the
pointwise first-appearance relabeling on every answer path.  Subsequent lemmas
prove preservation of freshness and nonloops, transport labelled `K₆`
copies, and compare the Bernoulli answer-vector probabilities in the required
direction.  Conversely, a canonical finite policy is
transported along `Fin (2*N) ↪ ℕ`, again with an exact replay identity.
The two constructions give

```lean
InfinitePolicyBridge.infiniteAchievable_iff_achievable
```

including the zero-budget edge case.  `Nat.find_congr'` then identifies the
least winning budgets, so the finite-board constants transfer unchanged.

## Verification commands

```sh
lake build
lake exe verify-k6-prefix
lake -R --no-cache build OnlineRamsey.InfiniteUnconditional
```

The last command rebuilds every dependency of the unconditional final theorem
without using cached project objects.

## Trust audit

The checked source has no `sorry`, `admit`, or user-declared axioms. The final
theorem uses the standard classical and quotient principles supplied by Lean
and Mathlib. The separate exhaustive classification is evaluated with
`native_decide`, adding the usual trust in Lean's native evaluator/compiler for
that computation.
