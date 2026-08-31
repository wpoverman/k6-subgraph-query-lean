# Lean 4 formalization of the `K₆` subgraph-query theorem

This Lean 4.24.0/Mathlib project contains an unconditional, end-to-end
formalization of the `K₆` subgraph-query power law in the standard
countably infinite vertex game. Its final theorem is

```lean
OnlineRamsey.InfiniteUnconditional.exists_infiniteCubicPowerLaw
```

and has no hypotheses:

```lean
∃ c : ℝ≥0∞, 0 < c ∧
  QueryComplexity.FiniteCubicPowerLaw
    InfinitePolicyBridge.InfiniteAchievable c
    (((UpperBudgetUniversal.slackUniversalUpperConstant * 2 ^ 10 : ℕ) : ℝ≥0∞))
```

Here `InfiniteAchievable p N` means that an admissible deterministic adaptive
strategy on unordered pairs of natural-number vertices makes `N` distinct
nonloop queries and finds a labelled `K₆` with probability at least `1/2`.
Its finite-horizon Bernoulli law is the exact finite sum over the `2^N`
possible answer vectors.  This is the operational law induced by querying
`G(ℕ,p)` for a finite number of fresh coordinates; the development does not
construct an infinite product probability space.

The formal definition uses exactly `N` queries.  This agrees with the usual
"at most `N`" convention because a successful shorter policy can be padded
with fresh nonloop queries without destroying a found clique;
`BudgetMonotonicity.achievable_mono_budget` proves this on the canonical side,
and the policy bridge transfers it to the infinite formulation.  Policies are
deterministic, as is standard without loss for an existential success
threshold: condition on the private random seed and fix a seed whose success
is at least the average.

The predicate
`FiniteCubicPowerLaw` says that, for every `0 < q ≤ 1`, the least achievable
budget at density `p = q³`, multiplied by `q¹⁰`, is bounded between a fixed
positive lower constant and a fixed finite upper constant. This is the
denominator-free formulation of

```text
f(K₆,p) = Θ(p^(-10/3)).
```

The explicit upper constant is

```text
(16384 + 769 * 184320) * 2^10 = 145160667136.
```

The lower constant is existential but is proved strictly positive.

The policy bridge is itself machine checked.  Along every answer path it
names vertices by first appearance, proves that one coherent policy on
`Fin (2*N)` has exactly the relabelled replay transcript, and establishes

```lean
InfinitePolicyBridge.infiniteAchievable_iff_achievable
```

for every `p` and `N`.  The two per-policy probability comparisons are
success-preserving inequalities, which are exactly what each direction of
achievability requires.  The reverse implication uses the fixed inclusion
`Fin (2*N) ↪ ℕ`.  Thus the infinite endpoint is not merely an informal
interpretation of the finite theorem.

## What Lean checks

The proof chain includes all of the following.

- Exhaustive classification of all `C(15,9) = 5005` labelled nine-edge
  graphs on six vertices, including all 21 unlabelled types and the exact
  exceptional orbits `H₃`, `(K₅-e) ⊎ K₁`, and `B₄`.
- Exact finite product laws for fresh adaptive queries, finite random-host
  bounds, stopping-history factorization, the four prefix cases, and the
  small-density error limit used for the lower bound.
- An unconditional positive normalized-budget obstruction:
  `UnconditionalLower.exists_global_queryBudget_lower_constant`.
- Exact first and second moments for the auxiliary `K₄` count,
  Paley--Zygmund, repeated-trial amplification, and monotonicity throughout
  every density bucket.
- A concrete globally admissible star/reservoir/branch/fill strategy, including
  query-budget bounds, reservoir and branch supply estimates, selector
  stability under adaptive replay, fill-query legality, and the pathwise
  embedding of a successful trial into a `K₆`.
- Arbitrary-density rounding and final minimization bookkeeping.

The last upper-bound chain is exposed in these modules:

```text
UpperPathGeometry
  → SlackBranchReady
  → UpperDeterministicAssembly
  → UpperProbabilityAssembly
  → UnconditionalUpper
```

The infinite-policy endpoint then adds

```text
InfinitePolicyBridge
  → InfiniteUnconditional
```

The delicate replay step is
`UpperPathGeometry.slackBaseBranch_get_mem_readySchedule`: it proves that a raw
newest-first branch answer occurs at the same stable coordinate selected by
the completed adaptive allocator. This discharges the final selector-alignment
premise rather than assuming it.

## Build and verify

The project-local toolchain is pinned by `lean-toolchain`; no global Lean
default needs to be changed.

```sh
lean --version
lake build
lake exe verify-k6-prefix
```

To replay every dependency of the final theorem without relying on cached
project objects:

```sh
lake -R --no-cache build OnlineRamsey.InfiniteUnconditional
```

The executable prints the independently checked finite-classification counts
and histograms.

## Trust boundary

The checked source contains no `sorry`, `admit`, or user-declared axioms. The
final mathematical chain uses ordinary kernel-checked proof terms and the
standard classical/quotient principles imported by Mathlib. The separate
exhaustive finite-classification theorem uses `native_decide`, so that
computation additionally relies on Lean's native evaluator/compiler, as is
standard for native-decision certificates.

See [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) for the exact theorem
statement and a compact dependency inventory.

## Main files

- `K6Prefix.lean`: exhaustive finite classification.
- `OnlineRamsey/QueryComplexity.lean`: the finite game and normalized
  power-law definition.
- `OnlineRamsey/InfinitePolicyBridge.lean`: the countably infinite game,
  coherent first-appearance reduction, and exact equivalence of achievable
  budgets.
- `OnlineRamsey/InfiniteUnconditional.lean`: the unconditional theorem in the
  standard countably infinite formulation.
- `OnlineRamsey/UnconditionalLower.lean`: unconditional lower constant.
- `OnlineRamsey/UpperStrategy.lean`: concrete adaptive strategy and success
  certificate.
- `OnlineRamsey/UpperPathGeometry.lean` and
  `OnlineRamsey/SlackBranchReady.lean`: legality, replay stability, and branch
  allocator counting.
- `OnlineRamsey/UpperProbabilityAssembly.lean`: exact finite Bernoulli mass
  estimate.
- `OnlineRamsey/UnconditionalUpper.lean`: bucketwise achievability and the
  unconditional canonical finite-board theorem.
- `Main.lean`: finite-certificate reporting executable.
