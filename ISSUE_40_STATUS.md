# Issue 40: common atlas refinements and presentation groupoids

Upstream: https://github.com/Paul-Lez/GromovWitten/issues/40

This branch is based on `d31abfc6a80148596ca5b1300d06396626aabb7f`.
It develops scheme-level presentation tools beyond the existing stack-valued
refinements in `AtlasRefinement.lean`.

## Verified construction

- `SchemeAtlasRefinement.lean` constructs the pullback presentation of a map
  between represented schemes using the actual scheme pullback. It promotes
  base-change-stable scheme morphism properties to the represented stack map.
- `SchemeAtlasRefinementChart.lean` converts a chart pullback presentation into
  a stack-morphism presentation and transfers representable properties. Its
  comparison laws retain the target-stack isomorphisms. Discreteness is used
  only in the represented source fibre, so this does not discard stabilizers.
- `SchemeAtlasRefinementReverse.lean` recovers chart presentations from stack
  morphism presentations and proves equivalence of the two property notions.
  It constructs a common scheme atlas and proves its two projections smooth
  and surjective. The fibrewise comparison is the pullback of the actual
  universal overlap isomorphism.
- `SchemeAtlasRefinementCoherence.lean` assembles that comparison into an actual
  `StackIso2` between the two composite chart maps. Naturality holds for every
  scheme pullback, using strong-transformation coherence and naturality of
  the target stack's compositor. No discreteness of target-stack arrows is
  assumed.
- `SchemeAtlasRefinementGroupoids.lean` constructs functors from the common
  scheme atlas's presentation groupoid to both input presentation groupoids.
  The right functor uses the constructed comparison 2-cell. Both functors are
  fully faithful on every test-scheme fibre, preserving all stabilizer arrows.
  The combined existence theorem constructs the common atlas and comparisons
  from the two smooth surjective charts.

## Remaining scope

The new results do not supply the full scheme-level groupoid laws, coherence
under iterated refinements, or an equivalence between the presented stack and
the original stack. Existing quotient-topology and stack-valued refinement
theorems are baseline work, not new claims of this branch. The full upstream
issue is not claimed closed.

## Review

Four distinct `gpt-5.6-luna` agents at `xhigh` were assigned successive discovery,
implementation, conversion, and integration tasks. Three further Luna/xhigh
agents were assigned coherence repair and independent final review. The
orchestrator independently reviewed and repaired proofs, including the final
coherent comparison, and integrated the groupoid functors. The final reviewer
confirmed the comparison orientation, arbitrary-base naturality, source-only
use of discreteness, and preservation of stabilizers.

All Lean/Lake commands ran under the shared build lock with two Lean threads.
A lock-timeout result was rejected as evidence of compilation; final success
was checked against actual completed builds and kernel-dependency audits.

## Validation

The complete default build passed with warnings treated as errors (8,984
jobs). The public umbrella imports all five new modules. The six central
coherence and groupoid declarations, as well as the earlier presentation and
existence declarations, were audited with `#print axioms`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No new `sorry`, `admit`, custom
axioms, `native_decide`, or warning suppression is used.
