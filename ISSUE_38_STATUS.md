# Issue 38: the diagonal and inertia

This file records the state of [issue 38](https://github.com/Paul-Lez/GromovWitten/issues/38).

## Constructed and proved

`Stacks/DiagonalComparison.lean` turns a scheme representing an isomorphism sheaf into a
scheme presentation of the actual diagonal stack morphism, with the comparison cell, the
classifying map and both uniqueness proofs. Hence representability of the diagonal in the
isomorphism-sheaf encoding implies representability in the stack-morphism encoding, and the
actual diagonal and inertia projection of an algebraic stack are representable.

`Stacks/EtaleAtlasDiagonal.lean` proves the direction "étale atlas ⇒ unramified diagonal" with
no hypothesis: `StackChart.hasUnramifiedIsom_of_isEtaleSurjective` realises the isomorphism
scheme of two chart objects as an ordinary scheme pullback of the chart's self-overlap
presentation, so `DeligneMumfordStack.stackDiagonal_unramified'` and
`AlgebraicStack.stackDiagonal_unramified_of_etaleChart` follow. `DeligneMumfordStack` has no
diagonal field.

`Stacks/InertiaFunctoriality.lean` constructs the global inertia map of every stack morphism
through the genuine bilimit, and `Stacks/InertiaCoherence.lean` proves its two-dimensional
functoriality: `inertiaMap_congr`, `inertiaMap_id`, `inertiaMap_comp`, and
`inertiaEquivalence` (equivalent stacks have equivalent inertia stacks); `inertiaMap_aut` and
`representedStack_aut` identify inertia of represented stacks with the schemes themselves.

`Stacks/EtaleSlice.lean` proves the commutative-algebra core of the converse (Stacks 06N3):
cutting a standard smooth algebra of relative dimension `n` by `n` elements whose differentials
generate the cotangent module gives an étale algebra
(`etale_of_span_eq_top_of_isStandardSmooth`), and an unramified composite forces
surjectivity of the base-changed cotangent map (`surjective_mapBaseChange_of_formallyUnramified`).
`SiteChart.restrict` (`Sites/StackSiteContinuity.lean`) realises a slice `W → U → X` of a chart as
a chart and computes its comparison data.

`Stacks/DeligneMumfordCriterionAssembly.lean`, `Stacks/EtaleSliceLocal.lean`,
`Stacks/DeligneMumfordCriterionFinal.lean` and `Stacks/EtaleSliceLocalSlicing.lean` reduce the
converse "unramified diagonal ⇒ étale atlas" to one scheme-theoretic statement: representable
properties of a sliced chart are tested on the slice morphism, étale slices whose slice
morphisms cover the atlas glue to an étale surjective chart (`SaturatedEtaleSliceExists` is
necessary and sufficient), the affine slicing step is proved, and
`AlgebraicStack.exists_etaleChart_of_unramified_diagonal_of_saturated` follows from the
hypothesis `SaturatedLocalSlicing`. The first formulation `LocalSlicing`, which demanded a slice
through every point, is false and nothing is deduced from it.

## Precise remaining scope

`SaturatedLocalSlicing` (Stacks 06N3, local step) is not proved: near every point of a smooth
atlas with unramified self-overlap pair, a slice whose slice morphism is étale has to be found,
and the differentials of the chosen functions must generate the relative cotangent module at
every point of the slice's preimage, which needs the groupoid structure of `U ×_X U` (now
available as scheme morphisms `StackChart.selfOverlapUnit/Inv/Comp`). The comparison of inertia
for quotient stacks (stabilisers) is not started.
