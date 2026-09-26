# Handoff: issue #5

Partial implementation of [étale-local standard node charts](https://github.com/Paul-Lez/GromovWitten/issues/5).

Implemented in `GromovWitten/AlgebraicGeometry/Curves/StableReduction/`:

- `LocalNodeChart.lean`: explicit unit normalization of `xy = a`, positive DVR factorization, uniqueness, and coefficient naturality.
- `LocalNodeIntrinsicThickness.lean`: the actual differential-Fitting quotient, its length `n` for `xy = πⁿ`, infinite length for `xy = 0`, and ramified tensor base change with length `e*n`.
- `LocalNodeChartInvariance.lean`: intrinsic differential-Fitting ideal transport and thickness invariance under arbitrary algebra isomorphisms over the coefficient ring.
- `LocalNodeChartScheme.lean`: the actual ramified affine scheme isomorphism and its two projection squares.

Next: construct étale-local charts for an arbitrary nodal DVR family, including the finite étale DVR extension and algebraization step. The current results begin with an explicit node algebra. Nonzero nonunit smoothing is needed for finite positive thickness. Invariance here is under coefficient-algebra isomorphisms; arbitrary étale covers can change length through residue degree.

Useful cleanup: weaken unnecessary DVR/injectivity assumptions on the raw ramified coordinate maps. Exponent equality for isomorphic standard charts follows by combining `nodeThickness_eq_of_algEquiv` with `nodeThickness_eq_of_irreducible`.

Validation: `lake build` passed (Lean/Mathlib 4.33.1, warnings treated as errors). Audits of the main declarations report only `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or custom axioms were added.
