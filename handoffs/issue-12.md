# Handoff: issue #12

Partial prerequisites for [nodal ampleness and pluricanonical generation](https://github.com/Paul-Lez/GromovWitten/issues/12).

- `GromovWitten/AlgebraicGeometry/Veronese.lean` constructs the external Veronese graded algebra, its canonical map (injective for positive index), and generation from degrees zero and one under `MultiplicationSpans`. Generation over the coefficient ring also requires `DegreeZeroGenerated`. Polynomial gradings satisfy the multiplication hypothesis.
- `VeroneseLocalization.lean` constructs the positive-index chart comparison. The map for the
  element corresponding to `s^d` is restricted to homogeneous localization, its representative
  formula is public, and injectivity/surjectivity are proved over arbitrary commutative rings,
  including zero divisors and a zero chart element. `veroneseLocalizationEquiv` packages the
  resulting actual ring equivalence. The inverse fraction representative of `b/s^m` has numerator
  `b*s^((d-1)*m)` and denominator `(s^d)^m`; injectivity clears an ordinary-localization
  annihilator by `s^((d-1)*k)` before applying the positive-index Veronese injection. The separate
  `VeroneseLocalizationScheme.lean` file packages each such ring equivalence as the corresponding
  affine `Spec` isomorphism and exposes its contravariant homomorphism and inverse.

Next: prove arbitrary tensor base change using Mathlib's `GradedAlgebra.baseChange` and direct-sum
decomposition, then use the affine chart isomorphisms to glue a global `Proj` comparison.

Actual line-bundle ampleness, identification with pluricanonical section rings, and geometric generation bounds remain open. Abstract graded-algebra results alone do not establish these.

Validation: `lake build` passed (Lean/Mathlib 4.33.1, warnings treated as errors). Audits of the main declarations report only `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or custom axioms were added.
