# Handoff: issue #12

Partial prerequisites for [nodal ampleness and pluricanonical generation](https://github.com/Paul-Lez/GromovWitten/issues/12).

- `GromovWitten/AlgebraicGeometry/Veronese.lean` constructs the external Veronese graded algebra, its canonical map (injective for positive index), and generation from degrees zero and one under `MultiplicationSpans`. Generation over the coefficient ring also requires `DegreeZeroGenerated`. Polynomial gradings satisfy the multiplication hypothesis.
- `VeroneseLocalization.lean` starts the chart comparison: the element corresponding to `s^d`, a map to ordinary localization, and containment of its image in homogeneous localization. It does not yet construct the chart equivalence.

Next: restrict the fraction map and prove bijectivity for `d > 0`. A fraction `b/s^m` lifts with numerator `b*s^((d-1)*m)` and denominator `(s^d)^m`; the proof must allow zero divisors. Then prove tensor base change using Mathlib's `GradedAlgebra.baseChange` and direct-sum decomposition, and glue the chart equivalences to compare Proj.

Actual line-bundle ampleness, identification with pluricanonical section rings, and geometric generation bounds remain open. Abstract graded-algebra results alone do not establish these.

Validation: `lake build` passed (Lean/Mathlib 4.33.1, warnings treated as errors). Audits of the main declarations report only `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or custom axioms were added.
