# Issue 41: global cones and vector bundles

This branch advances [issue 41](https://github.com/Paul-Lez/GromovWitten/issues/41).
It does not complete the stack-level acceptance criteria.

## Constructed and proved

- Relative spectrum is functorial in compatible affine algebra maps, with faithful maps and
  isomorphism transport. Polynomial extension has a constructed cartesian comparison
  `Spec_X A[t] ≅ Spec_X A ×_X A¹_X`.
- Compatible affine polynomial coactions and vertex augmentations glue to an actual action
  morphism on the relative spectrum. The unit law, coassociativity in the polynomial
  presentation, scalar multiplication law, and factorization of zero contraction through the
  vertex are proved. The vertex is a section. The affine line supplies a concrete global
  instance with its restriction compatibility proved from polynomial formulas.
- Symmetric algebras are functorial in module maps. Their base-change equivalence
  `B ⊗_R Sym_R M ≃ Sym_B(B ⊗_R M)` is constructed, with naturality and coaction compatibility.
  The scheme pullback theorem currently uses the tensor-product presentation.
- Symmetric algebras of projective modules are formally smooth. For finite projective modules
  they are finitely presented and smooth, including after scalar extension. The proof of
  finite presentation uses an explicit algebra-retract theorem over arbitrary commutative rings.
- A scheme bundle with finitely many polynomial coordinates in its given affine charts has
  smooth and surjective projection. Surjectivity uses the constructed zero section.

The new APIs are exported by `GromovWitten.lean`. Principal files are
`Cones/GlobalContraction.lean`, `Cones/GlobalConeExamples.lean`,
`Cones/SymmetricFunctoriality.lean`, `Cones/ProjectiveSmoothness.lean`,
`VectorBundleSmooth.lean`, and `RelativeSpec*.lean` under `GromovWitten/AlgebraicGeometry`.

## Precise remaining scope

`ConeAlgebraData` specifies local coactions and their defining algebraic laws; it does not
assume a global action. Constructing it from every graded quasi-coherent algebra on an
algebraic stack, and proving stack descent of the constructions, remain open. There is no
claim here of a general stack-level abelian-hull or closed-subcone construction.

The existing `BundleData` allows augmented polynomial chart transitions, which can be
nonlinear. Smoothness follows from these charts, but they alone do not define a vector bundle.
The converse characterization by finite locally free modules, the equality with module rank,
and a global scalar action derived from genuine linear transition maps remain open.
The action's associativity is exported in its isomorphic polynomial presentation, rather than
as an iterated-pullback monoid-action package.

## Verification and review

Four distinct Luna agents at xhigh were assigned; the orchestrator reviewed the algebra and
geometry and repaired the concrete global example. Lean/Lake commands are serialized by the
shared build lock with two Lean threads. New declarations use no admitted proofs, custom
axioms, native decision proofs, or disabled linters. Targeted builds and representative axiom
checks pass. The final full `lake build`, including the public umbrella, passed on
2026-09-25 (8,998 jobs) with warnings treated as errors. The umbrella check caught and resolved
a name collision with the existing relative-Proj data type; the cone API uses `ConeAlgebraData`.

Revalidated against upstream `master` at `64bcf85ea95c270ef30bb951ce41a31754c97367` on
2026-09-26: the full public build passed (9,026 jobs), with warnings treated as errors.
