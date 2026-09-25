# Issue 58: square-zero deformation theory

This branch advances [issue 58](https://github.com/Paul-Lez/GromovWitten/issues/58).
Its results concern affine algebra lifting problems and two-term presentation complexes;
they do not constitute the full deformation theorem for algebraic stacks.

## Constructed and proved

`SquareZeroDerivedExt.lean` constructs the degreewise short exact sequence
`F[0] → [C → F] → C[1]` and its distinguished derived triangle. If `F` is projective,
every derived map to a module in degree `-1` is represented by a chain map. This gives a
surjection from the explicit obstruction cokernel to derived degree-one Hom. There is no
projectivity assumption on the conormal module `C`. For polynomial presentations the
cotangent-space term `F` is free, so the projectivity hypothesis is discharged explicitly.

`SquareZeroDerivedKernel.lean` proves injectivity of this map without projectivity of either
term, using naturality of the distinguished triangle for `[C → F] → [F → F]`. It therefore
identifies the obstruction cokernel with actual derived `Ext¹` when only `F` is projective.
The canonical derived obstruction vanishes exactly when a lift exists; this direction does
not require projectivity, only an ambient lift. For polynomial presentations formal smoothness
supplies that lift and the free cotangent-space basis supplies the equivalence hypothesis.

`SquareZeroSource.lean` constructs restriction of lifts and derivations along arbitrary
compatible source-algebra maps, and proves compatibility with the torsor operations. For maps
of presentations of the same algebra it constructs the induced obstruction-cokernel map,
proves naturality of the actual obstruction class, and proves independence of the chosen
presentation morphism using its explicit cotangent homotopy.

`SquareZeroPresentationEquiv.lean` proves identity and composition for the cokernel maps.
Mutual presentation maps therefore induce inverse linear equivalences; the comparison maps
need not themselves be inverse. Polynomial presentations always have such comparison maps,
and the constructed equivalence preserves the obstruction class without an ambient-lift
hypothesis, by formal smoothness of polynomial algebras.

`SquareZeroGroupoid.lean` constructs the restriction functor while preserving the actual
extension automorphism on every arrow. It is faithful for every compatible source map,
full for a surjective source map, and an equivalence for a bijective source map. Identity and
composition natural isomorphisms are proved. The derivation-kernel description of lift
automorphisms commutes with the functor, via a constructed map of the two kernels.

## Precise remaining scope

These results use the two-term presentation complex. A comparison with the full cotangent
complex for general rings and the stack-level lifting groupoid remains necessary for the
full upstream theorem. Presentation-obstruction naturality above is for two presentations of
the same target algebra; it is not a theorem about every semilinear change of target algebra.
The baseline also has target-extension maps, which are distinct from the new source restriction.

The existing `Lift` groupoid has automorphisms of the fixed square-zero extension as arrows.
Preserving those arrows does not identify it with the deformation groupoid of an arbitrary
algebraic stack over a fixed extension. No such identification is claimed here.

## Verification and review

Four distinct Luna agents at xhigh were assigned, followed by an additional repair agent for
the derived kernel calculation. The orchestrator reviewed the actual short exact sequence,
projectivity hypotheses, variance of all cokernel maps, and the presentation-homotopy proof.
New source has no admitted proofs, custom axioms, native decision proofs, or disabled linters.
Representative axiom checks use only Lean's standard axioms. Builds use the shared lock and
two Lean threads. The final full `lake build`, including the public umbrella, passed on
2026-09-25 (8,993 jobs), with warnings treated as errors. A second agent independently
reviewed the derived-kernel argument and the presentation-independence proof.
