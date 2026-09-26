# Issue 38: the diagonal and inertia

This branch advances [issue 38](https://github.com/Paul-Lez/GromovWitten/issues/38).
It does not prove the full Deligne–Mumford diagonal criterion.

## Constructed and proved

`Stacks/DiagonalComparison.lean` turns a scheme representing an isomorphism sheaf into a
scheme presentation of the actual diagonal stack morphism. It constructs the comparison cell,
the classifying map, the source-object isomorphism, and both uniqueness proofs. Neither
uniqueness nor the compatibility equation is omitted or supplied as an extra hypothesis.

Consequently, representability of the diagonal in the isomorphism-sheaf encoding implies
representability in the stack-morphism encoding. The same construction transfers any property
of all the isomorphism schemes. The actual diagonal and inertia projection of an algebraic
stack are therefore representable. The existing conditional Deligne–Mumford corollary no
longer needs a separate morphism-level representability assumption.

`Stacks/InertiaFunctoriality.lean` constructs a global map on inertia for every stack morphism
using the genuine bilimit. Both projection isomorphisms and the full comparison face are
retained. `Stacks/StackProductProjections.lean` supplies the component calculations used in
these constructions; it does not treat morphisms of arbitrary stacks as discrete.

## Precise remaining scope

The conditional unramified-diagonal corollary still assumes that etale-surjective charts have
unramified isomorphism schemes. Deriving that fact from the etale atlas, and constructing an
etale atlas from an unramified diagonal, remain open. These are essential parts of the issue,
so this branch is not an unconditional diagonal criterion.

The baseline already constructs inertia as a genuine self-intersection and supplies fibrewise
comparisons. The new map construction is global, but identity and composition coherence and
invariance under stack equivalence remain open. The additional identity-coherence attempt
was not accepted as a proof and is excluded from the public source.

## Verification and review

Four distinct Luna agents at xhigh were assigned, followed by an additional agent for the
inertia identity coherence. The orchestrator completed and independently reviewed the diagonal
bridge; another agent reviewed it and found no missing uniqueness or comparison condition.
New source has no admitted proofs, custom axioms, native decision proofs, or disabled linters.
Representative axiom checks use only Lean's standard axioms. All builds use the shared lock
and two Lean threads. The final full `lake build`, including the public umbrella, passed
on 2026-09-25 (8,991 jobs), with warnings treated as errors.

Revalidated against upstream `master` at `64bcf85ea95c270ef30bb951ce41a31754c97367` on
2026-09-26: the full public build passed (9,019 jobs), with warnings treated as errors.
