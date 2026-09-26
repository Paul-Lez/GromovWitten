# Handoff: issue #16

Partial implementation toward [finite unramified automorphism schemes](https://github.com/Paul-Lez/GromovWitten/issues/16).

Files below are relative to `GromovWitten/AlgebraicGeometry/`.

- `ObstructionTheory/MarkedAutomorphisms.lean` and `MarkedAutomorphismsBase.lean`: split dual-number automorphisms correspond to derivations; target and marking constraints give their linear kernel, with a converse characterized by preserving the dual base and reducing to the identity.
- `Curves/StableMaps/PolynomialAutomorphisms.lean`: `Point f S` is a group, functorial for arbitrary test-algebra homomorphisms and naturally equivalent to maps from the explicit coordinate algebra. That algebra and its `Spec` are finite for nonconstant `f`, and formally unramified when `f.derivative ≠ 0`.
- `PolynomialAffineIntegral.lean` and `PolynomialAffineRigidity.lean`: integral universal coordinates and square-zero uniqueness, retaining arbitrary test algebras with nilpotents.
- `PolynomialFrobenius.lean`: explicit infinitesimal scaling preserving Frobenius and translation when the derivative vanishes. `coordinateRing_formallyUnramified_iff` proves formal unramifiedness exactly when the derivative is nonzero, in every characteristic.

Remaining: geometric stable-curve/map representability, the geometric tangent-kernel identification and stability criteria, polarization independence, and the exponent-at-least-three theorem. The affine-linear stabilizer does not include all affine-line automorphisms over nonreduced algebras. The Frobenius obstruction requires qualifying the proposed stable-map unramifiedness statement; the projective stable-map example is not yet formalized.

Validation: full `lake build` passed with warnings as errors (Lean/Mathlib 4.33.1). Audited principal declarations, including the group laws and derivative criterion, use only `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or custom axioms were added. Builds were serialized through the shared lock.
