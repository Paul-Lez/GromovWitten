# Handoff: issue #16

Partial implementation toward [finite unramified automorphism schemes](https://github.com/Paul-Lez/GromovWitten/issues/16).

- `ObstructionTheory/MarkedAutomorphisms.lean`: actual split dual-number automorphisms correspond to derivations; target and marking constraints give their linear kernel.
- `ObstructionTheory/MarkedAutomorphismsBase.lean`: characterizes these automorphisms by preserving the dual-number base and reducing to the identity.
- `Curves/StableMaps/PolynomialAffineIntegral.lean`: scale, inverse scale, and translation of an affine substitution preserving a nonconstant polynomial are integral, including over algebras with nilpotents.
- `Curves/StableMaps/PolynomialAutomorphisms.lean`: initial coordinate presentation by `ac=1` and the coefficients of `f(aX+b)-f(X)`, maps between algebra homomorphisms and stabilizing substitutions, and actual polynomial substitution automorphisms. Their equivalence and naturality remain to be proved.

Paths above are relative to `GromovWitten/AlgebraicGeometry/`.

Next: prove the point correspondence and naturality, use coordinate integrality to establish module finiteness, then prove formal unramifiedness under `f.derivative ≠ 0`. A square-zero change of substitution gives `f'(aX+b)*(δa*X+δb)=0`; the leading coefficient is a unit. Full stable-curve/map representability and rigidity still need geometric proofs. The affine-linear stabilizer does not describe every affine-line automorphism over nonreduced algebras.

The issue needs a separability/characteristic qualification: in characteristic `p`, `t ↦ (1+ε)t` preserves `t^p` over dual numbers, so unconditional stable-map unramifiedness is false. This example is explained in the issue comment; it is not yet formalized here.

Validation: `lake build` passed (Lean/Mathlib 4.33.1, warnings treated as errors). Audits of the main declarations report only `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or custom axioms were added.
