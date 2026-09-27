/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyExactSequence

/-!
# The normalization genus formula from the long exact cohomology sequence

`Curves/ArithmeticGenusNormalization.lean` derives the normalization formula for the arithmetic
genus `p_a(X) + h⁰(N) = h¹(N) + δ + 1` (`arithmeticGenus_add_of_normalizationSequence`) from a
*hypothesised* five-term exact sequence of `k`-vector spaces, because at the time of writing no
long exact cohomology sequence was available for `CategoryTheory.Sheaf.H`.
`Curves/CohomologyExactSequence.lean` has since supplied that long exact sequence for any short
exact sequence `S` of `𝒪_X`-modules (`cohomology_exact_at_X₁/X₂/X₃`, `cohomologyConnectingHom`),
packaged into the Euler-characteristic identity `eulerCharacteristic_add_of_shortExact`.

This file replaces the hypothesised exactness by that proved long exact sequence: the *only*
geometric input is now a short exact sequence

`0 → 𝒪_X → S.X₂ → S.X₃ → 0`

of `𝒪_X`-modules (`S : ShortComplex X.Modules`, `hS : S.ShortExact`) with `S.X₁` identified with
the structure sheaf via an isomorphism `e : structureModule X ≅ S.X₁` — for the normalization
sequence, `S.X₂ = ν_*𝒪_X̃` and `S.X₃` is the cokernel, a skyscraper module supported at the nodes.

## Main declarations

* `arithmeticGenus_add_of_normalizationShortExact` — the integer-valued normalization formula
  `p_a(X) + h⁰(X, S.X₂) = h¹(X, S.X₂) + h⁰(X, S.X₃) - h¹(X, S.X₃) + 1`, derived from
  `hS : S.ShortExact`, an identification `e : structureModule X ≅ S.X₁`, `h⁰(X, 𝒪_X) = 1`,
  finite-dimensionality of the six cohomology spaces and `H²(X, 𝒪_X) = 0` (the last two exactly
  as in `eulerCharacteristic_add_of_shortExact`).
* `arithmeticGenus_add_of_normalizationShortExact_of_hDim_one` — the specialisation to
  `h¹(X, S.X₃) = 0` (automatic when `S.X₃` is a finite direct sum of skyscraper modules, since
  skyscraper sheaves have no higher cohomology) and `h⁰(X, S.X₃) = δ`: the natural-number formula
  `p_a(X) + h⁰(X, S.X₂) = h¹(X, S.X₂) + δ + 1`, matching the shape of
  `arithmeticGenus_add_of_normalizationSequence` exactly, but now with the five-term exactness
  hypothesis replaced by the two hypotheses `h⁰(X, S.X₃) = δ` and `h¹(X, S.X₃) = 0` on the
  cokernel `S.X₃` alone.

## What is still missing

Mathlib has no theory of skyscraper `𝒪_X`-modules or of their cohomology, so `h¹(X, S.X₃) = 0`
for a finite direct sum of skyscraper modules remains a hypothesis rather than a proved fact;
this is the same gap already documented in `Curves/ArithmeticGenusNormalization.lean`.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- **The normalization genus formula from the long exact cohomology sequence.**  Let `S` be a
short exact sequence of `𝒪_X`-modules whose first term is (isomorphic to) the structure sheaf,
`0 → 𝒪_X → S.X₂ → S.X₃ → 0`; assume `H⁰(X, 𝒪_X)` is one-dimensional (e.g. `X` proper, connected
and reduced) and, as in `eulerCharacteristic_add_of_shortExact`, that the six cohomology spaces in
degrees `0, 1` are finite-dimensional and `H²(X, 𝒪_X) = 0`.  Then
`p_a(X) + h⁰(X, S.X₂) = h¹(X, S.X₂) + h⁰(X, S.X₃) - h¹(X, S.X₃) + 1`.  This is the six-term
long-exact-sequence replacement for the hypothesised five-term exactness of
`arithmeticGenus_add_of_normalizationSequence`. -/
theorem arithmeticGenus_add_of_normalizationShortExact
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (e : structureModule X ≅ S.X₁)
    (h2 : Subsingleton (cohomologyModuleCat k f S.X₁ 2))
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 1)]
    (hX0 : hDim k f S.X₁ 0 = 1) :
    (arithmeticGenus k f : ℤ) + hDim k f S.X₂ 0
      = hDim k f S.X₂ 1 + hDim k f S.X₃ 0 - hDim k f S.X₃ 1 + 1 := by
  have hgenus : arithmeticGenus k f = hDim k f S.X₁ 1 := arithmeticGenus_eq_of_iso k f e
  have h := eulerCharacteristic_add_of_shortExact hS k f h2
  omega

/-- **Specialisation to a skyscraper cokernel.**  When the cokernel `S.X₃` of the normalization
sequence has vanishing `H¹` (as it does when `S.X₃` is a finite direct sum of skyscraper modules,
since skyscraper sheaves have no higher cohomology — a fact not yet available in this repository,
see the module docstring) and `H⁰(X, S.X₃)` has dimension `δ` (the number of nodes with
multiplicity, for a sum of length-`1` skyscrapers), the normalization formula takes the natural
number shape `p_a(X) + h⁰(X, S.X₂) = h¹(X, S.X₂) + δ + 1`, exactly as in
`arithmeticGenus_add_of_normalizationSequence`, but now with `hS : S.ShortExact` (via the proved
long exact cohomology sequence) as the only exactness input, instead of a hypothesised five-term
exact sequence of abstract linear maps. -/
theorem arithmeticGenus_add_of_normalizationShortExact_of_hDim_one
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (e : structureModule X ≅ S.X₁)
    (h2 : Subsingleton (cohomologyModuleCat k f S.X₁ 2))
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 1)]
    (hX0 : hDim k f S.X₁ 0 = 1) (δ : ℕ) (hQ0 : hDim k f S.X₃ 0 = δ)
    (hQ1 : hDim k f S.X₃ 1 = 0) :
    arithmeticGenus k f + hDim k f S.X₂ 0 = hDim k f S.X₂ 1 + δ + 1 := by
  have h := arithmeticGenus_add_of_normalizationShortExact k f S hS e h2 hX0
  omega

/-- **Agreement with the dual-graph genus, from a short exact sequence alone.**  Chaining
`arithmeticGenus_add_of_normalizationShortExact_of_hDim_one` with
`arithmeticGenus_eq_dualGraph_arithmeticGenus` (`Curves/ArithmeticGenusNormalization.lean`):
given the short exact normalization sequence `hS` as above and a dual graph `G` whose vertex
genera sum to `h¹(X, S.X₂)`, whose edges are the `δ` nodes and whose vertices are the
`h⁰(X, S.X₂)` connected components of the normalization, the cohomological arithmetic genus
`p_a(X)` agrees with the dual-graph genus `G.arithmeticGenus`. -/
theorem arithmeticGenus_eq_dualGraph_arithmeticGenus_of_shortExact
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (e : structureModule X ≅ S.X₁)
    (h2 : Subsingleton (cohomologyModuleCat k f S.X₁ 2))
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 0)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₁ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₂ 1)]
    [FiniteDimensional k (cohomologyModuleCat k f S.X₃ 1)]
    (hX0 : hDim k f S.X₁ 0 = 1) (δ : ℕ) (hQ0 : hDim k f S.X₃ 0 = δ)
    (hQ1 : hDim k f S.X₃ 1 = 0) (G : DualGraph.{u})
    (hgenus : ∑ v, G.genus v = hDim k f S.X₂ 1)
    (hedge : Fintype.card G.Edge = δ)
    (hvertex : Fintype.card G.Vertex = hDim k f S.X₂ 0) :
    arithmeticGenus k f = G.arithmeticGenus :=
  arithmeticGenus_eq_dualGraph_arithmeticGenus k f S.X₂ δ G hgenus hedge hvertex
    (arithmeticGenus_add_of_normalizationShortExact_of_hDim_one k f S hS e h2 hX0 δ hQ0 hQ1)

end

end GromovWitten.AlgebraicGeometry.Curves
