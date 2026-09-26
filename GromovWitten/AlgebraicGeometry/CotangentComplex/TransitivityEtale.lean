/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.Full
import GromovWitten.AlgebraicGeometry.CotangentComplex.Transitivity
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Étale (and localization) base change of `H⁻¹` of the cotangent complex

`Transitivity.lean` proves that `jzH1BaseChange R S T : H⁻¹(L_{S/R}) ⊗_S T ⟶ H⁻¹(L_{T/R})` is
*surjective* when `T` is flat and formally étale over `S`, but leaves **bijectivity** open,
since Mathlib's route to it (`Algebra.Extension.tensorH1CotangentOfFormallyEtale`) needs a
*compatible presentation pair*: extensions `P` of `S/R` and `Q` of `T/R` together with a hom
`f : P.Hom Q` such that `f.toRingHom` is formally étale and `Q.ker ≃ Q.Ring ⊗[P.Ring] P.ker`.

This file:

* proves bijectivity (hence the isomorphism `H⁻¹(L_{S/R}) ⊗_S T ≅ H⁻¹(L_{T/R})`) in the
  **localization** special case, by reusing Mathlib's `Algebra.tensorH1CotangentOfIsLocalization`
  and matching it against `jzH1BaseChange`;
* records precisely, in this docstring, why the compatible-presentation route is blocked in
  general for `Algebra.Generators.self`-style presentations, and what extra construction (based
  on `Algebra.IsStandardEtale`) would be needed to remove the localization restriction.

## Why the naive "`Generators.self` on both sides" route fails

`Algebra.H1Cotangent.map R R S T` (the map underlying `jzH1BaseChange`) is, by definition,
`Extension.H1Cotangent.map (Generators.defaultHom (Generators.self R S) (Generators.self R T))
  .toExtensionHom`, and by `Extension.H1Cotangent.map_eq`, this map is *independent of the choice*
of hom between the fixed extensions `P := (Generators.self R S).toExtension` and
`Q := (Generators.self R T).toExtension`. So to invoke `tensorH1CotangentOfFormallyEtale` with
*these particular* `P, Q` (avoiding any further presentation-independence transport, since
`Algebra.H1Cotangent R S` and `Algebra.H1Cotangent R T` are *definitionally* `P.H1Cotangent` and
`Q.H1Cotangent`), one would need *some* hom `f : P.Hom Q` with `f.toRingHom` formally étale.
But `Q.Ring = MvPolynomial T R` is free on *all* of `T` over `R`, while any `f.toRingHom :
MvPolynomial S R → MvPolynomial T R` compatible with `algebraMap S T` sends each generator `X_s`
to some polynomial evaluating to `algebraMap S T s`; the image of `f.toRingHom` is generated (as
an `R`-algebra) by at most `#S`-many elements, so unless `algebraMap S T` is essentially
surjective, `f.toRingHom` has an enormous (free, of "rank" `#T − #S`-ish) relative cotangent
space and is very far from unramified. **This is a genuine mathematical obstruction, not a
missing API**: no hom between the two `Generators.self` presentations can be formally étale
unless `S → T` is already close to an isomorphism.

## The route that *would* work (not completed here)

Mathlib's own proof of `Algebra.tensorH1CotangentOfIsLocalization` sidesteps this by keeping
`P := (Generators.self R S).toExtension` (so the *source* still matches `Algebra.H1Cotangent R S`
on the nose) but choosing a *different* extension `Q` of `T/R` — not `Generators.self R T` — built
from a genuinely formally-étale `P.Ring`-algebra (there, a suitable localization of `P.Ring`), and
only *afterwards* transports `Q.H1Cotangent` to the canonical `Algebra.H1Cotangent R T` via
`Extension.equivH1CotangentOfFormallySmooth` (using that `Q.Ring` is formally smooth over `R`).

The same strategy works for `T` standard-étale over `S` (`Algebra.IsStandardEtale S T`): given a
`StandardEtalePresentation S T` (a pair `f g : S[X]` and `x : T` with `T ≅ S[X][Y]/⟨f, Yg-1⟩`),
one can lift `f` to a *monic* polynomial `f' : P.Ring[X]` of the same degree via
`Polynomial.lifts_and_natDegree_eq_and_monic` (using `P.algebraMap_surjective`), lift the Bézout
witnesses `p₁, p₂` from `f`'s separability condition to `p₁', p₂' : P.Ring[X]`, and set
`g' := f'.derivative * p₁' + f' * p₂'` (so the separability condition holds for `(f', g')` *by
construction*, with Bézout data `(p₁', p₂', 1)`, avoiding the need to lift `g` and its condition
separately). This gives a `StandardEtalePair P.Ring`, hence (by the library's own
`instance : Algebra.FormallyEtale P.Ring _`) a formally-étale `P.Ring`-algebra `Q.Ring`, with a
natural map `Q.Ring →ₐ[R] T` (sending the pair's generator to `algebraMap S T x`) that one still
needs to show **surjective** (matching `T`'s own standard-étale presentation) and whose kernel
one needs to identify with `Q.Ring ⊗[P.Ring] P.ker` (using that `Q.Ring` is flat, in fact étale,
over `P.Ring`). Completing this — the surjectivity comparison and the flat-base-change kernel
identification — is a substantial independent construction that was not completed in this round;
see the "Not done" section of this file's accompanying report for the precise state.

## Main declarations

* `bijective_jzH1BaseChange_of_isLocalization`, `hNegOneBaseChangeIso_of_isLocalization`: the
  full bijectivity/isomorphism `H⁻¹(L_{S/R}) ⊗_S T ≅ H⁻¹(L_{T/R})` when `T` is a localization of
  `S` at a submonoid `M`.

## Not done

* The general case `[Algebra.FormallyEtale S T]` (or even `[Algebra.IsStandardEtale S T]`) is
  **not** proved bijective here; only the localization special case is. See the docstring above
  for the precise mathematical obstruction and the (substantial, uncompleted) construction that
  would remove it.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Transitivity

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- `jzH1BaseChange`'s underlying map is, up to the (iso) identification of `H⁻¹(L_{T/R})` with
`Algebra.H1Cotangent R T`, exactly `(Algebra.H1Cotangent.map R R S T).liftBaseChange T`: the
composite defining `jzH1BaseChange`, unfolded. -/
theorem jzH1BaseChange_hom_eq :
    (jzH1BaseChange R S T).hom =
      (Full.cohomologyNegOne R T).toLinearEquiv.symm.toLinearMap.comp
        ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by
  rw [jzH1BaseChange, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    Iso.toLinearEquiv_symm, Iso.toLinearMap_toLinearEquiv, Iso.symm_hom]

/-- Along a localization `S → T` at a submonoid `M`, `jzH1BaseChange` is bijective: the full
`H⁻¹` base-change isomorphism in this special case, via Mathlib's
`Algebra.tensorH1CotangentOfIsLocalization`. -/
theorem bijective_jzH1BaseChange_of_isLocalization (M : Submonoid S) [IsLocalization M T] :
    Function.Bijective (jzH1BaseChange R S T).hom := by
  rw [jzH1BaseChange_hom_eq]
  refine (Function.Bijective.of_comp_iff'
    (f := (Full.cohomologyNegOne R T).toLinearEquiv.symm.toLinearMap)
    (Full.cohomologyNegOne R T).toLinearEquiv.symm.bijective
    ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)).mpr ?_
  rw [show (Algebra.H1Cotangent.map R R S T).liftBaseChange T =
      (Algebra.tensorH1CotangentOfIsLocalization R T M).toLinearMap from
    (Algebra.tensorH1CotangentOfIsLocalization_toLinearMap R T M).symm]
  exact (Algebra.tensorH1CotangentOfIsLocalization R T M).bijective

/-- The isomorphism `H⁻¹(L_{S/R}) ⊗_S T ≅ H⁻¹(L_{T/R})` when `T` is a localization of `S`. -/
noncomputable def hNegOneBaseChangeIso_of_isLocalization (M : Submonoid S) [IsLocalization M T] :
    ModuleCat.of T (T ⊗[S] Algebra.H1Cotangent R S) ≅
      Full.cohomology (Full.cotangentComplex R T) (-1) :=
  haveI : IsIso (jzH1BaseChange R S T) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_jzH1BaseChange_of_isLocalization R S T M)
  asIso (jzH1BaseChange R S T)

end Transitivity

end GromovWitten.AlgebraicGeometry.CotangentComplex
