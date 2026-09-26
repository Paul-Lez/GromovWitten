/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.SmoothQuasiregular
import GromovWitten.AlgebraicGeometry.Cones.SmoothIntrinsicNormalSheaf
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.LciFormula
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.LciFormulaPure

/-!
# The smooth formula and the smooth case of the lci formula

This file assembles issues #64/#66's remaining "smooth case" glue.  It contains no new
mathematics beyond `SmoothQuasiregular.lean`, `SmoothIntrinsicNormalSheaf.lean`,
`LciFormula.lean` and `LciFormulaPure.lean`: it discharges the injectivity hypothesis `hinj`
appearing throughout those files by
`AffineNormalCone.normalSheafCoordinateMap_injective_of_formallySmooth`
(`SmoothQuasiregular.lean`'s "formally smooth ⇒ quasi-regular" theorem), giving hypothesis-free
statements of Behrend–Fantechi's smooth formula and of the smooth case of the lci formula.

## Main declarations

* `SmoothIntrinsicNormalSheaf.smoothIntrinsicNormalConeEquivalence'`,
  `smoothIntrinsicNormalCone_isConnected'`, `smoothIntrinsicNormalCone_autEquivDerivation'`:
  Behrend–Fantechi's smooth formula `𝔠_U = B T_U` in the affine model, for a formally smooth
  affine embedding `U = Spec (k[x]/I) ↪ M = Spec k[x]`, with no hypothesis beyond formal
  smoothness of `k[x]/I`.
* `VirtualFundamentalClass.OverField.smooth_lci_formula`,
  `VirtualFundamentalClass.OverField.smooth_lci_formula'`: the smooth case of the lci formula
  `[X]^vir = [X]` over an infinite field `k`, for `X = Spec (k[x_1,…,x_n]/I)` formally smooth
  over `k`.

## What is left as an explicit hypothesis

Formal smoothness of `S = R/I` only gives that the conormal module `I.Cotangent` is a finite
*projective* `S`-module (a direct summand of the finite free module
`NormalConeAction.Tangent I`); a finite projective module need not be free over a general ring,
so `Module.Free (R ⧸ I) I.Cotangent` remains an explicit hypothesis of the lci-formula
statements below (it holds e.g. when `S` is local, or when `Pic S` is trivial).  Purity of the
chosen dimension function of `X` (`hpureX`) is likewise inherited unchanged from
`LciFormula.lean`.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

/-! ## Goal 1: the hypothesis-free affine smooth formula -/

namespace SmoothIntrinsicNormalSheaf

variable {k : Type u} [CommRing k] {σ : Type u} (I : Ideal (MvPolynomial σ k))
  [Algebra.FormallySmooth k (MvPolynomial σ k ⧸ I)]

/-- **Behrend–Fantechi's smooth formula (affine model), hypothesis-free.**  For a formally
smooth affine embedding `U = Spec (k[x]/I) ↪ M = Spec k[x]`, the intrinsic normal cone equals
the intrinsic normal sheaf as quotient groupoids over every test algebra `B`: `𝔠_U = B T_U`.
This is `smoothIntrinsicNormalConeEquivalence` with the injectivity hypothesis discharged by
`AffineNormalCone.normalSheafCoordinateMap_injective_of_formallySmooth`. -/
noncomputable def smoothIntrinsicNormalConeEquivalence' (B : Type u) [CommRing B]
    [Algebra (NormalConeAction.Base I) B] :
    ConeQuotient.QuotientGroupoid (NormalConeAction.normalConeAction I) B ≌
      ConeQuotient.QuotientGroupoid
        (AffineNormalCone.normalSheafTangentAction k (MvPolynomial σ k) I) B :=
  smoothIntrinsicNormalConeEquivalence I
    (AffineNormalCone.normalSheafCoordinateMap_injective_of_formallySmooth I) B

/-- **Behrend–Fantechi's smooth formula, hypothesis-free: connectivity.**  Every two `B`-points
of the intrinsic normal cone `[C_{U/M}/T_M|_U]` of a formally smooth affine embedding are
isomorphic. -/
theorem smoothIntrinsicNormalCone_isConnected'
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B]
    (c c' : ConeQuotient.QuotientGroupoid (NormalConeAction.normalConeAction I) B) :
    Nonempty (c ≅ c') :=
  smoothIntrinsicNormalCone_isConnected I
    (AffineNormalCone.normalSheafCoordinateMap_injective_of_formallySmooth I) B c c'

/-- **Behrend–Fantechi's smooth formula, hypothesis-free: automorphisms.**  The automorphism
group of every `B`-point of `[C_{U/M}/T_M|_U]` is `Hom_S(Ω_{S/k}, B)`, the group of
`k`-derivations of `S = k[x]/I` valued in `B`. -/
noncomputable def smoothIntrinsicNormalCone_autEquivDerivation'
    (B : Type u) [CommRing B] [Algebra (NormalConeAction.Base I) B] [Algebra k B]
    [IsScalarTower k (NormalConeAction.Base I) B]
    (c : ConeQuotient.QuotientGroupoid (NormalConeAction.normalConeAction I) B) :
    (c ⟶ c) ≃ Derivation k (NormalConeAction.Base I) B :=
  smoothIntrinsicNormalCone_autEquivDerivation I
    (AffineNormalCone.normalSheafCoordinateMap_injective_of_formallySmooth I) B c

end SmoothIntrinsicNormalSheaf

end GromovWitten.AlgebraicGeometry

/-! ## Goal 2: the smooth case of the lci formula -/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {σ : Type u} [Finite σ] (k : Type u) [Field k] [Infinite k]
  (I : Ideal (MvPolynomial σ k)) [Nontrivial (MvPolynomial σ k ⧸ I)]
  [Algebra.FormallySmooth k (MvPolynomial σ k ⧸ I)]

omit [Infinite k] [Nontrivial (MvPolynomial σ k ⧸ I)] in
/-- **Finiteness of the conormal module of a formally smooth quotient.**  `I.Cotangent` is a
quotient of the finite free `S`-module `NormalConeAction.Tangent I` (`NormalConeAction.
tangentBasis`) along the retraction `SmoothIntrinsicNormalSheaf.conormalRetraction` supplied by
formal smoothness, hence finite.  Registered as an instance so that later statements involving
`Module.Finite (R ⧸ I) I.Cotangent` resolve automatically. -/
instance finite_cotangent_of_formallySmooth :
    Module.Finite (MvPolynomial σ k ⧸ I) I.Cotangent := by
  have : Module.Finite (NormalConeAction.Base I) (NormalConeAction.Tangent I) :=
    Module.Finite.of_basis (NormalConeAction.tangentBasis I)
  exact Module.Finite.of_surjective (SmoothIntrinsicNormalSheaf.conormalRetraction I)
    fun x => ⟨AffineNormalCone.conormalMap k (MvPolynomial σ k) I x,
      SmoothIntrinsicNormalSheaf.conormalRetraction_apply_conormalMap I x⟩

variable [Module.Free (MvPolynomial σ k ⧸ I) I.Cotangent]

/-- **The smooth case of the lci formula** (Behrend–Fantechi): for `k` an infinite field and `I`
an ideal of `R = k[x_1,…,x_n]` such that `S = R/I` is formally smooth over `k`, the virtual
fundamental class of the identity ("lci") obstruction theory on `X = Spec S` is the class of the
fundamental cycle of `X`, given purity `hpureX` of the chosen dimension function of `X` at the
virtual dimension.  `[Module.Free (R ⧸ I) I.Cotangent]` is assumed explicitly (see the module
docstring); `Module.Finite` is derived automatically from formal smoothness
(`finite_cotangent_of_formallySmooth`). -/
theorem smooth_lci_formula
    (dimX : DimensionFunction (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))) dimX
      (VirtualClass.virtualDimension (VirtualClass.lciHom k I)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)) dimE
      (VirtualClass.coneDegree (VirtualClass.lciHom k I)))
    (hpureX : ∀ p : Spec (CommRingCat.of (MvPolynomial σ k ⧸ I)), IsMax p →
      dimX p = VirtualClass.virtualDimension (VirtualClass.lciHom k I)) :
    virtualClass (VirtualClass.lciHom k I) dimX dimE RX RE =
      RX.quotientMap (cyclesOfDimension.fundamental hpureX) :=
  virtualClass_eq_fundamental_of_injective k I
    (AffineNormalCone.normalSheafCoordinateMap_injective_of_formallySmooth I) dimX dimE RX RE
    hpureX

variable [Fintype σ]

/-- **Corollary: the smooth lci formula with purity phrased dimension-theoretically.**  Same
setting, with `hpureX` stated as the more geometric "every irreducible component of
`X = Spec (R/I)` has dimension `card σ - rank I.Cotangent`", identified with the virtual
dimension via `VirtualClass.virtualDimension_lciHom_eq`. -/
theorem smooth_lci_formula'
    (dimX : DimensionFunction (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (MvPolynomial σ k ⧸ I))) dimX
      (VirtualClass.virtualDimension (VirtualClass.lciHom k I)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (VirtualClass.lciHom k I)) dimE
      (VirtualClass.coneDegree (VirtualClass.lciHom k I)))
    (hpureX : ∀ p : Spec (CommRingCat.of (MvPolynomial σ k ⧸ I)), IsMax p →
      dimX p = (Fintype.card σ : ℤ) - (Module.finrank (MvPolynomial σ k ⧸ I) I.Cotangent : ℤ)) :
    virtualClass (VirtualClass.lciHom k I) dimX dimE RX RE =
      RX.quotientMap (cyclesOfDimension.fundamental
        (fun p hp => (hpureX p hp).trans (VirtualClass.virtualDimension_lciHom_eq k I).symm)) :=
  smooth_lci_formula k I dimX dimE RX RE _

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField
