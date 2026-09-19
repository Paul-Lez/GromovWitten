/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.QuasiIsoInvariance

/-!
# The virtual fundamental class with no hypotheses beyond the base ring

Round 14's construction of the virtual fundamental class
(`VirtualFundamentalClass/Construction.lean`) carries two explicit hypotheses:

* `hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE`, the homogeneity of
  principal divisors on the total space of the bundle `E₁ = Spec Sym(E⁻¹)`, needed by the
  localisation sequence and hence by the surjectivity of the flat pullback `π^*`;
* `hinj : Function.Injective (VirtualClass.bundlePullback φ dimX dimE RX RE)`, the injectivity of
  `π^*`, the remaining half of homotopy invariance for Chow groups.

Both are consequences of two conditions on the *base ring* alone, isolated in
`IntersectionTheory/BundleHomotopyInjective.lean`:

* `VectorBundle.HasUniversalDimensionFormula (R ⧸ I)`: every prime quotient of every polynomial
  algebra `MvPolynomial ι (R ⧸ I)` in finitely many variables satisfies the dimension formula
  `dim (A ⧸ P) + ht P = dim A`;
* `VectorBundle.UnitDifferences (R ⧸ I)`: `R ⧸ I` contains an infinite subset whose pairwise
  differences are units.

This file packages the two hypotheses away.  For `hdim` and `hunit` as above it defines
`Unconditional.virtualClass φ dimX dimE RX RE hdim hunit`, proves its defining property
`pullback_virtualClass`, its uniqueness `eq_virtualClass_of_pullback_eq`, its description as a
zero-section Gysin pullback `virtualClass_eq_zeroSectionGysinEquiv''`, and restates the
quasi-isomorphism invariance of `VirtualFundamentalClass/QuasiIsoInvariance.lean` with **no
hypotheses left except `hdim` and `hunit`**: the auxiliary homogeneity and injectivity
hypotheses `hhom₁`, `hinj₁` for the intermediate complex `F ⊕ [E⁰ = E⁰]` are discharged by the
very same two lemmas.

Beyond `hdim` and `hunit`, the inputs are exactly those of round 14: `R` Noetherian, `E` a
perfect two-term complex, and `φ : E ⟶ conormalComplex k R I` (whose obstruction-theory
property is not needed for the *construction*, only for its geometric meaning).

Neither `hdim` nor `hunit` is proved for a concrete ring here.  For a finitely generated algebra
`A` over an infinite field `k`, `UnitDifferences A` is
`VectorBundle.unitDifferences_of_field k A`, and `HasUniversalDimensionFormula A` is the
dimension formula for finite-type algebras over a field, which is *not yet available* in this
repository (`GromovWitten/Algebra/FiniteTypeKrullDimension.lean` and
`GromovWitten/Algebra/DimensionFormula.lean` contain partial material); supplying it would make
everything below unconditional for finite-type algebras over an infinite field.
-/

universe u

-- The coordinate ring `gr_I(R) ⊗_{R/I} Sym(E⁰)` of the resolved cone needs a deeper instance
-- search than the default, exactly as in `ResolvedCone.lean` and `QuasiIsoInvariance.lean`.
set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Unconditional

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

/-! ## Discharging the two hypotheses of the construction -/

section Hypotheses

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))

/-- **The homogeneity hypothesis of the construction, from the universal dimension formula.**
The bundle space `E₁ = Spec Sym(E⁻¹)` is a polynomial ring over `R ⧸ I` in the chosen
trivialisation, so `VectorBundle.principalDivisorsHomogeneous_of_hasUniversalDimensionFormula`
applies to it. -/
theorem hhomOf (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I)) :
    PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE :=
  VectorBundle.principalDivisorsHomogeneous_of_hasUniversalDimensionFormula
    (VirtualClass.trivialization φ) dimE hdim

/-- **The injectivity hypothesis of the construction, in an arbitrary degree `i`.**  This is
`VectorBundle.chowPullbackBundle_injective` for the canonical trivialisation of `E₁`. -/
theorem hinjAt (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (i + (VirtualClass.bundleRank φ : ℤ)))
    (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) :
    Function.Injective
      (VectorBundle.chowPullbackBundle (VirtualClass.trivialization φ) dimX dimE i RX RE) :=
  VectorBundle.chowPullbackBundle_injective (VirtualClass.trivialization φ) dimX dimE i RX RE
    hdim hunit

variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
    (VirtualClass.virtualDimension φ))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (VirtualClass.coneDegree φ))

/-- **The injectivity hypothesis of the construction**, in the degree `vd + a` in which the
resolved-cone class lives. -/
theorem hinjOf (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) :
    Function.Injective (VirtualClass.bundlePullback φ dimX dimE RX RE) :=
  hinjAt φ dimX dimE (VirtualClass.virtualDimension φ) RX RE hdim hunit

/-! ## The virtual class -/

/-- **The virtual fundamental class** `[X]^vir ∈ A_{vd}(X)` of the obstruction theory `φ`, with
the two hypotheses of `VirtualClass.virtualClass` replaced by the two conditions `hdim`, `hunit`
on the base ring `R ⧸ I`.  Apart from these, the inputs are those of round 14: `R` Noetherian
and `E` a perfect two-term complex. -/
noncomputable def virtualClass (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) : RX.ChowGroup :=
  VirtualClass.virtualClass φ dimX dimE RX RE (hhomOf φ dimE hdim)
    (hinjOf φ dimX dimE RX RE hdim hunit)

/-- **The defining property of the virtual class**: it pulls back to the resolved-cone class
along the flat pullback `π^* : A_{vd}(X) → A_{vd+a}(E₁)`. -/
@[simp]
theorem pullback_virtualClass (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) :
    VirtualClass.bundlePullback φ dimX dimE RX RE (virtualClass φ dimX dimE RX RE hdim hunit) =
      VirtualClass.resolvedConeClass φ dimE RE :=
  VirtualClass.pullback_virtualClass φ dimX dimE RX RE _ _

/-- **Uniqueness of the virtual class**: any class pulling back to the resolved-cone class is
the virtual class. -/
theorem eq_virtualClass_of_pullback_eq (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) (α : RX.ChowGroup)
    (hα : VirtualClass.bundlePullback φ dimX dimE RX RE α =
      VirtualClass.resolvedConeClass φ dimE RE) :
    α = virtualClass φ dimX dimE RX RE hdim hunit :=
  VirtualClass.eq_virtualClass_of_pullback_eq φ dimX dimE RX RE _ _ α hα

/-- The virtual class is the unique class with the defining property. -/
theorem virtualClass_unique (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) :
    ∃! α : RX.ChowGroup, VirtualClass.bundlePullback φ dimX dimE RX RE α =
      VirtualClass.resolvedConeClass φ dimE RE :=
  VirtualClass.virtualClass_unique φ dimX dimE RX RE (hhomOf φ dimE hdim)
    (hinjOf φ dimX dimE RX RE hdim hunit)

/-- **The virtual class is the zero-section Gysin pullback of the resolved-cone class**, along
the now unconditional Gysin isomorphism `0^! : A_{vd+a}(E₁) ≃ A_{vd}(X)` of
`VectorBundle.zeroSectionGysinEquiv''`. -/
theorem virtualClass_eq_zeroSectionGysinEquiv''
    (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) :
    virtualClass φ dimX dimE RX RE hdim hunit =
      VectorBundle.zeroSectionGysinEquiv'' (VirtualClass.trivialization φ) dimX dimE
        (VirtualClass.virtualDimension φ) RX RE hdim hunit
        (VirtualClass.resolvedConeClass φ dimE RE) :=
  rfl

end Hypotheses

/-! ## Quasi-isomorphism invariance with the two base hypotheses only -/

section QuasiIso

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable [Nontrivial (R ⧸ I)]
variable {E F : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable [Module.Free (R ⧸ I) E.degreeOne] [Module.Finite (R ⧸ I) E.degreeOne]
variable [Module.Free (R ⧸ I) F.degreeZero] [Module.Finite (R ⧸ I) F.degreeZero]
variable [Module.Free (R ⧸ I) F.degreeOne] [Module.Finite (R ⧸ I) F.degreeOne]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (ψ : LinearTwoTermComplex.Hom F (conormalComplex k R I))
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
  (dimF : DimensionFunction (ResolvedCone.bundleSpace ψ))
  (dim₁ : DimensionFunction (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)))
  (dim₂ : DimensionFunction (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)))
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
    (VirtualClass.virtualDimension φ))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (VirtualClass.coneDegree φ))
  (RF : RationalEquivalenceSystem (ResolvedCone.bundleSpace ψ) dimF
    (VirtualClass.virtualDimension φ + (VirtualClass.bundleRank ψ : ℤ)))
  (R₁ : RationalEquivalenceSystem
    (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic ψ E.degreeOne)) dim₁
    (VirtualClass.virtualDimension φ +
      (VirtualClass.bundleRank (VirtualClass.sumAcyclic ψ E.degreeOne) : ℤ)))
  (R₂ : RationalEquivalenceSystem
    (ResolvedCone.bundleSpace (VirtualClass.sumAcyclic φ F.degreeOne)) dim₂
    (VirtualClass.virtualDimension φ +
      (VirtualClass.bundleRank (VirtualClass.sumAcyclic ψ E.degreeOne) : ℤ)))
  (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
  (hunit : VectorBundle.UnitDifferences (R ⧸ I))

include dim₁ dim₂ R₁ R₂ in
/-- **Behrend–Fantechi, Proposition 5.3, with the two base hypotheses as the only inputs.**

Let `f : E ⟶ F` be a quasi-isomorphism of perfect two-term complexes with
`ψ⁻¹ ∘ f⁻¹ = φ⁻¹`.  Then `φ` and `ψ` have the same virtual fundamental class.  Every
homogeneity and injectivity hypothesis of `QuasiIsoInvariance.virtualClass_eq_of_quasiIso` —
including `hhom₁` and `hinj₁` for the intermediate bundle space of `F ⊕ [E⁰ = E⁰]` — is
discharged by `hhomOf` and `hinjAt`.

As in `QuasiIsoInvariance.virtualClass_eq_of_quasiIso`, the right-hand side is written with
`VirtualClass.virtualClassAt ψ (trivialization ψ)` in the degree `virtualDimension φ`: this *is*
the virtual class of `ψ` (`VirtualClass.virtualClassAt_trivialization` is `rfl`), but
`virtualDimension ψ = virtualDimension φ` holds only propositionally
(`QuasiIsoInvariance.virtualDimension_eq_of_quasiIso`), while the type `RX.ChowGroup` depends on
the degree. -/
theorem virtualClass_eq_of_quasiIso (f : LinearTwoTermComplex.Hom E F)
    (hf : f.IsQuasiIsomorphism) (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero) :
    virtualClass φ dimX dimE RX RE hdim hunit =
      VirtualClass.virtualClassAt ψ (VirtualClass.trivialization ψ) dimX dimF
        (VirtualClass.virtualDimension φ) RX RF (hhomOf ψ dimF hdim)
        (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF hdim hunit) :=
  QuasiIsoInvariance.virtualClass_eq_of_quasiIso φ ψ f hf hcomp dimX dimE dimF dim₁ dim₂
    RX RE RF R₁ R₂ (hhomOf (VirtualClass.sumAcyclic ψ E.degreeOne) dim₁ hdim)
    (hinjAt (VirtualClass.sumAcyclic ψ E.degreeOne) dimX dim₁
      (VirtualClass.virtualDimension φ) RX R₁ hdim hunit)
    (hhomOf φ dimE hdim) (hinjOf φ dimX dimE RX RE hdim hunit) (hhomOf ψ dimF hdim)
    (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF hdim hunit)

include dim₁ dim₂ R₁ R₂ in
/-- **Chain-homotopy invariance of the virtual class**, with the two base hypotheses as the only
inputs: a chain-homotopy equivalence `he : E ≃ F` with `ψ⁻¹ ∘ he.hom⁻¹ = φ⁻¹` does not change
the virtual class. -/
theorem virtualClass_eq_of_homotopyEquivalence (he : LinearTwoTermComplex.HomotopyEquivalence E F)
    (hcomp : ψ.degreeZero.comp he.hom.degreeZero = φ.degreeZero) :
    virtualClass φ dimX dimE RX RE hdim hunit =
      VirtualClass.virtualClassAt ψ (VirtualClass.trivialization ψ) dimX dimF
        (VirtualClass.virtualDimension φ) RX RF (hhomOf ψ dimF hdim)
        (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF hdim hunit) :=
  virtualClass_eq_of_quasiIso φ ψ dimX dimE dimF dim₁ dim₂ RX RE RF R₁ R₂ hdim hunit he.hom
    he.isQuasiIsomorphism hcomp

include dim₁ dim₂ R₁ R₂ in
/-- **Quasi-isomorphism invariance when `φ` and `ψ` are compatible only up to a degree-zero
homotopy** `ψ⁻¹ ∘ f⁻¹ = φ⁻¹ + h ∘ d_E`, with the two base hypotheses as the only inputs. -/
theorem virtualClass_eq_of_quasiIso_homotopy (f : LinearTwoTermComplex.Hom E F)
    (hf : f.IsQuasiIsomorphism)
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)
    (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero + h.comp E.differential) :
    virtualClass φ dimX dimE RX RE hdim hunit =
      VirtualClass.virtualClassAt ψ (VirtualClass.trivialization ψ) dimX dimF
        (VirtualClass.virtualDimension φ) RX RF (hhomOf ψ dimF hdim)
        (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF hdim hunit) :=
  QuasiIsoInvariance.virtualClassAt_eq_of_quasiIso_homotopy φ ψ f hf h hcomp
    (VirtualClass.trivialization φ) (VirtualClass.trivialization ψ)
    (VirtualClass.trivialization (VirtualClass.sumAcyclic ψ E.degreeOne))
    dimX dimE dimF dim₁ dim₂ (VirtualClass.virtualDimension φ) RX RE RF R₁ R₂
    (VirtualClass.card_chooseBasisIndex_sumAcyclic (E := F) E.degreeOne)
    (QuasiIsoInvariance.card_chooseBasisIndex_sum_of_quasiIso f hf)
    (hhomOf (VirtualClass.sumAcyclic ψ E.degreeOne) dim₁ hdim)
    (hinjAt (VirtualClass.sumAcyclic ψ E.degreeOne) dimX dim₁
      (VirtualClass.virtualDimension φ) RX R₁ hdim hunit)
    (hhomOf φ dimE hdim) (hinjOf φ dimX dimE RX RE hdim hunit) (hhomOf ψ dimF hdim)
    (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF hdim hunit)

end QuasiIso

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Unconditional
