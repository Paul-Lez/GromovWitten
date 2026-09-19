/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.Algebra.FiniteTypeDimensionFormula
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Unconditional
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedConeTrivialisation

/-!
# The virtual fundamental class over an infinite field

`VirtualFundamentalClass/Unconditional.lean` reduces the two auxiliary hypotheses of the
construction of the virtual class (homogeneity of principal divisors on the bundle space, and
injectivity of the flat pullback along it) to two conditions on the base ring `R ⧸ I`:

* `VectorBundle.HasUniversalDimensionFormula (R ⧸ I)`;
* `VectorBundle.UnitDifferences (R ⧸ I)`.

This file discharges both for the geometric situation of Behrend–Fantechi: `R` a finitely
generated algebra over an infinite field `k` and `I` a proper ideal.  The first is
`GromovWitten.Algebra.FiniteTypeDimensionFormula.hasUniversalDimensionFormula_of_finiteType`
applied to the finite-type `k`-algebra `R ⧸ I`; the second is
`IntersectionTheory.VectorBundle.unitDifferences_of_field` applied to the nontrivial
`k`-algebra `R ⧸ I`.

Consequently every result of `Unconditional.lean` is restated here with **no hypotheses beyond
the standing ones** (`R` of finite type over `k`, `E` a perfect two-term complex,
`φ : E ⟶ conormalComplex k R I`): `OverField.virtualClass`, `pullback_virtualClass`,
`eq_virtualClass_of_pullback_eq`, `virtualClass_unique`,
`virtualClass_eq_zeroSectionGysinEquiv''`, `virtualClass_eq_of_quasiIso`,
`virtualClass_eq_of_homotopyEquivalence`, `virtualClass_eq_of_quasiIso_homotopy`.

The same is done for the purity statements of `ResolvedConeDimension.lean` and
`ResolvedConeTrivialisation.lean` in the polynomial model `R = k[x_i]_{i ∈ σ}`: their conditional
input `HasDimensionFormula (extendedRees (MvPolynomial σ k) I)` is discharged by
`GromovWitten.Algebra.hasDimensionFormula_extendedRees`, giving
`OverField.ringKrullDim_quotient_ring_eq`, `OverField.dimension_eq_of_isMax` and their
obstruction-theoretic variants with no conditional input at all.

## Remaining hypotheses

The instance `[IsNoetherianRing R]` is kept in the statements below even though it follows from
`[Algebra.FiniteType k R]` by `isNoetherianRing_of_finiteType` (Hilbert's basis theorem): the
implication is not an instance, since instance search cannot guess the base field `k`.
Likewise `[Nontrivial (R ⧸ I)]`, that is `I ≠ ⊤`, is genuinely needed — the empty scheme has no
infinite set of pairwise-unit differences.
-/

universe u

-- The coordinate ring `gr_I(R) ⊗_{R/I} Sym(E⁰)` of the resolved cone needs a deeper instance
-- search than the default, exactly as in `Unconditional.lean`.
set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

/-! ## The two conditions on the base ring, for a finite-type algebra over a field -/

/-- A finitely generated algebra over a field is Noetherian (Hilbert's basis theorem).  This is
not made an instance: instance search cannot guess the base field `k`. -/
theorem isNoetherianRing_of_finiteType (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] : IsNoetherianRing R :=
  Algebra.FiniteType.isNoetherianRing k R

/-- A quotient of a finitely generated `k`-algebra is a finitely generated `k`-algebra. -/
theorem finiteType_quotient (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) : Algebra.FiniteType k (R ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ_surjective k I)

/-- **The universal dimension formula for a finite-type algebra over a field.**  Every prime
quotient of every polynomial algebra `(R ⧸ I)[x_1, …, x_n]` satisfies the dimension formula,
because `R ⧸ I` is again of finite type over `k`. -/
theorem hasUniversalDimensionFormula (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) :
    VectorBundle.HasUniversalDimensionFormula (R ⧸ I) :=
  have : Algebra.FiniteType k (R ⧸ I) := finiteType_quotient k R I
  GromovWitten.Algebra.FiniteTypeDimensionFormula.hasUniversalDimensionFormula_of_finiteType k
    (R ⧸ I)

/-- **Unit differences for a nontrivial algebra over an infinite field**: the image of `k` in
`R ⧸ I` is an infinite set whose pairwise differences are units. -/
theorem unitDifferences (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    (I : Ideal R) [Nontrivial (R ⧸ I)] : VectorBundle.UnitDifferences (R ⧸ I) :=
  VectorBundle.unitDifferences_of_field k (R ⧸ I)

/-! ## The virtual class over an infinite field -/

section Basic

variable {k R : Type u} [Field k] [Infinite k] [CommRing R] [Algebra k R]
variable [Algebra.FiniteType k R] [IsNoetherianRing R] {I : Ideal R} [Nontrivial (R ⧸ I)]
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))

omit [Infinite k] [Nontrivial (R ⧸ I)] in
/-- **The homogeneity hypothesis of the construction, over an infinite field.**  This is
`Unconditional.hhomOf` with the universal dimension formula discharged. -/
theorem hhomOf : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE :=
  Unconditional.hhomOf φ dimE (hasUniversalDimensionFormula k R I)

/-- **The injectivity hypothesis of the construction, in an arbitrary degree `i`, over an
infinite field.**  This is `Unconditional.hinjAt` with both conditions discharged. -/
theorem hinjAt (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (i + (VirtualClass.bundleRank φ : ℤ))) :
    Function.Injective
      (VectorBundle.chowPullbackBundle (VirtualClass.trivialization φ) dimX dimE i RX RE) :=
  Unconditional.hinjAt φ dimX dimE i RX RE (hasUniversalDimensionFormula k R I)
    (unitDifferences k R I)

variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
    (VirtualClass.virtualDimension φ))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (VirtualClass.coneDegree φ))

/-- **The injectivity hypothesis of the construction**, in the degree `vd + a` in which the
resolved-cone class lives, over an infinite field. -/
theorem hinjOf : Function.Injective (VirtualClass.bundlePullback φ dimX dimE RX RE) :=
  Unconditional.hinjOf φ dimX dimE RX RE (hasUniversalDimensionFormula k R I)
    (unitDifferences k R I)

/-- **The virtual fundamental class** `[X]^vir ∈ A_{vd}(X)` of the obstruction theory `φ` over an
infinite field `k`, with no hypotheses left: `R` is a finitely generated `k`-algebra, `I ≠ ⊤` and
`E` is a perfect two-term complex. -/
noncomputable def virtualClass : RX.ChowGroup :=
  Unconditional.virtualClass φ dimX dimE RX RE (hasUniversalDimensionFormula k R I)
    (unitDifferences k R I)

/-- **The defining property of the virtual class**: it pulls back to the resolved-cone class
along the flat pullback `π^* : A_{vd}(X) → A_{vd+a}(E₁)`. -/
@[simp]
theorem pullback_virtualClass :
    VirtualClass.bundlePullback φ dimX dimE RX RE (virtualClass φ dimX dimE RX RE) =
      VirtualClass.resolvedConeClass φ dimE RE :=
  Unconditional.pullback_virtualClass φ dimX dimE RX RE _ _

/-- **Uniqueness of the virtual class**: any class pulling back to the resolved-cone class is the
virtual class. -/
theorem eq_virtualClass_of_pullback_eq (α : RX.ChowGroup)
    (hα : VirtualClass.bundlePullback φ dimX dimE RX RE α =
      VirtualClass.resolvedConeClass φ dimE RE) :
    α = virtualClass φ dimX dimE RX RE :=
  Unconditional.eq_virtualClass_of_pullback_eq φ dimX dimE RX RE _ _ α hα

/-- The virtual class is the unique class with the defining property. -/
theorem virtualClass_unique :
    ∃! α : RX.ChowGroup, VirtualClass.bundlePullback φ dimX dimE RX RE α =
      VirtualClass.resolvedConeClass φ dimE RE :=
  Unconditional.virtualClass_unique φ dimX dimE RX RE (hasUniversalDimensionFormula k R I)
    (unitDifferences k R I)

/-- **The virtual class is the zero-section Gysin pullback of the resolved-cone class**, along
the Gysin isomorphism `0^! : A_{vd+a}(E₁) ≃ A_{vd}(X)`, which over an infinite field is available
with no further input. -/
theorem virtualClass_eq_zeroSectionGysinEquiv'' :
    virtualClass φ dimX dimE RX RE =
      VectorBundle.zeroSectionGysinEquiv'' (VirtualClass.trivialization φ) dimX dimE
        (VirtualClass.virtualDimension φ) RX RE (hasUniversalDimensionFormula k R I)
        (unitDifferences k R I) (VirtualClass.resolvedConeClass φ dimE RE) :=
  rfl

end Basic

/-! ## Quasi-isomorphism invariance over an infinite field -/

section QuasiIso

variable {k R : Type u} [Field k] [Infinite k] [CommRing R] [Algebra k R]
variable [Algebra.FiniteType k R] [IsNoetherianRing R] {I : Ideal R} [Nontrivial (R ⧸ I)]
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

include dim₁ dim₂ R₁ R₂ in
/-- **Behrend–Fantechi, Proposition 5.3, over an infinite field, with no hypotheses left.**

Let `f : E ⟶ F` be a quasi-isomorphism of perfect two-term complexes with
`ψ⁻¹ ∘ f⁻¹ = φ⁻¹`.  Then `φ` and `ψ` have the same virtual fundamental class.

As in `Unconditional.virtualClass_eq_of_quasiIso`, the right-hand side is written with
`VirtualClass.virtualClassAt ψ (trivialization ψ)` in the degree `virtualDimension φ`: this *is*
the virtual class of `ψ`, but `virtualDimension ψ = virtualDimension φ` holds only
propositionally, while the type `RX.ChowGroup` depends on the degree. -/
theorem virtualClass_eq_of_quasiIso (f : LinearTwoTermComplex.Hom E F)
    (hf : f.IsQuasiIsomorphism) (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero) :
    virtualClass φ dimX dimE RX RE =
      VirtualClass.virtualClassAt ψ (VirtualClass.trivialization ψ) dimX dimF
        (VirtualClass.virtualDimension φ) RX RF (hhomOf ψ dimF)
        (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF) :=
  Unconditional.virtualClass_eq_of_quasiIso φ ψ dimX dimE dimF dim₁ dim₂ RX RE RF R₁ R₂
    (hasUniversalDimensionFormula k R I) (unitDifferences k R I) f hf hcomp

include dim₁ dim₂ R₁ R₂ in
/-- **Chain-homotopy invariance of the virtual class over an infinite field**: a chain-homotopy
equivalence `he : E ≃ F` with `ψ⁻¹ ∘ he.hom⁻¹ = φ⁻¹` does not change the virtual class. -/
theorem virtualClass_eq_of_homotopyEquivalence (he : LinearTwoTermComplex.HomotopyEquivalence E F)
    (hcomp : ψ.degreeZero.comp he.hom.degreeZero = φ.degreeZero) :
    virtualClass φ dimX dimE RX RE =
      VirtualClass.virtualClassAt ψ (VirtualClass.trivialization ψ) dimX dimF
        (VirtualClass.virtualDimension φ) RX RF (hhomOf ψ dimF)
        (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF) :=
  Unconditional.virtualClass_eq_of_homotopyEquivalence φ ψ dimX dimE dimF dim₁ dim₂ RX RE RF
    R₁ R₂ (hasUniversalDimensionFormula k R I) (unitDifferences k R I) he hcomp

include dim₁ dim₂ R₁ R₂ in
/-- **Quasi-isomorphism invariance when `φ` and `ψ` are compatible only up to a degree-zero
homotopy** `ψ⁻¹ ∘ f⁻¹ = φ⁻¹ + h ∘ d_E`, over an infinite field. -/
theorem virtualClass_eq_of_quasiIso_homotopy (f : LinearTwoTermComplex.Hom E F)
    (hf : f.IsQuasiIsomorphism)
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)
    (hcomp : ψ.degreeZero.comp f.degreeZero = φ.degreeZero + h.comp E.differential) :
    virtualClass φ dimX dimE RX RE =
      VirtualClass.virtualClassAt ψ (VirtualClass.trivialization ψ) dimX dimF
        (VirtualClass.virtualDimension φ) RX RF (hhomOf ψ dimF)
        (hinjAt ψ dimX dimF (VirtualClass.virtualDimension φ) RX RF) :=
  Unconditional.virtualClass_eq_of_quasiIso_homotopy φ ψ dimX dimE dimF dim₁ dim₂ RX RE RF R₁ R₂
    (hasUniversalDimensionFormula k R I) (unitDifferences k R I) f hf h hcomp

end QuasiIso

/-! ## Purity of the resolved cone in the polynomial model, with no conditional input -/

section Purity

open Order

attribute [local instance] specializationOrder

variable {k : Type u} [Field k] {σ : Type u} [Finite σ] {I : Ideal (MvPolynomial σ k)}
variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}
variable [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
variable [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero]
variable [Module.Free (MvPolynomial σ k ⧸ I) E.degreeOne]
variable [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeOne]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))

/-- **The dimension formula for the extended Rees algebra** of an ideal of a polynomial ring over
a field: the single conditional input of `ResolvedConeDimension.lean`, discharged by
`GromovWitten.Algebra.hasDimensionFormula_extendedRees`. -/
theorem hasDimensionFormula_extendedRees :
    HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I) :=
  GromovWitten.Algebra.hasDimensionFormula_extendedRees k I

omit [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
  [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero] in
/-- **Purity of `C ×_X E₀`, with no conditional input**: every irreducible component of the
product `C ×_X E₀` has dimension `|σ| + rank E⁰`. -/
theorem ringKrullDim_quotient_productRing (hI : I ≠ ⊤)
    {P : Ideal (ResolvedCone.productRing φ)} (hP : P ∈ minimalPrimes (ResolvedCone.productRing φ)) :
    ringKrullDim (ResolvedCone.productRing φ ⧸ P) =
      ((Nat.card σ + Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ) : ℕ∞) :=
  ResolvedCone.ringKrullDim_quotient_productRing φ hI hasDimensionFormula_extendedRees hP

/-- **Purity of the resolved cone, with no conditional input beyond the trivialisation of the
torsor**: every irreducible component of `C(E)` has dimension `b = rank E⁰`. -/
theorem ringKrullDim_quotient_ring_eq (hI : I ≠ ⊤)
    (htriv : ResolvedCone.IsPolynomialTrivialisation φ)
    {q : Ideal (ResolvedCone.ring φ)} (hq : q ∈ minimalPrimes (ResolvedCone.ring φ)) :
    ringKrullDim (ResolvedCone.ring φ ⧸ q) =
      ((Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ∞)) :=
  ResolvedCone.ringKrullDim_quotient_ring_eq φ hI hasDimensionFormula_extendedRees htriv hq

/-- **Purity in the form used by the Chow groups, with no conditional input beyond the
trivialisation of the torsor.** -/
theorem dimension_eq_of_isMax (dimC : DimensionFunction (ResolvedCone.scheme φ)) (hI : I ≠ ⊤)
    (htriv : ResolvedCone.IsPolynomialTrivialisation φ) (x : ↥(ResolvedCone.scheme φ))
    (hx : IsMax x) :
    dimC x = (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) :=
  ResolvedCone.dimension_eq_of_isMax φ dimC hI hasDimensionFormula_extendedRees htriv x hx

/-- The same purity statement on the ambient bundle `E₁`, along the closed immersion
`toBundle φ : C(E) ↪ E₁`, with no conditional input beyond the trivialisation. -/
theorem dimension_toBundle_eq_of_isMax (dimC : DimensionFunction (ResolvedCone.scheme φ))
    (dimB : DimensionFunction (ResolvedCone.bundleSpace φ)) (hI : I ≠ ⊤)
    (htriv : ResolvedCone.IsPolynomialTrivialisation φ) (x : ↥(ResolvedCone.scheme φ))
    (hx : IsMax x) :
    dimB ((ResolvedCone.toBundle φ).base x) =
      (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) :=
  ResolvedCone.dimension_toBundle_eq_of_isMax φ dimC dimB hI hasDimensionFormula_extendedRees
    htriv x hx

/-- **Purity of the resolved cone of an obstruction theory, with no conditional input at all**:
the trivialisation of the torsor is supplied by `ResolvedCone.isPolynomialTrivialisation` and the
dimension formula by `hasDimensionFormula_extendedRees`. -/
theorem ringKrullDim_quotient_ring_eq' (hI : I ≠ ⊤)
    (hobs : PicardCriteria.IsObstructionTheory φ)
    {q : Ideal (ResolvedCone.ring φ)} (hq : q ∈ minimalPrimes (ResolvedCone.ring φ)) :
    ringKrullDim (ResolvedCone.ring φ ⧸ q) =
      ((Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ∞)) :=
  ResolvedCone.ringKrullDim_quotient_ring_eq' φ hI hasDimensionFormula_extendedRees hobs hq

/-- **Purity in the form used by the Chow groups, with no conditional input at all.** -/
theorem dimension_eq_of_isMax' (dimC : DimensionFunction (ResolvedCone.scheme φ)) (hI : I ≠ ⊤)
    (hobs : PicardCriteria.IsObstructionTheory φ) (x : ↥(ResolvedCone.scheme φ)) (hx : IsMax x) :
    dimC x = (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) :=
  ResolvedCone.dimension_eq_of_isMax' φ dimC hI hasDimensionFormula_extendedRees hobs x hx

/-- The same purity statement on the ambient bundle `E₁`, with no conditional input at all. -/
theorem dimension_toBundle_eq_of_isMax' (dimC : DimensionFunction (ResolvedCone.scheme φ))
    (dimB : DimensionFunction (ResolvedCone.bundleSpace φ)) (hI : I ≠ ⊤)
    (hobs : PicardCriteria.IsObstructionTheory φ) (x : ↥(ResolvedCone.scheme φ)) (hx : IsMax x) :
    dimB ((ResolvedCone.toBundle φ).base x) =
      (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) :=
  ResolvedCone.dimension_toBundle_eq_of_isMax' φ dimC dimB hI hasDimensionFormula_extendedRees
    hobs x hx

end Purity

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField
