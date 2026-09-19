/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopy
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyRankOne

/-!
# Homotopy surjectivity without the rank-one hypothesis

`IntersectionTheory/BundleHomotopy.lean` proves Fulton's Proposition 1.9 (surjectivity of the
flat pullback along a trivialised affine vector bundle on rational Chow groups) from the rank-one
key lemma `VectorBundle.RankOneKey`, and `IntersectionTheory/BundleHomotopyRankOne.lean` proves
that lemma.  This file discharges the hypothesis (`VectorBundle.rankOneKey`) and restates the
results of `BundleHomotopy.lean` without it:

* `VectorBundle.chowPullbackBundle_surjective'`, `VectorBundle.exists_pullback_eq'`: the
  surjectivity of `π^* : A_i(X) → A_{i+r}(E)`, under homogeneity of principal divisors on the total
  space only;
* `VectorBundle.chowQuotientEquiv'`: `A_i(X) ⧸ ker π^* ≃ A_{i+r}(E)`;
* `VectorBundle.zeroSectionGysin'`: the zero-section Gysin isomorphism `0^! : A_{i+r}(E) ≃ A_i(X)`
  under the explicit remaining input that `π^*` is injective (full homotopy invariance, Fulton
  Theorem 3.3(a), which needs Chern classes and is not available here).
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace VectorBundle

/-- The rank-one key lemma holds: this is `VectorBundle.exists_rankOne_generator`. -/
theorem rankOneKey : RankOneKey.{u} :=
  fun _ _ _ dimE P hP => exists_rankOne_generator dimE P hP

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
  (dimX : DimensionFunction (Spec (CommRingCat.of R)))
  (dimE : DimensionFunction (Spec (CommRingCat.of A))) (i : ℤ)
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
  (RE : RationalEquivalenceSystem (Spec (CommRingCat.of A)) dimE (i + (Nat.card ι : ℤ)))

/-- **Fulton, Proposition 1.9**, with the rank-one key lemma discharged: the flat pullback along
a trivialised affine vector bundle over a Noetherian ring is surjective on dimension-graded
rational Chow groups, assuming only homogeneity of principal divisors on the total space. -/
theorem chowPullbackBundle_surjective'
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE) :
    Function.Surjective (chowPullbackBundle e dimX dimE i RX RE) :=
  chowPullbackBundle_surjective e dimX dimE i RX RE rankOneKey hhom

/-- Every rational Chow class on the total space is the flat pullback of a class on the base. -/
theorem exists_pullback_eq'
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE) (β : RE.ChowGroup) :
    ∃ α : RX.ChowGroup, chowPullbackBundle e dimX dimE i RX RE α = β :=
  chowPullbackBundle_surjective' e dimX dimE i RX RE hhom β

/-- The Chow group of the total space is the Chow group of the base modulo the kernel of the
flat pullback. -/
noncomputable def chowQuotientEquiv'
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE) :
    (RX.ChowGroup ⧸ LinearMap.ker (chowPullbackBundle e dimX dimE i RX RE)) ≃ₗ[ℚ]
      RE.ChowGroup :=
  chowQuotientEquiv e dimX dimE i RX RE rankOneKey hhom

/-- The zero-section Gysin isomorphism `0^! : A_{i+r}(E) ≃ A_i(X)`, inverse to the flat pullback,
under the explicit hypothesis that the flat pullback is injective. -/
noncomputable def zeroSectionGysin'
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE)) :
    RE.ChowGroup ≃ₗ[ℚ] RX.ChowGroup :=
  zeroSectionGysinEquiv e dimX dimE i RX RE rankOneKey hhom hinj

/-- The zero-section Gysin map undoes the flat pullback. -/
@[simp]
theorem zeroSectionGysin'_pullback
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE)) (α : RX.ChowGroup) :
    zeroSectionGysin' e dimX dimE i RX RE hhom hinj (chowPullbackBundle e dimX dimE i RX RE α) =
      α :=
  zeroSectionGysinEquiv_pullback e dimX dimE i RX RE rankOneKey hhom hinj α

/-- The flat pullback undoes the zero-section Gysin map. -/
@[simp]
theorem pullback_zeroSectionGysin'
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of A)) dimE)
    (hinj : Function.Injective (chowPullbackBundle e dimX dimE i RX RE)) (β : RE.ChowGroup) :
    chowPullbackBundle e dimX dimE i RX RE (zeroSectionGysin' e dimX dimE i RX RE hhom hinj β) =
      β :=
  pullback_zeroSectionGysinEquiv e dimX dimE i RX RE rankOneKey hhom hinj β

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
