/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.ProjectiveLineCharts
import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackGamma
import GromovWitten.AlgebraicGeometry.Curves.AffineFinitePresentation
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Sections on the standard charts of the projective line

This file records the actual module objects of sections on the two standard
affine charts and on their Laurent overlap.  The definitions retain the
canonical `ModuleCat` scalar structures, which is useful when comparing the
two chart restrictions with the common overlap.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme
open GromovWitten.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves
open scoped LaurentPolynomial
open LaurentPolynomial

namespace GromovWitten.AlgebraicGeometry.ProjectiveLine

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The canonical Laurent-polynomial model of the overlap ring. -/
noncomputable def overlapLaurentEquiv :
    overlapRing R ≃ₐ[Polynomial R] LaurentPolynomial R :=
  IsLocalization.algEquiv (Submonoid.powers (Polynomial.X : Polynomial R))
    (overlapRing R) (LaurentPolynomial R)

@[simp]
lemma overlapLaurentEquiv_algebraMap_X :
    overlapLaurentEquiv R (algebraMap (Polynomial R) (overlapRing R) Polynomial.X) =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) := by
  simpa only [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X] using
    (overlapLaurentEquiv R).commutes Polynomial.X

@[simp]
lemma overlapLaurentEquiv_tInv :
    overlapLaurentEquiv R (tInv R) = (LaurentPolynomial.T (-1) : LaurentPolynomial R) := by
  have h := congrArg (overlapLaurentEquiv R) (algebraMap_X_mul_tInv R)
  have h' : (LaurentPolynomial.T 1 : LaurentPolynomial R) *
      overlapLaurentEquiv R (tInv R) = 1 := by
    simpa only [map_mul, map_one, overlapLaurentEquiv_algebraMap_X] using h
  apply (LaurentPolynomial.isUnit_T 1).mul_left_cancel
  calc
    (LaurentPolynomial.T 1 : LaurentPolynomial R) * overlapLaurentEquiv R (tInv R) = 1 := h'
    _ = LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) := by
      rw [← LaurentPolynomial.T_add]
      norm_num

@[simp]
lemma overlapLaurentEquiv_flipHom_X :
    overlapLaurentEquiv R (flipHom R Polynomial.X) =
      (LaurentPolynomial.T (-1) : LaurentPolynomial R) := by
  rw [flipHom_X]
  exact overlapLaurentEquiv_tInv R

/-! The second chart uses the transition homomorphism as its affine algebra map. -/

lemma flipHom_isLocalization_away :
    letI := (flipHom R).toAlgebra
    IsLocalization.Away (Polynomial.X : Polynomial R) (overlapRing R) := by
  have h := (IsLocalization.isLocalization_iff_of_ringEquiv
    (Submonoid.powers (Polynomial.X : Polynomial R)) (flipRingEquiv R)).mp inferInstance
  have e : (flipRingEquiv R).toRingHom.comp
      (algebraMap (Polynomial R) (overlapRing R)) = flipHom R := by
    apply RingHom.ext
    intro p
    exact flipRingHom_algebraMap R p
  rw [e] at h
  exact h

/-- The module of global sections of a module on one of the two standard charts. -/
abbrev chartSections (M : (scheme R).Modules) (b : Bool) :
    ModuleCat (CommRingCat.of (Polynomial R)) :=
  AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of (Polynomial R)).obj
    ((Scheme.Modules.pullback (chartMap R b)).obj M)

/-- The module of global sections of a module on the Laurent overlap. -/
abbrev overlapSections (M : (scheme R).Modules) :
    ModuleCat (CommRingCat.of (overlapRing R)) :=
  AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of (overlapRing R)).obj
    ((Scheme.Modules.pullback (overlapι R)).obj M)

/-- Finitely presented sheaves have finitely presented chart section modules. -/
lemma chartSections_isFinitePresentation
    {M : (scheme R).Modules} [M.IsFinitePresentation] [IsNoetherianRing R]
    (b : Bool) :
    Module.FinitePresentation (Polynomial R) (chartSections R M b : Type u) := by
  exact moduleSpecΓ_isFinitePresentation ((Scheme.Modules.pullback (chartMap R b)).obj M)

/-- Finitely presented sheaves have finitely presented overlap section modules. -/
lemma overlapSections_isFinitePresentation
    {M : (scheme R).Modules} [M.IsFinitePresentation] [IsNoetherianRing R] :
    Module.FinitePresentation (overlapRing R) (overlapSections R M : Type u) := by
  exact moduleSpecΓ_isFinitePresentation ((Scheme.Modules.pullback (overlapι R)).obj M)

/-- The overlap pullback obtained through the first chart. -/
def chartZeroOverlapPullback (M : (scheme R).Modules) :
    (overlap R).Modules :=
  (Scheme.Modules.pullback (overlapToChartZero R)).obj
    ((Scheme.Modules.pullback (chartZero R)).obj M)

/-- The overlap pullback obtained through the second chart. -/
def chartOneOverlapPullback (M : (scheme R).Modules) :
    (overlap R).Modules :=
  (Scheme.Modules.pullback (overlapToChartOne R)).obj
    ((Scheme.Modules.pullback (chartOne R)).obj M)

/-- Canonical identification of the first iterated overlap pullback with the overlap pullback. -/
def chartZeroOverlapPullbackIso (M : (scheme R).Modules) :
    chartZeroOverlapPullback R M ≅
      (Scheme.Modules.pullback (overlapι R)).obj M :=
  (Scheme.Modules.pullbackComp (overlapToChartZero R) (chartZero R)).app M ≪≫
    (Scheme.Modules.pullbackCongr (overlapToChartZero_comp R)).app M

/-- Canonical identification of the second iterated overlap pullback with the overlap pullback. -/
def chartOneOverlapPullbackIso (M : (scheme R).Modules) :
    chartOneOverlapPullback R M ≅
      (Scheme.Modules.pullback (overlapι R)).obj M :=
  (Scheme.Modules.pullbackComp (overlapToChartOne R) (chartOne R)).app M ≪≫
    (Scheme.Modules.pullbackCongr (overlapToChartOne_comp R)).app M

/-- Sections of the first iterated pullback and the common overlap are canonically isomorphic. -/
def chartZeroOverlapSectionsIso (M : (scheme R).Modules) :
    AlgebraicGeometry.moduleSpecΓFunctor
        (R := CommRingCat.of (overlapRing R)).obj (chartZeroOverlapPullback R M) ≅
      overlapSections R M :=
  AlgebraicGeometry.moduleSpecΓFunctor
    (R := CommRingCat.of (overlapRing R)).mapIso (chartZeroOverlapPullbackIso R M)

/-- Sections of the second iterated pullback and the common overlap are canonically isomorphic. -/
def chartOneOverlapSectionsIso (M : (scheme R).Modules) :
    AlgebraicGeometry.moduleSpecΓFunctor
        (R := CommRingCat.of (overlapRing R)).obj (chartOneOverlapPullback R M) ≅
      overlapSections R M :=
  AlgebraicGeometry.moduleSpecΓFunctor
    (R := CommRingCat.of (overlapRing R)).mapIso (chartOneOverlapPullbackIso R M)

/-- Restriction of first-chart sections to the common overlap. -/
def chartZeroRestrictionMap (M : (scheme R).Modules) :
    chartSections R M false ⟶
      (ModuleCat.restrictScalars
        (CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R))).hom).obj
        (overlapSections R M) := by
  let φ : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (overlapRing R) :=
    CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R))
  exact affinePullbackGammaUnit φ
      ((Scheme.Modules.pullback (chartZero R)).obj M) ≫
    (ModuleCat.restrictScalars φ.hom).map (chartZeroOverlapSectionsIso R M).hom

/-- Restriction of second-chart sections to the common overlap. -/
def chartOneRestrictionMap (M : (scheme R).Modules) :
    chartSections R M true ⟶
      (ModuleCat.restrictScalars (CommRingCat.ofHom (flipHom R)).hom).obj
        (overlapSections R M) := by
  let φ : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (overlapRing R) :=
    CommRingCat.ofHom (flipHom R)
  exact affinePullbackGammaUnit φ
      ((Scheme.Modules.pullback (chartOne R)).obj M) ≫
    (ModuleCat.restrictScalars φ.hom).map (chartOneOverlapSectionsIso R M).hom

/-- The first-chart restriction is the localization map at the chart coordinate. -/
lemma chartZeroRestrictionMap_isLocalizedModule
    {M : (scheme R).Modules} [M.IsQuasicoherent] :
    IsLocalizedModule.Away (Polynomial.X : Polynomial R)
      (chartZeroRestrictionMap R M).hom := by
  let φ : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (overlapRing R) :=
    CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R))
  have h := affinePullbackGammaUnit_isLocalizedModule
    (R := Polynomial R) (S := overlapRing R)
    (Submonoid.powers (Polynomial.X : Polynomial R))
    ((Scheme.Modules.pullback (chartZero R)).obj M)
  have hlocal : IsLocalizedModule (Submonoid.powers (Polynomial.X : Polynomial R))
      (affinePullbackGammaUnit
        (CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R)))
        ((Scheme.Modules.pullback (chartZero R)).obj M)).hom := h
  let e := (ModuleCat.restrictScalars φ.hom).mapIso
    (chartZeroOverlapSectionsIso R M)
  change IsLocalizedModule (Submonoid.powers (Polynomial.X : Polynomial R))
    (e.hom.hom.comp
      (affinePullbackGammaUnit
        (CommRingCat.ofHom (algebraMap (Polynomial R) (overlapRing R)))
        ((Scheme.Modules.pullback (chartZero R)).obj M)).hom)
  exact IsLocalizedModule.of_linearEquiv
    (Submonoid.powers (Polynomial.X : Polynomial R)) _ e.toLinearEquiv (hf := hlocal)

/-- The second-chart restriction is the same localization after the transition map. -/
lemma chartOneRestrictionMap_isLocalizedModule
    {M : (scheme R).Modules} [M.IsQuasicoherent] :
    IsLocalizedModule.Away (Polynomial.X : Polynomial R)
      (chartOneRestrictionMap R M).hom := by
  let : Algebra (Polynomial R) (overlapRing R) := (flipHom R).toAlgebra
  have hloc : IsLocalization.Away (Polynomial.X : Polynomial R) (overlapRing R) :=
    flipHom_isLocalization_away R
  let φ : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (overlapRing R) :=
    CommRingCat.ofHom (flipHom R)
  have h := affinePullbackGammaUnit_isLocalizedModule
    (R := Polynomial R) (S := overlapRing R)
    (Submonoid.powers (Polynomial.X : Polynomial R))
    ((Scheme.Modules.pullback (chartOne R)).obj M)
  have hlocal : IsLocalizedModule (Submonoid.powers (Polynomial.X : Polynomial R))
      (affinePullbackGammaUnit
        (CommRingCat.ofHom (flipHom R))
        ((Scheme.Modules.pullback (chartOne R)).obj M)).hom := h
  let e := (ModuleCat.restrictScalars φ.hom).mapIso
    (chartOneOverlapSectionsIso R M)
  change IsLocalizedModule (Submonoid.powers (Polynomial.X : Polynomial R))
    (e.hom.hom.comp
      (affinePullbackGammaUnit
        (CommRingCat.ofHom (flipHom R))
        ((Scheme.Modules.pullback (chartOne R)).obj M)).hom)
  exact IsLocalizedModule.of_linearEquiv
    (Submonoid.powers (Polynomial.X : Polynomial R)) _ e.toLinearEquiv (hf := hlocal)

end
end GromovWitten.AlgebraicGeometry.ProjectiveLine
