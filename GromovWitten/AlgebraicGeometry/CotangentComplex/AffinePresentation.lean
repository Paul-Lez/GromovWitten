/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Picard
import GromovWitten.AlgebraicGeometry.ObstructionTheory.Basic
import Mathlib.RingTheory.Extension.Cotangent.BaseChange

/-!
# The affine presentation cotangent complex

For a polynomial presentation of an algebra, Mathlib constructs the conormal module, the free
module of ambient differentials, and the cotangent differential between them.  This file packages
that actual map as the cohomological two-term complex in degrees `-1,0` used by local embeddings.
Its exact sequence to Kähler differentials is the affine comparison input for the geometric
cotangent complex.  The presentation is also localized to an actual derived object below, and
when its two terms are finite locally free it supplies its own global two-term resolution.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

open CategoryTheory TensorProduct

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

namespace AffinePresentation

attribute [local instance] HasDerivedCategory.standard

variable (P : Algebra.Extension.{v} R S)

/-- The presentation complex `I/I² → ⊕ S dx_i`, displayed in cohomological degrees
`-1,0` (and reindexed as degrees zero and one for the Picard quotient API). -/
noncomputable def twoTerm : LinearTwoTermComplex S where
  degreeZero := P.Cotangent
  degreeOne := P.CotangentSpace
  differential := P.cotangentComplex

@[simp]
theorem twoTerm_differential : (twoTerm R S P).differential = P.cotangentComplex :=
  rfl

/-- The affine presentation as an honest cochain complex in degrees `-1` and `0`. -/
noncomputable def cochainComplex : CochainComplex (ModuleCat.{v} S) ℤ :=
  (twoTerm R S P).toCochainComplex

/-- The derived object represented by the actual affine cotangent presentation. -/
noncomputable def derivedObject : DerivedCategory (ModuleCat.{v} S) :=
  DerivedCategory.Q.obj (cochainComplex R S P)

/-- The degree `-1` term of the cochain realization is the conormal module. -/
theorem cochainComplex_X_negOne :
    (cochainComplex R S P).X (-1) = ModuleCat.of S P.Cotangent :=
  (twoTerm R S P).toCochainComplex_X_negOne

/-- The degree `0` term of the cochain realization is the ambient cotangent-space module. -/
theorem cochainComplex_X_zero :
    (cochainComplex R S P).X 0 = ModuleCat.of S P.CotangentSpace :=
  (twoTerm R S P).toCochainComplex_X_zero

/-
Retired predicate-parametric resolution constructor.  Although its complex was concrete, the
meaning of `FiniteLocallyFree` was caller-selectable.  The proper-point example constructs its
fixed finite-free resolution directly from this file's `cochainComplex`.

/-- The affine presentation itself gives a global two-term resolution of its derived
localization as soon as its two displayed terms satisfy the requested finite-locally-free
predicate.  No independently chosen complex or comparison is accepted. -/
noncomputable def globalResolution
    (FiniteLocallyFree : ModuleCat.{v} S → Prop)
    (hNeg : FiniteLocallyFree (ModuleCat.of S P.Cotangent))
    (hZero : FiniteLocallyFree (ModuleCat.of S P.CotangentSpace)) :
    DerivedObstructionTheory.GlobalTwoTermResolution
      FiniteLocallyFree (derivedObject R S P) where
  complex := cochainComplex R S P
  zero_outside i hiNeg hiZero :=
    (twoTerm R S P).toCochainComplex_X_isZero i hiNeg hiZero
  negative_finiteLocallyFree := by
    rw [cochainComplex_X_negOne]
    exact hNeg
  zero_finiteLocallyFree := by
    rw [cochainComplex_X_zero]
    exact hZero
  comparison := Iso.refl _

-/

/-- The degree `-1` cohomology of the presentation complex is Mathlib's first cotangent
module. -/
abbrev hNegOne := P.H1Cotangent

/-- The degree `0` cycles map canonically to Kähler differentials. -/
noncomputable abbrev toKaehler : P.CotangentSpace →ₗ[S] KaehlerDifferential R S :=
  P.toKaehler

/-- Exactness of the presentation cotangent differential followed by the map to Kähler
differentials. -/
theorem exact_cotangent_toKaehler :
    Function.Exact (twoTerm R S P).differential (toKaehler R S P) :=
  P.exact_cotangentComplex_toKaehler

/-- The image of the degree `-1` differential is the kernel of the map to Kähler
differentials. -/
theorem range_differential_eq_ker_toKaehler :
    LinearMap.range (twoTerm R S P).differential = LinearMap.ker (toKaehler R S P) :=
  (LinearMap.exact_iff.mp (exact_cotangent_toKaehler R S P)).symm

/-- A morphism of polynomial presentations gives the functorial map on conormal terms. -/
noncomputable abbrev mapCotangent {P' : Algebra.Extension.{v} R S} (f : P.Hom P') :
    P.Cotangent →ₗ[S] P'.Cotangent :=
  Algebra.Extension.Cotangent.map f

/-- A morphism of polynomial presentations gives the functorial map on ambient differential
terms. -/
noncomputable abbrev mapCotangentSpace {P' : Algebra.Extension.{v} R S} (f : P.Hom P') :
    P.CotangentSpace →ₗ[S] P'.CotangentSpace :=
  Algebra.Extension.CotangentSpace.map f

/-- Functoriality commutes with the cotangent differential. -/
theorem map_comm {P' : Algebra.Extension.{v} R S} (f : P.Hom P') :
    (mapCotangentSpace R S P f).comp (twoTerm R S P).differential =
      (twoTerm R S P').differential.comp (mapCotangent R S P f) :=
  Algebra.Extension.CotangentSpace.map_comp_cotangentComplex f

section BaseChange

variable (T : Type*) [CommRing T] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The degree-zero ambient differential term commutes with arbitrary scalar base change. -/
noncomputable abbrev tensorCotangentSpace :
    (T ⊗[R] P.CotangentSpace) ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace :=
  P.tensorCotangentSpace T

/-- Under flat scalar extension, the conormal term of the presentation complex commutes with
base change. -/
noncomputable abbrev tensorCotangentOfFlat [Module.Flat R T] :
    (T ⊗[R] P.Cotangent) ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  P.tensorCotangentOfFlat T

/-- Under flat scalar extension, degree `-1` cohomology of the presentation cotangent complex
commutes with base change. -/
noncomputable abbrev tensorHNegOneOfFlat [Module.Flat R T] :
    (T ⊗[R] P.H1Cotangent) ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  P.tensorH1CotangentOfFlat T

@[simp]
theorem tensorCotangentSpace_tmul (t : T) (x : P.CotangentSpace) :
    tensorCotangentSpace R S P T (t ⊗ₜ[R] x) =
      t • Algebra.Extension.CotangentSpace.map (P.toBaseChange T) x :=
  P.tensorCotangentSpace_tmul T t x

@[simp]
theorem tensorCotangentOfFlat_tmul [Module.Flat R T]
    (t : T) (x : P.Cotangent) :
    tensorCotangentOfFlat R S P T (t ⊗ₜ[R] x) =
      t • Algebra.Extension.Cotangent.map (P.toBaseChange T) x :=
  P.tensorCotangentOfFlat_tmul T t x

theorem tensorHNegOneOfFlat_tmul [Module.Flat R T]
    (t : T) (x : P.H1Cotangent) :
    tensorHNegOneOfFlat R S P T (t ⊗ₜ[R] x) =
      t • Algebra.Extension.H1Cotangent.map (P.toBaseChange T) x :=
  P.tensorH1CotangentOfFlat_tmul T t x

end BaseChange

end AffinePresentation

end GromovWitten.AlgebraicGeometry.CotangentComplex
