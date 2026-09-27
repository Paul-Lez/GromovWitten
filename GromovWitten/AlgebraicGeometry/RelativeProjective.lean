/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.RelativeProj
import Mathlib.RingTheory.GradedAlgebra.FiniteType

/-!
# Relative projective morphisms

`RelativeProj.relativeProj` is a construction from affine-local graded data.  This file records
the data needed to use that construction as a projective morphism: an identification with the
given morphism, degree-zero identification with the base, and finite type over degree zero.
Positive homogeneous generators are derived from finite type when a downstream construction needs
them, so an arbitrary graded algebra cannot be mistaken for a projective presentation.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u
noncomputable section

structure RelativeProjective {X Y : Scheme.{u}} (p : Y ⟶ X) where
  /-- The affine-local graded algebra presenting the source. -/
  data : GradedAlgebraData X
  /-- The chosen identification of the source with the glued relative `Proj`. -/
  iso : Y ≅ RelativeProj.relativeProj X data
  /-- The identification is over the base. -/
  iso_toBase : iso.hom ≫ RelativeProj.toBase X data = p
  /-- Each affine graded algebra is finite type over its degree-zero part. -/
  finiteType : ∀ U, Algebra.FiniteType (data.grading U 0) (data.ring U)
  /-- The degree-zero algebra is the section ring of the affine open. -/
  degreeZero : ∀ U,
    Function.Bijective (algebraMap Γ(X, U.1) (data.grading U 0))

namespace RelativeProjective

variable {X Y : Scheme.{u}} {p : Y ⟶ X} (P : RelativeProjective p)

/-- The canonical projectivity witness for the morphism constructed by `RelativeProj`.  This
construction is useful when the source is introduced as the relative `Proj` itself: no source
isomorphism or projectivity result is supplied by the caller. -/
def ofRelativeProj (X : Scheme.{u}) (data : GradedAlgebraData X)
    (hfinite : ∀ U, Algebra.FiniteType (data.grading U 0) (data.ring U))
    (hzero : ∀ U, Function.Bijective (algebraMap Γ(X, U.1) (data.grading U 0))) :
    RelativeProjective (RelativeProj.toBase X data) where
  data := data
  iso := Iso.refl _
  iso_toBase := by simp
  finiteType := hfinite
  degreeZero := hzero

/-- The positive homogeneous generation field follows from finite type, but is exposed by the
projectivity witness so downstream constructions can use it without reconstructing generators. -/
theorem positiveGenerators_of_finiteType (U : X.affineOpens) :
    ∃ s : Finset (P.data.ring U),
      Algebra.adjoin (A := P.data.ring U) (P.data.grading U 0) s = ⊤ ∧
        ∀ a ∈ s, ∃ n ≠ 0, a ∈ P.data.grading U n := by
  let _ : Algebra.FiniteType (P.data.grading U 0) (P.data.ring U) := P.finiteType U
  exact GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero
    (P.data.grading U)

/-- A finite-type relative projective presentation gives a proper morphism. -/
theorem isProper (P : RelativeProjective p) : IsProper p := by
  rw [← P.iso_toBase]
  have h : IsProper (RelativeProj.toBase X P.data) :=
    @RelativeProj.toBase_isProper X P.data P.finiteType P.degreeZero
  infer_instance

/-- Source isomorphisms transport a relative projective presentation. -/
def transportSource {Y' : Scheme.{u}} (e : Y' ≅ Y) :
    RelativeProjective (e.hom ≫ p) where
  data := P.data
  iso := e ≪≫ P.iso
  iso_toBase := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [P.iso_toBase]
  finiteType := P.finiteType
  degreeZero := P.degreeZero

@[simp]
theorem transportSource_iso_toBase {Y' : Scheme.{u}} (e : Y' ≅ Y) :
    (transportSource P e).iso.hom ≫ RelativeProj.toBase X P.data = e.hom ≫ p := by
  exact (transportSource P e).iso_toBase

/-! ### Affine restriction -/

/-- The affine chart over an affine base is itself a canonical relative-projective presentation.
The source is the whole-base affine `Proj`, identified with the glued relative `Proj` by the
cartesian affine restriction theorem. -/
def ofAffineRelativeProj [IsAffine X] (data : GradedAlgebraData X)
    (hfinite : ∀ U, Algebra.FiniteType (data.grading U 0) (data.ring U))
    (hzero : ∀ U, Function.Bijective (algebraMap Γ(X, U.1) (data.grading U 0))) :
    RelativeProjective
      ((RelativeProj.affineιIso X data).hom ≫ RelativeProj.toBase X data) :=
  transportSource (ofRelativeProj X data hfinite hzero) (RelativeProj.affineιIso X data)

/-- On an affine base the source has a canonical affine `Proj` model. -/
def affineModelIso [IsAffine X] :
    Y ≅ (RelativeProj.gluingFunctor X P.data).obj (RelativeProj.topIndex X) :=
  P.iso ≪≫ (RelativeProj.affineιIso X P.data).symm

theorem affineModelIso_hom_comp_affineι [IsAffine X] :
    (affineModelIso P).hom ≫ (RelativeProj.affineιIso X P.data).hom =
      P.iso.hom := by
  change (P.iso.hom ≫ (RelativeProj.affineιIso X P.data).inv) ≫
      (RelativeProj.affineιIso X P.data).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end RelativeProjective

end
end GromovWitten.AlgebraicGeometry
