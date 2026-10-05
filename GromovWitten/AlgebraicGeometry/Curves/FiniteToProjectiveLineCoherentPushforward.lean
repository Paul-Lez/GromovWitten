/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CoherentHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.FiniteToProjectiveLineCohomology
import GromovWitten.AlgebraicGeometry.ProjectiveLineSeparated

/-!
# Coherence of higher direct images over the projective line

For a finite morphism to the projective line over a Noetherian ring, finite cohomology over the
base gives finite presentation of every higher direct image.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- Every higher direct image of a finitely presented module under a finite morphism to the
projective line is finitely presented over the Noetherian base. -/
theorem isFinitePresentation_higherDirectImageModule_of_finite_to_projectiveLine
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] (n : ℕ) :
    (higherDirectImageModule (f ≫ structureMap A) M n).IsFinitePresentation := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  exact (isFinitePresentation_higherDirectImageModule_iff_finite_cohomology
      (s := f ≫ structureMap A) M n).2
    (finite_cohomology_of_finite_to_projectiveLine A f M n)

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- The pushforward to the affine base of a finite projective-line family is finitely presented
in degree zero. -/
lemma isFinitePresentation_pushforward_structureMap_of_finite_to_projectiveLine
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward (f ≫ structureMap A)).obj M).IsFinitePresentation := by
  exact (SheafOfModules.isFinitePresentation
      (Spec (CommRingCat.of A)).ringCatSheaf).prop_of_iso
    (higherDirectImageModuleZeroIso (f ≫ structureMap A) M)
    (isFinitePresentation_higherDirectImageModule_of_finite_to_projectiveLine A f M 0)

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- The first higher direct image of a finite projective-line family is finitely presented over
the Noetherian base. -/
lemma isFinitePresentation_higherDirectImageModule_one_of_finite_to_projectiveLine
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] :
    (higherDirectImageModule (f ≫ structureMap A) M 1).IsFinitePresentation :=
  isFinitePresentation_higherDirectImageModule_of_finite_to_projectiveLine A f M 1

end GromovWitten.AlgebraicGeometry.Curves
