/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCoherentPushforward
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCoherentHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.FiniteToProjectiveLineCohomology

/-!
# Coherence of higher direct images over a projective line

For a finite morphism to the projective line over a Noetherian ring, the standard two affine charts
and their affine overlap supply finite degree-zero and degree-one cohomology.  The two-affine
vanishing argument kills all higher degrees, giving finite presentation of every higher direct
image.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- The pushforward to the affine base of a finite projective-line family is finitely presented
in degree zero. -/
lemma isFinitePresentation_pushforward_structureMap_of_finite_to_projectiveLine
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward (f ≫ structureMap A)).obj M).IsFinitePresentation := by
  let _ : M.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let U : X.Opens := f ⁻¹ᵁ (chartZero A).opensRange
  let V : X.Opens := f ⁻¹ᵁ (chartOne A).opensRange
  have hU : IsAffineOpen U := by
    dsimp [U]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartZero A)
  have hV : IsAffineOpen V := by
    dsimp [V]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartOne A)
  have hIbase : IsAffineOpen (overlapι A).opensRange :=
    isAffineOpen_opensRange _
  have hI : IsAffineOpen (U ⊓ V) := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_inf, opensRange_chartZero_inf_chartOne A]
    exact IsAffineHom.isAffine_preimage (f := f) _ hIbase
  have hcover : U ⊔ V = ⊤ := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_sup, opensRange_chartZero_sup_chartOne A,
      Scheme.Hom.preimage_top]
  have h0 : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 0) :=
    finite_cohomology_of_finite_to_projectiveLine A f M 0
  simpa [U, V] using
    (isFinitePresentation_pushforward_of_twoAffine (s := f ≫ structureMap A) M U V
      hU hV hI hcover h0)

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- The first higher direct image of a finite projective-line family is finitely presented over
the Noetherian base. -/
lemma isFinitePresentation_higherDirectImageModule_one_of_finite_to_projectiveLine
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] :
    (higherDirectImageModule (f ≫ structureMap A) M 1).IsFinitePresentation := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let U : X.Opens := f ⁻¹ᵁ (chartZero A).opensRange
  let V : X.Opens := f ⁻¹ᵁ (chartOne A).opensRange
  have hU : IsAffineOpen U := by
    dsimp [U]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartZero A)
  have hV : IsAffineOpen V := by
    dsimp [V]
    exact IsAffineHom.isAffine_preimage (f := f) _
      (isAffineOpen_opensRange_chartOne A)
  have hIbase : IsAffineOpen (overlapι A).opensRange :=
    isAffineOpen_opensRange _
  have hI : IsAffineOpen (U ⊓ V) := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_inf, opensRange_chartZero_inf_chartOne A]
    exact IsAffineHom.isAffine_preimage (f := f) _ hIbase
  have hcover : U ⊔ V = ⊤ := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_sup, opensRange_chartZero_sup_chartOne A,
      Scheme.Hom.preimage_top]
  have h1 : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 1) :=
    finite_cohomology_of_finite_to_projectiveLine A f M 1
  simpa [U, V] using
    (isFinitePresentation_higherDirectImageModule_one_of_twoAffine
      (s := f ≫ structureMap A) M U V hU hV hI hcover h1)

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
  cases n with
  | zero =>
      exact (SheafOfModules.isFinitePresentation
        (Spec (CommRingCat.of A)).ringCatSheaf).prop_of_iso
        (higherDirectImageModuleZeroIso (f ≫ structureMap A) M).symm
        (isFinitePresentation_pushforward_structureMap_of_finite_to_projectiveLine A f M)
  | succ n =>
      cases n with
      | zero =>
          exact isFinitePresentation_higherDirectImageModule_one_of_finite_to_projectiveLine
            A f M
      | succ n =>
          exact module_isFinitePresentation_of_isZero _
            (isZero_higherDirectImageModule_of_affine_to_projectiveLine A f M n)

end GromovWitten.AlgebraicGeometry.Curves
