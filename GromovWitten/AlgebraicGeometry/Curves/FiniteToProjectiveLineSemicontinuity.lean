/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteToProjectiveLineCohomology
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFibreCohomologyZero
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFibreCohomologyOne

/-!
# Fibre cohomology semicontinuity over the projective line

For a finite morphism to the projective line, relative stalk flatness and finite actual base
cohomology give upper semicontinuity of the degree-zero and degree-one fibre dimensions.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- Fibre dimensions in degrees zero and one are upper semicontinuous for a finite morphism to the
projective line under relative stalk flatness. -/
theorem finite_to_projectiveLine_fibre_cohomology_semicontinuous
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation]
    (hflat : ∀ x : X,
      Module.Flat A (relativeStalkBase (f ≫ structureMap A) M x)) :
    UpperSemicontinuous (fun q : PrimeSpectrum A =>
      Module.finrank q.asIdeal.ResidueField
        (affineBaseFibreCohomology (f ≫ structureMap A) M q 0)) ∧
    UpperSemicontinuous (fun q : PrimeSpectrum A =>
      Module.finrank q.asIdeal.ResidueField
        (affineBaseFibreCohomology (f ≫ structureMap A) M q 1)) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : M.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  let _ : LocallyOfFiniteType (f ≫ structureMap A) := inferInstance
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
  have h1 : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 1) :=
    finite_cohomology_of_finite_to_projectiveLine A f M 1
  let _ : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 1) := h1
  exact ⟨
    upperSemicontinuous_affineBaseFibreCohomology_zero
      (s := f ≫ structureMap A) M U V hU hV hI hcover hflat h0 h1,
    upperSemicontinuous_affineBaseFibreCohomology_one
      (s := f ≫ structureMap A) M U V hU hV hI hcover⟩

end GromovWitten.AlgebraicGeometry.Curves
