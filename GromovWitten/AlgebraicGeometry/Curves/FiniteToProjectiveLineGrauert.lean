/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteToProjectiveLineCohomology
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineGrauert

/-!
# Grauert conclusions for finite morphisms to the projective line

For a finite morphism to the projective line, relative stalk flatness and local constancy of the
actual degree-one fibre dimensions give projectivity of the degree-zero and degree-one cohomology.
The same specialized hypotheses give arbitrary scalar base change in degree zero.  These are
finite-to-projective-line results and do not assert a general proper-curve theorem.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : Scheme.{u}}

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- H⁰ and H¹ are projective for a finite morphism to the projective line under actual fibre H¹
local constancy and relative stalk flatness. -/
theorem finite_to_projectiveLine_projective_cohomology_zero_one
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation]
    (hflat : ∀ x : X,
      Module.Flat A (relativeStalkBase (f ≫ structureMap A) M x))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum A =>
      Module.finrank q.asIdeal.ResidueField
        (affineBaseFibreCohomology (f ≫ structureMap A) M q 1))) :
    Module.Projective A (cohomologyModuleCat A (f ≫ structureMap A) M 0) ∧
      Module.Projective A (cohomologyModuleCat A (f ≫ structureMap A) M 1) := by
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
      (cohomologyModuleCat A (f ≫ structureMap A) M 0) := h0
  let _ : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 1) := h1
  exact projective_cohomology_zero_one_of_locallyConstant_fibre
    (s := f ≫ structureMap A) M U V hU hV hI hcover hflat hd

open GromovWitten.AlgebraicGeometry.ProjectiveLine in
/-- Degree-zero cohomology has arbitrary scalar base change under the same finite-to-projective-line
Grauert hypotheses. -/
def finite_to_projectiveLine_cohomology_zero_baseChangeIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (f : X ⟶ scheme A) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation]
    (hflat : ∀ x : X,
      Module.Flat A (relativeStalkBase (f ≫ structureMap A) M x))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum A =>
      Module.finrank q.asIdeal.ResidueField
        (affineBaseFibreCohomology (f ≫ structureMap A) M q 1)))
    {T : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : CommRingCat.of A ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g (f ≫ structureMap A) (Spec.map φ)) :
    (ModuleCat.extendScalars φ.hom).obj
        (cohomologyModuleCat A (f ≫ structureMap A) M 0) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 0 := by
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
  have h1 : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 1) :=
    finite_cohomology_of_finite_to_projectiveLine A f M 1
  let _ : Module.Finite A
      (cohomologyModuleCat A (f ≫ structureMap A) M 1) := h1
  exact twoAffineCohomologyZeroBaseChangeIso_of_locallyConstant_fibre
    (s := f ≫ structureMap A) M U V hU hV hI hcover hflat hd φ p g h

end GromovWitten.AlgebraicGeometry.Curves
