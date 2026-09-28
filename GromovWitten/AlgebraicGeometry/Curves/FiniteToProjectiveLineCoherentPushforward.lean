/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCoherentPushforward
import GromovWitten.AlgebraicGeometry.Curves.FiniteToProjectiveLineCohomology

/-!
# Degree-zero coherence over a projective line

For a finite morphism to the projective line over a Noetherian ring, the standard two affine charts
and their affine overlap supply the finite degree-zero cohomology needed by the two-affine
pushforward theorem.  This records the degree-zero coherence consequence only.
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

end GromovWitten.AlgebraicGeometry.Curves
