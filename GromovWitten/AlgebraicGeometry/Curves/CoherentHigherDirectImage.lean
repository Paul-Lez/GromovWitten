/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImageSections
import GromovWitten.AlgebraicGeometry.Curves.AffineFinitePresentation
import GromovWitten.AlgebraicGeometry.Curves.FinitePushforward

/-!
# Finite presentation of higher direct images over affine bases

Over a Noetherian affine base, finite presentation of a quasi-coherent higher direct image is
equivalent to finite generation of its actual base-linear cohomology module.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} [IsNoetherianRing R]
  {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A higher direct image over an affine Noetherian base is finitely presented exactly when its
actual base-linear cohomology module is finite. -/
theorem isFinitePresentation_higherDirectImageModule_iff_finite_cohomology
    (s : X ⟶ Spec R) [QuasiCompact s] [IsSeparated s]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (higherDirectImageModule s M n).IsFinitePresentation ↔
      Module.Finite R (cohomologyModuleCat R s M n) := by
  constructor
  · intro h
    let H := higherDirectImageModule s M n
    let _ : H.IsFinitePresentation := h
    let _ : H.IsQuasicoherent :=
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation H
    let _ : IsIso H.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent H
    let _ : Module.FinitePresentation R (moduleSpecΓFunctor.obj H : Type u) :=
      moduleSpecΓ_isFinitePresentation H (R := R)
    have hΓ : Module.Finite R (moduleSpecΓFunctor.obj H : Type u) := inferInstance
    let _ : Module.Finite R (moduleSpecΓFunctor.obj H : Type u) := hΓ
    exact Module.Finite.equiv
      (higherDirectImageSectionsIsoCohomology s M n).toLinearEquiv
  · intro h
    let H := higherDirectImageModule s M n
    let _ : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_Spec.mpr inferInstance
    let _ : H.IsQuasicoherent :=
      isQuasicoherent_higherDirectImageModule_of_quasiCompact_separated s M n
    let _ : Module.Finite R (cohomologyModuleCat R s M n : Type u) := h
    have hΓ : Module.Finite R (moduleSpecΓFunctor.obj H : Type u) :=
      Module.Finite.equiv
        (higherDirectImageSectionsIsoCohomology s M n).symm.toLinearEquiv
    let _ : Module.Finite R (moduleSpecΓFunctor.obj H : Type u) := hΓ
    let _ : Module.FinitePresentation R (moduleSpecΓFunctor.obj H : Type u) :=
      Module.finitePresentation_of_finite R (moduleSpecΓFunctor.obj H : Type u)
    let _ : IsIso H.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent H
    exact spec_module_isFinitePresentation H

end GromovWitten.AlgebraicGeometry.Curves
