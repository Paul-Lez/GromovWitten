/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleDerived
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineQuasiCoherent
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward
/-! # Vanishing of module-valued higher direct images for affine morphisms -/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped ZeroObject
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y : Scheme.{u}}
/-- Affine morphisms have no positive higher direct images of quasi-coherent modules. -/
theorem isZero_higherDirectImageModule_affine_succ (f : X ⟶ Y)
    [IsAffineHom f] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (higherDirectImageModule f M (n + 1)) := by
  apply module_isZero_of_underlying
  exact IsZero.of_iso
    (SheafCohomology.isZero_affineHom_rightDerived_succ f M n)
    (higherDirectImageModuleAbIso f M (n + 1))

private theorem isQuasicoherent_of_isZero (N : Y.Modules) (hN : IsZero N) :
    N.IsQuasicoherent := by
  let R : CommRingCat := Γ(Y, ⊤)
  let A : ModuleCat R := 0
  let T := (tilde.functor (R := R)).obj A
  have hT : T.IsQuasicoherent := by
    exact (presentationTilde A Set.univ (by simp) _ (Submodule.span_eq _)).isQuasicoherent
  let _ : T.IsQuasicoherent := hT
  let P := (Scheme.Modules.pullback Y.toSpecΓ).obj T
  have hP : P.IsQuasicoherent := by infer_instance
  have hTz : IsZero T := by
    exact (tilde.functor (R := R)).map_isZero (isZero_zero _)
  have hPz : IsZero P := by
    exact (Scheme.Modules.pullback Y.toSpecΓ).map_isZero hTz
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (hPz.iso hN) hP

/-- Affine pushforward is quasi-coherent in degree zero. -/
theorem isQuasicoherent_higherDirectImageModule_affine_zero (f : X ⟶ Y)
    [IsAffineHom f] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent] :
    (higherDirectImageModule f M 0).IsQuasicoherent := by
  let _ : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (higherDirectImageModuleZeroIso f M).symm inferInstance

/-- Affine pushforward is quasi-coherent in every degree. -/
theorem isQuasicoherent_higherDirectImageModule_affine (f : X ⟶ Y)
    [IsAffineHom f] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : (higherDirectImageModule f M n).IsQuasicoherent := by
  induction n with
  | zero => exact isQuasicoherent_higherDirectImageModule_affine_zero f M
  | succ n =>
      exact isQuasicoherent_of_isZero _
        (isZero_higherDirectImageModule_affine_succ f M n)
end GromovWitten.AlgebraicGeometry.Curves
