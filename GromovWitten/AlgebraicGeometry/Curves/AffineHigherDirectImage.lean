/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleDerived
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineQuasiCoherent
/-! # Vanishing of module-valued higher direct images for affine morphisms -/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
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
end GromovWitten.AlgebraicGeometry.Curves
