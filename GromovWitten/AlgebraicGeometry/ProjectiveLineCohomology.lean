/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineHigherVanishing
import GromovWitten.AlgebraicGeometry.ProjectiveLineCharts

/-!
# Higher direct-image vanishing for the projective line

The two standard affine charts and their affine overlap give a relative vanishing theorem for
quasi-coherent modules on the projective line over a Noetherian base ring.
-/

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.ProjectiveLine

/-- Higher direct images along the structure morphism of the projective line vanish in degrees
at least two for every quasi-coherent module over a Noetherian base ring. -/
theorem isZero_higherDirectImageModule_structureMap
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : (scheme R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (higherDirectImageModule (structureMap R) M (n + 2)) := by
  let U : (scheme R).Opens := (chartZero R).opensRange
  let V : (scheme R).Opens := (chartOne R).opensRange
  let _ : IsAffine U.toScheme := isAffineOpen_opensRange_chartZero R
  let _ : IsAffine V.toScheme := isAffineOpen_opensRange_chartOne R
  have hI : IsAffineOpen (U ⊓ V) := by
    dsimp [U, V]
    rw [opensRange_chartZero_inf_chartOne R]
    exact isAffineOpen_opensRange _
  let _ : IsAffine (U ⊓ V).toScheme := hI
  let _ : IsAffineHom (U.ι ≫ structureMap R) := inferInstance
  let _ : IsAffineHom (V.ι ≫ structureMap R) := inferInstance
  let _ : IsAffineHom ((U ⊓ V).ι ≫ structureMap R) := inferInstance
  exact isZero_higherDirectImageModule_twoAffineCover (structureMap R) U V
    (opensRange_chartZero_sup_chartOne R) M n

end GromovWitten.AlgebraicGeometry.ProjectiveLine
