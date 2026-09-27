/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImage
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChange
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPullback

/-!
# Affine higher base change

For an affine family, the positive-degree terms of the flat base-change comparison
are isomorphisms because both terms vanish.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Z : Scheme.{u}}

/-- In positive degrees, flat base change for an affine family is an isomorphism.

The pulled-back module is quasi-coherent by the general pullback theorem. -/
theorem moduleFlatHigherBaseChange_succ_isIso
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsAffineHom f] [Flat b]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso ((moduleFlatHigherBaseChangeNatTrans f b p g h (n + 1)).app M) := by
  let _ : IsAffineHom g :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h inferInstance
  have hsource : IsZero ((Scheme.Modules.pullback b).obj
      (higherDirectImageModule f M (n + 1))) :=
    (Scheme.Modules.pullback b).map_isZero
      (isZero_higherDirectImageModule_affine_succ f M n)
  have htarget : IsZero (higherDirectImageModule g ((Scheme.Modules.pullback p).obj M) (n + 1)) :=
    isZero_higherDirectImageModule_affine_succ g ((Scheme.Modules.pullback p).obj M) n
  exact hsource.isIso htarget
    ((moduleFlatHigherBaseChangeNatTrans f b p g h (n + 1)).app M)

end GromovWitten.AlgebraicGeometry.Curves
