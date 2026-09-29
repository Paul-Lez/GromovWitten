/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward

/-!
# Affine-locality of quasicoherence

Quasicoherence of a module on a scheme follows from quasicoherence after pullback
to every affine open.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

set_option backward.isDefEq.respectTransparency false in
/-- Quasicoherence can be checked after restricting to every affine open. -/
lemma isQuasicoherent_of_affine_pullback
    {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ U : X.affineOpens,
      ((Scheme.Modules.pullback U.1.ι).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  let Q : M.QuasicoherentData :=
    { I := X.affineOpens
      X := fun U => U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact iSup_affineOpens_eq_top X
      presentation := fun U => by
        let _ : IsAffine U.1.toScheme := U.2
        have hR : (M.restrict U.1.ι).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app M).symm (hM U)
        let _ : (M.restrict U.1.ι).IsQuasicoherent := hR
        exact modulePresentationOver U.1 (moduleAffinePresentation (M.restrict U.1.ι)) }
  exact Q.isQuasicoherent

end GromovWitten.AlgebraicGeometry.SheafCohomology
