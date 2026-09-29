/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechDerived
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechGlobalSections
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineCokernelSections

/-!
# Global sections of the first relative higher direct image

For an affine two-open cover, the relative Čech comparison and the canonical affine
global-sections comparison identify global sections of the first higher direct image with the
first cohomology module.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : CommRingCat.{u}} {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- Global sections of relative first higher direct image agree with first cohomology.

The source is locally Noetherian and quasicoherent, while the two open composites and their
intersection are affine over the base and cover the source.
-/
def higherDirectImageOneSectionsIsoCohomology
    (s : X ⟶ Spec R) (M : X.Modules) [IsLocallyNoetherian X] [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤) :
    (moduleSpecΓFunctor (R := R)).obj (higherDirectImageModule s M 1) ≅
      ModuleCat.of R (cohomologyModuleCat R s M 1) := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let _ : IsAffine (U ⊓ V).toScheme := hI
  let _ : ((relativeOpenPushforward s U).obj M ⨯
      (relativeOpenPushforward s V).obj M).IsQuasicoherent :=
    relativeCechPairFunctor_isQuasicoherent s U V M
  let _ : ((relativeOpenPushforward s (U ⊓ V)).obj M).IsQuasicoherent :=
    relativeOpenPushforward_isQuasicoherent s (U ⊓ V) M
  exact (moduleSpecΓFunctor (R := R)).mapIso
      (relativeCechCokernelIsoHigherDirectImageOne s M U V hcover).symm ≪≫
    (moduleSpecΓCokernelIso (relativeCechFromPair s M U V)).symm ≪≫
    relativeCechGammaCokernelIso s M U V ≪≫
    baseCechCokernelIsoCohomology s M U V hU hV hcover
end GromovWitten.AlgebraicGeometry.Curves
