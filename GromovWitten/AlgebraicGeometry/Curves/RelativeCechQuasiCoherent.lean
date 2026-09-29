/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentProducts
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentKernels
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward

/-!
# Quasicoherence of relative two-open Čech modules

Affine composite morphisms make the relative open pushforwards quasicoherent.  Products and
cokernels of the resulting modules are then quasicoherent without additional finiteness or
flatness hypotheses.
-/

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The relative pushforward from an open piece is quasicoherent when its composite is affine. -/
lemma relativeOpenPushforward_isQuasicoherent (s : X ⟶ S) (U : X.Opens)
    (M : X.Modules) [M.IsQuasicoherent] [IsAffineHom (U.ι ≫ s)] :
    ((relativeOpenPushforward s U).obj M).IsQuasicoherent := by
  have hP : ((pushforward (U.ι ≫ s)).obj (M.restrict U.ι)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((pushforwardComp U.ι s).app (M.restrict U.ι)).symm hP

set_option backward.isDefEq.respectTransparency false in
/-- The pair of relative open pushforwards is quasicoherent when both composites are affine. -/
lemma relativeCechPairFunctor_isQuasicoherent (s : X ⟶ S) (U V : X.Opens)
    (M : X.Modules) [M.IsQuasicoherent] [IsAffineHom (U.ι ≫ s)]
    [IsAffineHom (V.ι ≫ s)] :
    ((relativeCechPairFunctor s U V).obj M).IsQuasicoherent := by
  let hU : ((relativeOpenPushforward s U).obj M).IsQuasicoherent :=
    relativeOpenPushforward_isQuasicoherent s U M
  let hV : ((relativeOpenPushforward s V).obj M).IsQuasicoherent :=
    relativeOpenPushforward_isQuasicoherent s V M
  change ((relativeOpenPushforward s U).obj M ⨯
    (relativeOpenPushforward s V).obj M).IsQuasicoherent
  exact @isQuasicoherent_prod _ _ _ hU hV

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech cokernel is quasicoherent when all three affine composites are affine. -/
lemma relativeCechFromPair_cokernel_isQuasicoherent (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) [M.IsQuasicoherent] [IsAffineHom (U.ι ≫ s)]
    [IsAffineHom (V.ι ≫ s)] [IsAffineHom ((U ⊓ V).ι ≫ s)] :
    (cokernel (relativeCechFromPair s M U V)).IsQuasicoherent := by
  let hPair : ((relativeCechPairFunctor s U V).obj M).IsQuasicoherent :=
    relativeCechPairFunctor_isQuasicoherent s U V M
  let hI : ((relativeOpenPushforward s (U ⊓ V)).obj M).IsQuasicoherent :=
    relativeOpenPushforward_isQuasicoherent s (U ⊓ V) M
  exact @isQuasicoherent_cokernel _ _ _ (relativeCechFromPair s M U V) hPair hI

end GromovWitten.AlgebraicGeometry.Curves
