/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentKernels
import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackExact

/-!
# Products of quasicoherent module sheaves

Binary products of quasicoherent module sheaves are quasicoherent.  The proof first compares
products on affine spectra through the tilde--global-sections adjunction, then transports the
comparison across affine charts and assembles it over the canonical affine-open cover.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A product of quasicoherent module sheaves on an affine spectrum is quasicoherent. -/
lemma isQuasicoherent_prod_of_isQuasicoherent
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨯ N).IsQuasicoherent := by
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) moduleSpecΓFunctor :=
    (tilde.adjunction (R := R)).rightAdjoint_preservesLimits.preservesLimitsOfShape
  let _ : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let _ : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let eM : (tilde.functor R).obj (moduleSpecΓFunctor.obj M) ≅ M :=
    asIso M.fromTildeΓ
  let eN : (tilde.functor R).obj (moduleSpecΓFunctor.obj N) ≅ N :=
    asIso N.fromTildeΓ
  let eP : (tilde.functor R).obj (moduleSpecΓFunctor.obj (M ⨯ N)) ≅ M ⨯ N :=
    (tilde.functor R).mapIso (PreservesLimitPair.iso moduleSpecΓFunctor M N) ≪≫
    PreservesLimitPair.iso (tilde.functor R)
      (moduleSpecΓFunctor.obj M) (moduleSpecΓFunctor.obj N) ≪≫
      prod.mapIso eM eN
  have hQ : ((tilde.functor R).obj (moduleSpecΓFunctor.obj (M ⨯ N))).IsQuasicoherent := by
    infer_instance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso eP hQ

set_option backward.isDefEq.respectTransparency false in
/-- A product of quasicoherent module sheaves on an affine scheme is quasicoherent. -/
lemma isQuasicoherent_prod_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨯ N).IsQuasicoherent := by
  let p := X.isoSpec.inv
  let F := Scheme.Modules.pullback p
  have hprod : (F.obj M ⨯ F.obj N).IsQuasicoherent := by
    exact isQuasicoherent_prod_of_isQuasicoherent
  have hF : (F.obj (M ⨯ N)).IsQuasicoherent := by
    exact (SheafOfModules.isQuasicoherent
      (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesLimitPair.iso F M N).symm hprod
  have hP : ((Scheme.Modules.pushforward p).obj (F.obj (M ⨯ N))).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (M ⨯ N))).symm hP

set_option backward.isDefEq.respectTransparency false in
/-- Binary products preserve quasicoherence on every scheme. -/
lemma isQuasicoherent_prod {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⨯ N).IsQuasicoherent := by
  let K := M ⨯ N
  let Q : K.QuasicoherentData :=
    { I := X.affineOpens
      X := fun U => U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact iSup_affineOpens_eq_top X
      presentation := fun U => by
        let _ : IsAffine U.1.toScheme := U.2
        let F := Scheme.Modules.pullback U.1.ι
        let _ : PreservesFiniteLimits F :=
          Functor.preservesFiniteLimits_of_preservesHomology F
        have hMN : (F.obj M ⨯ F.obj N).IsQuasicoherent :=
          isQuasicoherent_prod_of_isAffine
        have hKF : (F.obj K).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            (PreservesLimitPair.iso F M N).symm hMN
        have : (K.restrict U.1.ι).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app K).symm hKF
        exact modulePresentationOver U.1 (moduleAffinePresentation (K.restrict U.1.ι)) }
  exact Q.isQuasicoherent

end GromovWitten.AlgebraicGeometry.SheafCohomology
