/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.TildeExact
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.Curves.ModulePullbackExact
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward

/-!
# Kernels and cokernels of quasi-coherent modules

This file proves that kernels and cokernels of morphisms between quasi-coherent modules remain
quasi-coherent on arbitrary schemes.  The affine statement is transported through the exact tilde
functor, and affine-local presentations then give the general result.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- On an affine spectrum, the kernel of a morphism between quasi-coherent modules is
quasi-coherent. -/
lemma isQuasicoherent_kernel_of_isQuasicoherent
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  let _ : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let _ : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let eM : (tilde.functor R).obj (moduleSpecΓFunctor.obj M) ≅ M :=
    asIso M.fromTildeΓ
  let eN : (tilde.functor R).obj (moduleSpecΓFunctor.obj N) ≅ N :=
    asIso N.fromTildeΓ
  have hsq : (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f) ≫ eN.hom =
      eM.hom ≫ f := by
    change (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f
    exact (tilde.adjunction (R := R)).counit.naturality f
  let eK : (tilde.functor R).obj (kernel ((moduleSpecΓFunctor (R := R)).map f)) ≅
      kernel f :=
    PreservesKernel.iso (tilde.functor R) ((moduleSpecΓFunctor (R := R)).map f) ≪≫
      kernel.mapIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f)) f eM eN hsq
  have hQ : ((tilde.functor R).obj
      (kernel ((moduleSpecΓFunctor (R := R)).map f))).IsQuasicoherent := by
    infer_instance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso eK hQ

set_option backward.isDefEq.respectTransparency false in
/-- On an affine spectrum, the cokernel of a morphism between quasi-coherent modules is
quasi-coherent. -/
lemma isQuasicoherent_cokernel_of_isQuasicoherent
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  let _ : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let _ : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let eM : (tilde.functor R).obj (moduleSpecΓFunctor.obj M) ≅ M :=
    asIso M.fromTildeΓ
  let eN : (tilde.functor R).obj (moduleSpecΓFunctor.obj N) ≅ N :=
    asIso N.fromTildeΓ
  have hsq : (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f) ≫ eN.hom =
      eM.hom ≫ f := by
    change (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f
    exact (tilde.adjunction (R := R)).counit.naturality f
  let eQ : (tilde.functor R).obj (cokernel ((moduleSpecΓFunctor (R := R)).map f)) ≅
      cokernel f :=
    PreservesCokernel.iso (tilde.functor R) ((moduleSpecΓFunctor (R := R)).map f) ≪≫
      cokernel.mapIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map f)) f eM eN hsq
  have hQ : ((tilde.functor R).obj
      (cokernel ((moduleSpecΓFunctor (R := R)).map f))).IsQuasicoherent := by
    infer_instance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso eQ hQ

set_option backward.isDefEq.respectTransparency false in
/-- On any affine scheme, the kernel of a morphism between quasi-coherent modules is
quasi-coherent. -/
lemma isQuasicoherent_kernel_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  let p := X.isoSpec.inv
  let F := Scheme.Modules.pullback p
  have : (kernel (F.map f)).IsQuasicoherent :=
    isQuasicoherent_kernel_of_isQuasicoherent (F.map f)
  have : (F.obj (kernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesKernel.iso F f).symm inferInstance
  have hP : ((Scheme.Modules.pushforward p).obj (F.obj (kernel f))).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (kernel f))).symm hP

set_option backward.isDefEq.respectTransparency false in
/-- On any affine scheme, the cokernel of a morphism between quasi-coherent modules is
quasi-coherent. -/
lemma isQuasicoherent_cokernel_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  let p := X.isoSpec.inv
  let F := Scheme.Modules.pullback p
  have : (cokernel (F.map f)).IsQuasicoherent :=
    isQuasicoherent_cokernel_of_isQuasicoherent (F.map f)
  have : (F.obj (cokernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso F f).symm inferInstance
  have hP : ((Scheme.Modules.pushforward p).obj (F.obj (cokernel f))).IsQuasicoherent :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (cokernel f))).symm hP

set_option backward.isDefEq.respectTransparency false in
/-- Kernels of morphisms between quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (kernel f).IsQuasicoherent := by
  let K := kernel f
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
        have : (kernel (F.map f)).IsQuasicoherent :=
          isQuasicoherent_kernel_of_isAffine (F.map f)
        have hKF : (F.obj K).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            (PreservesKernel.iso F f).symm inferInstance
        have : (K.restrict U.1.ι).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app K).symm hKF
        exact modulePresentationOver U.1 (moduleAffinePresentation (K.restrict U.1.ι)) }
  exact Q.isQuasicoherent

set_option backward.isDefEq.respectTransparency false in
/-- Cokernels of morphisms between quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_cokernel {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (cokernel f).IsQuasicoherent := by
  let K := cokernel f
  let Q : K.QuasicoherentData :=
    { I := X.affineOpens
      X := fun U => U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact iSup_affineOpens_eq_top X
      presentation := fun U => by
        let _ : IsAffine U.1.toScheme := U.2
        let F := Scheme.Modules.pullback U.1.ι
        have : (cokernel (F.map f)).IsQuasicoherent :=
          isQuasicoherent_cokernel_of_isAffine (F.map f)
        have hKF : (F.obj K).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            (PreservesCokernel.iso F f).symm inferInstance
        have : (K.restrict U.1.ι).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app K).symm hKF
        exact modulePresentationOver U.1 (moduleAffinePresentation (K.restrict U.1.ι)) }
  exact Q.isQuasicoherent

end GromovWitten.AlgebraicGeometry.SheafCohomology
