/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Quasi-coherence of affine pushforward

The affine `Spec` theorem follows from the localization criterion for quasi-coherence. Transport
along the canonical affine isomorphisms and restriction to target affine opens proves the result
for arbitrary affine morphisms. No Noetherian hypothesis is used.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry Scheme.Modules
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y : Scheme.{u}}
/-- Pushforward along an isomorphism is restriction along its inverse. -/
def modulePushforwardIsoRestrict (e : X ≅ Y) :
    pushforward e.hom ≅ restrictFunctor e.inv :=
  (pushforward e.hom).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft _ ((restrictFunctorId (X := Y)).symm ≪≫
      (restrictFunctorCongr e.inv_hom_id).symm ≪≫ restrictFunctorComp e.inv e.hom) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictFunctorAdjCounitIso e.hom) _ ≪≫
    Functor.leftUnitor _

private theorem isQuasicoherent_pushforwardIso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward e.hom).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((modulePushforwardIsoRestrict e).app M).symm inferInstance

private theorem isQuasicoherent_pushforwardSpec {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
  exact isIso_fromTildeΓ_pushforward φ M

set_option backward.isDefEq.respectTransparency false in
private theorem isQuasicoherent_pushforwardBetweenAffines (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  have hf : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  let e : pushforward X.isoSpec.hom ⋙ pushforward (Spec.map f.appTop) ⋙
      pushforward Y.isoSpec.inv ≅ pushforward f :=
    Functor.isoWhiskerLeft _ (pushforwardComp _ _) ≪≫ pushforwardComp _ _ ≪≫
      pushforwardCongr hf
  let N := (pushforward X.isoSpec.hom).obj M
  let P := (pushforward (Spec.map f.appTop)).obj N
  have : N.IsQuasicoherent := isQuasicoherent_pushforwardIso X.isoSpec M
  have : P.IsQuasicoherent := isQuasicoherent_pushforwardSpec f.appTop N
  have : ((pushforward Y.isoSpec.inv).obj P).IsQuasicoherent :=
    isQuasicoherent_pushforwardIso Y.isoSpec.symm P
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (e.app M) this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pushforward commutes with restriction to an open subset of the target. -/
def modulePushforwardOpenRestrictIso (f : X ⟶ Y) (U : Y.Opens) :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) := by
  let _ := Functor.isContinuous_comp U.ι.opensFunctor (Opens.map f.base)
    (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X)
  let _ := Functor.isContinuous_comp (Opens.map (f ∣_ U).base) (f ⁻¹ᵁ U).ι.opensFunctor
    (Opens.grothendieckTopology U.toScheme) (Opens.grothendieckTopology (f ⁻¹ᵁ U).toScheme)
    (Opens.grothendieckTopology X)
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _
    (NatIso.ofComponents (fun W => eqToIso (image_morphismRestrict_preimage f U W))
      (fun _ => rfl)) ?_
  ext W r
  dsimp
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
    (f.app (U.ι ''ᵁ W.unop) r) = (f ∣_ U).app W.unop r
  exact ConcreteCategory.congr_hom (morphismRestrict_app f U W.unop).symm r



set_option backward.isDefEq.respectTransparency false in
/-- Every quasi-coherent module on an affine scheme has a global presentation. -/
def moduleAffinePresentation [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    M.Presentation := by
  let N := M.restrict X.isoSpec.inv
  have hN : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor X.isoSpec.inv M
  let _ : IsIso N.fromTildeΓ :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ N hN
  let _ : PreservesColimitsOfSize.{u, u} (restrictFunctor X.isoSpec.hom) :=
    (restrictAdjunction X.isoSpec.hom).leftAdjoint_preservesColimits
  let A := moduleSpecΓFunctor.obj N
  let P : N.Presentation :=
    (presentationTilde A Set.univ (by simp) _ (Submodule.span_eq _)).ofIsIso N.fromTildeΓ
  let e : (restrictFunctor X.isoSpec.hom).obj N ≅ M :=
    (restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm.app M ≪≫
      (restrictFunctorCongr X.isoSpec.hom_inv_id).app M ≪≫ (restrictFunctorId (X := X)).app M
  exact (P.map (restrictFunctor X.isoSpec.hom) (restrictUnitIso X.isoSpec.hom).symm).ofIsIso e.hom

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward along an affine morphism preserves quasi-coherence. -/
instance moduleAffinePushforward_isQuasicoherent (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let N := (pushforward f).obj M
  let Q : N.QuasicoherentData :=
    { I := Y.affineOpens
      X := fun U => U.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact iSup_affineOpens_eq_top Y
      presentation := fun U => by
        let _ : IsAffine U.1.toScheme := U.2
        let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := IsAffineHom.isAffine_preimage (f := f) _ U.2
        let P := M.restrict (f ⁻¹ᵁ U.1).ι
        have : ((pushforward (f ∣_ U.1)).obj P).IsQuasicoherent :=
          isQuasicoherent_pushforwardBetweenAffines _ P
        have : (N.restrict U.1.ι).IsQuasicoherent :=
          (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
            ((modulePushforwardOpenRestrictIso f U.1).app M).symm this
        exact modulePresentationOver U.1 (moduleAffinePresentation (N.restrict U.1.ι)) }
  exact Q.isQuasicoherent

end GromovWitten.AlgebraicGeometry.Curves
