/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves
import GromovWitten.AlgebraicGeometry.Curves.AffineSectionsBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenSections
import GromovWitten.AlgebraicGeometry.SheafCohomology.CechPairBaseModule

/-!
# Relative Čech global sections

This file compares the global sections of the relative two-open Čech pair with the corresponding
base-section pair.  The final cokernel isomorphism is the global-sections transport used by the
relative Čech model.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/- The global-sections functor is additive by definition on module morphisms. -/
instance moduleSpecΓFunctor_additive : (moduleSpecΓFunctor (R := R)).Additive :=
  ⟨by intros; rfl⟩

set_option backward.isDefEq.respectTransparency false in
private def relativeOpenGammaIso (s : X ⟶ Spec R) (M : X.Modules) (U : X.Opens) :
    (moduleSpecΓFunctor (R := R)).obj ((relativeOpenPushforward s U).obj M) ≅
      baseSectionModule s U M :=
  (moduleSpecΓFunctor (R := R)).mapIso ((pushforwardComp U.ι s).app (M.restrict U.ι)) ≪≫
    (pushforwardSectionsBaseLinearEquiv (U.ι ≫ s) (M.restrict U.ι)).toModuleIso ≪≫
    (baseTopSectionsEquiv (U.ι ≫ s) (M.restrict U.ι)).symm.toModuleIso ≪≫
    (restrictBaseSectionsLinearEquiv s U.ι M ⊤).toModuleIso ≪≫
    (baseSectionCongr s M (by simp)).toModuleIso
set_option backward.isDefEq.respectTransparency false in
private lemma relativeOpenGammaIso_hom_apply (s : X ⟶ Spec R) (M : X.Modules) (U : X.Opens)
    (x : (moduleSpecΓFunctor (R := R)).obj ((relativeOpenPushforward s U).obj M)) :
    (relativeOpenGammaIso s M U).hom x =
      M.presheaf.map (eqToHom (show U = U.ι ''ᵁ (U.ι ⁻¹ᵁ (s ⁻¹ᵁ ⊤)) by simp)).op x := by
  rfl
set_option backward.isDefEq.respectTransparency false in
private lemma relativeOpenGammaIso_restriction (s : X ⟶ Spec R) (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) :
    (moduleSpecΓFunctor (R := R)).map
        ((pushforward s).map (openRestrictionMap M h)) ≫
      (relativeOpenGammaIso s M V).hom =
      (relativeOpenGammaIso s M U).hom ≫
        baseSectionRestrictionMap s M (homOfLE h) := by
  apply ModuleCat.hom_ext
  ext x
  change Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ (s ⁻¹ᵁ ⊤))) at x
  let hU : U = U.ι ''ᵁ (U.ι ⁻¹ᵁ (s ⁻¹ᵁ ⊤)) := by simp
  let hV : V = V.ι ''ᵁ (V.ι ⁻¹ᵁ (s ⁻¹ᵁ ⊤)) := by simp
  change M.presheaf.map (eqToHom hV).op
      ((openRestrictionMap M h).app (s ⁻¹ᵁ ⊤) x) =
    M.presheaf.map (homOfLE h).op (M.presheaf.map (eqToHom hU).op x)
  rw [openRestrictionMap_app_eq]
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
private def gammaProdIso (A B : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj (A ⨯ B) ≅
      ModuleCat.of R ((moduleSpecΓFunctor.obj A) × (moduleSpecΓFunctor.obj B)) := by
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) (moduleSpecΓFunctor (R := R)) :=
    (tilde.adjunction (R := R)).rightAdjoint_preservesLimits.preservesLimitsOfShape
  exact PreservesLimitPair.iso (moduleSpecΓFunctor (R := R)) A B ≪≫
    (IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      (ModuleCat.binaryProductLimitCone _ _).isLimit)

set_option backward.isDefEq.respectTransparency false in
private lemma gammaProdIso_hom_fst (A B : (Spec R).Modules) :
    (gammaProdIso A B).hom ≫ ModuleCat.ofHom (LinearMap.fst R _ _) =
      (moduleSpecΓFunctor (R := R)).map (prod.fst : A ⨯ B ⟶ A) := by
  dsimp only [gammaProdIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (ModuleCat.binaryProductLimitCone _ _).cone.π.app
    ⟨WalkingPair.left⟩ = _
  erw [IsLimit.conePointUniqueUpToIso_hom_comp]
  rfl
set_option backward.isDefEq.respectTransparency false in
private lemma gammaProdIso_hom_snd (A B : (Spec R).Modules) :
    (gammaProdIso A B).hom ≫ ModuleCat.ofHom (LinearMap.snd R _ _) =
      (moduleSpecΓFunctor (R := R)).map (prod.snd : A ⨯ B ⟶ B) := by
  dsimp only [gammaProdIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (ModuleCat.binaryProductLimitCone _ _).cone.π.app
    ⟨WalkingPair.right⟩ = _
  erw [IsLimit.conePointUniqueUpToIso_hom_comp]
  rfl
set_option backward.isDefEq.respectTransparency false in
private def relativePairGammaIso (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    (moduleSpecΓFunctor (R := R)).obj ((relativeCechPairFunctor s U V).obj M) ≅
      ModuleCat.of R (baseSectionModule s U M × baseSectionModule s V M) :=
  gammaProdIso _ _ ≪≫
    ((relativeOpenGammaIso s M U).toLinearEquiv.prodCongr
      (relativeOpenGammaIso s M V).toLinearEquiv).toModuleIso

set_option backward.isDefEq.respectTransparency false in
private lemma relativePairGammaIso_hom_fst (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    (relativePairGammaIso s M U V).hom ≫ ModuleCat.ofHom (LinearMap.fst R _ _) =
      (moduleSpecΓFunctor (R := R)).map prod.fst ≫ (relativeOpenGammaIso s M U).hom := by
  dsimp only [relativePairGammaIso, Iso.trans_hom]
  rw [Category.assoc]
  have hh : ((relativeOpenGammaIso s M U).toLinearEquiv.prodCongr
      (relativeOpenGammaIso s M V).toLinearEquiv).toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.fst R _ _) =
      ModuleCat.ofHom (LinearMap.fst R
        ((moduleSpecΓFunctor (R := R)).obj ((relativeOpenPushforward s U).obj M))
        ((moduleSpecΓFunctor (R := R)).obj ((relativeOpenPushforward s V).obj M))) ≫
        (relativeOpenGammaIso s M U).hom := rfl
  erw [hh, ← Category.assoc, gammaProdIso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
private lemma relativePairGammaIso_hom_snd (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    (relativePairGammaIso s M U V).hom ≫ ModuleCat.ofHom (LinearMap.snd R _ _) =
      (moduleSpecΓFunctor (R := R)).map prod.snd ≫ (relativeOpenGammaIso s M V).hom := by
  dsimp only [relativePairGammaIso, Iso.trans_hom]
  rw [Category.assoc]
  have hh : ((relativeOpenGammaIso s M U).toLinearEquiv.prodCongr
      (relativeOpenGammaIso s M V).toLinearEquiv).toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.snd R _ _) =
      ModuleCat.ofHom (LinearMap.snd R
        ((moduleSpecΓFunctor (R := R)).obj ((relativeOpenPushforward s U).obj M))
        ((moduleSpecΓFunctor (R := R)).obj ((relativeOpenPushforward s V).obj M))) ≫
        (relativeOpenGammaIso s M V).hom := rfl
  erw [hh, ← Category.assoc, gammaProdIso_hom_snd]

set_option backward.isDefEq.respectTransparency false in
private lemma relativeCechGamma_comm (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    (moduleSpecΓFunctor (R := R)).map (relativeCechFromPair s M U V) ≫
      (relativeOpenGammaIso s M (U ⊓ V)).hom =
    (relativePairGammaIso s M U V).hom ≫ baseCechPairMap s M U V := by
  have hd : baseCechPairMap s M U V =
      ModuleCat.ofHom (LinearMap.fst R (baseSectionModule s U M) (baseSectionModule s V M)) ≫
        baseSectionRestrictionMap s M (homOfLE inf_le_left) -
      ModuleCat.ofHom (LinearMap.snd R (baseSectionModule s U M) (baseSectionModule s V M)) ≫
        baseSectionRestrictionMap s M (homOfLE inf_le_right) := rfl
  rw [hd, Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
    relativePairGammaIso_hom_fst, relativePairGammaIso_hom_snd]
  dsimp only [relativeCechFromPair]
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, Preadditive.sub_comp]
  simp only [Category.assoc]
  apply congrArg₂ (fun a b => a - b)
  · exact congrArg (fun t => (moduleSpecΓFunctor (R := R)).map
      (prod.fst : (relativeOpenPushforward s U).obj M ⨯
        (relativeOpenPushforward s V).obj M ⟶ (relativeOpenPushforward s U).obj M) ≫ t)
      (relativeOpenGammaIso_restriction s M (inf_le_left : U ⊓ V ≤ U))
  · exact congrArg (fun t => (moduleSpecΓFunctor (R := R)).map
      (prod.snd : (relativeOpenPushforward s U).obj M ⨯
        (relativeOpenPushforward s V).obj M ⟶ (relativeOpenPushforward s V).obj M) ≫ t)
      (relativeOpenGammaIso_restriction s M (inf_le_right : U ⊓ V ≤ V))

set_option backward.isDefEq.respectTransparency false in
/-- The global-sections cokernel of the relative Čech differential is canonically identified with
the cokernel of the corresponding base-section differential. -/
def relativeCechGammaCokernelIso (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    cokernel ((moduleSpecΓFunctor (R := R)).map (relativeCechFromPair s M U V)) ≅
      cokernel (baseCechPairMap s M U V) :=
  cokernel.mapIso _ _ (relativePairGammaIso s M U V)
    (relativeOpenGammaIso s M (U ⊓ V)) (relativeCechGamma_comm s M U V)
end GromovWitten.AlgebraicGeometry.Curves
