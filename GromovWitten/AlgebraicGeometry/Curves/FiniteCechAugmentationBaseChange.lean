/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCechGeometricBaseChange
import GromovWitten.AlgebraicGeometry.Curves.FiniteCechCohomologyZero


/-!
# Compatibility of finite Čech base change with global sections

The geometric finite Čech base-change map commutes with the canonical
augmentations from global sections. This square includes the scalar-extension,
single-complex, evaluation, and preimage identifications and uses the canonical
open-section comparison at the top open. It requires no affine-cover,
quasi-coherence, flatness, or Noetherian hypothesis.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

noncomputable local instance extendScalars_preservesBinaryBiproducts (φ : R ⟶ T) :
    PreservesBinaryBiproducts (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
  preservesBinaryBiproducts_of_preservesBinaryCoproducts _

noncomputable local instance extendScalars_additive (φ : R ⟶ T) :
    (ModuleCat.extendScalars.{u, u, u} φ.hom).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

noncomputable local instance mapPresheaf_extendScalars_additive (φ : R ⟶ T) :
    (mapPresheafFunctor (X := X.toTopCat)
      (ModuleCat.extendScalars.{u, u, u} φ.hom)).Additive :=
  mapPresheafFunctor_additive (X := X.toTopCat) _

set_option backward.isDefEq.respectTransparency false in
private lemma finiteCechGeometricBaseChange_singlePoint
    (s : X ⟶ Spec R) (φ : R ⟶ T) (M : X.Modules) :
    let E := ModuleCat.extendScalars φ.hom
    let EHC := E.mapHomologicalComplex (.up ℤ)
    let P := baseSectionsPresheaf s M
    let H := mapPresheafFunctor (X := X.toTopCat) E
    let evR := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤)
    let evT := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
    EHC.map ((singleMapHomologicalComplex evR (.up ℤ) 0).inv.app P) ≫
      (evT.mapHomologicalComplex (.up ℤ)).map
        ((singleMapHomologicalComplex H (.up ℤ) 0).hom.app P) =
    (singleMapHomologicalComplex E (.up ℤ) 0).hom.app (evR.obj P) ≫
        (singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (H.obj P) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      singleMapHomologicalComplex_inv_app_self,
      singleMapHomologicalComplex_hom_app_self]
    dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      mapPresheafFunctor]
    change (ModuleCat.extendScalars φ.hom).map (𝟙 ((baseSectionsPresheaf s M).obj (op ⊤))) ≫
      (ModuleCat.extendScalars φ.hom).map (𝟙 ((baseSectionsPresheaf s M).obj (op ⊤))) ≫
        𝟙 _ =
      ((ModuleCat.extendScalars φ.hom).map (𝟙 ((baseSectionsPresheaf s M).obj (op ⊤))) ≫
        𝟙 _) ≫ 𝟙 _
    simp
  · have hz0 : IsZero
        ((((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
          ((single (ModuleCat R) (.up ℤ) 0).obj (baseSectionModule s ⊤ M))).X i) := by
      change IsZero ((ModuleCat.extendScalars φ.hom).obj
        (((single (ModuleCat R) (.up ℤ) 0).obj (baseSectionModule s ⊤ M)).X i))
      apply Functor.map_isZero
      exact isZero_single_obj_X (.up ℤ) 0 (baseSectionModule s ⊤ M) i hi
    ext x
    have hx : x = 0 := @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hz0) x 0
    rw [hx]
    simp

set_option backward.isDefEq.respectTransparency false in
private lemma finiteCechGeometricBaseChange_sourceMiddle_augmentation
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) (U : List X.Opens) :
    let E := ModuleCat.extendScalars φ.hom
    let EHC := E.mapHomologicalComplex (.up ℤ)
    let P := baseSectionsPresheaf s M
    let Q := baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M)
    let preH := reindexPresheafFunctor (X := X.toTopCat) (Y := Y.toTopCat)
      (R := T) p.base
    let evR := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤)
    let evT := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
    EHC.map (baseFiniteCechAugmentation s M U) ≫
      (finiteCechGeometricBaseChangeSourceIso s φ M U).hom ≫
      (evaluatePresheafComplexMap
        (finiteCechMap
          ((single (Presheaves X.toTopCat T) (.up ℤ) 0).map
            (baseSectionsPresheafBaseChange s φ p g h M)) U)).app (op ⊤) =
    (singleMapHomologicalComplex E (.up ℤ) 0).hom.app (evR.obj P) ≫
      (single (ModuleCat T) (.up ℤ) 0).map
        (openSectionsBaseChangeMap s φ p g h M ⊤) ≫
      ((singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (preH.obj Q) ≫
        (evaluatePresheafComplexMap
          (finiteCechData
            ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation).app
          (op ⊤)) := by
  let E := ModuleCat.extendScalars φ.hom
  let EHC := E.mapHomologicalComplex (.up ℤ)
  let P := baseSectionsPresheaf s M
  let H := mapPresheafFunctor (X := X.toTopCat) E
  let Q := baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M)
  let preH := reindexPresheafFunctor (X := X.toTopCat) (Y := Y.toTopCat)
    (R := T) p.base
  let evR := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤)
  let evT := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
  let evRHC := evR.mapHomologicalComplex (.up ℤ)
  let evTHC := evT.mapHomologicalComplex (.up ℤ)
  let F := baseSectionsSingle s M
  let scalarIso : EHC.obj (evRHC.obj (finiteCechData F U).complex) ≅
      evTHC.obj (finiteCechData ((mapPresheafComplexFunctor E).obj F) U).complex :=
    finiteCechScalarComparisonAt E F U ⊤
  let singleHIso : (mapPresheafComplexFunctor E).obj F ≅
      (single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (H.obj P) :=
    (singleMapHomologicalComplex H (.up ℤ) 0).app P
  let tau : H.obj P ⟶ preH.obj Q := baseSectionsPresheafBaseChange s φ p g h M
  let singleTau := (single (Presheaves X.toTopCat T) (.up ℤ) 0).map tau
  let cechTau := evTHC.map (finiteCechMap singleTau U)
  have hScalarAug := finiteCechScalarComparisonAt_augmentation E F U ⊤
  have hSingleHAug := finiteCechMap_augmentation_natural singleHIso.hom U
  have hTauAug := finiteCechMap_augmentation_natural singleTau U
  have hPoint := finiteCechGeometricBaseChange_singlePoint s φ M
  have hNat := (singleMapHomologicalComplex evT (.up ℤ) 0).inv.naturality tau
  have hAugR : baseFiniteCechAugmentation s M U =
      (singleMapHomologicalComplex evR (.up ℤ) 0).inv.app P ≫
        (evaluatePresheafComplexMap (finiteCechData F U).augmentation).app (op ⊤) := by
    rfl
  have hSourceA : EHC.map (baseFiniteCechAugmentation s M U) ≫ scalarIso.hom =
      EHC.map ((singleMapHomologicalComplex evR (.up ℤ) 0).inv.app P) ≫
        evTHC.map (finiteCechData ((mapPresheafComplexFunctor E).obj F) U).augmentation := by
    rw [hAugR, Functor.map_comp, Category.assoc]
    apply congrArg (fun f => EHC.map
      ((singleMapHomologicalComplex evR (.up ℤ) 0).inv.app P) ≫ f)
    exact hScalarAug
  have hSourceB :
      evTHC.map ((finiteCechData ((mapPresheafComplexFunctor E).obj F) U).augmentation) ≫
        evTHC.map (finiteCechMap singleHIso.hom U) =
      evTHC.map singleHIso.hom ≫
        evTHC.map (finiteCechData
          ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (H.obj P)) U).augmentation := by
    have h := congrArg (fun f => evTHC.map f) hSingleHAug
    simpa [mapPresheafComplexFunctor, mapPresheafFunctor, baseSectionsSingle, H, F] using h
  have hSourceC :
      evTHC.map (finiteCechData
          ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (H.obj P)) U).augmentation ≫
        evTHC.map (finiteCechMap singleTau U) =
      evTHC.map singleTau ≫
        evTHC.map (finiteCechData
          ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation := by
    have h := congrArg (fun f => evTHC.map f) hTauAug
    simpa [singleTau, tau, mapPresheafFunctor, reindexPresheafFunctor, H, P, preH, Q] using h
  have hPoint' :
      EHC.map ((singleMapHomologicalComplex evR (.up ℤ) 0).inv.app P) ≫
        evTHC.map singleHIso.hom =
      (singleMapHomologicalComplex E (.up ℤ) 0).hom.app (evR.obj P) ≫
        (singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (H.obj P) := by
    simpa [EHC, H, evR, evT, singleHIso] using hPoint
  have hNat' :
      (singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (H.obj P) ≫
        evTHC.map singleTau =
      (single (ModuleCat T) (.up ℤ) 0).map (evT.map tau) ≫
        (singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (preH.obj Q) := by
    have h := hNat.symm
    change (singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (H.obj P) ≫
        evTHC.map singleTau =
      (single (ModuleCat T) (.up ℤ) 0).map (evT.map tau) ≫
        (singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (preH.obj Q) at h
    exact h
  change EHC.map (baseFiniteCechAugmentation s M U) ≫
      (scalarIso.hom ≫ evTHC.map (finiteCechMap singleHIso.hom U)) ≫ cechTau =
    (singleMapHomologicalComplex E (.up ℤ) 0).hom.app (evR.obj P) ≫
      (single (ModuleCat T) (.up ℤ) 0).map (evT.map tau) ≫
      (singleMapHomologicalComplex evT (.up ℤ) 0).inv.app (preH.obj Q) ≫
      evTHC.map (finiteCechData
        ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation
  simp only [Category.assoc]
  rw [reassoc_of% hSourceA, reassoc_of% hSourceB, reassoc_of% hPoint', hSourceC,
    reassoc_of% hNat']
private lemma finiteCechPreimage_singleEvaluationPoint
    (p : Y ⟶ X) (Q : Y.Opensᵒᵖ ⥤ ModuleCat T) :
    let preH := reindexPresheafFunctor (X := X.toTopCat) (Y := Y.toTopCat)
      (R := T) p.base
    let evX := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
    let evY : Presheaves.{u, u, u} Y.toTopCat T ⥤ ModuleCat.{u} T :=
      (evaluation Y.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
    (singleMapHomologicalComplex evX (.up ℤ) 0).inv.app (preH.obj Q) ≫
      (evX.mapHomologicalComplex (.up ℤ)).map
        ((singleMapHomologicalComplex preH (.up ℤ) 0).inv.app Q) =
    (singleMapHomologicalComplex evY (.up ℤ) 0).inv.app Q := by
  let preH := reindexPresheafFunctor (X := X.toTopCat) (Y := Y.toTopCat)
    (R := T) p.base
  let evX := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
  let evY : Presheaves.{u, u, u} Y.toTopCat T ⥤ ModuleCat.{u} T :=
    (evaluation Y.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      singleMapHomologicalComplex_inv_app_self]
    dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      reindexPresheafFunctor]
    change (𝟙 (Q.obj (op ⊤)) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 (Q.obj (op ⊤)) ≫ 𝟙 _
    simp
  · have hz : IsZero (((single (ModuleCat T) (.up ℤ) 0).obj
        (evX.obj (preH.obj Q))).X i) :=
      isZero_single_obj_X (.up ℤ) 0 (evX.obj (preH.obj Q)) i hi
    ext x
    have hx : x = 0 := @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hz) x 0
    rw [hx]
    simp [hi]

set_option backward.isDefEq.respectTransparency false in
private lemma finiteCechGeometricBaseChangeTargetIso_augmentation
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (M : X.Modules) (U : List X.Opens) :
    let Q := baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M)
    let preH := reindexPresheafFunctor (X := X.toTopCat) (Y := Y.toTopCat)
      (R := T) p.base
    let evX := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
    (singleMapHomologicalComplex evX (.up ℤ) 0).inv.app (preH.obj Q) ≫
      (evaluatePresheafComplexMap
        (finiteCechData
          ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation).app
        (op ⊤) ≫
      (finiteCechGeometricBaseChangeTargetIso p g M U).hom =
    baseFiniteCechAugmentation g ((Scheme.Modules.pullback p).obj M)
      (U.map (TopologicalSpace.Opens.map p.base).obj) := by
  let Q := baseSectionsPresheaf g ((Scheme.Modules.pullback p).obj M)
  let preH := reindexPresheafFunctor (X := X.toTopCat) (Y := Y.toTopCat)
    (R := T) p.base
  let preHC := reindexPresheafComplexFunctor
    (X := X.toTopCat) (Y := Y.toTopCat) (R := T) p.base
  let evX := (evaluation X.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
  let dstSingle := baseSectionsSingle g ((Scheme.Modules.pullback p).obj M)
  let preimageData := finiteCechPreimageData p.base dstSingle U
  let singlePreimageIso : preHC.obj dstSingle ≅
      (single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q) := by
    dsimp [preHC, dstSingle, baseSectionsSingle]
    exact (singleMapHomologicalComplex preH (.up ℤ) 0).app Q
  let dataIso : preHC.obj (finiteCechData dstSingle
      (U.map (TopologicalSpace.Opens.map p.base).obj)).complex ≅
      (finiteCechData ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).complex :=
    preimageData.complexIso ≪≫
    (finiteCechFunctor (X := X.toTopCat) (R := T) U).mapIso singlePreimageIso
  have hAug := preimageData.augmentation_natural
  have hSingle :
      (finiteCechData (preHC.obj dstSingle) U).augmentation ≫
          finiteCechMap singlePreimageIso.hom U =
        singlePreimageIso.hom ≫
          (finiteCechData
            ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation := by
    exact finiteCechMap_augmentation_natural singlePreimageIso.hom U
  have hData : preHC.map (finiteCechData dstSingle
      (U.map (TopologicalSpace.Opens.map p.base).obj)).augmentation ≫
      dataIso.hom =
      singlePreimageIso.hom ≫
        (finiteCechData
          ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation := by
    dsimp only [dataIso, Iso.trans_hom, Functor.mapIso_hom, finiteCechFunctor]
    rw [← Category.assoc, hAug, hSingle]
  let E := evX.mapHomologicalComplex (.up ℤ)
  let evY := (evaluation Y.Opensᵒᵖ (ModuleCat T)).obj (op ⊤)
  have hInvComp :
      E.map (finiteCechData
        ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation ≫
        E.map dataIso.inv =
      E.map singlePreimageIso.inv ≫ E.map (preHC.map
        (finiteCechData dstSingle
          (U.map (TopologicalSpace.Opens.map p.base).obj)).augmentation) := by
    have hInv :
        (finiteCechData
        ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation ≫
        dataIso.inv = singlePreimageIso.inv ≫ preHC.map
          (finiteCechData dstSingle
            (U.map (TopologicalSpace.Opens.map p.base).obj)).augmentation := by
      apply (cancel_mono dataIso.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hData]
      simp only [Iso.inv_hom_id_assoc]
    simpa only [Functor.map_comp] using congrArg E.map hInv
  have hPoint := finiteCechPreimage_singleEvaluationPoint p Q
  have hFinal :
      E.map (preHC.map (finiteCechData dstSingle
        (U.map (TopologicalSpace.Opens.map p.base).obj)).augmentation) ≫
        (eqToIso (reindex_evaluate_top_obj p.base
          ((finiteCechFunctor (X := Y.toTopCat) (R := T)
            (U.map (TopologicalSpace.Opens.map p.base).obj)).obj dstSingle))).hom =
      ((evY.mapHomologicalComplex (.up ℤ)).map
        (finiteCechData dstSingle
          (U.map (TopologicalSpace.Opens.map p.base).obj)).augmentation) := by
    rfl
  change (singleMapHomologicalComplex evX (.up ℤ) 0).inv.app (preH.obj Q) ≫
      E.map (finiteCechData
        ((single (Presheaves X.toTopCat T) (.up ℤ) 0).obj (preH.obj Q)) U).augmentation ≫
      E.map dataIso.inv ≫
      (eqToIso (reindex_evaluate_top_obj p.base
        ((finiteCechFunctor (X := Y.toTopCat) (R := T)
          (U.map (TopologicalSpace.Opens.map p.base).obj)).obj dstSingle))).hom =
    (singleMapHomologicalComplex evY (.up ℤ) 0).inv.app Q ≫ _
  rw [← Category.assoc (E.map _) (E.map dataIso.inv), hInvComp]
  rw [Category.assoc, hFinal, ← Category.assoc]
  exact congrArg (fun f => f ≫ (evY.mapHomologicalComplex (.up ℤ)).map
    (finiteCechData dstSingle (U.map (TopologicalSpace.Opens.map p.base).obj)).augmentation)
    hPoint

set_option backward.isDefEq.respectTransparency false in
/-- The geometric finite Čech comparison commutes with its global-section augmentations. -/
lemma finiteCechGeometricBaseChangeMap_augmentation
    (s : X ⟶ Spec R) (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ)) (M : X.Modules) (U : List X.Opens) :
    let E := ModuleCat.extendScalars φ.hom
    let EHC := E.mapHomologicalComplex (.up ℤ)
    let P := baseSectionsPresheaf s M
    let evR := (evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤)
    EHC.map (baseFiniteCechAugmentation s M U) ≫
      finiteCechGeometricBaseChangeMap s φ p g h M U =
    (singleMapHomologicalComplex E (.up ℤ) 0).hom.app (evR.obj P) ≫
      (single (ModuleCat T) (.up ℤ) 0).map
        (openSectionsBaseChangeMap s φ p g h M ⊤) ≫
      baseFiniteCechAugmentation g ((Scheme.Modules.pullback p).obj M)
        (U.map (TopologicalSpace.Opens.map p.base).obj) := by
  let E := ModuleCat.extendScalars φ.hom
  let EHC := E.mapHomologicalComplex (.up ℤ)
  have hSource := finiteCechGeometricBaseChange_sourceMiddle_augmentation s φ p g h M U
  have hTarget := finiteCechGeometricBaseChangeTargetIso_augmentation p g M U
  change EHC.map (baseFiniteCechAugmentation s M U) ≫
      (finiteCechGeometricBaseChangeSourceIso s φ M U).hom ≫
      (evaluatePresheafComplexMap
        (finiteCechMap
          ((single (Presheaves X.toTopCat T) (.up ℤ) 0).map
            (baseSectionsPresheafBaseChange s φ p g h M)) U)).app (op ⊤) ≫
      (finiteCechGeometricBaseChangeTargetIso p g M U).hom = _
  rw [reassoc_of% hSource, hTarget]

end GromovWitten.AlgebraicGeometry.Curves
