/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechAugmentation
import GromovWitten.CategoryTheory.MappingCoconeLiftTransport
import GromovWitten.CategoryTheory.AdditiveBiprodSquare
import Mathlib.Topology.Category.TopCat.Opens

/-!
# Finite Čech complexes and preimages of opens

The finite Čech construction commutes with precomposition by inverse image on
opens, preserving the augmentation. The preimage of a cover is again a cover.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

universe u v

variable {X Y : TopCat.{u}} {R : Type v} [Ring R]

private lemma opensMap_sup (p : Y ⟶ X) (U V : Opens X) :
    (Opens.map p).obj (U ⊔ V) = (Opens.map p).obj U ⊔ (Opens.map p).obj V := by
  ext y
  simp

private lemma opensMap_bot (p : Y ⟶ X) :
    (Opens.map p).obj (⊥ : Opens X) = (⊥ : Opens Y) := by
  ext y
  simp

/-- Inverse image takes the union of a finite list to the union of its preimages. -/
lemma coverUnion_preimage (p : Y ⟶ X) (U : List (Opens X)) :
    coverUnion (U.map (Opens.map p).obj) =
      (Opens.map p).obj (coverUnion U) := by
  induction U with
  | nil =>
      simp only [List.map_nil, coverUnion, List.foldr_nil]
      exact opensMap_bot p
  | cons V tail ih =>
      change (Opens.map p).obj V ⊔ coverUnion (tail.map (Opens.map p).obj) =
        (Opens.map p).obj (V ⊔ coverUnion tail)
      rw [ih, opensMap_sup]

/-- Precompose a presheaf with inverse image on open sets. -/
noncomputable def reindexPresheafFunctor (p : Y ⟶ X) :
    Presheaves Y R ⥤ Presheaves X R :=
  (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Y)ᵒᵖ (ModuleCat R)).obj
    (Opens.map p).op

noncomputable instance reindexPresheafFunctor_additive (p : Y ⟶ X) :
    (reindexPresheafFunctor (X := X) (Y := Y) (R := R) p).Additive := by
  dsimp [reindexPresheafFunctor]
  infer_instance

/-- Precompose each term of a complex of presheaves with inverse image on opens. -/
noncomputable def reindexPresheafComplexFunctor (p : Y ⟶ X) :
    PresheafComplex Y R ⥤ PresheafComplex X R :=
  (reindexPresheafFunctor (X := X) (Y := Y) (R := R) p).mapHomologicalComplex
    (ComplexShape.up ℤ)

noncomputable instance reindexPresheafComplexFunctor_additive (p : Y ⟶ X) :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).Additive := by
  dsimp [reindexPresheafComplexFunctor]
  infer_instance

/-- Evaluation on the whole space is unchanged by reindexing. -/
lemma reindex_evaluate_top_obj (p : Y ⟶ X) (K : PresheafComplex Y R) :
    (evaluatePresheafComplex
      ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj K)).obj
        (Opposite.op (⊤ : Opens X)) =
      (evaluatePresheafComplex K).obj (Opposite.op (⊤ : Opens Y)) := by
  rfl

private lemma map_restrictionComplexNatTrans_app (p : Y ⟶ X) (U : Opens X)
    (F : PresheafComplex Y R) :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).map
        ((restrictionComplexNatTrans (X := Y) (R := R)
          ((Opens.map p).obj U)).app F) =
      (restrictionComplexNatTrans (X := X) (R := R) U).app
        ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F) := by
  rfl

private lemma map_restrictionComplexMap (p : Y ⟶ X) (U : Opens X)
    {F G : PresheafComplex Y R} (f : F ⟶ G) :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).map
        ((restrictionComplexFunctor (X := Y) (R := R)
          ((Opens.map p).obj U)).map f) =
      (restrictionComplexFunctor (X := X) (R := R) U).map
        ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).map f) := by
  rfl

/-- Comparison of finite Čech complexes under inverse image, including their augmentations. -/
structure FiniteCechPreimageData (p : Y ⟶ X)
    (F : PresheafComplex Y R) (U : List (Opens X)) where
  complexIso :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj
        (finiteCechData F (U.map (Opens.map p).obj)).complex ≅
      (finiteCechData
        ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F)
        U).complex
  augmentation_natural :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).map
        (finiteCechData F (U.map (Opens.map p).obj)).augmentation ≫ complexIso.hom =
      (finiteCechData
        ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F)
        U).augmentation

private structure FiniteCechConsPreimageData (p : Y ⟶ X)
    (F : PresheafComplex Y R) (U : Opens X)
    (A : AugmentedCechComplex F)
    (B : AugmentedCechComplex
      ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F)) where
  complexIso :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj
        (finiteCechConsData F ((Opens.map p).obj U) A).complex ≅
      (finiteCechConsData
        ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F)
        U B).complex
  augmentation_natural :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).map
        (finiteCechConsData F ((Opens.map p).obj U) A).augmentation ≫ complexIso.hom =
      (finiteCechConsData
        ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F)
        U B).augmentation

set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteCechConsPreimageData
    (p : Y ⟶ X) (F : PresheafComplex Y R) (U : Opens X)
    (tailF : AugmentedCechComplex F)
    (tailG : AugmentedCechComplex
      ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F))
    (tailIso : (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj
      tailF.complex ≅ tailG.complex)
    (hTailAug : (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).map
      tailF.augmentation ≫ tailIso.hom = tailG.augmentation) :
    FiniteCechConsPreimageData (X := X) (Y := Y) p F U tailF tailG := by
  let HC := reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p
  let H := reindexPresheafFunctor (X := X) (Y := Y) (R := R) p
  letI : HC.Additive := reindexPresheafComplexFunctor_additive p
  letI : H.Additive := reindexPresheafFunctor_additive p
  let U' := (Opens.map p).obj U
  let restrictF := restrictionComplexFunctor (X := Y) (R := R) U'
  let restrictG := restrictionComplexFunctor (X := X) (R := R) U
  let resF : F ⟶ restrictF.obj F :=
    (restrictionComplexNatTrans (X := Y) (R := R) U').app F
  let resB : tailF.complex ⟶ restrictF.obj tailF.complex :=
    (restrictionComplexNatTrans (X := Y) (R := R) U').app tailF.complex
  let resBH : HC.obj tailF.complex ⟶ restrictG.obj (HC.obj tailF.complex) :=
    (restrictionComplexNatTrans (X := X) (R := R) U).app (HC.obj tailF.complex)
  let resG : HC.obj F ⟶ restrictG.obj (HC.obj F) :=
    (restrictionComplexNatTrans (X := X) (R := R) U).app (HC.obj F)
  let resC : tailG.complex ⟶ restrictG.obj tailG.complex :=
    (restrictionComplexNatTrans (X := X) (R := R) U).app tailG.complex
  let alphaF : F ⟶ restrictF.obj F ⊞ tailF.complex :=
    biprod.lift resF tailF.augmentation
  let phiF : restrictF.obj F ⊞ tailF.complex ⟶ restrictF.obj tailF.complex :=
    biprod.desc (restrictF.map tailF.augmentation) (-resB)
  let alphaG : HC.obj F ⟶ restrictG.obj (HC.obj F) ⊞ tailG.complex :=
    biprod.lift resG tailG.augmentation
  let phiG : restrictG.obj (HC.obj F) ⊞ tailG.complex ⟶ restrictG.obj tailG.complex :=
    biprod.desc (restrictG.map tailG.augmentation) (-resC)
  have hresF : tailF.augmentation ≫ resB =
      resF ≫ restrictF.map tailF.augmentation := by
    simpa only [Functor.id_map] using
      (restrictionComplexNatTrans (X := Y) (R := R) U').naturality tailF.augmentation
  have hresG : tailG.augmentation ≫ resC =
      resG ≫ restrictG.map tailG.augmentation := by
    simpa only [Functor.id_map] using
      (restrictionComplexNatTrans (X := X) (R := R) U).naturality tailG.augmentation
  have hzeroF : alphaF ≫ phiF = 0 := by
    dsimp [alphaF, phiF]
    rw [biprod.lift_desc]
    simp [hresF]
  have hzeroG : alphaG ≫ phiG = 0 := by
    dsimp [alphaG, phiG]
    rw [biprod.lift_desc]
    simp [hresG]
  have hLiftF : CochainComplex.HomComplex.δ (-1) 0 0 +
      CochainComplex.HomComplex.Cochain.ofHom (alphaF ≫ phiF) = 0 := by
    simp [hzeroF]
  have hLiftG : CochainComplex.HomComplex.δ (-1) 0 0 +
      CochainComplex.HomComplex.Cochain.ofHom (alphaG ≫ phiG) = 0 := by
    simp [hzeroG]
  letI : PreservesBinaryBiproducts HC := preservesBinaryBiproducts_of_preservesBiproducts HC
  let biprodIso : HC.obj (restrictF.obj F ⊞ tailF.complex) ≅
      HC.obj (restrictF.obj F) ⊞ HC.obj tailF.complex := HC.mapBiprod _ _
  let restrictionIsoA : HC.obj (restrictF.obj F) ≅ restrictG.obj (HC.obj F) :=
    Iso.refl _
  let alphaIso : HC.obj (restrictF.obj F ⊞ tailF.complex) ≅
      restrictG.obj (HC.obj F) ⊞ tailG.complex := biprodIso ≪≫
    biprod.mapIso restrictionIsoA tailIso
  let coneIso : HC.obj (restrictF.obj tailF.complex) ≅ restrictG.obj tailG.complex :=
    restrictG.mapIso tailIso
  have hResNat : resBH ≫ coneIso.hom = tailIso.hom ≫ resC := by
    exact ((restrictionComplexNatTrans (X := X) (R := R) U).naturality
      tailIso.hom).symm
  have hFirstArmBase :
      HC.map (restrictF.map tailF.augmentation) ≫ coneIso.hom =
        restrictG.map tailG.augmentation := by
    calc
      HC.map (restrictF.map tailF.augmentation) ≫ coneIso.hom =
          restrictG.map (HC.map tailF.augmentation) ≫ restrictG.map tailIso.hom := by
            rw [map_restrictionComplexMap]
            rfl
      _ = restrictG.map (HC.map tailF.augmentation ≫ tailIso.hom) := by
            have hMapComp :
                restrictG.map (HC.map tailF.augmentation ≫ tailIso.hom) =
                  restrictG.map (HC.map tailF.augmentation) ≫ restrictG.map tailIso.hom :=
              restrictG.map_comp (HC.map tailF.augmentation) tailIso.hom
            exact hMapComp.symm
      _ = restrictG.map tailG.augmentation := by
            exact congrArg (fun f => restrictG.map f) hTailAug
  have hFirstArm : HC.map (restrictF.map tailF.augmentation) ≫ coneIso.hom =
      restrictionIsoA.hom ≫ restrictG.map tailG.augmentation := by
    exact hFirstArmBase.trans (Category.id_comp _).symm
  have hUnit : HC.map resF ≫ restrictionIsoA.hom = resG := by
    change resG ≫ 𝟙 _ = resG
    exact Category.comp_id _
  have hMapResB : HC.map resB = resBH := by
    exact map_restrictionComplexNatTrans_app p U tailF.complex
  have hNegRes : HC.map (-resB) = -resBH := by
    exact (Functor.map_neg HC).trans (congrArg Neg.neg hMapResB)
  have hSecondArm : HC.map (-resB) ≫ coneIso.hom = tailIso.hom ≫ (-resC) := by
    calc
      HC.map (-resB) ≫ coneIso.hom = (-resBH) ≫ coneIso.hom :=
        congrArg (fun f => f ≫ coneIso.hom) hNegRes
      _ = -(resBH ≫ coneIso.hom) := by simp
      _ = -(tailIso.hom ≫ resC) := by rw [hResNat]
      _ = tailIso.hom ≫ (-resC) := by simp
  have hSquare : HC.map phiF ≫ coneIso.hom = alphaIso.hom ≫ phiG := by
    simpa only [alphaIso, biprodIso] using
      Functor.mapBiprodDescSquare HC restrictionIsoA tailIso coneIso
        (restrictF.map tailF.augmentation) resB
        (restrictG.map tailG.augmentation) resC hFirstArm hSecondArm
  have hAugSquare : HC.map alphaF ≫ alphaIso.hom = alphaG := by
    have hLift : HC.map alphaF ≫ biprodIso.hom =
        biprod.lift (HC.map resF) (HC.map tailF.augmentation) := by
      change HC.map (biprod.lift resF tailF.augmentation) ≫
          (HC.mapBiprod (restrictF.obj F) tailF.complex).hom = _
      exact biprod.map_lift_mapBiprod HC (restrictF.obj F) tailF.complex
        resF tailF.augmentation
    have hLiftAfter : HC.map alphaF ≫ alphaIso.hom =
        biprod.lift (HC.map resF) (HC.map tailF.augmentation) ≫
          biprod.map restrictionIsoA.hom tailIso.hom := by
      change HC.map alphaF ≫ biprodIso.hom ≫
          biprod.map restrictionIsoA.hom tailIso.hom = _
      exact congrArg
        (fun k => k ≫ biprod.map restrictionIsoA.hom tailIso.hom) hLift
    rw [hLiftAfter]
    apply biprod.hom_ext
    · calc
        (biprod.lift (HC.map resF) (HC.map tailF.augmentation) ≫
            biprod.map restrictionIsoA.hom tailIso.hom) ≫ biprod.fst =
            (biprod.lift (HC.map resF) (HC.map tailF.augmentation) ≫ biprod.fst) ≫
            restrictionIsoA.hom := by
                rw [Category.assoc, biprod.map_fst, ← Category.assoc]
        _ = HC.map resF ≫ restrictionIsoA.hom := by rw [biprod.lift_fst]
        _ = resG := hUnit
        _ = biprod.lift resG tailG.augmentation ≫ biprod.fst := by simp only [biprod.lift_fst]
    · calc
        (biprod.lift (HC.map resF) (HC.map tailF.augmentation) ≫
            biprod.map restrictionIsoA.hom tailIso.hom) ≫ biprod.snd =
            (biprod.lift (HC.map resF) (HC.map tailF.augmentation) ≫ biprod.snd) ≫
              tailIso.hom := by
                rw [Category.assoc, biprod.map_snd, ← Category.assoc]
        _ = HC.map tailF.augmentation ≫ tailIso.hom := by rw [biprod.lift_snd]
        _ = tailG.augmentation := hTailAug
        _ = biprod.lift resG tailG.augmentation ≫ biprod.snd := by simp only [biprod.lift_snd]
  have hCompHC : HC.map alphaF ≫ HC.map phiF = 0 := by
    rw [← Functor.map_comp, hzeroF]
    simp
  have hLiftHC : CochainComplex.HomComplex.δ (-1) 0 0 +
      CochainComplex.HomComplex.Cochain.ofHom (HC.map alphaF ≫ HC.map phiF) = 0 := by
    simp [hCompHC]
  let transport := CochainComplex.additiveMappingCoconeLiftData
    H phiF phiG alphaIso coneIso hSquare alphaF alphaG hAugSquare
    hLiftF hLiftG hLiftHC
  refine ⟨transport.iso, ?_⟩
  exact transport.lift_natural

set_option backward.isDefEq.respectTransparency false in
/-- Inverse image on opens commutes with the augmented finite Čech construction. -/
noncomputable def finiteCechPreimageData (p : Y ⟶ X)
    (F : PresheafComplex Y R) :
    (U : List (Opens X)) → FiniteCechPreimageData (X := X) (Y := Y) p F U
  | [] => by
      let HC := reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p
      letI : HC.Additive := reindexPresheafComplexFunctor_additive p
      have hSource : IsZero (HC.obj (finiteCechData F []).complex) := by
        have hZero : IsZero (HomologicalComplex.zero : PresheafComplex Y R) :=
          HomologicalComplex.isZero_zero
        simpa [finiteCechData] using Functor.map_isZero HC hZero
      have hTarget : IsZero (finiteCechData (HC.obj F) []).complex := by
        have hZero : IsZero (HomologicalComplex.zero : PresheafComplex X R) :=
          HomologicalComplex.isZero_zero
        simpa [finiteCechData] using hZero
      refine ⟨hSource.isoZero ≪≫ hTarget.isoZero.symm, ?_⟩
      simp [finiteCechData, List.map]
  | U :: tail => by
      let HC := reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p
      let tailF := finiteCechData F (tail.map (Opens.map p).obj)
      let tailG := finiteCechData (HC.obj F) tail
      let tailComparison := finiteCechPreimageData p F tail
      let consComparison := finiteCechConsPreimageData p F U tailF tailG
        tailComparison.complexIso tailComparison.augmentation_natural
      refine ⟨?_, ?_⟩
      · simpa [finiteCechData] using consComparison.complexIso
      · change HC.map
            (finiteCechConsData F ((Opens.map p).obj U) tailF).augmentation ≫
              consComparison.complexIso.hom =
          (finiteCechConsData (HC.obj F) U tailG).augmentation
        exact consComparison.augmentation_natural

/-- The finite Čech complex commutes with inverse image on opens. -/
noncomputable def finiteCechPreimageIso (p : Y ⟶ X) (F : PresheafComplex Y R)
    (U : List (Opens X)) :
    (reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj
        (finiteCechData F (U.map (Opens.map p).obj)).complex ≅
      (finiteCechData
        ((reindexPresheafComplexFunctor (X := X) (Y := Y) (R := R) p).obj F)
        U).complex :=
  (finiteCechPreimageData p F U).complexIso

end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
