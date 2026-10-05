/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechComplex
import GromovWitten.CategoryTheory.MappingCoconeLiftTransport
import GromovWitten.CategoryTheory.AdditiveBiprodSquare

/-!
# Additive coefficient functors and finite Čech complexes

Postcomposition with an additive functor commutes with the finite Čech complex
and its augmentation. No exactness or flatness of the functor is required.
-/

namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite CochainComplex
  CochainComplex.HomComplex

universe w

variable {X : TopCat.{u}} {R : Type v} [Ring R]
  {T : Type w} [Ring T]

/-- Postcompose a module presheaf with a coefficient functor. -/
noncomputable def mapPresheafFunctor (H : ModuleCat R ⥤ ModuleCat T) :
    Presheaves X R ⥤
      Presheaves X T :=
  (Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat R) (ModuleCat T)).obj H

noncomputable instance mapPresheafFunctor_additive
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive] :
  (mapPresheafFunctor (X := X) H).Additive where
  map_add := by
    intro P Q f g
    apply NatTrans.ext
    funext U
    change H.map (f.app U + g.app U) = H.map (f.app U) + H.map (g.app U)
    exact H.map_add

/-- Postcompose each term of a complex of module presheaves. -/
noncomputable def mapPresheafComplexFunctor
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive] :
    PresheafComplex X R ⥤
      PresheafComplex X T :=
  (mapPresheafFunctor (X := X) H).mapHomologicalComplex (ComplexShape.up ℤ)

noncomputable instance mapPresheafComplexFunctor_additive
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive] :
    (mapPresheafComplexFunctor (X := X) H).Additive := by
  dsimp [mapPresheafComplexFunctor]
  infer_instance

private lemma map_restrictionComplexNatTrans_app
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (U : Opens X) (F : PresheafComplex X R) :
    (mapPresheafComplexFunctor (X := X) H).map
        ((restrictionComplexNatTrans
          (X := X) (R := R) U).app F) =
      (restrictionComplexNatTrans
        (X := X) (R := T) U).app ((mapPresheafComplexFunctor (X := X) H).obj F) := by
  rfl

private lemma map_restrictionComplexMap
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (U : Opens X) {F G : PresheafComplex X R} (f : F ⟶ G) :
    (mapPresheafComplexFunctor (X := X) H).map
        ((restrictionComplexFunctor
          (X := X) (R := R) U).map f) =
      (restrictionComplexFunctor
        (X := X) (R := T) U).map ((mapPresheafComplexFunctor (X := X) H).map f) := by
  rfl

/-- Finite Čech comparison under an additive functor, including its augmentation. -/
structure FiniteCechScalarMapData
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R)
    (U : List (Opens X)) where
  complexIso :
    (mapPresheafComplexFunctor (X := X) H).obj
        (finiteCechData F U).complex ≅
      (finiteCechData
        ((mapPresheafComplexFunctor (X := X) H).obj F) U).complex
  augmentation_natural :
    (mapPresheafComplexFunctor (X := X) H).map
        (finiteCechData F U).augmentation ≫ complexIso.hom =
      (finiteCechData
        ((mapPresheafComplexFunctor (X := X) H).obj F) U).augmentation

private structure FiniteCechConsScalarMapData
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R)
    (U : Opens X)
    (A : AugmentedCechComplex F)
    (B : AugmentedCechComplex
      ((mapPresheafComplexFunctor (X := X) H).obj F)) where
  complexIso :
    (mapPresheafComplexFunctor (X := X) H).obj
        (finiteCechConsData F U A).complex ≅
      (finiteCechConsData
        ((mapPresheafComplexFunctor (X := X) H).obj F) U B).complex
  augmentation_natural :
    (mapPresheafComplexFunctor (X := X) H).map
        (finiteCechConsData F U A).augmentation ≫ complexIso.hom =
      (finiteCechConsData
        ((mapPresheafComplexFunctor (X := X) H).obj F) U B).augmentation

private structure FiniteCechConsScalarSquareData
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R) (U : Opens X)
    (tailF : AugmentedCechComplex F)
    (tailG : AugmentedCechComplex
      ((mapPresheafComplexFunctor (X := X) H).obj F))
    (tailIso : (mapPresheafComplexFunctor (X := X) H).obj tailF.complex ≅ tailG.complex) where
  alphaIso :
    (mapPresheafComplexFunctor (X := X) H).obj
        ((restrictionComplexFunctor
          (X := X) (R := R) U).obj F ⊞ tailF.complex) ≅
      (restrictionComplexFunctor
          (X := X) (R := T) U).obj
        ((mapPresheafComplexFunctor (X := X) H).obj F) ⊞ tailG.complex
  coneIso :
    (mapPresheafComplexFunctor (X := X) H).obj
        ((restrictionComplexFunctor
          (X := X) (R := R) U).obj tailF.complex) ≅
      (restrictionComplexFunctor
          (X := X) (R := T) U).obj tailG.complex
  hSquare :
    (mapPresheafComplexFunctor (X := X) H).map
        (biprod.desc
          ((restrictionComplexFunctor
            (X := X) (R := R) U).map tailF.augmentation)
          (-((restrictionComplexNatTrans
            (X := X) (R := R) U).app tailF.complex))) ≫ coneIso.hom =
      alphaIso.hom ≫ biprod.desc
        ((restrictionComplexFunctor
          (X := X) (R := T) U).map tailG.augmentation)
        (-((restrictionComplexNatTrans
          (X := X) (R := T) U).app tailG.complex))
  hAugSquare :
    (mapPresheafComplexFunctor (X := X) H).map
        (biprod.lift
          ((restrictionComplexNatTrans
            (X := X) (R := R) U).app F) tailF.augmentation) ≫ alphaIso.hom =
      biprod.lift
        ((restrictionComplexNatTrans
          (X := X) (R := T) U).app ((mapPresheafComplexFunctor (X := X) H).obj F))
        tailG.augmentation

set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteCechConsScalarSquareData
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R) (U : Opens X)
    (tailF : AugmentedCechComplex F)
    (tailG : AugmentedCechComplex
      ((mapPresheafComplexFunctor (X := X) H).obj F))
    (tailIso : (mapPresheafComplexFunctor (X := X) H).obj tailF.complex ≅ tailG.complex)
    (hTailAug : (mapPresheafComplexFunctor (X := X) H).map tailF.augmentation ≫
      tailIso.hom = tailG.augmentation) :
    FiniteCechConsScalarSquareData (X := X) H F U tailF tailG tailIso := by
  letI : HasBinaryBiproducts (PresheafComplex X R) := ⟨fun _ _ => inferInstance⟩
  letI : HasBinaryBiproducts (PresheafComplex X T) := ⟨fun _ _ => inferInstance⟩
  let HC := mapPresheafComplexFunctor (X := X) H
  letI : HC.Additive := mapPresheafComplexFunctor_additive (X := X) H
  let restrictF := restrictionComplexFunctor
    (X := X) (R := R) U
  let restrictG := restrictionComplexFunctor
    (X := X) (R := T) U
  let resF : F ⟶ restrictF.obj (F) := (restrictionComplexNatTrans
    (X := X) (R := R) U).app F
  let resB : tailF.complex ⟶ restrictF.obj (tailF.complex) := (restrictionComplexNatTrans
    (X := X) (R := R) U).app tailF.complex
  let resBH : HC.obj tailF.complex ⟶ restrictG.obj (HC.obj tailF.complex) :=
    (restrictionComplexNatTrans
    (X := X) (R := T) U).app (HC.obj tailF.complex)
  let resG : HC.obj F ⟶ restrictG.obj (HC.obj F) := (restrictionComplexNatTrans
    (X := X) (R := T) U).app (HC.obj F)
  let resC : tailG.complex ⟶ restrictG.obj (tailG.complex) := (restrictionComplexNatTrans
    (X := X) (R := T) U).app tailG.complex
  let phiF : restrictF.obj F ⊞ tailF.complex ⟶ restrictF.obj tailF.complex :=
    biprod.desc (restrictF.map tailF.augmentation) (-resB)
  let phiG : restrictG.obj (HC.obj F) ⊞ tailG.complex ⟶ restrictG.obj tailG.complex :=
    biprod.desc (restrictG.map tailG.augmentation) (-resC)
  let alphaF : F ⟶ restrictF.obj F ⊞ tailF.complex := biprod.lift resF tailF.augmentation
  letI : PreservesBinaryBiproducts HC :=
    preservesBinaryBiproducts_of_preservesBiproducts HC
  let biprodIso : HC.obj (restrictF.obj F ⊞ tailF.complex) ≅
      HC.obj (restrictF.obj F) ⊞ HC.obj tailF.complex :=
    HC.mapBiprod (restrictF.obj F)
      tailF.complex
  let restrictionIsoA : HC.obj (restrictF.obj F) ≅ restrictG.obj (HC.obj F) :=
    Iso.refl _
  let alphaIso : HC.obj (restrictF.obj F ⊞ tailF.complex) ≅
      restrictG.obj (HC.obj F) ⊞ tailG.complex := biprodIso ≪≫
    biprod.mapIso restrictionIsoA tailIso
  let coneIso : HC.obj (restrictF.obj tailF.complex) ≅ restrictG.obj tailG.complex :=
    restrictG.mapIso tailIso
  have hResNat : resBH ≫ coneIso.hom = tailIso.hom ≫ resC := by
    exact ((restrictionComplexNatTrans
      (X := X) (R := T) U).naturality tailIso.hom).symm
  have hFirstArm : HC.map (restrictF.map tailF.augmentation) ≫ coneIso.hom =
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
      _ = restrictG.map tailG.augmentation :=
            congrArg (fun f => restrictG.map f) hTailAug
  have hNegRes : HC.map (-resB) = -resBH := by
    exact (Functor.map_neg HC).trans
      (congrArg Neg.neg (map_restrictionComplexNatTrans_app (X := X) H U tailF.complex))
  have hSecondArm : HC.map (-resB) ≫ coneIso.hom = tailIso.hom ≫ (-resC) := by
    calc
      HC.map (-resB) ≫ coneIso.hom = (-resBH) ≫ coneIso.hom :=
        congrArg (fun f => f ≫ coneIso.hom) hNegRes
      _ = -(resBH ≫ coneIso.hom) := by simp
      _ = -(tailIso.hom ≫ resC) := by rw [hResNat]
      _ = tailIso.hom ≫ (-resC) := by simp
  have hFirstArm' : HC.map (restrictF.map tailF.augmentation) ≫ coneIso.hom =
      restrictionIsoA.hom ≫ restrictG.map tailG.augmentation := by
    exact hFirstArm.trans (Category.id_comp _).symm
  have hSquare : HC.map phiF ≫ coneIso.hom = alphaIso.hom ≫ phiG := by
    exact Functor.mapBiprodDescSquare HC restrictionIsoA tailIso coneIso
      (restrictF.map tailF.augmentation) resB
      (restrictG.map tailG.augmentation) resC hFirstArm' hSecondArm
  have hUnit : HC.map resF ≫ restrictionIsoA.hom = resG := by
    change resG ≫ 𝟙 _ = resG
    exact Category.comp_id _
  have hAugSquare : HC.map alphaF ≫ alphaIso.hom =
      biprod.lift resG tailG.augmentation := by
    have hlift := Functor.mapBiprodLiftSquare HC restrictionIsoA tailIso resF tailF.augmentation
    exact hlift.trans (congrArg₂ biprod.lift hUnit hTailAug)
  exact ⟨alphaIso, coneIso, hSquare, hAugSquare⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteCechConsScalarMapData
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R) (U : Opens X)
    (tailF : AugmentedCechComplex F)
    (tailG : AugmentedCechComplex
      ((mapPresheafComplexFunctor (X := X) H).obj F))
    (tailIso : (mapPresheafComplexFunctor (X := X) H).obj tailF.complex ≅ tailG.complex)
    (hTailAug : (mapPresheafComplexFunctor (X := X) H).map tailF.augmentation ≫
      tailIso.hom = tailG.augmentation) :
    FiniteCechConsScalarMapData (X := X) H F U tailF tailG := by
  letI : HasBinaryBiproducts (PresheafComplex X R) := ⟨fun _ _ => inferInstance⟩
  letI : HasBinaryBiproducts (PresheafComplex X T) := ⟨fun _ _ => inferInstance⟩
  let HC := mapPresheafComplexFunctor (X := X) H
  letI : HC.Additive := mapPresheafComplexFunctor_additive (X := X) H
  let restrictF := restrictionComplexFunctor
    (X := X) (R := R) U
  let restrictG := restrictionComplexFunctor
    (X := X) (R := T) U
  let resF : F ⟶ restrictF.obj (F) := (restrictionComplexNatTrans
    (X := X) (R := R) U).app F
  let resB : tailF.complex ⟶ restrictF.obj (tailF.complex) := (restrictionComplexNatTrans
    (X := X) (R := R) U).app tailF.complex
  let resG : HC.obj F ⟶ restrictG.obj (HC.obj F) := (restrictionComplexNatTrans
    (X := X) (R := T) U).app (HC.obj F)
  let resC : tailG.complex ⟶ restrictG.obj (tailG.complex) := (restrictionComplexNatTrans
    (X := X) (R := T) U).app tailG.complex
  let phiF : restrictF.obj F ⊞ tailF.complex ⟶ restrictF.obj tailF.complex :=
    biprod.desc (restrictF.map tailF.augmentation) (-resB)
  let phiG : restrictG.obj (HC.obj F) ⊞ tailG.complex ⟶ restrictG.obj tailG.complex :=
    biprod.desc (restrictG.map tailG.augmentation) (-resC)
  let alphaF : F ⟶ restrictF.obj F ⊞ tailF.complex := biprod.lift resF tailF.augmentation
  let alphaG : HC.obj F ⟶ restrictG.obj (HC.obj F) ⊞ tailG.complex :=
    biprod.lift resG tailG.augmentation
  let squares := finiteCechConsScalarSquareData H F U tailF tailG tailIso hTailAug
  have hresF : tailF.augmentation ≫ resB = resF ≫ restrictF.map tailF.augmentation := by
    simpa only [Functor.id_map] using
      (restrictionComplexNatTrans
        (X := X) (R := R) U).naturality tailF.augmentation
  have hresG : tailG.augmentation ≫ resC = resG ≫ restrictG.map tailG.augmentation := by
    simpa only [Functor.id_map] using
      (restrictionComplexNatTrans
        (X := X) (R := T) U).naturality tailG.augmentation
  have hzeroF : alphaF ≫ phiF = 0 := by
    dsimp [alphaF, phiF]
    rw [biprod.lift_desc]
    simp [hresF]
  have hzeroG : alphaG ≫ phiG = 0 := by
    dsimp [alphaG, phiG]
    rw [biprod.lift_desc]
    simp [hresG]
  have hLiftF : δ (-1) 0 0 + Cochain.ofHom (alphaF ≫ phiF) = 0 := by simp [hzeroF]
  have hLiftG : δ (-1) 0 0 + Cochain.ofHom (alphaG ≫ phiG) = 0 := by simp [hzeroG]
  have hCompHC : HC.map alphaF ≫ HC.map phiF = 0 := by
    rw [← Functor.map_comp, hzeroF]
    simp
  have hLiftHC : δ (-1) 0 0 + Cochain.ofHom (HC.map alphaF ≫ HC.map phiF) = 0 := by
    simp [hCompHC]
  let liftData := CochainComplex.additiveMappingCoconeLiftData
    (H := mapPresheafFunctor (X := X) H) phiF phiG
    squares.alphaIso squares.coneIso squares.hSquare alphaF alphaG squares.hAugSquare
    hLiftF hLiftG hLiftHC
  refine ⟨liftData.iso, ?_⟩
  change HC.map (CochainComplex.mappingCocone.lift phiF alphaF 0 hLiftF) ≫
      liftData.iso.hom = CochainComplex.mappingCocone.lift phiG alphaG 0 hLiftG
  exact liftData.lift_natural

set_option backward.isDefEq.respectTransparency false in
/-- An additive coefficient functor commutes with the augmented finite Čech construction. -/
noncomputable def finiteCechScalarMapData
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R) :
    (U : List (Opens X)) → FiniteCechScalarMapData (X := X) H F U
  | [] => by
      let HC := mapPresheafComplexFunctor (X := X) H
      letI : HC.Additive := mapPresheafComplexFunctor_additive (X := X) H
      let hSource : IsZero (HC.obj (finiteCechData F []).complex) := by
        have hZero : IsZero
            (HomologicalComplex.zero : PresheafComplex X R) :=
          HomologicalComplex.isZero_zero
        simpa [finiteCechData] using Functor.map_isZero HC hZero
      let hTarget : IsZero (finiteCechData (HC.obj F) []).complex := by
        have hZero : IsZero
            (HomologicalComplex.zero : PresheafComplex X T) :=
          HomologicalComplex.isZero_zero
        simpa [finiteCechData] using hZero
      refine ⟨hSource.isoZero ≪≫ hTarget.isoZero.symm, ?_⟩
      simp [finiteCechData]
  | U :: tail => by
      let HC := mapPresheafComplexFunctor (X := X) H
      letI : HC.Additive := mapPresheafComplexFunctor_additive (X := X) H
      let tailF := finiteCechData F tail
      let tailG := finiteCechData (HC.obj F) tail
      let tailComparison := finiteCechScalarMapData H F tail
      let consComparison := finiteCechConsScalarMapData H F U tailF tailG
        tailComparison.complexIso tailComparison.augmentation_natural
      refine ⟨?_, ?_⟩
      · simpa [finiteCechData] using consComparison.complexIso
      · simpa [finiteCechData] using
          consComparison.augmentation_natural

end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
