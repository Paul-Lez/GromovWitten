/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves
import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris
import GromovWitten.AlgebraicGeometry.SheafCohomology.ModuleSectionsExact

/-!
# Sections of the relative two-open Čech complex

The sections of the relative Čech complex over an open of the base identify with the ordinary
Mayer--Vietoris sections complex on the corresponding inverse-image opens. The resulting
isomorphism is used to transfer short exactness from flasque Mayer--Vietoris complexes.
-/
open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.Curves
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X S : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- Sections over a base open of the pushforward from `U` identify with sections on the
intersection of `U` and its inverse image. -/
def relativeOpenSectionsIso (s : X ⟶ S) (M : X.Modules) (U : X.Opens) (W : S.Opens) :
    (sections W).obj ((moduleToSheafAb S).obj
      ((pushforward s).obj ((pushforward U.ι).obj (M.restrict U.ι)))) ≅
    (sections (U ⊓ s ⁻¹ᵁ W)).obj ((moduleToSheafAb X).obj M) := by
  change M.presheaf.obj (op ((Scheme.Hom.opensFunctor U.ι).obj
    (U.ι ⁻¹ᵁ (s ⁻¹ᵁ W)))) ≅ _
  exact M.presheaf.mapIso (eqToIso (by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι])).op
set_option backward.isDefEq.respectTransparency false in
/-- The open-section comparison is compatible with restriction from a larger open to a smaller
one. -/
lemma relativeOpenSectionsIso_restriction (s : X ⟶ S) (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map ((pushforward s).map (openRestrictionMap M h)) ≫
        (relativeOpenSectionsIso s M V W).hom =
      (relativeOpenSectionsIso s M U W).hom ≫ M.presheaf.map
        (homOfLE (inf_le_inf_right (s ⁻¹ᵁ W) h)).op := by
  change (openRestrictionMap M h).app (s ⁻¹ᵁ W) ≫ _ = _
  rw [openRestrictionMap_app_eq]
  dsimp only [relativeOpenSectionsIso, id_eq, Functor.mapIso_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private lemma relativeOpenSectionsIso_unit (s : X ⟶ S) (M : X.Modules)
    (U : X.Opens) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map
        ((pushforward s).map ((restrictAdjunction U.ι).unit.app M)) ≫
      (relativeOpenSectionsIso s M U W).hom =
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ s ⁻¹ᵁ W ≤ s ⁻¹ᵁ W)).op := by
  change ((restrictAdjunction U.ι).unit.app M).app (s ⁻¹ᵁ W) ≫ _ = _
  rw [restrictAdjunction_unit_app_app]
  dsimp only [relativeOpenSectionsIso, id_eq, Functor.mapIso_hom]
  erw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private def relativeProdSectionsIso (W : S.Opens) (A B : S.Modules) :
    (sections W).obj ((moduleToSheafAb S).obj (A ⨯ B)) ≅
      AddCommGrpCat.of (Γ(A, W) × Γ(B, W)) := by
  let E := moduleToSheafAb S ⋙ sections W
  exact (PreservesLimitPair.iso E A B) ≪≫
    (IsLimit.conePointUniqueUpToIso (prodIsProd (E.obj A) (E.obj B))
      (AddCommGrpCat.binaryProductLimitCone (E.obj A) (E.obj B)).isLimit)

set_option backward.isDefEq.respectTransparency false in
private lemma relativeProdSectionsIso_hom_fst (W : S.Opens) (A B : S.Modules) :
    (relativeProdSectionsIso W A B).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (moduleToSheafAb S ⋙ sections W).map (prod.fst : A ⨯ B ⟶ A) := by
  dsimp only [relativeProdSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (AddCommGrpCat.binaryProductLimitCone _ _).cone.π.app
    ⟨WalkingPair.left⟩ = _
  erw [IsLimit.conePointUniqueUpToIso_hom_comp]
  rfl
set_option backward.isDefEq.respectTransparency false in
private lemma relativeProdSectionsIso_hom_snd (W : S.Opens) (A B : S.Modules) :
    (relativeProdSectionsIso W A B).hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (moduleToSheafAb S ⋙ sections W).map (prod.snd : A ⨯ B ⟶ B) := by
  dsimp only [relativeProdSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ _ ≫ (AddCommGrpCat.binaryProductLimitCone _ _).cone.π.app
    ⟨WalkingPair.right⟩ = _
  erw [IsLimit.conePointUniqueUpToIso_hom_comp]
  rfl
set_option backward.isDefEq.respectTransparency false in
/-- Sections of the relative Čech pair identify with the pair of sections on the two inverse-image
opens. -/
def relativePairSectionsIso (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).obj ((relativeCechPairFunctor s U V).obj M) ≅
      sectionsPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) :=
  relativeProdSectionsIso W _ _ ≪≫
    (AddEquiv.prodCongr (relativeOpenSectionsIso s M U W).addCommGroupIsoToAddEquiv
      (relativeOpenSectionsIso s M V W).addCommGroupIsoToAddEquiv).toAddCommGrpIso

set_option backward.isDefEq.respectTransparency false in
/-- The pair-section comparison commutes with projection to the first open. -/
lemma relativePairSectionsIso_hom_fst (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (W : S.Opens) :
    (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (moduleToSheafAb S ⋙ sections W).map prod.fst ≫
        (relativeOpenSectionsIso s M U W).hom := by
  dsimp only [relativePairSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  have hh :
      (AddEquiv.prodCongr (relativeOpenSectionsIso s M U W).addCommGroupIsoToAddEquiv
        (relativeOpenSectionsIso s M V W).addCommGroupIsoToAddEquiv).toAddCommGrpIso.hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) ≫
        (relativeOpenSectionsIso s M U W).hom := by rfl
  erw [hh, ← Category.assoc, relativeProdSectionsIso_hom_fst]
  rfl
set_option backward.isDefEq.respectTransparency false in
/-- The pair-section comparison commutes with projection to the second open. -/
lemma relativePairSectionsIso_hom_snd (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (W : S.Opens) :
    (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (moduleToSheafAb S ⋙ sections W).map prod.snd ≫
        (relativeOpenSectionsIso s M V W).hom := by
  dsimp only [relativePairSectionsIso, Iso.trans_hom]
  rw [Category.assoc]
  have hh :
      (AddEquiv.prodCongr (relativeOpenSectionsIso s M U W).addCommGroupIsoToAddEquiv
        (relativeOpenSectionsIso s M V W).addCommGroupIsoToAddEquiv).toAddCommGrpIso.hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) ≫
        (relativeOpenSectionsIso s M V W).hom := by rfl
  erw [hh, ← Category.assoc, relativeProdSectionsIso_hom_snd]
  rfl
set_option backward.isDefEq.respectTransparency false in
private lemma relativeToPairSections_fst (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map (relativeCechToPair s M U V) ≫
      (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ s ⁻¹ᵁ W ≤ s ⁻¹ᵁ W)).op := by
  rw [relativePairSectionsIso_hom_fst, ← Category.assoc, ← Functor.map_comp]
  dsimp only [relativeCechToPair]
  erw [prod.lift_fst]
  exact relativeOpenSectionsIso_unit s M U W

set_option backward.isDefEq.respectTransparency false in
private lemma relativeToPairSections_snd (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map (relativeCechToPair s M U V) ≫
      (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      M.presheaf.map (homOfLE (inf_le_right : V ⊓ s ⁻¹ᵁ W ≤ s ⁻¹ᵁ W)).op := by
  rw [relativePairSectionsIso_hom_snd, ← Category.assoc, ← Functor.map_comp]
  dsimp only [relativeCechToPair]
  erw [prod.lift_snd]
  exact relativeOpenSectionsIso_unit s M V W

set_option backward.isDefEq.respectTransparency false in
/-- Sections of the relative pushforward from the overlap identify with sections on the intersection
of the two inverse-image opens. -/
def relativeIntersectionSectionsIso (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).obj
      ((relativeOpenPushforward s (U ⊓ V)).obj M) ≅
      (sections ((U ⊓ s ⁻¹ᵁ W) ⊓ (V ⊓ s ⁻¹ᵁ W))).obj ((moduleToSheafAb X).obj M) :=
  relativeOpenSectionsIso s M (U ⊓ V) W ≪≫
    M.presheaf.mapIso (eqToIso (by simp only [inf_assoc, inf_left_comm, inf_idem])).op

set_option backward.isDefEq.respectTransparency false in
private lemma relativeIntersectionSectionsIso_left (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map
        ((pushforward s).map (openRestrictionMap M (inf_le_left : U ⊓ V ≤ U))) ≫
      (relativeIntersectionSectionsIso s M U V W).hom =
      (relativeOpenSectionsIso s M U W).hom ≫
        M.presheaf.map (homOfLE (inf_le_left :
          (U ⊓ s ⁻¹ᵁ W) ⊓ (V ⊓ s ⁻¹ᵁ W) ≤ U ⊓ s ⁻¹ᵁ W)).op := by
  dsimp only [relativeIntersectionSectionsIso, Iso.trans_hom]
  rw [← Category.assoc, relativeOpenSectionsIso_restriction, Category.assoc]
  dsimp only [Functor.mapIso_hom]
  erw [← Functor.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
private lemma relativeIntersectionSectionsIso_right (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map
        ((pushforward s).map (openRestrictionMap M (inf_le_right : U ⊓ V ≤ V))) ≫
      (relativeIntersectionSectionsIso s M U V W).hom =
      (relativeOpenSectionsIso s M V W).hom ≫
        M.presheaf.map (homOfLE (inf_le_right :
          (U ⊓ s ⁻¹ᵁ W) ⊓ (V ⊓ s ⁻¹ᵁ W) ≤ V ⊓ s ⁻¹ᵁ W)).op := by
  dsimp only [relativeIntersectionSectionsIso, Iso.trans_hom]
  rw [← Category.assoc, relativeOpenSectionsIso_restriction, Category.assoc]
  dsimp only [Functor.mapIso_hom]
  erw [← Functor.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- The section map of the relative Čech differential commutes with the pair and overlap
comparisons. -/
lemma relativeFromPairSections_comm (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).map (relativeCechFromPair s M U V) ≫
      (relativeIntersectionSectionsIso s M U V W).hom =
    (relativePairSectionsIso s M U V W).hom ≫
      sectionsFromPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) := by
  have hd : sectionsFromPair ((moduleToSheafAb X).obj M)
      (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) =
      AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) ≫
        M.presheaf.map (homOfLE inf_le_left).op -
      AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) ≫
        M.presheaf.map (homOfLE inf_le_right).op := rfl
  rw [hd, Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
    relativePairSectionsIso_hom_fst, relativePairSectionsIso_hom_snd]
  dsimp only [relativeCechFromPair]
  rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, Preadditive.sub_comp]
  simp only [Category.assoc]
  apply congrArg₂ (fun a b => a - b)
  · exact congrArg (fun t => (moduleToSheafAb S ⋙ sections W).map
      (prod.fst : (relativeOpenPushforward s U).obj M ⨯
        (relativeOpenPushforward s V).obj M ⟶ (relativeOpenPushforward s U).obj M) ≫ t)
      (relativeIntersectionSectionsIso_left s M U V W)
  · exact congrArg (fun t => (moduleToSheafAb S ⋙ sections W).map
      (prod.snd : (relativeOpenPushforward s U).obj M ⨯
        (relativeOpenPushforward s V).obj M ⟶ (relativeOpenPushforward s V).obj M) ≫ t)
      (relativeIntersectionSectionsIso_right s M U V W)
set_option backward.isDefEq.respectTransparency false in
private def relativeUnionSectionsIso (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (W : S.Opens) :
    (moduleToSheafAb S ⋙ sections W).obj ((pushforward s).obj M) ≅
      (sections ((U ⊓ s ⁻¹ᵁ W) ⊔ (V ⊓ s ⁻¹ᵁ W))).obj ((moduleToSheafAb X).obj M) :=
  M.presheaf.mapIso (eqToIso (by rw [← inf_sup_right, hcover, top_inf_eq])).op

set_option backward.isDefEq.respectTransparency false in
private lemma relativeToPairSections_comm (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (W : S.Opens) :
    (relativeUnionSectionsIso s M U V hcover W).hom ≫
        sectionsToPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) =
      (moduleToSheafAb S ⋙ sections W).map (relativeCechToPair s M U V) ≫
        (relativePairSectionsIso s M U V W).hom := by
  have hfst : (relativeUnionSectionsIso s M U V hcover W).hom ≫
        sectionsToPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) =
      (moduleToSheafAb S ⋙ sections W).map (relativeCechToPair s M U V) ≫
        (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst _ _) := by
    rw [relativeToPairSections_fst]
    change (relativeUnionSectionsIso s M U V hcover W).hom ≫
      M.presheaf.map (homOfLE le_sup_left).op = _
    dsimp only [relativeUnionSectionsIso, Functor.mapIso_hom]
    erw [← Functor.map_comp]
    congr 1
  have hsnd : (relativeUnionSectionsIso s M U V hcover W).hom ≫
        sectionsToPair ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) =
      (moduleToSheafAb S ⋙ sections W).map (relativeCechToPair s M U V) ≫
        (relativePairSectionsIso s M U V W).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd _ _) := by
    rw [relativeToPairSections_snd]
    change (relativeUnionSectionsIso s M U V hcover W).hom ≫
      M.presheaf.map (homOfLE le_sup_right).op = _
    dsimp only [relativeUnionSectionsIso, Functor.mapIso_hom]
    erw [← Functor.map_comp]
    congr 1
  apply AddCommGrpCat.hom_ext
  ext x
  exact Prod.ext (ConcreteCategory.congr_hom hfst x) (ConcreteCategory.congr_hom hsnd x)

set_option backward.isDefEq.respectTransparency false in
def relativeCechSectionsIso (s : X ⟶ S) (M : X.Modules) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (W : S.Opens) :
    (relativeCechShortComplex s M U V).map (moduleToSheafAb S ⋙ sections W) ≅
      sectionsMV ((moduleToSheafAb X).obj M) (U ⊓ s ⁻¹ᵁ W) (V ⊓ s ⁻¹ᵁ W) :=
  ShortComplex.isoMk (relativeUnionSectionsIso s M U V hcover W)
    (relativePairSectionsIso s M U V W) (relativeIntersectionSectionsIso s M U V W)
    (relativeToPairSections_comm s M U V hcover W) (relativeFromPairSections_comm s M U V W).symm

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech short complex is short exact when the underlying abelian sheaf of the
module is flasque.
-/
lemma relativeCechShortComplex_shortExact (s : X ⟶ S) (M : X.Modules)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M)] :
    (relativeCechShortComplex s M U V).ShortExact := by
  apply module_shortExact_of_sections_shortExact
  intro W
  exact ShortComplex.shortExact_of_iso
    (relativeCechSectionsIso s M U V hcover W).symm
    (sectionsMV_shortExact _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech short complex of a flasque complex is degreewise short exact. -/
lemma relativeCechComplexMV_shortExact (K : CochainComplex (X.Modules) ℕ)
    (s : X ⟶ S) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n))) :
    (relativeCechComplexMV K s U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let _ := hK n
  exact relativeCechShortComplex_shortExact s (K.X n) U V hcover

end GromovWitten.AlgebraicGeometry.SheafCohomology
