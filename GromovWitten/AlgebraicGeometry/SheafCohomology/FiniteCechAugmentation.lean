/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechComplex
import GromovWitten.CategoryTheory.MappingCoconeQuasiIso
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Augmentations for finite open covers

The finite Čech augmentation factors through restriction to the union of the opens.
A binary Mayer–Vietoris comparison extends by induction to arbitrary finite covers.
-/

open CategoryTheory Limits HomologicalComplex CochainComplex TopologicalSpace Opposite

universe u v

namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

variable {X : TopCat.{u}} {R : Type v} [Ring R]

noncomputable def opensInfLENatTrans {U V : Opens X} (h : U ≤ V) :
    opensInfOp V ⟶ opensInfOp U where
  app W := (homOfLE (inf_le_inf_left W.unop h)).op
  naturality _ _ _ := by apply Subsingleton.elim

noncomputable def restrictionLENatTrans {U V : Opens X} (h : U ≤ V) :
    restrictionFunctor (X := X) (R := R) V ⟶ restrictionFunctor U where
  app F := Functor.whiskerRight (opensInfLENatTrans h) F
  naturality F G f := by
    apply NatTrans.ext
    funext W
    exact (f.naturality ((homOfLE (inf_le_inf_left W.unop h)).op)).symm

noncomputable def restrictionComplexLENatTrans {U V : Opens X} (h : U ≤ V) :
    restrictionComplexFunctor (X := X) (R := R) V ⟶ restrictionComplexFunctor U :=
  NatTrans.mapHomologicalComplex (restrictionLENatTrans h) (ComplexShape.up ℤ)

lemma restrictionComplexNatTrans_comp_LE (F : PresheafComplex X R)
    {U V : Opens X} (h : U ≤ V) :
    (restrictionComplexNatTrans V).app F ≫ (restrictionComplexLENatTrans h).app F =
      (restrictionComplexNatTrans U).app F := by
  apply HomologicalComplex.hom_ext
  intro n
  apply NatTrans.ext
  funext W
  change (F.X n).map _ ≫ (F.X n).map _ = (F.X n).map _
  rw [← Functor.map_comp]
  rfl

lemma restrictionComplexLE_inf_square (F : PresheafComplex X R)
    (U V : Opens X) :
    (restrictionComplexLENatTrans (le_sup_left : U ≤ U ⊔ V)).app F ≫
        (restrictionComplexFunctor U).map ((restrictionComplexNatTrans V).app F) =
      (restrictionComplexLENatTrans (le_sup_right : V ≤ U ⊔ V)).app F ≫
        (restrictionComplexNatTrans U).app ((restrictionComplexFunctor V).obj F) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply NatTrans.ext
  funext W
  change (F.X n).map _ ≫ (F.X n).map _ = (F.X n).map _ ≫ (F.X n).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl


lemma supported_augmentation_cons_zero
    (F B : PresheafComplex X R) (U V : Opens X)
    (α : F ⟶ B) (β : (restrictionComplexFunctor V).obj F ⟶ B)
    (hβ : (restrictionComplexNatTrans V).app F ≫ β = α) :
    biprod.lift ((restrictionComplexLENatTrans (le_sup_left : U ≤ U ⊔ V)).app F)
        ((restrictionComplexLENatTrans (le_sup_right : V ≤ U ⊔ V)).app F ≫ β) ≫
      biprod.desc ((restrictionComplexFunctor U).map α)
        (-((restrictionComplexNatTrans U).app B)) = 0 := by
  have hnat : β ≫ (restrictionComplexNatTrans U).app B =
      (restrictionComplexNatTrans U).app ((restrictionComplexFunctor V).obj F) ≫
        (restrictionComplexFunctor U).map β := by
    exact (restrictionComplexNatTrans U).naturality β
  rw [biprod.lift_desc]
  simp only [Preadditive.comp_neg, Category.assoc, hnat]
  rw [← hβ, Functor.map_comp, ← Category.assoc,
    restrictionComplexLE_inf_square F U V]
  simp only [Category.assoc, add_neg_cancel]

lemma supported_augmentation_cons_components
    (F B : PresheafComplex X R) (U V : Opens X)
    (α : F ⟶ B) (β : (restrictionComplexFunctor V).obj F ⟶ B)
    (hβ : (restrictionComplexNatTrans V).app F ≫ β = α) :
    (restrictionComplexNatTrans (U ⊔ V)).app F ≫
        biprod.lift ((restrictionComplexLENatTrans (le_sup_left : U ≤ U ⊔ V)).app F)
          ((restrictionComplexLENatTrans (le_sup_right : V ≤ U ⊔ V)).app F ≫ β) =
      biprod.lift ((restrictionComplexNatTrans U).app F) α := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst]
    exact restrictionComplexNatTrans_comp_LE F le_sup_left
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← Category.assoc, restrictionComplexNatTrans_comp_LE F le_sup_right, hβ]



/-- The union of a finite list of opens. -/
def coverUnion (U : List (Opens X)) : Opens X := U.foldr (· ⊔ ·) ⊥

/-- Factor the augmentation through restriction to the union of the chosen opens. -/
structure SupportedFiniteCechAugmentation (F : PresheafComplex X R) (U : List (Opens X)) where
  hom : (restrictionComplexFunctor (coverUnion U)).obj F ⟶ (finiteCechData F U).complex
  fac : (restrictionComplexNatTrans (coverUnion U)).app F ≫ hom =
    (finiteCechData F U).augmentation

set_option backward.isDefEq.respectTransparency false in
noncomputable def supportedFiniteCechAugmentation (F : PresheafComplex X R) :
    (U : List (Opens X)) → SupportedFiniteCechAugmentation F U
  | [] => ⟨0, by simp only [finiteCechData]; cat_disch⟩
  | U :: tail => by
      let T := finiteCechData F tail
      let V := coverUnion tail
      let B := (supportedFiniteCechAugmentation F tail).hom
      have hB : (restrictionComplexNatTrans V).app F ≫ B = T.augmentation :=
        (supportedFiniteCechAugmentation F tail).fac
      let r := restrictionComplexFunctor (X := X) (R := R) U
      let φ : r.obj F ⊞ T.complex ⟶ r.obj T.complex :=
        biprod.desc (r.map T.augmentation) (-((restrictionComplexNatTrans U).app T.complex))
      let α : (restrictionComplexFunctor (U ⊔ V)).obj F ⟶ r.obj F ⊞ T.complex :=
        biprod.lift ((restrictionComplexLENatTrans (le_sup_left : U ≤ U ⊔ V)).app F)
          ((restrictionComplexLENatTrans (le_sup_right : V ≤ U ⊔ V)).app F ≫ B)
      have hz : α ≫ φ = 0 := supported_augmentation_cons_zero F T.complex U V _ B hB
      let ψ := CochainComplex.mappingCocone.lift φ α 0 (by simp [hz])
      refine ⟨ψ, ?_⟩
      have hα : (restrictionComplexNatTrans (U ⊔ V)).app F ≫ α =
          biprod.lift ((restrictionComplexNatTrans U).app F) T.augmentation :=
        supported_augmentation_cons_components F T.complex U V _ B hB
      apply HomologicalComplex.hom_ext
      intro i
      change ((restrictionComplexNatTrans (U ⊔ V)).app F).f i ≫ ψ.f i =
        (CochainComplex.mappingCocone.lift φ
          (biprod.lift ((restrictionComplexNatTrans U).app F) T.augmentation) 0 (by
            have hz' :
                biprod.lift ((restrictionComplexNatTrans U).app F) T.augmentation ≫ φ = 0 := by
              rw [← hα, Category.assoc, hz, comp_zero]
            rw [hz']; simp)).f i
      rw [mappingCocone_lift_zero_factors_inl, mappingCocone_lift_zero_factors_inl]
      rw [← Category.assoc, ← HomologicalComplex.comp_f, hα]



noncomputable def cechDifference (F B : PresheafComplex X R) (U : Opens X) (α : F ⟶ B) :
    (restrictionComplexFunctor U).obj F ⊞ B ⟶ (restrictionComplexFunctor U).obj B :=
  biprod.desc ((restrictionComplexFunctor U).map α) (-((restrictionComplexNatTrans U).app B))

set_option backward.isDefEq.respectTransparency false in
noncomputable def supportedCechConsMap (F B : PresheafComplex X R) (U V : Opens X)
    (α : F ⟶ B) (β : (restrictionComplexFunctor V).obj F ⟶ B)
    (hβ : (restrictionComplexNatTrans V).app F ≫ β = α) :
    (restrictionComplexFunctor (U ⊔ V)).obj F ⟶
      CochainComplex.mappingCocone (cechDifference F B U α) := by
  let a : (restrictionComplexFunctor (U ⊔ V)).obj F ⟶
      (restrictionComplexFunctor U).obj F ⊞ B :=
    biprod.lift ((restrictionComplexLENatTrans (le_sup_left : U ≤ U ⊔ V)).app F)
      ((restrictionComplexLENatTrans (le_sup_right : V ≤ U ⊔ V)).app F ≫ β)
  have hz : a ≫ cechDifference F B U α = 0 :=
    supported_augmentation_cons_zero F B U V α β hβ
  exact CochainComplex.mappingCocone.lift (cechDifference F B U α) a 0 (by simp [hz])

set_option backward.isDefEq.respectTransparency false in
lemma supportedCechCons_square (F B : PresheafComplex X R) (U V : Opens X)
    (α : F ⟶ B) (β : (restrictionComplexFunctor V).obj F ⟶ B)
    (hβ : (restrictionComplexNatTrans V).app F ≫ β = α) :
    cechDifference F ((restrictionComplexFunctor V).obj F) U
        ((restrictionComplexNatTrans V).app F) ≫ (restrictionComplexFunctor U).map β =
      biprod.map (𝟙 _) β ≫ cechDifference F B U α := by
  apply biprod.hom_ext'
  · simp only [cechDifference, biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
    rw [← Functor.map_comp, hβ]
    exact (Category.id_comp _).symm
  · simp only [cechDifference, biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
      Preadditive.neg_comp, Preadditive.comp_neg]
    congr 1
    exact ((restrictionComplexNatTrans U).naturality β).symm

set_option backward.isDefEq.respectTransparency false in
lemma supportedCechConsMap_factor (F B : PresheafComplex X R) (U V : Opens X)
    (α : F ⟶ B) (β : (restrictionComplexFunctor V).obj F ⟶ B)
    (hβ : (restrictionComplexNatTrans V).app F ≫ β = α) :
    supportedCechConsMap F ((restrictionComplexFunctor V).obj F) U V
        ((restrictionComplexNatTrans V).app F) (𝟙 _) (by simp) ≫
      mappingCoconeMap
        (cechDifference F ((restrictionComplexFunctor V).obj F) U
          ((restrictionComplexNatTrans V).app F)) (cechDifference F B U α)
        (biprod.map (𝟙 _) β) ((restrictionComplexFunctor U).map β)
        (supportedCechCons_square F B U V α β hβ) =
      supportedCechConsMap F B U V α β hβ := by
  let r := restrictionComplexFunctor (X := X) (R := R) U
  let rV := restrictionComplexFunctor (X := X) (R := R) V
  let φ₀ := cechDifference F (rV.obj F) U ((restrictionComplexNatTrans V).app F)
  let φ := cechDifference F B U α
  let a₀ : (restrictionComplexFunctor (U ⊔ V)).obj F ⟶ r.obj F ⊞ rV.obj F :=
    biprod.lift ((restrictionComplexLENatTrans (le_sup_left : U ≤ U ⊔ V)).app F)
      (((restrictionComplexLENatTrans (le_sup_right : V ≤ U ⊔ V)).app F) ≫ 𝟙 _)
  let a : (restrictionComplexFunctor (U ⊔ V)).obj F ⟶ r.obj F ⊞ B :=
    biprod.lift ((restrictionComplexLENatTrans (le_sup_left : U ≤ U ⊔ V)).app F)
      ((restrictionComplexLENatTrans (le_sup_right : V ≤ U ⊔ V)).app F ≫ β)
  have hpair : a₀ ≫ biprod.map (𝟙 _) β = a := by
    apply biprod.hom_ext <;> simp [a₀, a]
  apply HomologicalComplex.hom_ext
  intro i
  dsimp only [HomologicalComplex.comp_f, supportedCechConsMap]
  rw [mappingCocone_lift_zero_factors_inl, mappingCocone_lift_zero_factors_inl,
    Category.assoc]
  have hmap := mappingCocone_inl_map φ₀ φ (biprod.map (𝟙 _) β)
    (r.map β) (supportedCechCons_square F B U V α β hβ) i
  have hh := congrArg (fun k => a₀.f i ≫ k) hmap
  have hh' : a₀.f i ≫
      (CochainComplex.mappingCocone.inl φ₀).v i i (add_zero i) ≫
        (mappingCoconeMap φ₀ φ (biprod.map (𝟙 _) β) (r.map β)
          (supportedCechCons_square F B U V α β hβ)).f i =
      (a₀ ≫ biprod.map (𝟙 _) β).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) := by
    simpa only [HomologicalComplex.comp_f, Category.assoc] using hh
  rw [hpair] at hh'
  exact hh'

lemma supportedFiniteCechAugmentation_cons_hom (F : PresheafComplex X R)
    (U : Opens X) (tail : List (Opens X)) :
    (supportedFiniteCechAugmentation F (U :: tail)).hom =
      supportedCechConsMap F (finiteCechData F tail).complex U (coverUnion tail)
        (finiteCechData F tail).augmentation (supportedFiniteCechAugmentation F tail).hom
        (supportedFiniteCechAugmentation F tail).fac := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Binary Mayer–Vietoris comparisons and the empty-open comparison imply the comparison
for any finite list of opens. -/
lemma supportedFiniteCechAugmentation_quasiIso_of_MV (F : PresheafComplex X R)
    (hnil : ∀ W, QuasiIso ((evaluatePresheafComplexMap
      (supportedFiniteCechAugmentation F []).hom).app (op W)))
    (hMV : ∀ U V W, QuasiIso ((evaluatePresheafComplexMap
      (supportedCechConsMap F ((restrictionComplexFunctor V).obj F) U V
        ((restrictionComplexNatTrans V).app F) (𝟙 _) (by simp))).app (op W)))
    (cover : List (Opens X)) :
    ∀ W, QuasiIso ((evaluatePresheafComplexMap
      (supportedFiniteCechAugmentation F cover).hom).app (op W)) := by
  induction cover with
  | nil => exact hnil
  | cons U tail ih =>
      intro W
      let H : Presheaves X R ⥤ ModuleCat R := (evaluation _ _).obj (op W)
      let E := H.mapHomologicalComplex (.up ℤ)
      let B := (finiteCechData F tail).complex
      let V := coverUnion tail
      let α := (finiteCechData F tail).augmentation
      let β := (supportedFiniteCechAugmentation F tail).hom
      have hβ : (restrictionComplexNatTrans V).app F ≫ β = α :=
        (supportedFiniteCechAugmentation F tail).fac
      let r := restrictionComplexFunctor (X := X) (R := R) U
      let φ₀ := cechDifference F ((restrictionComplexFunctor V).obj F) U
        ((restrictionComplexNatTrans V).app F)
      let φ := cechDifference F B U α
      have hqβ : QuasiIso (E.map β) := ih W
      have hqrβ : QuasiIso (E.map (r.map β)) := by
        change QuasiIso ((evaluatePresheafComplexMap β).app (op (W ⊓ U)))
        exact ih (W ⊓ U)
      have hqid : QuasiIso (E.map (𝟙 (r.obj F))) := by
        rw [E.map_id]
        infer_instance
      have hqa : QuasiIso (E.map (biprod.map (𝟙 (r.obj F)) β)) :=
        biprod_map_quasiIso_after_additive H (𝟙 (r.obj F)) β
      have hqm : QuasiIso (E.map
          (mappingCoconeMap φ₀ φ (biprod.map (𝟙 (r.obj F)) β) (r.map β)
            (supportedCechCons_square F B U V α β hβ))) :=
        mappingCocone_map_quasiIso_after_additive H φ₀ φ (biprod.map (𝟙 (r.obj F)) β)
          (r.map β) (supportedCechCons_square F B U V α β hβ)
      have hqMV : QuasiIso (E.map
          (supportedCechConsMap F ((restrictionComplexFunctor V).obj F) U V
            ((restrictionComplexNatTrans V).app F) (𝟙 _) (by simp))) := hMV U V W
      change QuasiIso (E.map (supportedFiniteCechAugmentation F (U :: tail)).hom)
      rw [supportedFiniteCechAugmentation_cons_hom]
      change QuasiIso (E.map (supportedCechConsMap F B U V α β hβ))
      rw [← supportedCechConsMap_factor F B U V α β hβ, E.map_comp]
      infer_instance
lemma evaluated_restriction_isIso (F : PresheafComplex X R) (U V : Opens X) (h : V ≤ U) :
    IsIso ((evaluatePresheafComplexMap ((restrictionComplexNatTrans U).app F)).app (op V)) := by
  let j : V ⊓ U ⟶ V := homOfLE inf_le_left
  have : IsIso j := ⟨⟨homOfLE (le_inf le_rfl h), by cat_disch, by cat_disch⟩⟩
  have hi (i : ℤ) : IsIso
      (((evaluatePresheafComplexMap ((restrictionComplexNatTrans U).app F)).app (op V)).f i) := by
    change IsIso ((F.X i).map j.op)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- On an open covered by the list, the supported comparison gives the ordinary augmentation. -/
lemma finiteCechAugmentation_quasiIso_of_supported
    (F : PresheafComplex X R) (U : List (Opens X)) (V : Opens X) (h : V ≤ coverUnion U)
    [QuasiIso ((evaluatePresheafComplexMap
      (supportedFiniteCechAugmentation F U).hom).app (op V))] :
    QuasiIso ((finiteCechAugmentation F U).app (op V)) := by
  let E := ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op V)).mapHomologicalComplex (.up ℤ)
  change QuasiIso (E.map (finiteCechData F U).augmentation)
  rw [← (supportedFiniteCechAugmentation F U).fac, E.map_comp]
  have : IsIso (E.map ((restrictionComplexNatTrans (coverUnion U)).app F)) :=
    evaluated_restriction_isIso F (coverUnion U) V h
  have : QuasiIso (E.map (supportedFiniteCechAugmentation F U).hom) :=
    inferInstanceAs (QuasiIso ((evaluatePresheafComplexMap
      (supportedFiniteCechAugmentation F U).hom).app (op V)))
  infer_instance

end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
