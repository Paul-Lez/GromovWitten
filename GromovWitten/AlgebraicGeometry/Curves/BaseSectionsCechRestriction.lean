/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsPresheaf
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechAugmentation

/-!
# Restriction maps in base-linear Čech complexes

The Mayer–Vietoris maps become the lift and difference of the usual restriction
maps under the canonical biproduct comparison. Evaluating presheaf restrictions
agrees with these maps.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}


/-- Restriction on the base-linear section complex, with its source and target stated
as the corresponding complexes of sections. -/
def baseSectionsComplexRestriction (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) {U V : X.Opens} (i : U ⟶ V) :
    ((baseSectionsFunctor s V).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((baseSectionsFunctor s U).mapHomologicalComplex (.up ℤ)).obj K :=
  (evaluatePresheafComplex
    (((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K)).map i.op

set_option backward.isDefEq.respectTransparency false in
lemma baseSectionsPairComplexIso_hom_fst_f (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U V : X.Opens) (i : ℤ) :
    (baseSectionsPairComplexIso s K U V).hom.f i ≫
      (biprod.fst : _ ⟶ ((baseSectionsFunctor s U).mapHomologicalComplex (.up ℤ)).obj K).f i =
    ModuleCat.ofHom (LinearMap.fst R (baseSectionModule s U (K.X i))
      (baseSectionModule s V (K.X i))) := by
  let A := ((baseSectionsFunctor s U).mapHomologicalComplex (.up ℤ)).obj K
  let B := ((baseSectionsFunctor s V).mapHomologicalComplex (.up ℤ)).obj K
  change ((ModuleCat.biprodIsoProd (A.X i) (B.X i)).inv ≫
    (HomologicalComplex.biprodXIso A B i).inv) ≫ (biprod.fst : A ⊞ B ⟶ A).f i = _
  rw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_fst A B i,
    Iso.inv_hom_id_assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma baseSectionsPairComplexIso_hom_snd_f (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U V : X.Opens) (i : ℤ) :
    (baseSectionsPairComplexIso s K U V).hom.f i ≫
      (biprod.snd : _ ⟶ ((baseSectionsFunctor s V).mapHomologicalComplex (.up ℤ)).obj K).f i =
    ModuleCat.ofHom (LinearMap.snd R (baseSectionModule s U (K.X i))
      (baseSectionModule s V (K.X i))) := by
  let A := ((baseSectionsFunctor s U).mapHomologicalComplex (.up ℤ)).obj K
  let B := ((baseSectionsFunctor s V).mapHomologicalComplex (.up ℤ)).obj K
  change ((ModuleCat.biprodIsoProd (A.X i) (B.X i)).inv ≫
    (HomologicalComplex.biprodXIso A B i).inv) ≫ (biprod.snd : A ⊞ B ⟶ B).f i = _
  rw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_snd A B i,
    Iso.inv_hom_id_assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma baseSectionsComplexMV_f_pairIso (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U V : X.Opens) :
    (baseSectionsComplexMV s K U V).f ≫ (baseSectionsPairComplexIso s K U V).hom =
      biprod.lift (baseSectionsComplexRestriction s K (homOfLE le_sup_left))
        (baseSectionsComplexRestriction s K (homOfLE le_sup_right)) := by
  dsimp only [baseSectionsComplexMV]
  apply biprod.hom_ext
  · rw [biprod.lift_fst, Category.assoc]
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, baseSectionsPairComplexIso_hom_fst_f]
    rfl
  · rw [biprod.lift_snd, Category.assoc]
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, baseSectionsPairComplexIso_hom_snd_f]
    rfl
set_option backward.isDefEq.respectTransparency false in
lemma baseSectionsPairIso_inv_MV_g (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U V : X.Opens) :
    (baseSectionsPairComplexIso s K U V).inv ≫ (baseSectionsComplexMV s K U V).g =
      biprod.desc (baseSectionsComplexRestriction s K (homOfLE inf_le_left))
        (-(baseSectionsComplexRestriction s K (homOfLE inf_le_right))) := by
  dsimp only [baseSectionsComplexMV]
  apply (cancel_epi (baseSectionsPairComplexIso s K U V).hom).mp
  rw [Iso.hom_inv_id_assoc, biprod.desc_eq, Preadditive.comp_add]
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
    HomologicalComplex.neg_f_apply]
  rw [← Category.assoc, baseSectionsPairComplexIso_hom_fst_f,
    ← Category.assoc, baseSectionsPairComplexIso_hom_snd_f]
  apply ModuleCat.hom_ext
  ext x
  let a := baseSectionRestrictionMap s (K.X i) (homOfLE (inf_le_left : U ⊓ V ≤ U)) x.1
  let b := baseSectionRestrictionMap s (K.X i) (homOfLE (inf_le_right : U ⊓ V ≤ V)) x.2
  change a - b = a + -b
  exact sub_eq_add_neg a b



lemma baseSectionsComplexRestriction_f (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) {U V : X.Opens} (f : U ⟶ V) (i : ℤ) :
    (baseSectionsComplexRestriction s K f).f i = baseSectionRestrictionMap s (K.X i) f := rfl

lemma baseSectionsComplexRestriction_id (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U : X.Opens) :
    baseSectionsComplexRestriction s K (𝟙 U) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  exact baseSectionRestrictionMap_id s (K.X i) U

lemma baseSectionsComplexRestriction_comp (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) {U V W : X.Opens} (f : U ⟶ V) (g : V ⟶ W) :
    baseSectionsComplexRestriction s K g ≫ baseSectionsComplexRestriction s K f =
      baseSectionsComplexRestriction s K (f ≫ g) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact baseSectionRestrictionMap_comp s (K.X i) g f

lemma baseSectionsComplexRestriction_eqToHom (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) {U V : X.Opens} (h : U = V) :
    baseSectionsComplexRestriction s K (eqToHom h.symm) =
      eqToHom (congrArg (fun W =>
        ((baseSectionsFunctor s W).mapHomologicalComplex (.up ℤ)).obj K) h) := by
  subst V
  exact baseSectionsComplexRestriction_id s K U


set_option backward.isDefEq.respectTransparency false in
lemma evaluate_baseSections_restrictionLE (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) {U V : X.Opens} (h : U ≤ V) (W : X.Opens) :
    (((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)).mapHomologicalComplex (.up ℤ)).map
      ((restrictionComplexLENatTrans h).app
        (((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K)) =
    baseSectionsComplexRestriction s K (homOfLE (inf_le_inf_left W h)) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma evaluate_baseSections_restricted_unit (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U V W : X.Opens) :
    (((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)).mapHomologicalComplex (.up ℤ)).map
      ((restrictionComplexFunctor U).map ((restrictionComplexNatTrans V).app
        (((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K))) =
    baseSectionsComplexRestriction s K
      (homOfLE (inf_le_left : (W ⊓ U) ⊓ V ≤ W ⊓ U)) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma evaluate_baseSections_unit_restriction (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U V W : X.Opens) :
    (((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)).mapHomologicalComplex (.up ℤ)).map
      ((restrictionComplexNatTrans U).app
        ((restrictionComplexFunctor V).obj
          (((baseSectionsPresheafFunctor s).mapHomologicalComplex (.up ℤ)).obj K))) =
    baseSectionsComplexRestriction s K
      (homOfLE (inf_le_inf_right V (inf_le_left : W ⊓ U ≤ W))) := rfl


end GromovWitten.AlgebraicGeometry.Curves
