/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueResolution
import GromovWitten.AlgebraicGeometry.SheafCohomology.PointSheaves
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.Grp.Biproducts
/-!
# Mayer–Vietoris vanishing for right derived sections

For a flasque sheaf the two-open sequence of sections is short exact. Applying this
degreewise to an injective resolution gives the Mayer–Vietoris vanishing implication for
actual right derived section functors. Exactness of the section sequence is proved from
the sheaf condition and flasqueness.
-/

open CategoryTheory Limits Opposite TopologicalSpace
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X : TopCat.{u}}
def sections (U : Opens X) : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)
instance (U : Opens X) : (sections U).Additive := ⟨by intros; rfl⟩

def sectionsPair (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    AddCommGrpCat.{u} := AddCommGrpCat.of (F.obj.obj (op U) × F.obj.obj (op V))
def sectionsToPair (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    F.obj.obj (op (U ⊔ V)) ⟶ sectionsPair F U V :=
  AddCommGrpCat.ofHom ((F.obj.map (homOfLE le_sup_left).op).hom.prod
    (F.obj.map (homOfLE le_sup_right).op).hom)
def sectionsFromPair (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    sectionsPair F U V ⟶ F.obj.obj (op (U ⊓ V)) :=
  AddCommGrpCat.ofHom
    (((F.obj.map (homOfLE inf_le_left).op).hom.comp (AddMonoidHom.fst _ _)) -
      ((F.obj.map (homOfLE inf_le_right).op).hom.comp (AddMonoidHom.snd _ _)))
lemma sectionsToPair_fromPair (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    sectionsToPair F U V ≫ sectionsFromPair F U V = 0 := by
  ext s
  change F.obj.map _ (F.obj.map _ s) - F.obj.map _ (F.obj.map _ s) = 0
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.obj.map_comp,
    ← F.obj.map_comp]
  exact sub_self _
def sectionsMV (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk _ _ (sectionsToPair_fromPair F U V)
set_option backward.isDefEq.respectTransparency false in
lemma sectionsToPair_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    Function.Injective (sectionsToPair F U V) := by
  intro s t h
  let W : Fin 2 → Opens X := ![U, V]
  have hW : iSup W = U ⊔ V := by
    apply le_antisymm
    · apply iSup_le; intro i; fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup W 0) (le_iSup W 1)
  have hs := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  change F.obj.map _ s = F.obj.map _ t at hs ht
  let e := F.obj.mapIso (eqToIso (congrArg op hW.symm))
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  apply F.eq_of_locally_eq W
  intro i
  fin_cases i
  · simp only [e, Functor.mapIso_hom, ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    convert hs using 1 <;> congr 2
  · simp only [e, Functor.mapIso_hom, ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    convert ht using 1 <;> congr 2

set_option backward.isDefEq.respectTransparency false in
lemma sectionsMV_exact (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U V : Opens X) :
    (sectionsMV F U V).Exact := by
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  change F.obj.map _ x.1 - F.obj.map _ x.2 = 0 at hx
  have hx' := sub_eq_zero.mp hx
  let W : Fin 2 → Opens X := ![U, V]
  let sf : (i : Fin 2) → F.obj.obj (op (W i)) 
    | 0 => x.1
    | 1 => x.2
  have hc : TopCat.Presheaf.IsCompatible F.obj W sf := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hx'
    · apply_fun (fun s => F.obj.map (eqToHom (congrArg op (inf_comm U V))) s) at hx'
      simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp] at hx'
      convert hx'.symm using 1 <;> congr 2
    · rfl
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing W sf hc
  have hW : iSup W = U ⊔ V := by
    apply le_antisymm
    · apply iSup_le; intro i; fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup W 0) (le_iSup W 1)
  refine ⟨F.obj.map (eqToHom (congrArg op hW)) s, ?_⟩
  apply Prod.ext
  · change F.obj.map _ (F.obj.map _ s) = x.1
    simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    convert hs 0 using 1 <;> congr 2
  · change F.obj.map _ (F.obj.map _ s) = x.2
    simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    convert hs 1 using 1 <;> congr 2

set_option backward.isDefEq.respectTransparency false in
lemma sectionsMV_shortExact (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [TopCat.Sheaf.IsFlasque F] (U V : Opens X) : (sectionsMV F U V).ShortExact where
  exact := sectionsMV_exact F U V
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (sectionsToPair_injective F U V)
  epi_g := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective
      (F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op)).mp inferInstance s
    exact ⟨(t, 0), by change F.obj.map _ t - F.obj.map _ 0 = s; rw [map_zero, ht, sub_zero]⟩

def sectionsPairFunctor (U V : Opens X) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} where
  obj F := sectionsPair F U V
  map f := AddCommGrpCat.ofHom ((f.hom.app (op U)).hom.prodMap (f.hom.app (op V)).hom)
instance (U V : Opens X) : (sectionsPairFunctor U V).Additive := ⟨by intros; rfl⟩

def sectionsToPairNat (U V : Opens X) : sections (U ⊔ V) ⟶ sectionsPairFunctor U V where
  app F := sectionsToPair F U V
  naturality _ _ f := by
    ext s
    apply Prod.ext
    · exact ConcreteCategory.congr_hom
        (f.hom.naturality (homOfLE (le_sup_left : U ≤ U ⊔ V)).op).symm s
    · exact ConcreteCategory.congr_hom
        (f.hom.naturality (homOfLE (le_sup_right : V ≤ U ⊔ V)).op).symm s

def sectionsFromPairNat (U V : Opens X) : sectionsPairFunctor U V ⟶ sections (U ⊓ V) where
  app F := sectionsFromPair F U V
  naturality F G f := by
    ext s
    change G.obj.map _ (f.hom.app _ s.1) - G.obj.map _ (f.hom.app _ s.2) =
      f.hom.app _ (F.obj.map _ s.1 - F.obj.map _ s.2)
    rw [map_sub]
    congr 1
    · exact ConcreteCategory.congr_hom
        (f.hom.naturality (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).symm s.1
    · exact ConcreteCategory.congr_hom
        (f.hom.naturality (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).symm s.2

def sectionsComplexMV (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (U V : Opens X) : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex (sectionsToPairNat U V) _).app K)
    ((NatTrans.mapHomologicalComplex (sectionsFromPairNat U V) _).app K) (by
      ext n : 1
      exact sectionsToPair_fromPair (K.X n) U V)

lemma sectionsComplexMV_shortExact (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (U V : Opens X) :
    (sectionsComplexMV K U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let _ := hK n
  exact sectionsMV_shortExact (K.X n) U V

lemma sectionsPairComplex_exactAt (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (U V : Opens X) (n : ℕ)
    (hU : ((sections U).mapHomologicalComplex (.up ℕ) |>.obj K).ExactAt n)
    (hV : ((sections V).mapHomologicalComplex (.up ℕ) |>.obj K).ExactAt n) :
    ((sectionsPairFunctor U V).mapHomologicalComplex (.up ℕ) |>.obj K).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff] at hU hV ⊢
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  have hxU := congrArg Prod.fst hx
  have hxV := congrArg Prod.snd hx
  obtain ⟨yU, hyU⟩ := (ShortComplex.ab_exact_iff _).mp hU x.1 hxU
  obtain ⟨yV, hyV⟩ := (ShortComplex.ab_exact_iff _).mp hV x.2 hxV
  exact ⟨(yU, yV), Prod.ext hyU hyV⟩

lemma sectionsComplex_isZero_homology_sup
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (U V : Opens X) (n : ℕ)
    (hU : ((sections U).mapHomologicalComplex (.up ℕ) |>.obj K).ExactAt (n + 1))
    (hV : ((sections V).mapHomologicalComplex (.up ℕ) |>.obj K).ExactAt (n + 1))
    (hUV : ((sections (U ⊓ V)).mapHomologicalComplex (.up ℕ) |>.obj K).ExactAt n) :
    IsZero (((sections (U ⊔ V)).mapHomologicalComplex (.up ℕ) |>.obj K).homology (n + 1)) :=
  ((sectionsComplexMV_shortExact K hK U V).homology_exact₁ n (n + 1) rfl).isZero_of_both_isZero
    hUV.isZero_homology (sectionsPairComplex_exactAt K U V (n + 1) hU hV).isZero_homology

/-- Two-open Mayer–Vietoris vanishing for actual derived sections. -/
lemma isZero_rightDerived_sections_sup (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U V : Opens X) (n : ℕ)
    (hU : IsZero (((sections U).rightDerived (n + 1)).obj F))
    (hV : IsZero (((sections V).rightDerived (n + 1)).obj F))
    (hUV : IsZero (((sections (U ⊓ V)).rightDerived n).obj F)) :
    IsZero (((sections (U ⊔ V)).rightDerived (n + 1)).obj F) := by
  let I := InjectiveResolution.of F
  apply IsZero.of_iso _ (I.isoRightDerivedObj (sections (U ⊔ V)) (n + 1))
  apply sectionsComplex_isZero_homology_sup I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V n
  · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hU.of_iso (I.isoRightDerivedObj (sections U) (n + 1)).symm)
  · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hV.of_iso (I.isoRightDerivedObj (sections V) (n + 1)).symm)
  · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hUV.of_iso (I.isoRightDerivedObj (sections (U ⊓ V)) n).symm)
end GromovWitten.AlgebraicGeometry.SheafCohomology
