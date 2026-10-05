/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenSections
import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Base-linear section presheaves and Mayer–Vietoris complexes

Sections retain their action by the affine base ring. For termwise flasque
complexes, the binary Mayer–Vietoris complex is short exact.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

universe u v

noncomputable section

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- Sections on opens, viewed as modules over the affine base ring. -/
def baseSectionsPresheaf (s : X ⟶ Spec R) (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := baseSectionModule s U.unop M
  map i := baseSectionRestrictionMap s M i.unop
  map_id U := baseSectionRestrictionMap_id s M U.unop
  map_comp i j := (baseSectionRestrictionMap_comp s M i.unop j.unop).symm

set_option backward.isDefEq.respectTransparency false in
/-- The additive functor sending a sheaf of modules to its base-linear section presheaf. -/
def baseSectionsPresheafFunctor (s : X ⟶ Spec R) :
    X.Modules ⥤ (X.Opensᵒᵖ ⥤ ModuleCat.{u} R) where
  obj M := baseSectionsPresheaf s M
  map {M N} f :=
    { app U := by
        change baseSectionModule s U.unop M ⟶ baseSectionModule s U.unop N
        let _ : Module R Γ(M, U.unop) := baseSectionModuleStructure s U.unop M
        let _ : Module R Γ(N, U.unop) := baseSectionModuleStructure s U.unop N
        exact ModuleCat.ofHom (baseSectionMapLinear s f U.unop)
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        ext x
        exact ConcreteCategory.congr_hom (f.mapPresheaf.naturality i) x }
  map_id M := by
    ext U x
    rfl
  map_comp f g := by
    ext U x
    rfl

instance (s : X ⟶ Spec R) : (baseSectionsPresheafFunctor s).Additive where
  map_add := by
    intro M N f g
    ext U x
    rfl

def baseSectionsPair (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) : ModuleCat R :=
  ModuleCat.of R (baseSectionModule s U M × baseSectionModule s V M)

def baseSectionsToPair (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    baseSectionModule s (U ⊔ V) M ⟶ baseSectionsPair s M U V := by
  let _ : Module R Γ(M, U ⊔ V) := baseSectionModuleStructure s (U ⊔ V) M
  let _ : Module R Γ(M, U) := baseSectionModuleStructure s U M
  let _ : Module R Γ(M, V) := baseSectionModuleStructure s V M
  exact ModuleCat.ofHom ((baseSectionRestrictionMap s M (homOfLE le_sup_left)).hom.prod
    (baseSectionRestrictionMap s M (homOfLE le_sup_right)).hom)

def baseSectionsFromPair (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    baseSectionsPair s M U V ⟶ baseSectionModule s (U ⊓ V) M := by
  let _ : Module R Γ(M, U ⊓ V) := baseSectionModuleStructure s (U ⊓ V) M
  let _ : Module R Γ(M, U) := baseSectionModuleStructure s U M
  let _ : Module R Γ(M, V) := baseSectionModuleStructure s V M
  exact ModuleCat.ofHom
    (((baseSectionRestrictionMap s M (homOfLE inf_le_left)).hom.comp (LinearMap.fst R _ _)) -
      ((baseSectionRestrictionMap s M (homOfLE inf_le_right)).hom.comp (LinearMap.snd R _ _)))

lemma baseSectionsToPair_fromPair (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    baseSectionsToPair s M U V ≫ baseSectionsFromPair s M U V = 0 := by
  apply ModuleCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom
    (sectionsToPair_fromPair ((moduleToSheafAb X).obj M) U V) x

/-- The base-linear Mayer–Vietoris short complex. -/
def baseSectionsMV (s : X ⟶ Spec R) (M : X.Modules) (U V : X.Opens) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk _ _ (baseSectionsToPair_fromPair s M U V)

lemma baseSectionsMV_shortExact (s : X ⟶ Spec R) (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj M)] (U V : X.Opens) :
    (baseSectionsMV s M U V).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    exact (ShortComplex.ab_exact_iff _).mp
      (sectionsMV_exact ((moduleToSheafAb X).obj M) U V)
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (sectionsToPair_injective ((moduleToSheafAb X).obj M) U V)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    ((AddCommGrpCat.epi_iff_surjective _).mp
      (sectionsMV_shortExact ((moduleToSheafAb X).obj M) U V).epi_g)

/-- Sections on a fixed open, viewed as modules over the affine base ring. -/
def baseSectionsFunctor (s : X ⟶ Spec R) (U : X.Opens) : X.Modules ⥤ ModuleCat R :=
  baseSectionsPresheafFunctor s ⋙ (evaluation _ _).obj (op U)

instance (s : X ⟶ Spec R) (U : X.Opens) : (baseSectionsFunctor s U).Additive :=
  inferInstanceAs ((baseSectionsPresheafFunctor s ⋙ (evaluation _ _).obj (op U)).Additive)

set_option backward.isDefEq.respectTransparency false in
def baseSectionsPairFunctor (s : X ⟶ Spec R) (U V : X.Opens) : X.Modules ⥤ ModuleCat R where
  obj M := baseSectionsPair s M U V
  map {M N} f := by
    let _ : Module R Γ(M, U) := baseSectionModuleStructure s U M
    let _ : Module R Γ(M, V) := baseSectionModuleStructure s V M
    let _ : Module R Γ(N, U) := baseSectionModuleStructure s U N
    let _ : Module R Γ(N, V) := baseSectionModuleStructure s V N
    exact ModuleCat.ofHom ((baseSectionMapLinear s f U).prodMap (baseSectionMapLinear s f V))
  map_id M := by ext x <;> rfl
  map_comp f g := by ext x <;> rfl

instance (s : X ⟶ Spec R) (U V : X.Opens) : (baseSectionsPairFunctor s U V).Additive where
  map_add := by intro M N f g; ext x; rfl

set_option backward.isDefEq.respectTransparency false in
def baseSectionsToPairNat (s : X ⟶ Spec R) (U V : X.Opens) :
    baseSectionsFunctor s (U ⊔ V) ⟶ baseSectionsPairFunctor s U V where
  app M := baseSectionsToPair s M U V
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    ext x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom
        (f.mapPresheaf.naturality (homOfLE (le_sup_left : U ≤ U ⊔ V)).op).symm x
    · exact ConcreteCategory.congr_hom
        (f.mapPresheaf.naturality (homOfLE (le_sup_right : V ≤ U ⊔ V)).op).symm x

set_option backward.isDefEq.respectTransparency false in
def baseSectionsFromPairNat (s : X ⟶ Spec R) (U V : X.Opens) :
    baseSectionsPairFunctor s U V ⟶ baseSectionsFunctor s (U ⊓ V) where
  app M := baseSectionsFromPair s M U V
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    ext x
    change N.presheaf.map _ (f.app U x.1) - N.presheaf.map _ (f.app V x.2) =
      f.app (U ⊓ V) (M.presheaf.map _ x.1 - M.presheaf.map _ x.2)
    rw [map_sub]
    congr 1
    · exact ConcreteCategory.congr_hom
        (f.mapPresheaf.naturality (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).symm x.1
    · exact ConcreteCategory.congr_hom
        (f.mapPresheaf.naturality (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).symm x.2

/-- The Mayer–Vietoris short complex associated to a complex of sheaves of modules. -/
def baseSectionsComplexMV (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (U V : X.Opens) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex (baseSectionsToPairNat s U V) _).app K)
    ((NatTrans.mapHomologicalComplex (baseSectionsFromPairNat s U V) _).app K) (by
      ext n : 1
      exact baseSectionsToPair_fromPair s (K.X n) U V)

lemma baseSectionsComplexMV_shortExact (s : X ⟶ Spec R) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U V : X.Opens) : (baseSectionsComplexMV s K U V).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hK n
  exact baseSectionsMV_shortExact s (K.X n) U V

set_option backward.isDefEq.respectTransparency false in
/-- Identify the complex of pairs of sections with the biproduct of the section complexes. -/
noncomputable def baseSectionsPairComplexIso (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℤ) (U V : X.Opens) :
    ((baseSectionsPairFunctor s U V).mapHomologicalComplex (.up ℤ)).obj K ≅
      ((baseSectionsFunctor s U).mapHomologicalComplex (.up ℤ)).obj K ⊞
        ((baseSectionsFunctor s V).mapHomologicalComplex (.up ℤ)).obj K := by
  let A := ((baseSectionsFunctor s U).mapHomologicalComplex (.up ℤ)).obj K
  let B := ((baseSectionsFunctor s V).mapHomologicalComplex (.up ℤ)).obj K
  let e (i : ℤ) :=
    (ModuleCat.biprodIsoProd (A.X i) (B.X i)).symm ≪≫
      (HomologicalComplex.biprodXIso A B i).symm
  have hfst (i : ℤ) : (e i).hom ≫ (biprod.fst : A ⊞ B ⟶ A).f i =
      ModuleCat.ofHom (LinearMap.fst R (A.X i) (B.X i)) := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_fst A B i,
      Iso.inv_hom_id_assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
  have hsnd (i : ℤ) : (e i).hom ≫ (biprod.snd : A ⊞ B ⟶ B).f i =
      ModuleCat.ofHom (LinearMap.snd R (A.X i) (B.X i)) := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, ← HomologicalComplex.biprodXIso_hom_snd A B i,
      Iso.inv_hom_id_assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j hij
  apply (cancel_mono (HomologicalComplex.biprodXIso A B j).hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_fst]
    rw [← (biprod.fst : A ⊞ B ⟶ A).comm i j, ← Category.assoc, hfst, hfst]
    rfl
  · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_snd]
    rw [← (biprod.snd : A ⊞ B ⟶ B).comm i j, ← Category.assoc, hsnd, hsnd]
    rfl

end GromovWitten.AlgebraicGeometry.Curves
