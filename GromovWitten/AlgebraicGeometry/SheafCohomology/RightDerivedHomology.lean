/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
/-!
# Computing derived maps on resolution homology

The standard derived-object comparison lands in `homologyFunctor.obj`. This comparison
lands directly in the homology object of the mapped resolution, so the maps in a derived
sequence can be compared with the maps in the homology sequence without repeated transports.
-/

open CategoryTheory CategoryTheory.Abelian
noncomputable section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory.InjectiveResolution
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {X : C} (I : InjectiveResolution X)

/-- Compute a right-derived object as the homology of a mapped injective resolution. -/
def isoRightDerivedHomologyObj (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).obj X ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  I.isoRightDerivedObj F n ≪≫ eqToIso
    (HomologicalComplex.homologyFunctor_obj D (.up ℕ) n _)

set_option backward.isDefEq.respectTransparency false in
/-- Compute the chosen-resolution right-derived comparison directly. -/
lemma isoRightDerivedObj_hom_injectiveResolution (F : C ⥤ D) [F.Additive]
    (A : C) (n : ℕ) :
    ((injectiveResolution A).isoRightDerivedObj F n).hom =
      (HomotopyCategory.homologyFunctorFactors D (.up ℕ) n).hom.app
        ((F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex) := by
  have h : (injectiveResolution A).iso.hom = 𝟙 _ := by
    change (injectiveResolutions C).map (𝟙 A) = 𝟙 _
    exact (injectiveResolutions C).map_id A
  dsimp only [InjectiveResolution.isoRightDerivedObj, Iso.trans_hom, Functor.mapIso_hom,
    InjectiveResolution.isoRightDerivedToHomotopyCategoryObj]
  rw [h]
  simp only [Functor.mapHomotopyCategoryFactors, Functor.map_id, Functor.map_comp]
  erw [Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Compute a derived natural transformation using the homology map of a resolution. -/
lemma rightDerived_app_eq_homologyMap {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (n : ℕ) :
    (NatTrans.rightDerived α n).app X =
      (I.isoRightDerivedHomologyObj F n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex) n ≫
        (I.isoRightDerivedHomologyObj G n).inv := by
  rw [I.rightDerived_app_eq α n]
  dsimp only [isoRightDerivedHomologyObj]
  simp only [Iso.trans_hom, Iso.trans_inv]
  rw [HomologicalComplex.homologyFunctor_map]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Iso.refl_inv,
    Iso.cancel_iso_hom_left]
  erw [Category.id_comp]
set_option backward.isDefEq.respectTransparency false in
/-- Compute a derived morphism as the homology map of a lift to injective resolutions. -/
lemma rightDerived_map_eq_homologyMap {Y : C} (J : InjectiveResolution Y)
    (f : X ⟶ Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (w : I.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ J.ι)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).map f =
      (I.isoRightDerivedHomologyObj F n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n ≫
        (J.isoRightDerivedHomologyObj F n).inv := by
  rw [F.rightDerived_map_eq n f φ w]
  dsimp only [isoRightDerivedHomologyObj]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.comp_map]
  rw [HomologicalComplex.homologyFunctor_map]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Iso.refl_inv,
    Iso.cancel_iso_hom_left]
  erw [Category.id_comp]
end CategoryTheory.InjectiveResolution
