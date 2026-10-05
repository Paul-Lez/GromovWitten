/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Transporting biproduct squares through additive functors
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Transport a biproduct descent square through an additive functor. -/
lemma mapBiprodDescSquare
    {C D : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (H : C ⥤ D) [H.Additive] [PreservesBinaryBiproducts H]
    {A B C₁ : C} {A' B' C₂ : D}
    (eA : H.obj A ≅ A') (eB : H.obj B ≅ B') (eC : H.obj C₁ ≅ C₂)
    (f : A ⟶ C₁) (r : B ⟶ C₁) (g : A' ⟶ C₂) (s : B' ⟶ C₂)
    (hf : H.map f ≫ eC.hom = eA.hom ≫ g)
    (hr : H.map (-r) ≫ eC.hom = eB.hom ≫ (-s)) :
    H.map (biprod.desc f (-r)) ≫ eC.hom =
      (H.mapBiprod A B ≪≫ biprod.mapIso eA eB).hom ≫ biprod.desc g (-s) := by
  let hAB := H.mapBiprod A B
  have hMapDesc : hAB.hom ≫ biprod.desc (H.map f) (H.map (-r)) =
      H.map (biprod.desc f (-r)) := by
    exact biprod.mapBiprod_hom_desc (F := H) (X := A) (Y := B) f (-r)
  calc
    H.map (biprod.desc f (-r)) ≫ eC.hom =
        hAB.hom ≫ biprod.desc (H.map f) (H.map (-r)) ≫ eC.hom := by
          simpa only [Category.assoc] using
            (congrArg (fun k => k ≫ eC.hom) hMapDesc).symm
    _ = hAB.hom ≫ biprod.map eA.hom eB.hom ≫ biprod.desc g (-s) := by
      congr 1
      apply biprod.hom_ext'
      · calc
          biprod.inl ≫ (biprod.desc (H.map f) (H.map (-r)) ≫ eC.hom) =
              H.map f ≫ eC.hom := by simp only [biprod.inl_desc_assoc]
          _ = eA.hom ≫ g := hf
          _ = biprod.inl ≫ (biprod.map eA.hom eB.hom ≫ biprod.desc g (-s)) := by
            simp only [biprod.inl_map_assoc, biprod.inl_desc]
      · calc
          biprod.inr ≫ (biprod.desc (H.map f) (H.map (-r)) ≫ eC.hom) =
              H.map (-r) ≫ eC.hom := by simp only [biprod.inr_desc_assoc]
          _ = eB.hom ≫ (-s) := hr
          _ = biprod.inr ≫ (biprod.map eA.hom eB.hom ≫ biprod.desc g (-s)) := by
            simp only [biprod.inr_map_assoc, biprod.inr_desc]
    _ = (H.mapBiprod A B ≪≫ biprod.mapIso eA eB).hom ≫ biprod.desc g (-s) := by
      simp only [Iso.trans_hom, biprod.mapIso_hom, hAB, Category.assoc]

/-- Transport a biproduct lift through an additive functor and component isomorphisms. -/
lemma mapBiprodLiftSquare
    {C D : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (H : C ⥤ D) [H.Additive] [PreservesBinaryBiproducts H]
    {A B Y : C} {A' B' : D}
    (eA : H.obj A ≅ A') (eB : H.obj B ≅ B')
    (x : Y ⟶ A) (y : Y ⟶ B) :
    H.map (biprod.lift x y) ≫ (H.mapBiprod A B ≪≫ biprod.mapIso eA eB).hom =
      biprod.lift (H.map x ≫ eA.hom) (H.map y ≫ eB.hom) := by
  let hAB := H.mapBiprod A B
  have hMapLift : H.map (biprod.lift x y) ≫ hAB.hom =
      biprod.lift (H.map x) (H.map y) := by
    exact biprod.map_lift_mapBiprod H A B x y
  change H.map (biprod.lift x y) ≫ hAB.hom ≫ biprod.map eA.hom eB.hom = _
  calc
    _ = biprod.lift (H.map x) (H.map y) ≫ biprod.map eA.hom eB.hom := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ biprod.map eA.hom eB.hom) hMapLift
    _ = biprod.lift (H.map x ≫ eA.hom) (H.map y ≫ eB.hom) := by
      apply biprod.hom_ext
      · simp
      · simp

end CategoryTheory.Functor
