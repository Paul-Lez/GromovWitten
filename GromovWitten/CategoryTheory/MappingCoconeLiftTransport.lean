/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.MappingCoconeFunctor

/-!
# Additive transport of augmented mapping cocones

An additive functor commutes with mapping cocones. A compatible square transports
both the cocone and a lift with zero homotopy; this packages the two facts for
recursive augmented-complex constructions.
-/

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex

/-- A cocone comparison together with compatibility of its canonical zero-homotopy lift. -/
structure AdditiveMappingCoconeLiftData
    {A B : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    [Category B] [Preadditive B] [HasBinaryBiproducts B]
    (H : A ⥤ B) [H.Additive]
    {K₁ L₁ : CochainComplex A ℤ} {K₂ L₂ : CochainComplex B ℤ}
    {M : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : (H.mapHomologicalComplex (.up ℤ)).obj K₁ ≅ K₂)
    (b : (H.mapHomologicalComplex (.up ℤ)).obj L₁ ≅ L₂)
    (comm : (H.mapHomologicalComplex (.up ℤ)).map φ₁ ≫ b.hom = a.hom ≫ φ₂)
    (α₁ : M ⟶ K₁) (α₂ : (H.mapHomologicalComplex (.up ℤ)).obj M ⟶ K₂)
    (hα : (H.mapHomologicalComplex (.up ℤ)).map α₁ ≫ a.hom = α₂)
    (h₁ : δ (-1) 0 0 + Cochain.ofHom (α₁ ≫ φ₁) = 0)
    (h₂ : δ (-1) 0 0 + Cochain.ofHom (α₂ ≫ φ₂) = 0) where
  iso :
    (H.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCocone φ₁) ≅
      CochainComplex.mappingCocone φ₂
  lift_natural :
    (H.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.lift φ₁ α₁ 0 h₁) ≫ iso.hom =
      CochainComplex.mappingCocone.lift φ₂ α₂ 0 h₂

/-- Transport a zero-homotopy lift through an additive functor and a commutative square. -/
noncomputable def additiveMappingCoconeLiftData
    {A B : Type*} [Category A] [Preadditive A] [HasBinaryBiproducts A]
    [Category B] [Preadditive B] [HasBinaryBiproducts B]
    (H : A ⥤ B) [H.Additive]
    {K₁ L₁ : CochainComplex A ℤ} {K₂ L₂ : CochainComplex B ℤ}
    {M : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : (H.mapHomologicalComplex (.up ℤ)).obj K₁ ≅ K₂)
    (b : (H.mapHomologicalComplex (.up ℤ)).obj L₁ ≅ L₂)
    (comm : (H.mapHomologicalComplex (.up ℤ)).map φ₁ ≫ b.hom = a.hom ≫ φ₂)
    (α₁ : M ⟶ K₁) (α₂ : (H.mapHomologicalComplex (.up ℤ)).obj M ⟶ K₂)
    (hα : (H.mapHomologicalComplex (.up ℤ)).map α₁ ≫ a.hom = α₂)
    (h₁ : δ (-1) 0 0 + Cochain.ofHom (α₁ ≫ φ₁) = 0)
    (h₂ : δ (-1) 0 0 + Cochain.ofHom (α₂ ≫ φ₂) = 0)
    (hH : δ (-1) 0 0 + Cochain.ofHom
      ((H.mapHomologicalComplex (.up ℤ)).map α₁ ≫
        (H.mapHomologicalComplex (.up ℤ)).map φ₁) = 0) :
    AdditiveMappingCoconeLiftData H φ₁ φ₂ a b comm α₁ α₂ hα h₁ h₂ := by
  let HC := H.mapHomologicalComplex (.up ℤ)
  let mappedIso := mapCoconeIso H φ₁
  let squareIso := mappingCoconeMapIso (HC.map φ₁) φ₂ a b comm
  have hMapLift : HC.map (CochainComplex.mappingCocone.lift φ₁ α₁ 0 h₁) ≫
      mappedIso.hom = CochainComplex.mappingCocone.lift (HC.map φ₁) (HC.map α₁) 0 hH := by
    exact map_cocone_lift_zero (H := H) φ₁ α₁ h₁ hH
  have hLiftNatural : HC.map (CochainComplex.mappingCocone.lift φ₁ α₁ 0 h₁) ≫
      (mappedIso ≪≫ squareIso).hom =
        CochainComplex.mappingCocone.lift φ₂ α₂ 0 h₂ := by
    calc
      _ = CochainComplex.mappingCocone.lift (HC.map φ₁) (HC.map α₁) 0 hH ≫
          squareIso.hom := by
            simpa only [Iso.trans_hom, Category.assoc] using
              congrArg (fun f => f ≫ squareIso.hom) hMapLift
      _ = CochainComplex.mappingCocone.lift φ₂ α₂ 0 h₂ := by
          change CochainComplex.mappingCocone.lift (HC.map φ₁) (HC.map α₁) 0 hH ≫
              mappingCoconeMap (HC.map φ₁) φ₂ a.hom b.hom comm = _
          exact cocone_lift_zero_map
            (HC.map φ₁) φ₂ a.hom b.hom comm (HC.map α₁) α₂ hα hH h₂
  exact ⟨mappedIso ≪≫ squareIso, hLiftNatural⟩

end CochainComplex
