/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedHomology

/-! # Right derived functors and exact postcomposition -/

open CategoryTheory Limits HomologicalComplex
noncomputable section

namespace CategoryTheory.Functor
variable {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [G.PreservesHomology]
/-- Exact postcomposition commutes with right derived functors. -/
def rightDerivedCompExactIso (A : C) (n : ℕ) :
    ((F ⋙ G).rightDerived n).obj A ≅ G.obj ((F.rightDerived n).obj A) := by
  let I := InjectiveResolution.of A
  exact I.isoRightDerivedObj (F ⋙ G) n ≪≫
    ShortComplex.mapHomologyIso (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc n) G ≪≫
    G.mapIso (I.isoRightDerivedObj F n).symm
end CategoryTheory.Functor


namespace CategoryTheory.NatIso
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C] {F G : C ⥤ D} [F.Additive] [G.Additive]
def rightDerivedIso (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]
end CategoryTheory.NatIso

namespace CategoryTheory.Functor
variable {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
set_option backward.isDefEq.respectTransparency false in
def mapComplexHomologyIso (n : ℕ) :
    G.mapHomologicalComplex (.up ℕ) ⋙ HomologicalComplex.homologyFunctor E _ n ≅
      HomologicalComplex.homologyFunctor D _ n ⋙ G :=
  NatIso.ofComponents (fun K => ShortComplex.mapHomologyIso (K.sc n) G)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor D (.up ℕ) n).map f) G)
set_option backward.isDefEq.respectTransparency false in
def mapHomotopyHomologyIso (n : ℕ) :
    G.mapHomotopyCategory (.up ℕ) ⋙ HomotopyCategory.homologyFunctor E _ n ≅
      HomotopyCategory.homologyFunctor D _ n ⋙ G :=
  Quotient.natIsoLift _
    (isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℕ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (G.mapHomologicalComplex (.up ℕ))
        (HomotopyCategory.homologyFunctorFactors E (.up ℕ) n) ≪≫
      mapComplexHomologyIso G n ≪≫
      isoWhiskerRight (HomotopyCategory.homologyFunctorFactors D (.up ℕ) n).symm G)

variable {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive]
/-- Exact postcomposition commutes naturally with right derivation. -/
def rightDerivedCompExactNatIso (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F.rightDerived n ⋙ G :=
  isoWhiskerRight
    (isoWhiskerLeft (injectiveResolutions C)
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℕ)).symm) _ ≪≫
    isoWhiskerLeft (F.rightDerivedToHomotopyCategory) (mapHomotopyHomologyIso G n)
end CategoryTheory.Functor

namespace CategoryTheory.Functor
variable {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact postcomposition respects the canonical map into the zeroth derived functor. -/
lemma rightDerivedCompExactNatIso_zero_comp (A : C) :
    (F ⋙ G).toRightDerivedZero.app A ≫ (rightDerivedCompExactNatIso G F 0).hom.app A =
      G.map (F.toRightDerivedZero.app A) := by
  dsimp [rightDerivedCompExactNatIso, mapHomotopyHomologyIso]
  simp only [Functor.mapHomotopyCategoryCompIso, Quotient.natIsoLift,
    Functor.mapHomologicalComplexCompIso, Quotient.natTransLift,
    NatIso.mapHomologicalComplex, Iso.refl_inv, Iso.refl_hom,
    NatTrans.mapHomologicalComplex_id]
  dsimp
  simp only [Functor.map_id, Category.id_comp]
  dsimp [Functor.mapHomotopyCategoryFactors, Functor.rightDerivedToHomotopyCategory]
  erw [Category.id_comp, Functor.map_id, Category.id_comp]
  change (F ⋙ G).toRightDerivedZero.app A ≫
    (HomotopyCategory.homologyFunctorFactors E (.up ℕ) 0).hom.app
      ((G.mapHomologicalComplex (.up ℕ)).obj
        ((F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex)) ≫
      (ShortComplex.mapHomologyIso
        (((F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex).sc 0) G).hom ≫
      G.map ((HomotopyCategory.homologyFunctorFactors D (.up ℕ) 0).inv.app
        ((F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex)) = _
  dsimp only [Functor.toRightDerivedZero]
  simp only [Functor.map_comp, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [← Category.assoc]
  congr 1
  let K := (F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex
  have hπ : ((K.sc 0).map G).homologyπ ≫ ((K.sc 0).mapHomologyIso G).hom =
      ((K.sc 0).mapCyclesIso G).hom ≫ G.map (K.sc 0).homologyπ := by
    rw [(K.sc 0).leftHomologyData.mapHomologyIso_eq,
      (K.sc 0).leftHomologyData.mapCyclesIso_eq]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
    change _ ≫ G.map _ ≫ G.map _ = _ ≫ G.map _ ≫ G.map _
    rw [← G.map_comp, ← G.map_comp,
      ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  dsimp only [CochainComplex.isoHomologyπ₀, asIso_hom]
  erw [Category.assoc, hπ, ← Category.assoc]
  congr 1
  apply (cancel_mono (G.map (K.sc 0).iCycles)).mp
  rw [Category.assoc, ShortComplex.mapCyclesIso_hom_iCycles]
  change (injectiveResolution A).toRightDerivedZero' (F ⋙ G) ≫ _ =
    G.map ((injectiveResolution A).toRightDerivedZero' F) ≫ G.map (K.iCycles 0)
  rw [← G.map_comp]
  erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Compute exact postcomposition on the chosen injective resolution. -/
lemma rightDerivedCompExactNatIso_app_eq (A : C) (n : ℕ) :
    (rightDerivedCompExactNatIso G F n).hom.app A =
      ((injectiveResolution A).isoRightDerivedObj (F ⋙ G) n).hom ≫
        (ShortComplex.mapHomologyIso
          (((F.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution A).cocomplex).sc n)
          G).hom ≫ G.map ((injectiveResolution A).isoRightDerivedObj F n).inv := by
  apply (cancel_mono (G.map ((injectiveResolution A).isoRightDerivedObj F n).hom)).mp
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.comp_id]
  rw [InjectiveResolution.isoRightDerivedObj_hom_injectiveResolution,
    InjectiveResolution.isoRightDerivedObj_hom_injectiveResolution]
  dsimp [rightDerivedCompExactNatIso, mapHomotopyHomologyIso]
  simp only [Functor.mapHomotopyCategoryCompIso, Quotient.natIsoLift,
    Functor.mapHomologicalComplexCompIso, Quotient.natTransLift,
    NatIso.mapHomologicalComplex, Iso.refl_inv, Iso.refl_hom,
    NatTrans.mapHomologicalComplex_id]
  dsimp
  simp only [Functor.map_id, Category.id_comp]
  dsimp [Functor.mapHomotopyCategoryFactors, Functor.rightDerivedToHomotopyCategory,
    mapComplexHomologyIso]
  simp only [Category.assoc, ← G.map_comp]
  erw [Functor.map_id, Category.id_comp, Category.id_comp,
    Iso.inv_hom_id_app, G.map_id, Category.comp_id]
  rfl

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C] {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Deriving a natural transformation respects the canonical degree-zero comparison. -/
lemma toRightDerivedZero_comp (A : C) :
    F.toRightDerivedZero.app A ≫ (NatTrans.rightDerived α 0).app A =
      α.app A ≫ G.toRightDerivedZero.app A := by
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory,
    NatTrans.mapHomotopyCategory]
  dsimp only [Functor.toRightDerivedZero]
  simp only [Category.assoc]
  have hnat := (HomotopyCategory.homologyFunctorFactors D (.up ℕ) 0).inv.naturality
    ((NatTrans.mapHomologicalComplex α (.up ℕ)).app (injectiveResolution A).cocomplex)
  dsimp only [Functor.comp_map] at hnat
  erw [← hnat]
  simp only [← Category.assoc]
  congr 1
  dsimp only [CochainComplex.isoHomologyπ₀, asIso_hom]
  erw [Category.assoc, homologyπ_naturality]
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (iCycles _ 0)).mp
  simp only [Category.assoc, cyclesMap_i,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
  exact α.naturality ((injectiveResolution A).ι.f 0)
end CategoryTheory.NatTrans
