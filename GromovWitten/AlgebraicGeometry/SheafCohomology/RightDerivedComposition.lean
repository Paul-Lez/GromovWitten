/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Right derived functors and exact postcomposition -/

open CategoryTheory Limits
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
