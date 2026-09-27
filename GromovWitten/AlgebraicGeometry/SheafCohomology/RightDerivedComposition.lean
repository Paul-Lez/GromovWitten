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
