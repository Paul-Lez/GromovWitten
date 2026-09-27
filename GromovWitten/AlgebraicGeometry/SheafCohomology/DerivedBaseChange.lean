/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedComposition
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedPrecomposition
/-!
# Higher base-change comparisons

A square of additive functors gives a map between the pullback of a higher derived
functor and the higher derived functor of the pullback when both horizontal functors
are exact. This uses exact postcomposition on the source and a comparison with an
injective resolution on the target. The map is not asserted to be an isomorphism.
-/

open CategoryTheory Limits
noncomputable section
namespace CategoryTheory.NatTrans
variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [Abelian C] [Abelian D] [Abelian E] [Abelian H]
    [EnoughInjectives C] [EnoughInjectives E]
    {Q : C ⥤ D} {M : D ⥤ H} {L : C ⥤ E} {P : E ⥤ H}
    [Q.Additive] [M.Additive] [L.Additive] [P.Additive]
    [M.PreservesHomology] [L.PreservesHomology]
/-- The higher comparison induced by a square with exact horizontal functors. -/
def rightDerivedBaseChange (α : Q ⋙ M ⟶ L ⋙ P) (n : ℕ) :
    Q.rightDerived n ⋙ M ⟶ L ⋙ P.rightDerived n :=
  (Functor.rightDerivedCompExactNatIso M Q n).inv ≫
    NatTrans.rightDerived α n ≫ Functor.rightDerivedPrecompComparison L P n
set_option backward.isDefEq.respectTransparency false in
/-- The higher comparison respects the canonical augmentations in degree zero. -/
lemma rightDerivedBaseChange_zero_comp (α : Q ⋙ M ⟶ L ⋙ P) (A : C) :
    M.map (Q.toRightDerivedZero.app A) ≫ (rightDerivedBaseChange α 0).app A =
      α.app A ≫ P.toRightDerivedZero.app (L.obj A) := by
  dsimp only [rightDerivedBaseChange, NatTrans.comp_app]
  rw [← Functor.rightDerivedCompExactNatIso_zero_comp Q M A]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, NatTrans.toRightDerivedZero_comp, Category.assoc,
    Functor.rightDerivedPrecompComparison_zero_comp]

/-- Under the standard degree-zero identifications, the higher comparison is the ordinary map. -/
lemma rightDerivedBaseChange_zero [PreservesFiniteLimits Q] [PreservesFiniteLimits P]
    (α : Q ⋙ M ⟶ L ⋙ P) (A : C) :
    M.map (Q.rightDerivedZeroIsoSelf.inv.app A) ≫ (rightDerivedBaseChange α 0).app A ≫
      P.rightDerivedZeroIsoSelf.hom.app (L.obj A) = α.app A := by
  change M.map (Q.toRightDerivedZero.app A) ≫ _ ≫ _ = _
  rw [← Category.assoc, rightDerivedBaseChange_zero_comp, Category.assoc,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app]
  exact Category.comp_id _
end CategoryTheory.NatTrans
