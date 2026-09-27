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
end CategoryTheory.NatTrans
