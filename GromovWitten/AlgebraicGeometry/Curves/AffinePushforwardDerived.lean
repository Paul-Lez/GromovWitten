/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.AcyclicResolutionAugmentation
import GromovWitten.AlgebraicGeometry.Curves.ModuleFlasqueResolution
import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImage
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedComposition

/-!
# Higher direct images after affine pushforward

For an affine morphism `f` with locally Noetherian source, this file constructs in
each degree an object isomorphism from the higher direct image after `f` and then
`g` to the higher direct image after the composite.  The construction assumes a
quasi-coherent module on the source and makes no naturality claim.
-/

open CategoryTheory Limits HomologicalComplex
open _root_.AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X Y Z : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Construct the degree-`n` isomorphism
`Rⁿg₊(f₊M) ≅ Rⁿ(g ∘ f)₊M` when `f` is affine, `X` is locally Noetherian, and
`M` is quasi-coherent. -/
def affinePushforwardHigherDirectImageIso
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsAffineHom f] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    higherDirectImageModule g ((Scheme.Modules.pushforward f).obj M) n ≅
      higherDirectImageModule (f ≫ g) M n := by
  let L := Scheme.Modules.pushforward f
  let F := Scheme.Modules.pushforward g
  let I := injectiveResolution M
  let K := (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let a : (CochainComplex.single₀ Y.Modules).obj (L.obj M) ⟶ K :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have ha : QuasiIso a := by
    exact Functor.quasiIso_resolutionAug_of_isZero_rightDerived_succ L M
      (fun m => isZero_higherDirectImageModule_affine_succ f M m)
  have hK (m : ℕ) : TopCat.Sheaf.IsFlasque ((moduleToSheafAb Y).obj (K.X m)) := by
    exact modulePushforward_isFlasque f (I.cocomplex.X m)
  exact moduleFlasqueResolutionRightDerivedIso g a hK n ≪≫
    (I.isoRightDerivedObj (L ⋙ F) n).symm ≪≫
    (NatIso.rightDerivedIso (Scheme.Modules.pushforwardComp f g) n).app M

end GromovWitten.AlgebraicGeometry.Curves
