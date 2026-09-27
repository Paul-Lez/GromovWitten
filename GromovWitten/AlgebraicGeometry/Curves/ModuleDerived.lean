/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ModuleEnoughInjectives
import GromovWitten.AlgebraicGeometry.Curves.ModuleExact
import GromovWitten.AlgebraicGeometry.Curves.ModuleFlasque
import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueResolution

/-!
# Module-valued derived pushforward

The category of sheaves of modules on a scheme has enough injectives.  This file therefore
constructs the module-valued right-derived pushforward itself.  The comparison with the
right-derived pushforward of the underlying abelian sheaf is deliberately kept separate: it
requires an exactness theorem for the scalar-forgetting functor, which is not an instance in the
pinned Mathlib.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S : Scheme.{u}}

/-- The `n`-th module-valued higher direct image. -/
def higherDirectImageModule (f : X ⟶ S) (M : X.Modules) (n : ℕ) : S.Modules :=
  ((Scheme.Modules.pushforward f).rightDerived n).obj M

/-- The degree-zero module-valued derived pushforward is ordinary pushforward. -/
def higherDirectImageModuleZeroIso (f : X ⟶ S) (M : X.Modules) :
    higherDirectImageModule f M 0 ≅ (Scheme.Modules.pushforward f).obj M :=
  Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward f) |>.app M

/-- Positive module-valued derived pushforwards of an injective object vanish. -/
theorem isZero_higherDirectImageModule_succ_of_injective (f : X ⟶ S) (M : X.Modules) (n : ℕ)
    [Injective M] :
    IsZero (higherDirectImageModule f M (n + 1)) :=
  Functor.isZero_rightDerived_obj_injective_succ (Scheme.Modules.pushforward f) n M

/-!
### Comparison with the underlying abelian derived functor

An injective module resolution is also a flasque resolution after forgetting the module
structure.  The scalar-forgetting functor preserves homology by `ModuleExact`, so the two
derived constructions are computed by the same pushed-forward complex.  This supplies the
underlying abelian sheaf of the module-valued higher direct image, rather than a separately
chosen module structure on an abelian derived object.
-/

noncomputable def higherDirectImageModuleAbIso (f : X ⟶ S) (M : X.Modules) (n : ℕ) :
    (moduleToSheafAb S).obj (higherDirectImageModule f M n) ≅
      higherDirectImageModuleAb f M n := by
  let I : InjectiveResolution M := InjectiveResolution.of M
  let A := moduleToSheafAb X
  let B := moduleToSheafAb S
  let Q := Scheme.Modules.pushforward f
  let K := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let eSingle := HomologicalComplex.singleMapHomologicalComplex A
    (ComplexShape.up ℕ) 0
  let a := (eSingle.inv.app M) ≫
    (A.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have hK (k : ℕ) : TopCat.Sheaf.IsFlasque (K.X k) := by
    exact module_isFlasque_of_injective _
  haveI : QuasiIso a := by infer_instance
  let hright := TopCat.Sheaf.flasqueResolutionRightDerivedIso
    (f := f.base) a hK n
  let hmodule := I.isoRightDerivedObj Q n
  let hBhom :
      B.obj ((HomologicalComplex.homologyFunctor S.Modules
        (ComplexShape.up ℕ) n).obj
        ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ≅
        (HomologicalComplex.homologyFunctor (TopCat.Sheaf Ab.{u} S)
          (ComplexShape.up ℕ) n).obj
          ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) := by
    exact (ShortComplex.mapHomologyIso
      (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n) B).symm
  exact
    (B.mapIso hmodule) ≪≫ hBhom ≪≫ hright.symm

end
end GromovWitten.AlgebraicGeometry.Curves
