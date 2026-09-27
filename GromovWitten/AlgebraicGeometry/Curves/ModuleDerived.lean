/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ModuleEnoughInjectives

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

end
end GromovWitten.AlgebraicGeometry.Curves
