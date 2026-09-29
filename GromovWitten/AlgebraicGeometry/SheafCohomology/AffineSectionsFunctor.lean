/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Additivity of the affine global-sections functor

The global-sections functor on modules over an affine scheme is additive on
module morphisms.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves
variable {R : CommRingCat.{u}}

/- The global-sections functor is additive by definition on module morphisms. -/
instance moduleSpecΓFunctor_additive : (moduleSpecΓFunctor (R := R)).Additive :=
  ⟨by intros; rfl⟩

end GromovWitten.AlgebraicGeometry.Curves
