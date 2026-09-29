/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Composition of pullback units

The unit of the pullback-pushforward adjunction is compatible with composition of scheme
morphisms.  The pointwise section formula is used by the relative open-section comparisons.
-/

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X Y Z : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The two successive pullback units agree with the unit for the composite morphism. -/
lemma pullbackUnit_comp_app (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (m : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U m)) =
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have hh := congrArg (fun k => k.app U) h
  have hx := ConcreteCategory.congr_hom hh m
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app] at hx
  change ((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U m) =
      ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U m) at hx
  rw [hx]
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pullback unit is unchanged when its scheme morphism is replaced by an equal morphism. -/
lemma pullbackUnit_congr_app {f g : X ⟶ Y} (h : f = g) (M : Y.Modules)
    (U : Y.Opens) (m : Γ(M, U)) :
    ((pullbackCongr h).hom.app M).app (g ⁻¹ᵁ U)
        (((pullback f).obj M).presheaf.map
          (eqToHom (show g ⁻¹ᵁ U = f ⁻¹ᵁ U from by subst g; rfl)).op
          (((pullbackPushforwardAdjunction f).unit.app M).app U m)) =
      ((pullbackPushforwardAdjunction g).unit.app M).app U m := by
  subst g
  simp [pullbackCongr]

end GromovWitten.AlgebraicGeometry.Curves
