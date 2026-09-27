/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeMate
/-!
# The base-change unit on global sections

The commuting pushforward square acts identically on global sections. Consequently
applying the canonical base-change map to the base pullback unit gives the source
pullback unit. These identities avoid expanding concrete affine scheme expressions.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X S T Z : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- The pushforward square acts identically on global sections. -/
lemma modulePushforwardSquare_app_top (f : X ⟶ S) (b : T ⟶ S)
    (p : Z ⟶ X) (g : Z ⟶ T) (w : p ≫ f = g ≫ b)
    (M : Z.Modules) (x : M.presheaf.obj (op ⊤)) :
    ((modulePushforwardSquare f b p g w).hom.app M).app ⊤ x = x := by
  simp only [modulePushforwardSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [Scheme.Modules.pushforwardComp_hom_app_app p f]
  rw [Scheme.Modules.pushforwardCongr_inv_app_app]
  rw [Scheme.Modules.pushforwardComp_inv_app_app g b]
  change (M.presheaf.map (𝟙 (op ⊤))) x = x
  rw [M.presheaf.map_id]
  rfl
set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison carries the base unit to the source unit on sections. -/
lemma moduleBaseChange_unit_app_top (f : X ⟶ S) (b : T ⟶ S)
    (p : Z ⟶ X) (g : Z ⟶ T) (h : IsPullback p g f b)
    (M : X.Modules) (x : M.presheaf.obj (op ⊤)) :
    ((modulePushforwardBaseChangeNatTrans f b p g h).app M).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
        ((Scheme.Modules.pushforward f).obj M)).app ⊤ x) =
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ x := by
  have hu := moduleBaseChange_unit_formula f b p g h M
  rw [Adjunction.homEquiv_unit] at hu
  have htop := congrArg (fun φ => φ.app ⊤) hu
  let xA : ((Scheme.Modules.pushforward f).obj M).presheaf.obj (op ⊤) := x
  have hx := ConcreteCategory.congr_hom htop xA
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hx
  erw [modulePushforwardSquare_app_top f b p g h.w
    ((Scheme.Modules.pullback p).obj M)] at hx
  exact hx
end
end GromovWitten.AlgebraicGeometry.Curves
