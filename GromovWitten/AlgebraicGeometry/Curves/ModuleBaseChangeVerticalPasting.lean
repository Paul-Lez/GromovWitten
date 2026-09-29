/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeMate

/-!
# Vertical pasting of pushforward comparisons

The pushforward comparison for a composite top morphism is the componentwise composite of the
comparisons for its two constituent squares.  This is the vertical counterpart of the
comparison-pasting isomorphism in `ModuleBaseChangePasting.lean`.
-/

open CategoryTheory Limits Functor
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X Y S T Z W : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Componentwise vertical pasting for the canonical module pushforward square. -/
lemma modulePushforwardSquare_vertical_pasting
    (f : X ⟶ Y) (a : Y ⟶ S) (b : T ⟶ S) (p : Z ⟶ Y) (g : Z ⟶ T)
    (q : W ⟶ X) (k : W ⟶ Z)
    (w₁ : q ≫ f = k ≫ p) (w₂ : p ≫ a = g ≫ b)
    (w₀ : q ≫ (f ≫ a) = (k ≫ g) ≫ b) (N : W.Modules) :
    (modulePushforwardSquare (f ≫ a) b q (k ≫ g) w₀).hom.app N =
      (Scheme.Modules.pushforwardComp f a).inv.app
          ((Scheme.Modules.pushforward q).obj N) ≫
        (Scheme.Modules.pushforward a).map
          ((modulePushforwardSquare f p q k w₁).hom.app N) ≫
        (modulePushforwardSquare a b p g w₂).hom.app
          ((Scheme.Modules.pushforward k).obj N) ≫
        (Scheme.Modules.pushforward b).map
          ((Scheme.Modules.pushforwardComp k g).hom.app N) := by
  ext U s
  simp only [Scheme.Modules.Hom.comp_app]
  rw [Scheme.Modules.pushforwardComp_inv_app_app f a]
  simp only [modulePushforwardSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.Hom.comp_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id,
    Scheme.Modules.pushforward_obj_presheaf_map]
  congr 2
  erw [Category.comp_id]
  simp only [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Canonical module base change is compatible with composition of the original map. -/
lemma moduleBaseChange_vertical_pasting
    (f : X ⟶ Y) (a : Y ⟶ S) (b : T ⟶ S) (p : Z ⟶ Y) (g : Z ⟶ T)
    (q : W ⟶ X) (k : W ⟶ Z)
    (h₁ : IsPullback q k f p) (h₂ : IsPullback p g a b)
    (M : X.Modules) :
    (modulePushforwardBaseChangeNatTrans (f ≫ a) b q (k ≫ g) (h₁.paste_vert h₂)).app M =
      (Scheme.Modules.pullback b).map ((Scheme.Modules.pushforwardComp f a).inv.app M) ≫
        (modulePushforwardBaseChangeNatTrans a b p g h₂).app
          ((Scheme.Modules.pushforward f).obj M) ≫
          (Scheme.Modules.pushforward g).map
            ((modulePushforwardBaseChangeNatTrans f p q k h₁).app M) ≫
            (Scheme.Modules.pushforwardComp k g).hom.app ((Scheme.Modules.pullback q).obj M) := by
  let ρ : Scheme.Modules.pushforward q ⋙
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward a) ⟶
      (Scheme.Modules.pushforward k ⋙ Scheme.Modules.pushforward g) ⋙
        Scheme.Modules.pushforward b :=
    whiskerRight (modulePushforwardSquare f p q k h₁.w).hom (Scheme.Modules.pushforward a) ≫
      whiskerLeft (Scheme.Modules.pushforward k) (modulePushforwardSquare a b p g h₂.w).hom
  have hunit := baseChange_unit_vertical_pasting
    (Scheme.Modules.pullbackPushforwardAdjunction b)
    (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction q)
    (modulePushforwardSquare f p q k h₁.w).hom
    (modulePushforwardSquare a b p g h₂.w).hom M
    ((modulePushforwardBaseChangeNatTrans f p q k h₁).app M)
    ((modulePushforwardBaseChangeNatTrans a b p g h₂).app ((Scheme.Modules.pushforward f).obj M))
    (moduleBaseChange_unit_formula f p q k h₁ M)
    (moduleBaseChange_unit_formula a b p g h₂ ((Scheme.Modules.pushforward f).obj M))
  have he := baseChange_eq_of_functor_transport
    (Scheme.Modules.pullbackPushforwardAdjunction b)
    (Scheme.Modules.pullbackPushforwardAdjunction q)
    (Scheme.Modules.pushforwardComp f a).inv (Scheme.Modules.pushforwardComp k g).hom
    (modulePushforwardSquare (f ≫ a) b q (k ≫ g) (h₁.paste_vert h₂).w).hom ρ
    (by
      intro N
      simpa only [ρ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.comp_obj, Category.assoc] using
        modulePushforwardSquare_vertical_pasting f a b p g q k h₁.w h₂.w
          (h₁.paste_vert h₂).w N)
    M ((modulePushforwardBaseChangeNatTrans (f ≫ a) b q (k ≫ g) (h₁.paste_vert h₂)).app M)
    ((modulePushforwardBaseChangeNatTrans a b p g h₂).app ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.pushforward g).map ((modulePushforwardBaseChangeNatTrans f p q k h₁).app M))
    (moduleBaseChange_unit_formula (f ≫ a) b q (k ≫ g) (h₁.paste_vert h₂) M)
    (by
      simpa only [ρ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.comp_map, Functor.comp_obj, Category.assoc] using hunit)
  simpa only [Category.assoc] using he
end
end GromovWitten.AlgebraicGeometry.Curves
