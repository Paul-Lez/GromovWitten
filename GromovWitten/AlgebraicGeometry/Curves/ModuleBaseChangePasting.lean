/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeMate

/-!
# Pasting pushforward comparisons

The pushforward comparison attached to a commuting square is compatible with pasting a second
commuting square below it.  The associators in `modulePushforwardSquarePaste` only record the
parenthesisation changes needed to compose the four displayed comparisons.
-/

open CategoryTheory Limits Functor
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S T Z V W : Scheme.{u}}

/-- The composite of the pushforward comparisons for two vertically pasted squares. -/
def modulePushforwardSquarePaste (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (w₁ : p ≫ f = g ≫ b) (w₂ : q ≫ g = k ≫ c) :
    Scheme.Modules.pushforward (q ≫ p) ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward k ⋙ Scheme.Modules.pushforward (c ≫ b) :=
  Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp q p).symm
      (Scheme.Modules.pushforward f) ≪≫
    Functor.associator (Scheme.Modules.pushforward q)
      (Scheme.Modules.pushforward p) (Scheme.Modules.pushforward f) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward q)
      (modulePushforwardSquare f b p g w₁) ≪≫
    (Functor.associator (Scheme.Modules.pushforward q)
      (Scheme.Modules.pushforward g) (Scheme.Modules.pushforward b)).symm ≪≫
    Functor.isoWhiskerRight
      (modulePushforwardSquare g c q k w₂) (Scheme.Modules.pushforward b) ≪≫
    Functor.associator (Scheme.Modules.pushforward k)
      (Scheme.Modules.pushforward c) (Scheme.Modules.pushforward b) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward k)
      (Scheme.Modules.pushforwardComp c b)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pushforward square agrees with the composite for pasted squares. -/
lemma modulePushforwardSquare_pasting (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (w₁ : p ≫ f = g ≫ b) (w₂ : q ≫ g = k ≫ c)
    (w₀ : (q ≫ p) ≫ f = k ≫ (c ≫ b)) :
    modulePushforwardSquare f (c ≫ b) (q ≫ p) k w₀ =
      modulePushforwardSquarePaste f b p g c q k w₁ w₂ := by
  apply Iso.ext
  ext M U s
  simp only [modulePushforwardSquarePaste, modulePushforwardSquare, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.Hom.comp_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id,
    Scheme.Modules.pushforward_obj_presheaf_map]
  simp only [← Functor.map_comp]
  congr 2


set_option backward.isDefEq.respectTransparency false in
/-- The component form of pushforward pasting, with the final composition cancelled. -/
lemma modulePushforwardSquare_pasting_app
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (w₁ : p ≫ f = g ≫ b) (w₂ : q ≫ g = k ≫ c)
    (w₀ : (q ≫ p) ≫ f = k ≫ (c ≫ b)) (N : W.Modules) :
    (modulePushforwardSquare f (c ≫ b) (q ≫ p) k w₀).hom.app N ≫
        (Scheme.Modules.pushforwardComp c b).inv.app ((Scheme.Modules.pushforward k).obj N) =
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforwardComp q p).inv.app N) ≫
        (modulePushforwardSquare f b p g w₁).hom.app ((Scheme.Modules.pushforward q).obj N) ≫
          (Scheme.Modules.pushforward b).map ((modulePushforwardSquare g c q k w₂).hom.app N) := by
  rw [modulePushforwardSquare_pasting f b p g c q k w₁ w₂ w₀]
  simp [modulePushforwardSquarePaste]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical module base-change map is compatible with successive base changes. -/
lemma moduleBaseChange_pasting
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (h₁ : IsPullback p g f b) (h₂ : IsPullback q k g c)
    (M : X.Modules) :
    (Scheme.Modules.pullbackComp c b).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
      (modulePushforwardBaseChangeNatTrans f (c ≫ b) (q ≫ p) k (h₂.paste_horiz h₁)).app M =
    (Scheme.Modules.pullback c).map ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M) ≫
      (modulePushforwardBaseChangeNatTrans g c q k h₂).app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pushforward k).map ((Scheme.Modules.pullbackComp q p).hom.app M) := by
  let ρ : (Scheme.Modules.pushforward q ⋙ Scheme.Modules.pushforward p) ⋙
      Scheme.Modules.pushforward f ⟶ Scheme.Modules.pushforward k ⋙
        (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward b) :=
    whiskerLeft (Scheme.Modules.pushforward q) (modulePushforwardSquare f b p g h₁.w).hom ≫
      whiskerRight (modulePushforwardSquare g c q k h₂.w).hom (Scheme.Modules.pushforward b)
  have hunit := baseChange_unit_pasting
    (Scheme.Modules.pullbackPushforwardAdjunction b)
    (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction c)
    (Scheme.Modules.pullbackPushforwardAdjunction q)
    (modulePushforwardSquare f b p g h₁.w).hom
    (modulePushforwardSquare g c q k h₂.w).hom M
    ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M)
    ((modulePushforwardBaseChangeNatTrans g c q k h₂).app ((Scheme.Modules.pullback p).obj M))
    (moduleBaseChange_unit_formula f b p g h₁ M)
    (moduleBaseChange_unit_formula g c q k h₂ ((Scheme.Modules.pullback p).obj M))
  have he := baseChange_eq_of_unit_transport
    (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ b))
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction c))
    (Scheme.Modules.pullbackPushforwardAdjunction (q ≫ p))
    ((Scheme.Modules.pullbackPushforwardAdjunction p).comp
      (Scheme.Modules.pullbackPushforwardAdjunction q))
    (Scheme.Modules.pullbackComp c b).hom (Scheme.Modules.pullbackComp q p).hom
    (modulePushforwardSquare f (c ≫ b) (q ≫ p) k (h₂.paste_horiz h₁).w).hom ρ
    (by
      intro N
      rw [conjugateEquiv_pullbackComp_hom, conjugateEquiv_pullbackComp_hom]
      simpa only [ρ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.comp_obj, Category.assoc]
        using modulePushforwardSquare_pasting_app f b p g c q k h₁.w h₂.w
          (h₂.paste_horiz h₁).w N)
    M ((modulePushforwardBaseChangeNatTrans f (c ≫ b) (q ≫ p) k (h₂.paste_horiz h₁)).app M)
    ((Scheme.Modules.pullback c).map ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M) ≫
      (modulePushforwardBaseChangeNatTrans g c q k h₂).app ((Scheme.Modules.pullback p).obj M))
    (moduleBaseChange_unit_formula f (c ≫ b) (q ≫ p) k (h₂.paste_horiz h₁) M)
    (by
      simpa only [ρ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.comp_obj, Category.assoc]
        using hunit)
  simpa only [Category.assoc] using he
end
end GromovWitten.AlgebraicGeometry.Curves
