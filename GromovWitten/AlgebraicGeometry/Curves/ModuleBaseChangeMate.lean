/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChange
import GromovWitten.CategoryTheory.BeckChevalley

/-!
# The unit description of module base change

The canonical module base-change comparison, defined using pullback composition
and a counit, is adjoint to the unit followed by the commuting pushforward square.
This description exposes the right-adjoint maps used in affine calculations.
-/
open CategoryTheory Limits
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X Y Z : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- Pullback transport along an equality is conjugate to inverse pushforward transport. -/
lemma conjugateEquiv_pullbackCongr_hom {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackCongr h).hom = (Scheme.Modules.pushforwardCongr h).inv := by
  subst g
  change conjugateEquiv _ _ (𝟙 _) = _
  rw [conjugateEquiv_id]
  ext M U
  simp
set_option backward.isDefEq.respectTransparency false in
/-- The pullback composition isomorphism is conjugate to inverse pushforward composition. -/
lemma conjugateEquiv_pullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackComp f g).hom = (Scheme.Modules.pushforwardComp f g).inv := by
  have h := conjugateEquiv_comm
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackComp f g).inv_hom_id
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  apply (cancel_mono (Scheme.Modules.pushforwardComp f g).hom).mp
  simpa using h
variable {S T : Scheme.{u}}
/-- The pushforward square induced by a commuting square of schemes. -/
def modulePushforwardSquare (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (w : p ≫ f = g ≫ b) :
    Scheme.Modules.pushforward p ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward g ⋙ Scheme.Modules.pushforward b :=
  Scheme.Modules.pushforwardComp p f ≪≫
    (Scheme.Modules.pushforwardCongr w.symm).symm ≪≫
    (Scheme.Modules.pushforwardComp g b).symm

set_option backward.isDefEq.respectTransparency false in
/-- The pullback and pushforward comparisons for a commuting square are conjugate. -/
lemma modulePullbackSquare_conjugate (f : X ⟶ S) (b : T ⟶ S)
    (p : Z ⟶ X) (g : Z ⟶ T) (w : p ≫ f = g ≫ b) :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction p))
      ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g))
      ((Scheme.Modules.pullbackComp g b).hom ≫
        (Scheme.Modules.pullbackCongr w.symm).hom ≫
        (Scheme.Modules.pullbackComp p f).inv) =
      (modulePushforwardSquare f b p g w).hom := by
  dsimp only [modulePushforwardSquare, Iso.trans_hom, Iso.symm_hom]
  rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv p f,
    ← conjugateEquiv_pullbackCongr_hom w.symm, ← conjugateEquiv_pullbackComp_hom g b]
  rw [conjugateEquiv_comp
    (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ f))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b))
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))]
  rw [conjugateEquiv_comp
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p))
    (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ f))
    ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The adjoint of canonical module base change is the pushforward of the unit,
followed by the pushforward comparison for the square. -/
lemma moduleBaseChange_unit_formula (f : X ⟶ S) (b : T ⟶ S)
    (p : Z ⟶ X) (g : Z ⟶ T) (h : IsPullback p g f b) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
      ((modulePushforwardBaseChangeNatTrans f b p g h).app M) =
    (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) ≫
      (modulePushforwardSquare f b p g h.w).hom.app
        ((Scheme.Modules.pullback p).obj M) := by
  have he := beckChevalley_unit_formula
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction b)
    (Scheme.Modules.pullbackPushforwardAdjunction p)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    ((Scheme.Modules.pullbackComp g b).hom ≫
      (Scheme.Modules.pullbackCongr h.w.symm).hom ≫
      (Scheme.Modules.pullbackComp p f).inv) M
  rw [modulePullbackSquare_conjugate f b p g h.w] at he
  simpa only [modulePushforwardBaseChangeNatTrans, moduleBaseChangePullbackMap,
    NatTrans.comp_app, Functor.comp_obj, Functor.id_obj, Category.assoc] using he
end
end GromovWitten.AlgebraicGeometry.Curves
