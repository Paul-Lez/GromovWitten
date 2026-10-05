/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeMate
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPushforward
/-!
# Base change along an open inclusion

The canonical module base-change map for the inverse-image square of an open
subset is an isomorphism, without a quasi-coherence hypothesis. We identify it
with the restriction comparison by its adjoint unit formula.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
set_option backward.isDefEq.respectTransparency false in
/-- The restriction comparison acts by the canonical equality of inverse-image opens. -/
lemma modulePushforwardOpenRestrictIso_hom_app (M : X.Modules) (W : U.toScheme.Opens) :
    ((modulePushforwardOpenRestrictIso f U).hom.app M).app W =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W)).op := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction comparison satisfies the unit formula for base change. -/
lemma moduleOpenRestrictIso_unit (M : X.Modules) :
    (Scheme.Modules.restrictAdjunction U.ι).homEquiv _ _
        ((modulePushforwardOpenRestrictIso f U).hom.app M) =
      (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M) ≫
        (modulePushforwardSquare f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
          (isPullback_morphismRestrict f U).flip.w).hom.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M) := by
  rw [Adjunction.homEquiv_unit]
  ext V s
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, ConcreteCategory.comp_apply,
    modulePushforwardSquare, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app,
    modulePushforwardOpenRestrictIso_hom_app, Scheme.Modules.pushforward_obj_presheaf_map,
    Scheme.Modules.restrict_map]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2
  erw [Category.comp_id, Category.comp_id, ← Functor.map_comp]
  congr 1
set_option backward.isDefEq.respectTransparency false in
/-- Base change along an open inclusion, using the restriction functors. -/
def moduleOpenBaseChangeIso (M : X.Modules) :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M) :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
    (modulePushforwardOpenRestrictIso f U).app M ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app M)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical adjunction mate is the restriction comparison. -/
lemma moduleOpenBaseChange_eq_iso (M : X.Modules) :
    (modulePushforwardBaseChangeNatTrans f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
      (isPullback_morphismRestrict f U).flip).app M = (moduleOpenBaseChangeIso f U M).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv _ _).injective
  rw [moduleBaseChange_unit_formula]
  symm
  exact baseChange_unit_leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι)
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι)
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
    (modulePushforwardSquare f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
      (isPullback_morphismRestrict f U).flip.w).hom M
    ((modulePushforwardOpenRestrictIso f U).hom.app M) (moduleOpenRestrictIso_unit f U M)

instance moduleBaseChange_open_isIso (M : X.Modules) :
    IsIso ((modulePushforwardBaseChangeNatTrans f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
      (isPullback_morphismRestrict f U).flip).app M) := by
  rw [moduleOpenBaseChange_eq_iso]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of the canonical adjunction unit `N ⟶ f_* f^* N` to an
open set is an isomorphism whenever `f` is an isomorphism over that open set. -/
theorem pullbackPushforwardUnit_isIso_of_isIso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] (N : Y.Modules) :
    IsIso ((Scheme.Modules.pullback U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)) := by
  let b := U.ι
  let p := (f ⁻¹ᵁ U).ι
  let g := f ∣_ U
  let h := (isPullback_morphismRestrict f U).flip
  let af := Scheme.Modules.pullbackPushforwardAdjunction f
  let ag := Scheme.Modules.pullbackPushforwardAdjunction g
  let σ : Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback p :=
    (Scheme.Modules.pullbackComp g b).hom ≫
      (Scheme.Modules.pullbackCongr h.w.symm).hom ≫
      (Scheme.Modules.pullbackComp p f).inv
  let β := (modulePushforwardBaseChangeNatTrans f b p g h).app
    ((Scheme.Modules.pullback f).obj N)
  let rhs := ag.homEquiv _ _ (σ.app N)
  have hbcMap : moduleBaseChangePullbackMap f b p g h ((Scheme.Modules.pullback f).obj N) =
      σ.app ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N)) ≫
        (Scheme.Modules.pullback p).map (af.counit.app ((Scheme.Modules.pullback f).obj N)) := by
    dsimp [moduleBaseChangePullbackMap, σ, af, b, p, g, h]
    simp only [Category.assoc]
  have hformula :
      (Scheme.Modules.pullback b).map (af.unit.app N) ≫ β = rhs := by
    change (Scheme.Modules.pullback b).map (af.unit.app N) ≫
      ag.homEquiv _ _ (moduleBaseChangePullbackMap f b p g h
        ((Scheme.Modules.pullback f).obj N)) = rhs
    rw [hbcMap]
    exact CategoryTheory.beckChevalley_vertical_unit_formula af ag σ N
  have hβ : IsIso β := by
    change IsIso ((modulePushforwardBaseChangeNatTrans f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
      (isPullback_morphismRestrict f U).flip).app ((Scheme.Modules.pullback f).obj N))
    infer_instance
  have hσ : IsIso (σ.app N) := by
    dsimp [σ]
    infer_instance
  have hrhs : IsIso rhs := by
    dsimp [rhs]
    rw [Adjunction.homEquiv_unit]
    infer_instance
  have hcomp : IsIso ((Scheme.Modules.pullback b).map (af.unit.app N) ≫ β) := by
    rw [hformula]
    exact hrhs
  exact IsIso.of_isIso_comp_right _ β
end
end GromovWitten.AlgebraicGeometry.Curves
