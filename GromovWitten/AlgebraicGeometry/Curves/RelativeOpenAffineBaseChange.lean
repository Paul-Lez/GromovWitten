/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.Curves.RestrictionPullbackMate
import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenBaseChange
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeVerticalPasting

/-!
# Affine relative open base change

The relative open base-change map is expressed after transport as the
base-change map for the restricted square.  In particular, for a quasicoherent
module it is an isomorphism when the relevant composite to the base is affine.
-/

open CategoryTheory AlgebraicGeometry Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- Expand the relative pushforward square through the restricted square. -/
lemma relativeOpenPushforwardSquare_composite (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U : X.Opens)
    (hU : (p ∣_ U) ≫ (U.ι ≫ s) = ((p ⁻¹ᵁ U).ι ≫ g) ≫ b) (N : Y.Modules) :
    (relativeOpenPushforwardSquare s b p g w U).hom.app N =
      (pushforwardComp U.ι s).hom.app ((restrictFunctor U.ι).obj ((pushforward p).obj N)) ≫
      (pushforward (U.ι ≫ s)).map ((modulePushforwardOpenRestrictIso p U).hom.app N) ≫
      (modulePushforwardSquare (U.ι ≫ s) b (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ g) hU).hom.app
        ((restrictFunctor (p ⁻¹ᵁ U).ι).obj N) ≫
      (pushforward b).map ((pushforwardComp (p ⁻¹ᵁ U).ι g).inv.app
        ((restrictFunctor (p ⁻¹ᵁ U).ι).obj N)) := by
  ext W m
  simp only [Hom.comp_app, pushforward_map_app,
    relativeOpenPushforwardSquare_hom_app_app,
    modulePushforwardOpenRestrictIso_hom_app,
    modulePushforwardSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app,
    ConcreteCategory.comp_apply]
  simp only [Functor.comp_obj, pushforward_obj_obj, restrict_obj]
  simp only [restrict_map, ← ConcreteCategory.comp_apply]
  congr 2
  simp only [Category.comp_id, Category.id_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Express relative open base change as the transported base-change map for
the restricted square. -/
lemma relativeOpenBaseChangeNatTrans_eq_composite (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (h : IsPullback p g s b) (U : X.Opens)
    (M : X.Modules) :
    (relativeOpenBaseChangeNatTrans s b p g h.w U).app M =
      (pullback b).map ((pushforwardComp U.ι s).hom.app ((restrictFunctor U.ι).obj M)) ≫
        (modulePushforwardBaseChangeNatTrans (U.ι ≫ s) b (p ∣_ U)
          ((p ⁻¹ᵁ U).ι ≫ g) ((isPullback_morphismRestrict p U).paste_vert h)).app
            ((restrictFunctor U.ι).obj M) ≫
        (pushforward ((p ⁻¹ᵁ U).ι ≫ g)).map ((restrictPullbackIso p U).hom.app M) ≫
        (pushforwardComp (p ⁻¹ᵁ U).ι g).inv.app ((restrictFunctor (p ⁻¹ᵁ U).ι).obj
          ((pullback p).obj M)) := by
  let hU := (isPullback_morphismRestrict p U).paste_vert h
  let ρ : pushforward p ⋙ (restrictFunctor U.ι ⋙ pushforward (U.ι ≫ s)) ⟶
      (restrictFunctor (p ⁻¹ᵁ U).ι ⋙ pushforward ((p ⁻¹ᵁ U).ι ≫ g)) ⋙ pushforward b :=
    Functor.whiskerRight (modulePushforwardOpenRestrictIso p U).hom
      (pushforward (U.ι ≫ s)) ≫
    Functor.whiskerLeft (restrictFunctor (p ⁻¹ᵁ U).ι)
      (modulePushforwardSquare (U.ι ≫ s) b (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ g) hU.w).hom
  have hunit := baseChange_unit_vertical_pasting
    (pullbackPushforwardAdjunction b) (pullbackPushforwardAdjunction (p ∣_ U))
    (pullbackPushforwardAdjunction p)
    (modulePushforwardOpenRestrictIso p U).hom
    (modulePushforwardSquare (U.ι ≫ s) b (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ g) hU.w).hom M
    ((restrictPullbackIso p U).hom.app M)
    ((modulePushforwardBaseChangeNatTrans (U.ι ≫ s) b (p ∣_ U)
      ((p ⁻¹ᵁ U).ι ≫ g) hU).app ((restrictFunctor U.ι).obj M))
    (restrictPullback_homEquiv p U M)
    (moduleBaseChange_unit_formula (U.ι ≫ s) b (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ g)
      hU ((restrictFunctor U.ι).obj M))
  have he := baseChange_eq_of_functor_transport
    (pullbackPushforwardAdjunction b) (pullbackPushforwardAdjunction p)
    (Functor.whiskerLeft (restrictFunctor U.ι) (pushforwardComp U.ι s).hom)
    (Functor.whiskerLeft (restrictFunctor (p ⁻¹ᵁ U).ι)
      (pushforwardComp (p ⁻¹ᵁ U).ι g).inv)
    (relativeOpenPushforwardSquare s b p g h.w U).hom ρ
    (by
      intro N
      simpa only [ρ, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.comp_obj, Category.assoc] using
        relativeOpenPushforwardSquare_composite s b p g h.w U hU.w N)
    M ((relativeOpenBaseChangeNatTrans s b p g h.w U).app M)
    ((modulePushforwardBaseChangeNatTrans (U.ι ≫ s) b (p ∣_ U)
      ((p ⁻¹ᵁ U).ι ≫ g) hU).app ((restrictFunctor U.ι).obj M) ≫
      (pushforward ((p ⁻¹ᵁ U).ι ≫ g)).map ((restrictPullbackIso p U).hom.app M))
    (relativeOpenBaseChangeNatTrans_homEquiv s b p g h.w U M)
    (by
      simpa only [ρ, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj, Category.assoc] using hunit)
  simpa only [Functor.whiskerLeft_app, Category.assoc, hU] using he


set_option backward.isDefEq.respectTransparency false in
/-- Relative open base change is invertible over an affine composite for quasicoherent modules. -/
lemma relativeOpenBaseChangeNatTrans_isIso (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (h : IsPullback p g s b) (U : X.Opens)
    [IsAffineHom (U.ι ≫ s)] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((relativeOpenBaseChangeNatTrans s b p g h.w U).app M) := by
  let hU := (isPullback_morphismRestrict p U).paste_vert h
  have := moduleBaseChange_isIso_of_isAffineHom (U.ι ≫ s) b (p ∣_ U)
    ((p ⁻¹ᵁ U).ι ≫ g) hU ((restrictFunctor U.ι).obj M)
  rw [relativeOpenBaseChangeNatTrans_eq_composite s b p g h U M]
  infer_instance
end GromovWitten.AlgebraicGeometry.Curves
