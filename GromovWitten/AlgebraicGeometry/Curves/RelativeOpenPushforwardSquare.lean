/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves
import GromovWitten.AlgebraicGeometry.Curves.ModuleOpenBaseChange

/-!
# Relative open pushforward squares

This file compares restriction of a pushforward to `U` with pushforward of
the restriction to `p⁻¹U`, then composes to the bases.  The comparison is
compatible with adjunction units and with restriction to a smaller open
subset.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

open GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward and restriction form the canonical square over a commutative diagram. -/
def relativeOpenPushforwardSquare (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U : X.Opens) :
    pushforward p ⋙ relativeOpenPushforward s U ≅
      relativeOpenPushforward g (p ⁻¹ᵁ U) ⋙ pushforward b := by
  let U' := p ⁻¹ᵁ U
  let pU := p ∣_ U
  have hw : (pU ≫ U.ι) ≫ s = (U'.ι ≫ g) ≫ b := by
    dsimp [pU, U']
    rw [morphismRestrict_ι, Category.assoc, w]
    simp only [Category.assoc]
  exact
    Functor.isoWhiskerRight (modulePushforwardOpenRestrictIso p U)
      (pushforward U.ι ⋙ pushforward s) ≪≫
    Functor.isoWhiskerLeft (restrictFunctor U'.ι)
      (Functor.isoWhiskerRight (pushforwardComp pU U.ι) (pushforward s) ≪≫
        pushforwardComp (pU ≫ U.ι) s ≪≫ pushforwardCongr hw ≪≫
        (pushforwardComp (U'.ι ≫ g) b).symm ≪≫
        Functor.isoWhiskerRight (pushforwardComp U'.ι g).symm (pushforward b))

end GromovWitten.AlgebraicGeometry.Curves
namespace GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X S T Y : Scheme.{u}}

private lemma relativeOpenSquare_image_eq (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U : X.Opens) (W : S.Opens) :
    (p ⁻¹ᵁ U).ι ''ᵁ ((p ⁻¹ᵁ U).ι ⁻¹ᵁ (g ⁻¹ᵁ (b ⁻¹ᵁ W))) =
      p ⁻¹ᵁ (U.ι ''ᵁ (U.ι ⁻¹ᵁ (s ⁻¹ᵁ W))) := by
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  change p ⁻¹ᵁ U ⊓ ((g ≫ b) ⁻¹ᵁ W) = p ⁻¹ᵁ U ⊓ ((p ≫ s) ⁻¹ᵁ W)
  rw [w]

set_option backward.isDefEq.respectTransparency false in
/-- The square acts on sections by the induced equality of open subsets. -/
lemma relativeOpenPushforwardSquare_hom_app_app (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U : X.Opens) (N : Y.Modules) (W : S.Opens) :
    ((relativeOpenPushforwardSquare s b p g w U).hom.app N).app W =
      N.presheaf.map (eqToHom (relativeOpenSquare_image_eq s b p g w U W)).op := by
  simp only [relativeOpenPushforwardSquare, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Hom.comp_app,
    pushforward_map_app, Functor.comp_map, pushforwardComp_hom_app_app,
    pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app,
    modulePushforwardOpenRestrictIso_hom_app, Iso.symm_hom]
  simp only [Functor.comp_obj, pushforward_obj_obj, restrict_obj, Category.comp_id,
    Category.id_comp]
  rw [Scheme.Modules.restrict_map, ← Functor.map_comp]
  congr 1
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The square commutes with the adjunction units for restriction to an open. -/
lemma relativeOpenPushforwardSquare_unit (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U : X.Opens) (N : Y.Modules) :
    (pushforward s).map ((restrictAdjunction U.ι).unit.app ((pushforward p).obj N)) ≫
      (relativeOpenPushforwardSquare s b p g w U).hom.app N =
    (modulePushforwardSquare s b p g w).hom.app N ≫
      (pushforward b).map
        ((pushforward g).map ((restrictAdjunction (p ⁻¹ᵁ U).ι).unit.app N)) := by
  ext W m
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    relativeOpenPushforwardSquare_hom_app_app, modulePushforwardSquare,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app, pushforward_obj_presheaf_map,
    ConcreteCategory.comp_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2
  erw [Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The square commutes with restriction from an open to a smaller open. -/
lemma relativeOpenPushforwardSquare_restriction (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) {U V : X.Opens} (h : V ≤ U) (N : Y.Modules) :
    (pushforward s).map (openRestrictionMap ((pushforward p).obj N) h) ≫
      (relativeOpenPushforwardSquare s b p g w V).hom.app N =
    (relativeOpenPushforwardSquare s b p g w U).hom.app N ≫
      (pushforward b).map ((pushforward g).map
        (openRestrictionMap N ((TopologicalSpace.Opens.map p.base).monotone h))) := by
  ext W m
  simp only [Hom.comp_app, pushforward_map_app, openRestrictionMap_app_eq,
    relativeOpenPushforwardSquare_hom_app_app, pushforward_obj_presheaf_map,
    ConcreteCategory.comp_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2
end GromovWitten.AlgebraicGeometry.Curves
