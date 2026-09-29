/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenSectionsUnit

/-!
# Naturality of open-section base change

The restriction-pullback comparison is compatible with the two adjunction units appearing in
the Cartesian square.  This identity is the categorical input for the pointwise generator
formula of the open-section base-change map.
-/

open CategoryTheory AlgebraicGeometry Opposite
open TensorProduct
open scoped ChangeOfRings
open Scheme.Modules

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X Y : Scheme.{u}}
variable {R T : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The restriction-pullback comparison transports the double pullback unit. -/
lemma restrictionPullback_unit_formula (p : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ((pullbackPushforwardAdjunction p).comp
        (pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι)).unit.app M ≫
      (modulePushforwardSquare p U.ι (p ⁻¹ᵁ U).ι (p ∣_ U)
        (morphismRestrict_ι p U).symm).hom.app
          ((pullback (p ⁻¹ᵁ U).ι).obj ((pullback p).obj M)) =
    ((pullbackPushforwardAdjunction U.ι).comp
        (pullbackPushforwardAdjunction (p ∣_ U))).unit.app M ≫
      (pushforward (p ∣_ U) ⋙ pushforward U.ι).map (restrictionPullbackIso p M U).hom := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction p).comp
      (pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι))
    ((pullbackPushforwardAdjunction U.ι).comp
      (pullbackPushforwardAdjunction (p ∣_ U)))
    ((pullbackComp (p ∣_ U) U.ι).hom ≫
      (pullbackCongr (morphismRestrict_ι p U)).hom ≫
      (pullbackComp (p ⁻¹ᵁ U).ι p).inv) M
  rw [modulePullbackSquare_conjugate p U.ι (p ⁻¹ᵁ U).ι (p ∣_ U)
    (morphismRestrict_ι p U).symm] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The restriction-pullback comparison identifies the two pointwise adjunction units. -/
lemma restrictionPullback_unit_app (p : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) :
    ((restrictionPullbackIso p M U).hom).app ⊤
      (((pullbackPushforwardAdjunction (p ∣_ U)).unit.app ((pullback U.ι).obj M)).app ⊤
        (((pullback U.ι).obj M).presheaf.map (eqToHom U.ι_preimage_self.symm).op
          (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m))) =
    ((pullback (p ⁻¹ᵁ U).ι).obj ((pullback p).obj M)).presheaf.map
      (eqToHom (p ⁻¹ᵁ U).ι_preimage_self.symm).op
        (((pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι).unit.app ((pullback p).obj M)).app
          (p ⁻¹ᵁ U) (((pullbackPushforwardAdjunction p).unit.app M).app U m)) := by
  have h := restrictionPullback_unit_formula p M U
  simp only [Adjunction.comp_unit_app] at h
  have hx := ConcreteCategory.congr_hom (congrArg (fun k => k.app U) h) m
  simp only [Hom.comp_app, pushforward_map_app, Functor.comp_map,
    ConcreteCategory.comp_apply] at hx
  let A := (pullback U.ι).obj M
  let B := (pullback (p ∣_ U)).obj A
  let C := (pullback (p ⁻¹ᵁ U).ι).obj ((pullback p).obj M)
  let η := (pullbackPushforwardAdjunction (p ∣_ U)).unit.app A
  let e := (restrictionPullbackIso p M U).hom
  let i : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ U :=
    eqToHom U.ι_preimage_self.symm
  let j := (TopologicalSpace.Opens.map (p ∣_ U).base).map i
  have hnη := η.mapPresheaf.naturality i.op
  have hne := e.mapPresheaf.naturality j.op
  change A.presheaf.map i.op ≫ η.app ⊤ =
    η.app (U.ι ⁻¹ᵁ U) ≫ B.presheaf.map j.op at hnη
  change B.presheaf.map j.op ≫ e.app ⊤ =
    e.app ((p ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U) ≫ C.presheaf.map j.op at hne
  have ht : A.presheaf.map i.op ≫ η.app ⊤ ≫ e.app ⊤ =
      η.app (U.ι ⁻¹ᵁ U) ≫ e.app ((p ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U) ≫
        C.presheaf.map j.op := by
    rw [← Category.assoc, hnη, Category.assoc, hne]
  have ht' := ConcreteCategory.congr_hom ht
    (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m)
  change e.app ⊤ (η.app ⊤ (A.presheaf.map i.op
    (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m))) =
      C.presheaf.map j.op (e.app ((p ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U)
        (η.app (U.ι ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m))) at ht'
  change e.app ⊤ (η.app ⊤ (A.presheaf.map i.op
    (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m))) = _
  have hx' : e.app ((p ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U)
      (η.app (U.ι ⁻¹ᵁ U) (((pullbackPushforwardAdjunction U.ι).unit.app M).app U m)) =
      ((modulePushforwardSquare p U.ι (p ⁻¹ᵁ U).ι (p ∣_ U)
        (morphismRestrict_ι p U).symm).hom.app C).app U
        (((pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι).unit.app ((pullback p).obj M)).app
          (p ⁻¹ᵁ U) (((pullbackPushforwardAdjunction p).unit.app M).app U m)) := hx.symm
  rw [ht', hx']
  simp only [modulePushforwardSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Hom.comp_app, ConcreteCategory.comp_apply, pushforwardComp_hom_app_app,
    pushforwardComp_inv_app_app, pushforwardCongr_inv_app_app]
  let k : (p ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U ⟶ (p ⁻¹ᵁ U).ι ⁻¹ᵁ p ⁻¹ᵁ U :=
    eqToHom (congrArg (fun q => q ⁻¹ᵁ U) (morphismRestrict_ι p U))
  let z : Γ(C, (p ⁻¹ᵁ U).ι ⁻¹ᵁ p ⁻¹ᵁ U) :=
    ((pullbackPushforwardAdjunction (p ⁻¹ᵁ U).ι).unit.app ((pullback p).obj M)).app
      (p ⁻¹ᵁ U) (((pullbackPushforwardAdjunction p).unit.app M).app U m)
  change C.presheaf.map j.op (C.presheaf.map k.op z) =
    C.presheaf.map (eqToHom (p ⁻¹ᵁ U).ι_preimage_self.symm).op z
  have hmaps : C.presheaf.map k.op ≫ C.presheaf.map j.op =
      C.presheaf.map (eqToHom (p ⁻¹ᵁ U).ι_preimage_self.symm).op := by
    rw [← Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hmaps z

set_option backward.isDefEq.respectTransparency false in
/-- The open-section base-change map sends the tensor generator to the pullback unit. -/
lemma openSectionsBaseChangeMap_one_tmul (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) (U : X.Opens) (m : baseSectionModule s U M) :
    openSectionsBaseChangeMap s φ p g h M U ((1 : T) ⊗ₜ[R, φ.hom] m) =
      ((pullbackPushforwardAdjunction p).unit.app M).app U (show Γ(M, U) from m) := by
  simp only [openSectionsBaseChangeMap, ConcreteCategory.comp_apply]
  rw [ModuleCat.ExtendScalars.map_tmul, sectionsBaseChangeMap_one_tmul]
  change (openSectionsOverBaseIso g ((pullback p).obj M) (p ⁻¹ᵁ U)).hom
    (((restrictionPullbackIso p M U).hom).app ⊤
      (((pullbackPushforwardAdjunction (p ∣_ U)).unit.app ((pullback U.ι).obj M)).app ⊤
        ((openSectionsOverBaseIso s M U).inv m))) = _
  rw [openSectionsOverBaseIso_inv, restrictionPullback_unit_app, openSectionsOverBaseIso_unit]

set_option backward.isDefEq.respectTransparency false in
/-- The open-section base-change map commutes with restriction of sections. -/
lemma openSectionsBaseChangeMap_restriction (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    (ModuleCat.extendScalars φ.hom).map (baseSectionRestrictionMap s M i) ≫
      openSectionsBaseChangeMap s φ p g h M V =
    openSectionsBaseChangeMap s φ p g h M U ≫
      baseSectionRestrictionMap g ((pullback p).obj M)
        ((TopologicalSpace.Opens.map p.base).map i) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  simp only [ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  rw [openSectionsBaseChangeMap_one_tmul, openSectionsBaseChangeMap_one_tmul]
  exact ConcreteCategory.congr_hom
    (((pullbackPushforwardAdjunction p).unit.app M).mapPresheaf.naturality i.op) m

end GromovWitten.AlgebraicGeometry.Curves
