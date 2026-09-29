/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechDerived
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChange
import GromovWitten.CategoryTheory.HomologySequenceFunctor

/-!
# Connecting maps for relative Čech base change

The degree-one connecting map of the relative Čech Mayer--Vietoris sequence
commutes with the canonical base-change map after choosing compatible injective
resolutions.  This is the connecting-map component used separately in the
comparison with the cokernel model.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech connecting morphism is compatible with canonical base
change for a Cartesian square and compatible injective resolutions. -/
lemma relativeCechConnecting_baseChange
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (h : IsPullback p g s b)
    [(Scheme.Modules.pullback b).PreservesHomology]
    [(Scheme.Modules.pullback p).PreservesHomology]
    (M : X.Modules) (U V : X.Opens)
    (hS : (relativeCechComplexMV (injectiveResolution M).cocomplex s U V).ShortExact)
    (hT : (relativeCechComplexMV
      (injectiveResolution ((Scheme.Modules.pullback p).obj M)).cocomplex
      g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).ShortExact)
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj
        (injectiveResolution M).cocomplex ⟶
      (injectiveResolution ((Scheme.Modules.pullback p).obj M)).cocomplex)
    (hφ : (singleMapHomologicalComplex (Scheme.Modules.pullback p) (.up ℕ) 0).inv.app M ≫
      ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).map
        (injectiveResolution M).ι ≫ φ =
      (injectiveResolution ((Scheme.Modules.pullback p).obj M)).ι) :
    (Scheme.Modules.pullback b).map
        ((relativeOpenPushforward s (U ⊓ V)).toRightDerivedZero.app M ≫
          ((injectiveResolution M).isoRightDerivedObj
            (relativeOpenPushforward s (U ⊓ V)) 0).hom ≫ hS.δ 0 1 rfl ≫
          ((injectiveResolution M).isoRightDerivedObj (pushforward s) 1).inv) ≫
      (moduleHigherBaseChangeNatTrans s b p g h 1).app M =
    (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M ≫
      (relativeOpenPushforward g (p ⁻¹ᵁ (U ⊓ V))).toRightDerivedZero.app
        ((Scheme.Modules.pullback p).obj M) ≫
      ((injectiveResolution ((Scheme.Modules.pullback p).obj M)).isoRightDerivedObj
        (relativeOpenPushforward g (p ⁻¹ᵁ (U ⊓ V))) 0).hom ≫ hT.δ 0 1 rfl ≫
      ((injectiveResolution ((Scheme.Modules.pullback p).obj M)).isoRightDerivedObj
        (pushforward g) 1).inv := by
  let F := Scheme.Modules.pullback b
  let L := Scheme.Modules.pullback p
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let CS := relativeCechComplexMV I.cocomplex s U V
  let CT := relativeCechComplexMV J.cocomplex g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  let hSF := hS.map_of_exact (F.mapHomologicalComplex (.up ℕ))
  let Φ : CS.map (F.mapHomologicalComplex (.up ℕ)) ⟶ CT :=
    relativeCechComplexBaseChange I.cocomplex s b p g h U V ≫
      relativeCechComplexMVMap φ g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  let e₁ := (CS.X₁.sc 1).mapHomologyIso F
  let e₃ := (CS.X₃.sc 0).mapHomologyIso F
  let zS := (relativeOpenPushforward s (U ⊓ V)).toRightDerivedZero.app M ≫
    (I.isoRightDerivedObj (relativeOpenPushforward s (U ⊓ V)) 0).hom
  let zT := (relativeOpenPushforward g (p ⁻¹ᵁ (U ⊓ V))).toRightDerivedZero.app (L.obj M) ≫
    (J.isoRightDerivedObj (relativeOpenPushforward g (p ⁻¹ᵁ (U ⊓ V))) 0).hom
  have hz : F.map zS ≫ e₃.inv ≫ HomologicalComplex.homologyMap Φ.τ₃ 0 =
      (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M ≫ zT := by
    simpa only [F, L, I, J, zS, zT, e₃, CS, CT, relativeCechComplexMV,
      Φ, ShortComplex.comp_τ₃, relativeCechComplexBaseChange,
      relativeCechComplexMVMap, homologyMap_comp, Scheme.Hom.preimage_inf, Category.assoc] using
      NatTrans.rightDerivedBaseChange_zero_resolution_comp
        (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)) M φ hφ
  have hd : F.map (hS.δ 0 1 rfl) ≫ e₁.inv = e₃.inv ≫ hSF.δ 0 1 rfl :=
    HomologicalComplex.HomologySequence.map_δ_inv F hS hSF 0 1 rfl
  have hn := HomologicalComplex.HomologySequence.δ_naturality Φ hSF hT 0 1 rfl
  have hb : (moduleHigherBaseChangeNatTrans s b p g h 1).app M =
      F.map (I.isoRightDerivedObj (pushforward s) 1).hom ≫ e₁.inv ≫
        HomologicalComplex.homologyMap Φ.τ₁ 1 ≫
          (J.isoRightDerivedObj (pushforward g) 1).inv := by
    simpa only [F, L, I, J, e₁, CS, relativeCechComplexMV, moduleHigherBaseChangeNatTrans,
      Φ, ShortComplex.comp_τ₁, relativeCechComplexBaseChange,
      relativeCechComplexMVMap, homologyMap_comp, Category.assoc] using
      NatTrans.rightDerivedBaseChange_app_eq_homologyMap
        (modulePushforwardBaseChangeNatTrans s b p g h) M 1 φ hφ
  change F.map (zS ≫ hS.δ 0 1 rfl ≫ (I.isoRightDerivedObj (pushforward s) 1).inv) ≫
      (moduleHigherBaseChangeNatTrans s b p g h 1).app M =
    (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app M ≫
      zT ≫ hT.δ 0 1 rfl ≫ (J.isoRightDerivedObj (pushforward g) 1).inv
  rw [hb]
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  calc
    _ = F.map zS ≫ e₃.inv ≫ hSF.δ 0 1 rfl ≫
        HomologicalComplex.homologyMap Φ.τ₁ 1 ≫
          (J.isoRightDerivedObj (pushforward g) 1).inv := by
      simpa only [Category.assoc] using congrArg
        (fun t => F.map zS ≫ t ≫ HomologicalComplex.homologyMap Φ.τ₁ 1 ≫
          (J.isoRightDerivedObj (pushforward g) 1).inv) hd
    _ = F.map zS ≫ e₃.inv ≫ HomologicalComplex.homologyMap Φ.τ₃ 0 ≫
        hT.δ 0 1 rfl ≫ (J.isoRightDerivedObj (pushforward g) 1).inv := by
      simpa only [Category.assoc] using congrArg
        (fun t => F.map zS ≫ e₃.inv ≫ t ≫
          (J.isoRightDerivedObj (pushforward g) 1).inv) hn
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ hT.δ 0 1 rfl ≫
          (J.isoRightDerivedObj (pushforward g) 1).inv) hz

end GromovWitten.AlgebraicGeometry.Curves
