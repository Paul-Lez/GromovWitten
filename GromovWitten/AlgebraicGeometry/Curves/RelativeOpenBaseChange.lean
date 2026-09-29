/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenPushforwardSquare

/-!
# Relative open base change

This file packages the mate of the canonical relative pushforward square as a
base-change natural transformation.  It records its adjunction characteristic
equation, compatibility with the canonical unit under a pullback square, and
compatibility with restriction to smaller opens.
-/

open CategoryTheory Limits AlgebraicGeometry Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The relative open base-change map obtained as the mate of the pushforward square. -/
def relativeOpenBaseChangeNatTrans (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U : X.Opens) :
    relativeOpenPushforward s U ⋙ pullback b ⟶
      pullback p ⋙ relativeOpenPushforward g (p ⁻¹ᵁ U) where
  app M := ((pullbackPushforwardAdjunction b).homEquiv _ _).symm
    ((relativeOpenPushforward s U).map ((pullbackPushforwardAdjunction p).unit.app M) ≫
      (relativeOpenPushforwardSquare s b p g w U).hom.app
        ((Scheme.Modules.pullback p).obj M))
  naturality M N f := by
    apply (pullbackPushforwardAdjunction b).homEquiv_naturality_right_square
    simp only [Category.assoc]
    rw [← Category.assoc, ← (relativeOpenPushforward s U).map_comp]
    have hη := (pullbackPushforwardAdjunction p).unit.naturality f
    simp only [Functor.id_map] at hη
    rw [hη]
    rw [Functor.map_comp]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun t => (relativeOpenPushforward s U).map
        ((pullbackPushforwardAdjunction p).unit.app M) ≫ t)
        ((relativeOpenPushforwardSquare s b p g w U).hom.naturality
          ((Scheme.Modules.pullback p).map f))

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction mate of `relativeOpenBaseChangeNatTrans` is its defining square map. -/
lemma relativeOpenBaseChangeNatTrans_homEquiv (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U : X.Opens)
    (M : X.Modules) :
    (pullbackPushforwardAdjunction b).homEquiv _ _
        ((relativeOpenBaseChangeNatTrans s b p g w U).app M) =
      (relativeOpenPushforward s U).map
          ((pullbackPushforwardAdjunction p).unit.app M) ≫
        (relativeOpenPushforwardSquare s b p g w U).hom.app
        ((Scheme.Modules.pullback p).obj M) := by
  exact Equiv.apply_symm_apply _ _

/- The remaining statements use the same namespace and the canonical square APIs. -/

set_option backward.isDefEq.respectTransparency false in
/-- The mate agrees with the canonical base-change map on the Čech section unit. -/
lemma relativeOpenBaseChangeNatTrans_unit (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (h : IsPullback p g s b) (U : X.Opens) (M : X.Modules) :
    (Scheme.Modules.pullback b).map
        ((pushforward s).map ((restrictAdjunction U.ι).unit.app M)) ≫
      (relativeOpenBaseChangeNatTrans s b p g h.w U).app M =
    (modulePushforwardBaseChangeNatTrans s b p g h).app M ≫
      (pushforward g).map
        ((restrictAdjunction (p ⁻¹ᵁ U).ι).unit.app ((Scheme.Modules.pullback p).obj M)) := by
  let N := (Scheme.Modules.pullback p).obj M
  let η := (pullbackPushforwardAdjunction p).unit.app M
  have hn : (pushforward s).map ((restrictAdjunction U.ι).unit.app M) ≫
      (relativeOpenPushforward s U).map η =
    (pushforward s).map η ≫
      (pushforward s).map ((restrictAdjunction U.ι).unit.app ((pushforward p).obj N)) := by
    simpa only [Functor.map_comp, Functor.comp_map, Functor.id_map, Functor.id_obj,
      Functor.comp_obj, N, relativeOpenPushforward] using
      (congrArg (pushforward s).map ((restrictAdjunction U.ι).unit.naturality η)).symm
  apply ((pullbackPushforwardAdjunction b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [relativeOpenBaseChangeNatTrans_homEquiv s b p g h.w U M,
    moduleBaseChange_unit_formula s b p g h M]
  rw [← Category.assoc, hn, Category.assoc, relativeOpenPushforwardSquare_unit]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The relative open base-change map commutes with restriction to a smaller open. -/
lemma relativeOpenBaseChangeNatTrans_restriction (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) {U V : X.Opens} (h : V ≤ U) (M : X.Modules) :
    (Scheme.Modules.pullback b).map ((pushforward s).map (openRestrictionMap M h)) ≫
      (relativeOpenBaseChangeNatTrans s b p g w V).app M =
    (relativeOpenBaseChangeNatTrans s b p g w U).app M ≫
      (pushforward g).map (openRestrictionMap ((Scheme.Modules.pullback p).obj M)
        ((TopologicalSpace.Opens.map p.base).monotone h)) := by
  let N := (Scheme.Modules.pullback p).obj M
  let η := (pullbackPushforwardAdjunction p).unit.app M
  have hn : (pushforward s).map (openRestrictionMap M h) ≫
      (relativeOpenPushforward s V).map η =
    (relativeOpenPushforward s U).map η ≫
      (pushforward s).map (openRestrictionMap ((pushforward p).obj N) h) := by
    simpa only [Functor.map_comp, Functor.comp_map, relativeOpenPushforward] using
      (congrArg (pushforward s).map
        (openRestrictionMap_naturality M ((pushforward p).obj N) η h)).symm
  apply ((pullbackPushforwardAdjunction b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [relativeOpenBaseChangeNatTrans_homEquiv s b p g w V M,
    relativeOpenBaseChangeNatTrans_homEquiv s b p g w U M]
  rw [← Category.assoc, hn, Category.assoc, relativeOpenPushforwardSquare_restriction]
  simp only [Category.assoc]
  rfl
end GromovWitten.AlgebraicGeometry.Curves
