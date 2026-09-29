/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenBaseChange
import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves

/-!
# Base change for relative two-open Čech pairs

The two-open Čech pair base-change map is assembled from the corresponding
maps for the two open pieces.  The projection formulas expose its two
components for later compatibility arguments.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The relative Čech pair base-change map, assembled from the two open pieces. -/
def relativeCechPairBaseChangeNatTrans (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U V : X.Opens) :
    relativeCechPairFunctor s U V ⋙ Scheme.Modules.pullback b ⟶
      Scheme.Modules.pullback p ⋙ relativeCechPairFunctor g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) where
  app M := prod.lift
    ((Scheme.Modules.pullback b).map prod.fst ≫
      (relativeOpenBaseChangeNatTrans s b p g w U).app M)
    ((Scheme.Modules.pullback b).map prod.snd ≫
      (relativeOpenBaseChangeNatTrans s b p g w V).app M)
  naturality M N f := by
    apply prod.hom_ext
    · simp only [relativeCechPairFunctor, Functor.comp_map, prod.lift_fst,
        prod.lift_fst_assoc, prod.map_fst, Category.assoc]
      rw [← Category.assoc, ← (Scheme.Modules.pullback b).map_comp]
      simp only [prod.map_fst, Functor.map_comp]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun t => (Scheme.Modules.pullback b).map prod.fst ≫ t)
          ((relativeOpenBaseChangeNatTrans s b p g w U).naturality f)
    · simp only [relativeCechPairFunctor, Functor.comp_map, prod.lift_snd,
        prod.lift_snd_assoc, prod.map_snd, Category.assoc]
      rw [← Category.assoc, ← (Scheme.Modules.pullback b).map_comp]
      simp only [prod.map_snd, Functor.map_comp]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun t => (Scheme.Modules.pullback b).map prod.snd ≫ t)
          ((relativeOpenBaseChangeNatTrans s b p g w V).naturality f)

set_option backward.isDefEq.respectTransparency false in
/-- Projection to the first open piece commutes with pair base change. -/
@[reassoc (attr := simp)]
lemma relativeCechPairBaseChangeNatTrans_fst (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U V : X.Opens)
    (M : X.Modules) :
    (relativeCechPairBaseChangeNatTrans s b p g w U V).app M ≫ prod.fst =
      (Scheme.Modules.pullback b).map prod.fst ≫
        (relativeOpenBaseChangeNatTrans s b p g w U).app M := by
  simp only [relativeCechPairBaseChangeNatTrans, prod.lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- Projection to the second open piece commutes with pair base change. -/
@[reassoc (attr := simp)]
lemma relativeCechPairBaseChangeNatTrans_snd (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U V : X.Opens)
    (M : X.Modules) :
    (relativeCechPairBaseChangeNatTrans s b p g w U V).app M ≫ prod.snd =
      (Scheme.Modules.pullback b).map prod.snd ≫
        (relativeOpenBaseChangeNatTrans s b p g w V).app M := by
  simp only [relativeCechPairBaseChangeNatTrans, prod.lift_snd]

set_option backward.isDefEq.respectTransparency false in
/-- The pair base-change map is invertible when both branch maps are invertible. -/
lemma relativeCechPairBaseChangeNatTrans_isIso (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U V : X.Opens)
    (M : X.Modules)
    [IsIso ((relativeOpenBaseChangeNatTrans s b p g w U).app M)]
    [IsIso ((relativeOpenBaseChangeNatTrans s b p g w V).app M)] :
    IsIso ((relativeCechPairBaseChangeNatTrans s b p g w U V).app M) := by
  let A := (relativeOpenPushforward s U).obj M
  let B := (relativeOpenPushforward s V).obj M
  let F := Scheme.Modules.pullback b
  let _ : PreservesLimit (pair A B) F := by infer_instance
  change IsIso (prod.lift
    ((Scheme.Modules.pullback b).map prod.fst ≫
      (relativeOpenBaseChangeNatTrans s b p g w U).app M)
    ((Scheme.Modules.pullback b).map prod.snd ≫
      (relativeOpenBaseChangeNatTrans s b p g w V).app M))
  have hfactor : prod.lift
      ((Scheme.Modules.pullback b).map prod.fst ≫
        (relativeOpenBaseChangeNatTrans s b p g w U).app M)
      ((Scheme.Modules.pullback b).map prod.snd ≫
        (relativeOpenBaseChangeNatTrans s b p g w V).app M) =
      prodComparison F A B ≫ prod.map
        ((relativeOpenBaseChangeNatTrans s b p g w U).app M)
        ((relativeOpenBaseChangeNatTrans s b p g w V).app M) := by
    apply prod.hom_ext
    · rw [prod.lift_fst]
      rw [Category.assoc, prod.map_fst, prodComparison_fst_assoc]
    · rw [prod.lift_snd]
      rw [Category.assoc, prod.map_snd, prodComparison_snd_assoc]
  rw [hfactor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Base change commutes with the Čech restriction map to the pair. -/
lemma relativeCechToPair_baseChange (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (h : IsPullback p g s b) (U V : X.Opens) (M : X.Modules) :
    (modulePushforwardBaseChangeNatTrans s b p g h).app M ≫
        relativeCechToPair g ((Scheme.Modules.pullback p).obj M)
          (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
      (Scheme.Modules.pullback b).map (relativeCechToPair s M U V) ≫
        (relativeCechPairBaseChangeNatTrans s b p g h.w U V).app M := by
  dsimp only [relativeCechPairFunctor]
  apply prod.hom_ext
  · simp only [relativeCechToPair, prod.lift_fst, Category.assoc]
    rw [relativeCechPairBaseChangeNatTrans_fst]
    rw [← Category.assoc, ← Functor.map_comp, prod.lift_fst]
    rw [← relativeOpenBaseChangeNatTrans_unit s b p g h U M]
  · simp only [relativeCechToPair, prod.lift_snd, Category.assoc]
    rw [relativeCechPairBaseChangeNatTrans_snd]
    rw [← Category.assoc, ← Functor.map_comp, prod.lift_snd]
    rw [← relativeOpenBaseChangeNatTrans_unit s b p g h V M]

set_option backward.isDefEq.respectTransparency false in
/-- Base change commutes with the Čech pair differential. -/
lemma relativeCechFromPair_baseChange (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X)
    (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U V : X.Opens) (M : X.Modules) :
    (relativeCechPairBaseChangeNatTrans s b p g w U V).app M ≫
        relativeCechFromPair g ((Scheme.Modules.pullback p).obj M)
          (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
      (Scheme.Modules.pullback b).map (relativeCechFromPair s M U V) ≫
        (relativeOpenBaseChangeNatTrans s b p g w (U ⊓ V)).app M := by
  dsimp only [relativeCechPairBaseChangeNatTrans, relativeCechPairFunctor]
  simp only [relativeCechFromPair, Preadditive.comp_sub, ← Category.assoc]
  erw [prod.lift_fst, prod.lift_snd]
  rw [Category.assoc]
  rw [← relativeOpenBaseChangeNatTrans_restriction s b p g w
      (inf_le_left : U ⊓ V ≤ U) M]
  rw [Category.assoc]
  rw [← relativeOpenBaseChangeNatTrans_restriction s b p g w
      (inf_le_right : U ⊓ V ≤ V) M]
  simp only [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp,
    Category.assoc]
  rfl

end GromovWitten.AlgebraicGeometry.Curves
