/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeOpenComplexBaseChange
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechBaseChange

/-!
# Relative Čech pair-complex base change

This file constructs the base-change map for the two-open Čech pair complex,
identifies its two projection components with the corresponding open-complex
maps, and lifts quasi-isomorphisms from the two opens to the pair complex.
-/

open CategoryTheory Limits AlgebraicGeometry HomologicalComplex
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The base-change morphism between the old and new two-open Čech pair
complexes, induced by the relative pair base-change transformation and a
cochain map on the coefficients. -/
def relativeCechPairComplexBaseChangeMap
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (w : p ≫ s = g ≫ b)
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (U V : X.Opens) :
    ((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℕ)).obj
      (((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K) ⟶
      ((relativeCechPairFunctor g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)).mapHomologicalComplex (.up ℕ)).obj J := by
  let F := Scheme.Modules.pullback b
  let L := Scheme.Modules.pullback p
  let Q := relativeCechPairFunctor s U V
  let P := relativeCechPairFunctor g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V)
  let a : (F.mapHomologicalComplex (.up ℕ)).obj
      ((Q.mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (P.mapHomologicalComplex (.up ℕ)).obj ((L.mapHomologicalComplex (.up ℕ)).obj K) :=
    (NatTrans.mapHomologicalComplex (relativeCechPairBaseChangeNatTrans s b p g w U V)
      (.up ℕ)).app K
  exact a ≫ (P.mapHomologicalComplex (.up ℕ)).map φ

set_option backward.isDefEq.respectTransparency false in
/-- The pair-complex base-change map followed by projection to `U` agrees
with the open-complex base-change map on `U`. -/
lemma relativeCechPairComplexBaseChangeMap_fst
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (w : p ≫ s = g ≫ b)
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (U V : X.Opens) :
    relativeCechPairComplexBaseChangeMap s b p g w φ U V ≫
        relativeCechPairProjectionU g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) J =
      ((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℕ)).map
          (relativeCechPairProjectionU s U V K) ≫
        relativeOpenComplexBaseChangeMap s b p g w φ U := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((relativeCechPairBaseChangeNatTrans s b p g w U V).app (K.X n) ≫
      prod.map ((relativeOpenPushforward g (p ⁻¹ᵁ U)).map (φ.f n))
        ((relativeOpenPushforward g (p ⁻¹ᵁ V)).map (φ.f n))) ≫ prod.fst =
    (Scheme.Modules.pullback b).map prod.fst ≫
      ((relativeOpenBaseChangeNatTrans s b p g w U).app (K.X n) ≫
        (relativeOpenPushforward g (p ⁻¹ᵁ U)).map (φ.f n))
  rw [Category.assoc, prod.map_fst, ← Category.assoc,
    relativeCechPairBaseChangeNatTrans_fst, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The pair-complex base-change map followed by projection to `V` agrees
with the open-complex base-change map on `V`. -/
lemma relativeCechPairComplexBaseChangeMap_snd
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (w : p ≫ s = g ≫ b)
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (U V : X.Opens) :
    relativeCechPairComplexBaseChangeMap s b p g w φ U V ≫
        relativeCechPairProjectionV g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) J =
      ((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℕ)).map
          (relativeCechPairProjectionV s U V K) ≫
        relativeOpenComplexBaseChangeMap s b p g w φ V := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ((relativeCechPairBaseChangeNatTrans s b p g w U V).app (K.X n) ≫
      prod.map ((relativeOpenPushforward g (p ⁻¹ᵁ U)).map (φ.f n))
        ((relativeOpenPushforward g (p ⁻¹ᵁ V)).map (φ.f n))) ≫ prod.snd =
    (Scheme.Modules.pullback b).map prod.snd ≫
      ((relativeOpenBaseChangeNatTrans s b p g w V).app (K.X n) ≫
        (relativeOpenPushforward g (p ⁻¹ᵁ V)).map (φ.f n))
  rw [Category.assoc, prod.map_snd, ← Category.assoc,
    relativeCechPairBaseChangeNatTrans_snd, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- If the open-complex base-change maps on `U` and `V` are
quasi-isomorphisms, then so is the induced map on their Čech pair complex. -/
lemma relativeCechPairComplexBaseChangeMap_quasiIso
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (w : p ≫ s = g ≫ b)
    {K : CochainComplex X.Modules ℕ} {J : CochainComplex Y.Modules ℕ}
    (φ : ((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K ⟶ J)
    (U V : X.Opens)
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g w φ U)]
    [QuasiIso (relativeOpenComplexBaseChangeMap s b p g w φ V)] :
    QuasiIso (relativeCechPairComplexBaseChangeMap s b p g w φ U V) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor T.Modules (.up ℕ) n
  let F := (Scheme.Modules.pullback b).mapHomologicalComplex (.up ℕ)
  let G := F ⋙ H
  let eS := relativeCechPair_mapProdIso s U V K G
  let eT := relativeCechPair_mapProdIso g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) J H
  let β := relativeCechPairComplexBaseChangeMap s b p g w φ U V
  let βU := relativeOpenComplexBaseChangeMap s b p g w φ U
  let βV := relativeOpenComplexBaseChangeMap s b p g w φ V
  have hfst : H.map β ≫ eT.hom ≫ prod.fst = eS.hom ≫ prod.fst ≫ H.map βU := by
    rw [relativeCechPair_mapProdIso_hom_fst, ← H.map_comp,
      relativeCechPairComplexBaseChangeMap_fst, H.map_comp]
    rw [← Category.assoc, relativeCechPair_mapProdIso_hom_fst]
    rfl
  have hsnd : H.map β ≫ eT.hom ≫ prod.snd = eS.hom ≫ prod.snd ≫ H.map βV := by
    rw [relativeCechPair_mapProdIso_hom_snd, ← H.map_comp,
      relativeCechPairComplexBaseChangeMap_snd, H.map_comp]
    rw [← Category.assoc, relativeCechPair_mapProdIso_hom_snd]
    rfl
  have heq : eS.inv ≫ H.map β ≫ eT.hom = prod.map (H.map βU) (H.map βV) := by
    apply prod.hom_ext
    · apply (cancel_epi eS.hom).mp
      simp only [Category.assoc, Iso.hom_inv_id_assoc, prod.map_fst]
      exact hfst
    · apply (cancel_epi eS.hom).mp
      simp only [Category.assoc, Iso.hom_inv_id_assoc, prod.map_snd]
      exact hsnd
  have hU : IsIso (H.map βU) := by
    change IsIso (homologyMap βU n)
    infer_instance
  have hV : IsIso (H.map βV) := by
    change IsIso (homologyMap βV n)
    infer_instance
  have hβ : IsIso (eS.inv ≫ H.map β ≫ eT.hom) := by rw [heq]; infer_instance
  have : IsIso (H.map β ≫ eT.hom) := IsIso.of_isIso_comp_left eS.inv _
  exact IsIso.of_isIso_comp_right (H.map β) eT.hom
end GromovWitten.AlgebraicGeometry.Curves
