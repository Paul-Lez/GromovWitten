/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves
import GromovWitten.AlgebraicGeometry.Curves.DerivedOpenPushforward
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentProducts
import Mathlib.Algebra.Homology.Additive

/-!
# Homology, product comparison, and acyclicity of the relative two-open Čech pair

The homology of the pair term is canonically the product of the homologies of the two
open-piece complexes, and an additive functor sends the pair complex to the product of its
two factors.  The resulting homology is quasicoherent when both factors are.  In particular,
the pair term is homologically zero whenever both open-piece complexes are homologically
zero.  Affine open composites provide the corresponding right-derived vanishing in positive
degrees.
-/

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
open CochainComplex
noncomputable section
universe u v w

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S : Scheme.{u}}

private abbrev openComplex (s : X ⟶ S) (W : X.Opens)
    (K : CochainComplex X.Modules ℕ) : CochainComplex S.Modules ℕ :=
  ((relativeOpenPushforward s W).mapHomologicalComplex (.up ℕ)).obj K

private abbrev pairComplex (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) : CochainComplex S.Modules ℕ :=
  ((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K

/-- The projection from the pair complex to the first open-piece complex. -/
def relativeCechPairProjectionU (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) :
    (((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K) :=
  HomologicalComplex.Hom.mk (fun n => prod.fst) (by
    intro i j hij
    change prod.fst ≫ (relativeOpenPushforward s U).map (K.d i j) =
      prod.map ((relativeOpenPushforward s U).map (K.d i j))
        ((relativeOpenPushforward s V).map (K.d i j)) ≫ prod.fst
    rw [prod.map_fst])

/-- The projection from the pair complex to the second open-piece complex. -/
def relativeCechPairProjectionV (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) :
    (((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj K) :=
  HomologicalComplex.Hom.mk (fun n => prod.snd) (by
    intro i j hij
    change prod.snd ≫ (relativeOpenPushforward s V).map (K.d i j) =
      prod.map ((relativeOpenPushforward s U).map (K.d i j))
        ((relativeOpenPushforward s V).map (K.d i j)) ≫ prod.snd
    rw [prod.map_snd])

private def pairInclusionU (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) : openComplex s U K ⟶ pairComplex s U V K :=
  HomologicalComplex.Hom.mk (fun n => prod.lift (𝟙 _) 0) (by
    intro i j hij
    change prod.lift (𝟙 _) 0 ≫
        prod.map ((relativeOpenPushforward s U).map (K.d i j))
          ((relativeOpenPushforward s V).map (K.d i j)) =
      (relativeOpenPushforward s U).map (K.d i j) ≫ prod.lift (𝟙 _) 0
    rw [prod.lift_map]
    simp)

private def pairInclusionV (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) : openComplex s V K ⟶ pairComplex s U V K :=
  HomologicalComplex.Hom.mk (fun n => prod.lift 0 (𝟙 _)) (by
    intro i j hij
    change prod.lift 0 (𝟙 _) ≫
        prod.map ((relativeOpenPushforward s U).map (K.d i j))
          ((relativeOpenPushforward s V).map (K.d i j)) =
      (relativeOpenPushforward s V).map (K.d i j) ≫ prod.lift 0 (𝟙 _)
    rw [prod.lift_map]
    simp)

set_option backward.isDefEq.respectTransparency false in
private lemma pair_split (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ) :
    relativeCechPairProjectionU s U V K ≫ pairInclusionU s U V K +
      relativeCechPairProjectionV s U V K ≫ pairInclusionV s U V K = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply prod.hom_ext
  · change (prod.fst ≫ prod.lift (𝟙 _) 0 + prod.snd ≫ prod.lift 0 (𝟙 _)) ≫
      prod.fst = 𝟙 _ ≫ prod.fst
    rw [Preadditive.add_comp]
    simp
  · change (prod.fst ≫ prod.lift (𝟙 _) 0 + prod.snd ≫ prod.lift 0 (𝟙 _)) ≫
      prod.snd = 𝟙 _ ≫ prod.snd
    rw [Preadditive.add_comp]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor sends the pair complex to the product of its two factors. -/
noncomputable def relativeCechPair_mapProdIso
    {C : Type v} [Category.{w} C] [Preadditive C] [HasBinaryProducts C]
    (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ)
    (G : CochainComplex S.Modules ℕ ⥤ C) [G.Additive] :
    G.obj (((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K) ≅
      G.obj (((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K) ⨯
        G.obj (((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj K) := by
  let πU := G.map (relativeCechPairProjectionU s U V K)
  let πV := G.map (relativeCechPairProjectionV s U V K)
  let ιU := G.map (pairInclusionU s U V K)
  let ιV := G.map (pairInclusionV s U V K)
  refine
    { hom := prod.lift πU πV
      inv := prod.fst ≫ ιU + prod.snd ≫ ιV
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · have hs := congrArg G.map (pair_split s U V K)
    dsimp [πU, πV, ιU, ιV] at hs ⊢
    rw [Functor.map_add, Functor.map_comp, Functor.map_comp, G.map_id] at hs
    rw [← hs]
    simp
  · apply prod.hom_ext
    · dsimp [πU, πV, ιU, ιV]
      simp only [Preadditive.add_comp, Category.assoc, prod.lift_fst]
      have hUU : pairInclusionU s U V K ≫ relativeCechPairProjectionU s U V K = 𝟙 _ := by
        apply HomologicalComplex.Hom.ext
        funext m
        simp [pairInclusionU, relativeCechPairProjectionU]
      have hVU : pairInclusionV s U V K ≫ relativeCechPairProjectionU s U V K = 0 := by
        apply HomologicalComplex.Hom.ext
        funext m
        simp [pairInclusionV, relativeCechPairProjectionU]
      rw [← G.map_comp, ← G.map_comp, hUU, hVU]
      simp
    · dsimp [πU, πV, ιU, ιV]
      simp only [Preadditive.add_comp, Category.assoc, prod.lift_snd]
      have hUV : pairInclusionU s U V K ≫ relativeCechPairProjectionV s U V K = 0 := by
        apply HomologicalComplex.Hom.ext
        funext m
        simp [pairInclusionU, relativeCechPairProjectionV]
      have hVV : pairInclusionV s U V K ≫ relativeCechPairProjectionV s U V K = 𝟙 _ := by
        apply HomologicalComplex.Hom.ext
        funext m
        simp [pairInclusionV, relativeCechPairProjectionV]
      rw [← G.map_comp, ← G.map_comp, hUV, hVV]
      simp

set_option backward.isDefEq.respectTransparency false in
/-- The generic pair isomorphism has the expected first projection. -/
lemma relativeCechPair_mapProdIso_hom_fst
    {C : Type v} [Category.{w} C] [Preadditive C] [HasBinaryProducts C]
    (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ)
    (G : CochainComplex S.Modules ℕ ⥤ C) [G.Additive] :
    (relativeCechPair_mapProdIso s U V K G).hom ≫ prod.fst =
      G.map (relativeCechPairProjectionU s U V K) := by
  dsimp [relativeCechPair_mapProdIso]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The generic pair isomorphism has the expected second projection. -/
lemma relativeCechPair_mapProdIso_hom_snd
    {C : Type v} [Category.{w} C] [Preadditive C] [HasBinaryProducts C]
    (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ)
    (G : CochainComplex S.Modules ℕ ⥤ C) [G.Additive] :
    (relativeCechPair_mapProdIso s U V K G).hom ≫ prod.snd =
      G.map (relativeCechPairProjectionV s U V K) := by
  dsimp [relativeCechPair_mapProdIso]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Homology of the relative pair complex vanishes when both open pieces vanish. -/
lemma isZero_relativeCechPair_homology
    (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ) (n : ℕ)
    (hU : IsZero ((((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K).homology n))
    (hV : IsZero
      ((((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj K).homology n)) :
    IsZero
      ((((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K).homology n) := by
  rw [IsZero.iff_id_eq_zero]
  have hπU : HomologicalComplex.homologyMap (relativeCechPairProjectionU s U V K) n = 0 :=
    hU.eq_of_tgt _ _
  have hπV : HomologicalComplex.homologyMap (relativeCechPairProjectionV s U V K) n = 0 :=
    hV.eq_of_tgt _ _
  let H := HomologicalComplex.homologyFunctor S.Modules (.up ℕ) n
  have htotal := congrArg H.map (pair_split s U V K)
  dsimp [H] at htotal
  rw [Functor.map_add, Functor.map_comp, Functor.map_comp,
    HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyFunctor_map] at htotal
  rw [hπU, hπV, zero_comp, zero_comp, add_zero] at htotal
  rw [HomologicalComplex.homologyMap_id] at htotal
  exact htotal.symm

/-- Positive right-derived relative sections vanish on an affine open composite. -/
lemma isZero_relativeOpenPushforward_rightDerived_succ
    (s : X ⟶ S) (U : X.Opens) [IsAffineHom (U.ι ≫ s)] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((relativeOpenPushforward s U).rightDerived (n + 1)).obj M) := by
  let e := Functor.isoWhiskerLeft (restrictFunctor U.ι) (pushforwardComp U.ι s)
  exact (isZero_restrictPushforwardRightDerived_succ s U M n).of_iso
    ((NatIso.rightDerivedIso e (n + 1)).app M)


set_option backward.isDefEq.respectTransparency false in
/-- Homology of the relative pair is the product of the homologies of its open pieces. -/
noncomputable def relativeCechPair_homologyProdIso
    (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    (((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K).homology n ≅
      (((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K).homology n ⨯
        (((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj K).homology n := by
  exact relativeCechPair_mapProdIso s U V K
    (HomologicalComplex.homologyFunctor S.Modules (.up ℕ) n)


set_option backward.isDefEq.respectTransparency false in
/-- The pair homology is quasicoherent when the two open-piece homologies are. -/
lemma isQuasicoherent_relativeCechPair_homology
    (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ) (n : ℕ)
    (hU :
      let A :=
        (((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K).homology n
      A.IsQuasicoherent)
    (hV :
      let A :=
        (((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj K).homology n
      A.IsQuasicoherent) :
    let A :=
      (((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K).homology n
    A.IsQuasicoherent := by
  let e := relativeCechPair_homologyProdIso s U V K n
  let hprod :
      let A :=
        (((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K).homology n
      let B :=
        (((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj K).homology n
      (A ⨯ B).IsQuasicoherent := by
    exact isQuasicoherent_prod
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso e.symm hprod

end GromovWitten.AlgebraicGeometry.Curves
