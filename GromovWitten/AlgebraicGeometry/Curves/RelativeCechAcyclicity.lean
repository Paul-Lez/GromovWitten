/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves
import GromovWitten.AlgebraicGeometry.Curves.DerivedOpenPushforward
import Mathlib.Algebra.Homology.Additive

/-!
# Acyclicity of the relative two-open Čech pair

The product term of a relative two-open Čech complex is homologically zero whenever both
open-piece complexes are homologically zero.  Affine open composites provide the corresponding
right-derived vanishing in positive degrees.
-/

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
open CochainComplex
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S : Scheme.{u}}

private abbrev openComplex (s : X ⟶ S) (W : X.Opens)
    (K : CochainComplex X.Modules ℕ) : CochainComplex S.Modules ℕ :=
  ((relativeOpenPushforward s W).mapHomologicalComplex (.up ℕ)).obj K

private abbrev pairComplex (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) : CochainComplex S.Modules ℕ :=
  ((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K

private def pairProjectionU (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) : pairComplex s U V K ⟶ openComplex s U K :=
  HomologicalComplex.Hom.mk (fun n => prod.fst) (by
    intro i j hij
    change prod.fst ≫ (relativeOpenPushforward s U).map (K.d i j) =
      prod.map ((relativeOpenPushforward s U).map (K.d i j))
        ((relativeOpenPushforward s V).map (K.d i j)) ≫ prod.fst
    rw [prod.map_fst])

private def pairProjectionV (s : X ⟶ S) (U V : X.Opens)
    (K : CochainComplex X.Modules ℕ) : pairComplex s U V K ⟶ openComplex s V K :=
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
    pairProjectionU s U V K ≫ pairInclusionU s U V K +
      pairProjectionV s U V K ≫ pairInclusionV s U V K = 𝟙 _ := by
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
/-- Homology of the relative pair complex vanishes when both open pieces vanish. -/
lemma isZero_relativeCechPair_homology
    (s : X ⟶ S) (U V : X.Opens) (K : CochainComplex X.Modules ℕ) (n : ℕ)
    (hU : IsZero ((((relativeOpenPushforward s U).mapHomologicalComplex (.up ℕ)).obj K).homology n))
    (hV : IsZero
      ((((relativeOpenPushforward s V).mapHomologicalComplex (.up ℕ)).obj K).homology n)) :
    IsZero
      ((((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).obj K).homology n) := by
  rw [IsZero.iff_id_eq_zero]
  have hπU : HomologicalComplex.homologyMap (pairProjectionU s U V K) n = 0 :=
    hU.eq_of_tgt _ _
  have hπV : HomologicalComplex.homologyMap (pairProjectionV s U V K) n = 0 :=
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

end GromovWitten.AlgebraicGeometry.Curves
