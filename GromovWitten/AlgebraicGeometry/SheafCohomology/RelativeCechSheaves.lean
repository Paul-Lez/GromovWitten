/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestrictionMap
import Mathlib.Algebra.Homology.Additive

/-!
# Relative two-open Čech sheaves

For a morphism to a base scheme, this file packages the two-open Čech maps after pushing
the open pieces to the base.  The complex condition follows from compatibility of the
open restriction map with the adjunction units.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X S : Scheme.{u}}

/-- The relative pushforward of sections on an open subscheme. -/
abbrev relativeOpenPushforward (s : X ⟶ S) (U : X.Opens) : X.Modules ⥤ S.Modules :=
  restrictFunctor U.ι ⋙ pushforward U.ι ⋙ pushforward s

set_option backward.isDefEq.respectTransparency false in
/-- The product functor for the two relative open pushforwards. -/
def relativeCechPairFunctor (s : X ⟶ S) (U V : X.Opens) : X.Modules ⥤ S.Modules where
  obj M := (relativeOpenPushforward s U).obj M ⨯ (relativeOpenPushforward s V).obj M
  map f := prod.map ((relativeOpenPushforward s U).map f)
    ((relativeOpenPushforward s V).map f)
  map_id M := by simp
  map_comp f g := by
    simp only [Functor.map_comp, prod.map_map]

/-- The relative Čech map from the pushed-forward module to the two open pieces. -/
def relativeCechToPair (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) :
    (pushforward s).obj M ⟶
      (relativeOpenPushforward s U).obj M ⨯ (relativeOpenPushforward s V).obj M :=
  prod.lift ((pushforward s).map ((restrictAdjunction U.ι).unit.app M))
    ((pushforward s).map ((restrictAdjunction V.ι).unit.app M))

/-- The relative Čech difference map from the two open pieces to their intersection. -/
def relativeCechFromPair (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) :
    (relativeOpenPushforward s U).obj M ⨯ (relativeOpenPushforward s V).obj M ⟶
      (relativeOpenPushforward s (U ⊓ V)).obj M :=
  prod.fst ≫ (pushforward s).map
      (openRestrictionMap M (inf_le_left : U ⊓ V ≤ U)) -
    prod.snd ≫ (pushforward s).map
      (openRestrictionMap M (inf_le_right : U ⊓ V ≤ V))

set_option backward.isDefEq.respectTransparency false in
/-- The relative two-open Čech maps compose to zero. -/
lemma relativeCech_comp (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) :
    relativeCechToPair s M U V ≫ relativeCechFromPair s M U V = 0 := by
  simp only [relativeCechFromPair, Preadditive.comp_sub, ← Category.assoc,
    relativeCechToPair]
  erw [prod.lift_fst, prod.lift_snd]
  rw [← Functor.map_comp, ← Functor.map_comp, openRestrictionMap_unit,
    openRestrictionMap_unit, sub_self]

/-- The pointwise relative two-open Čech short complex. -/
def relativeCechShortComplex (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) :
    ShortComplex S.Modules :=
  ShortComplex.mk _ _ (relativeCech_comp s M U V)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the relative Čech map to the pair. -/
def relativeCechToPairNat (s : X ⟶ S) (U V : X.Opens) :
    pushforward s ⟶ relativeCechPairFunctor s U V where
  app M := relativeCechToPair s M U V
  naturality M N f := by
    apply prod.hom_ext
    · simp only [relativeCechPairFunctor, relativeCechToPair, prod.lift_fst_assoc,
        prod.lift_fst, prod.map_fst, Category.assoc]
      dsimp only [relativeOpenPushforward, Functor.comp_map]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (pushforward s).map ((restrictAdjunction U.ι).unit.naturality f)
    · simp only [relativeCechPairFunctor, relativeCechToPair, prod.lift_snd_assoc,
        prod.lift_snd, prod.map_snd, Category.assoc]
      dsimp only [relativeOpenPushforward, Functor.comp_map]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (pushforward s).map ((restrictAdjunction V.ι).unit.naturality f)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the relative Čech difference map. -/
def relativeCechFromPairNat (s : X ⟶ S) (U V : X.Opens) :
    relativeCechPairFunctor s U V ⟶ relativeOpenPushforward s (U ⊓ V) where
  app M := relativeCechFromPair s M U V
  naturality M N f := by
    dsimp only [relativeCechPairFunctor, relativeCechFromPair]
    rw [Preadditive.comp_sub, Preadditive.sub_comp]
    erw [prod.map_fst_assoc, prod.map_snd_assoc]
    simp only [Category.assoc]
    simp only [relativeOpenPushforward, Functor.comp_map, ← Functor.map_comp]
    congr 1
    · exact congrArg (fun z => prod.fst ≫ (pushforward s).map z)
        (openRestrictionMap_naturality M N f (inf_le_left : U ⊓ V ≤ U))
    · exact congrArg (fun z => prod.snd ≫ (pushforward s).map z)
        (openRestrictionMap_naturality M N f (inf_le_right : U ⊓ V ≤ V))

set_option backward.isDefEq.respectTransparency false in
instance relativeCechPairFunctor_additive (s : X ⟶ S) (U V : X.Opens) :
    (relativeCechPairFunctor s U V).Additive where
  map_add := by
    intros M N f g
    apply prod.hom_ext <;>
      simp only [relativeCechPairFunctor, prod.map_fst, prod.map_snd, Preadditive.add_comp,
        Functor.map_add, Preadditive.comp_add]

/-- The relative two-open Čech complex associated to a complex of module sheaves. -/
def relativeCechComplexMV (K : CochainComplex (X.Modules) ℕ) (s : X ⟶ S)
    (U V : X.Opens) : ShortComplex (CochainComplex S.Modules ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (relativeCechToPairNat s U V) (.up ℕ)).app K)
    ((NatTrans.mapHomologicalComplex (relativeCechFromPairNat s U V) (.up ℕ)).app K) (by
      ext n : 1
      exact relativeCech_comp s (K.X n) U V)

end GromovWitten.AlgebraicGeometry.SheafCohomology
