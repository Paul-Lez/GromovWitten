/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechSheaves
import Mathlib.Algebra.Homology.Additive

/-!
# Relative Čech maps from a finite union

The two-open Čech pair can be reached from the pushforward over the union without
assuming that the union is the whole scheme.  This is the fixed-resolution complex
used to compare finite affine covers under base change.
-/

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The union pushforward maps to the two open pushforwards. -/
def relativeCechUnionToPair (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) :
    (relativeOpenPushforward s (U ⊔ V)).obj M ⟶
      (relativeCechPairFunctor s U V).obj M :=
  prod.lift
    ((pushforward s).map (openRestrictionMap M (le_sup_left : U ≤ U ⊔ V)))
    ((pushforward s).map (openRestrictionMap M (le_sup_right : V ≤ U ⊔ V)))

set_option backward.isDefEq.respectTransparency false in
/-- The union-to-pair map is natural in the coefficient module. -/
def relativeCechUnionToPairNat (s : X ⟶ S) (U V : X.Opens) :
    relativeOpenPushforward s (U ⊔ V) ⟶ relativeCechPairFunctor s U V where
  app M := relativeCechUnionToPair s M U V
  naturality M N f := by
    apply prod.hom_ext
    · simp only [relativeCechPairFunctor, relativeCechUnionToPair, prod.lift_fst_assoc,
        prod.lift_fst, prod.map_fst, Category.assoc]
      dsimp only [relativeOpenPushforward, Functor.comp_map]
      rw [← Functor.map_comp]
      exact congrArg (pushforward s).map
        (openRestrictionMap_naturality M N f
          (le_sup_left : U ≤ U ⊔ V))
    · simp only [relativeCechPairFunctor, relativeCechUnionToPair, prod.lift_snd_assoc,
        prod.lift_snd, prod.map_snd, Category.assoc]
      dsimp only [relativeOpenPushforward, Functor.comp_map]
      rw [← Functor.map_comp]
      exact congrArg (pushforward s).map
        (openRestrictionMap_naturality M N f
          (le_sup_right : V ≤ U ⊔ V))

set_option backward.isDefEq.respectTransparency false in
/-- The union-to-pair map followed by the Čech difference map is zero. -/
lemma relativeCechUnion_comp (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) :
    relativeCechUnionToPair s M U V ≫ relativeCechFromPair s M U V = 0 := by
  simp only [relativeCechUnionToPair, relativeCechFromPair, Preadditive.comp_sub,
    ← Category.assoc]
  erw [prod.lift_fst, prod.lift_snd]
  rw [← Functor.map_comp, ← Functor.map_comp,
    openRestrictionMap_trans, openRestrictionMap_trans, sub_self]

/-- The Čech short complex with the union pushforward as its left term. -/
def relativeCechUnionShortComplex (s : X ⟶ S) (M : X.Modules) (U V : X.Opens) :
    ShortComplex S.Modules :=
  ShortComplex.mk (relativeCechUnionToPair s M U V) (relativeCechFromPair s M U V)
    (relativeCechUnion_comp s M U V)

set_option backward.isDefEq.respectTransparency false in
/-- The union-to-pair Čech map is natural on complexes. -/
def relativeCechUnionComplexMV (K : CochainComplex (X.Modules) ℕ) (s : X ⟶ S)
    (U V : X.Opens) : ShortComplex (CochainComplex S.Modules ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (relativeCechUnionToPairNat s U V) (.up ℕ)).app K)
    ((NatTrans.mapHomologicalComplex (relativeCechFromPairNat s U V) (.up ℕ)).app K) (by
      ext n : 1
      exact relativeCechUnion_comp s (K.X n) U V)

end GromovWitten.AlgebraicGeometry.SheafCohomology
