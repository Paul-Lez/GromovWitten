/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RelativeCechUnionSheaves
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechBaseChange

/-!
# Base change for relative Čech union complexes

The base-change maps for the union, pair, and overlap terms assemble into a
morphism of short complexes.  The construction uses only the commutative
base-map equation and does not assume a Cartesian square.
-/

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology
open Scheme.Modules
open HomologicalComplex

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X S T Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Base change commutes with the map from the union pushforward to the
two-open Čech pair. -/
lemma relativeCechUnionToPair_baseChange
    (s : X ⟶ S) (b : T ⟶ S) (p : Y ⟶ X) (g : Y ⟶ T)
    (w : p ≫ s = g ≫ b) (U V : X.Opens) (M : X.Modules) :
    (relativeOpenBaseChangeNatTrans s b p g w (U ⊔ V)).app M ≫
        relativeCechUnionToPair g ((Scheme.Modules.pullback p).obj M)
          (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
      (Scheme.Modules.pullback b).map (relativeCechUnionToPair s M U V) ≫
        (relativeCechPairBaseChangeNatTrans s b p g w U V).app M := by
  apply prod.hom_ext
  · simp only [relativeCechUnionToPair, prod.lift_fst, Category.assoc]
    rw [relativeCechPairBaseChangeNatTrans_fst]
    rw [← Category.assoc, ← Functor.map_comp, prod.lift_fst]
    rw [← relativeOpenBaseChangeNatTrans_restriction s b p g w
      (le_sup_left : U ≤ U ⊔ V) M]
  · simp only [relativeCechUnionToPair, prod.lift_snd, Category.assoc]
    rw [relativeCechPairBaseChangeNatTrans_snd]
    rw [← Category.assoc, ← Functor.map_comp, prod.lift_snd]
    rw [← relativeOpenBaseChangeNatTrans_restriction s b p g w
      (le_sup_right : V ≤ U ⊔ V) M]

set_option backward.isDefEq.respectTransparency false in
/-- The componentwise base-change morphism of a relative Čech union complex. -/
def relativeCechUnionComplexBaseChange
    (K : CochainComplex X.Modules ℕ) (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (w : p ≫ s = g ≫ b) (U V : X.Opens) :
    (relativeCechUnionComplexMV K s U V).map
        ((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℕ)) ⟶
      relativeCechUnionComplexMV
        (((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K)
        g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) where
  τ₁ :=
    (NatTrans.mapHomologicalComplex
      (relativeOpenBaseChangeNatTrans s b p g w (U ⊔ V)) (.up ℕ)).app K
  τ₂ :=
    (NatTrans.mapHomologicalComplex
      (relativeCechPairBaseChangeNatTrans s b p g w U V) (.up ℕ)).app K
  τ₃ :=
    (NatTrans.mapHomologicalComplex
      (relativeOpenBaseChangeNatTrans s b p g w (U ⊓ V)) (.up ℕ)).app K
  comm₁₂ := by
    ext n : 1
    change
      (relativeOpenBaseChangeNatTrans s b p g w (U ⊔ V)).app (K.X n) ≫
          relativeCechUnionToPair g ((Scheme.Modules.pullback p).obj (K.X n))
            (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
        (Scheme.Modules.pullback b).map (relativeCechUnionToPair s (K.X n) U V) ≫
          (relativeCechPairBaseChangeNatTrans s b p g w U V).app (K.X n)
    exact relativeCechUnionToPair_baseChange s b p g w U V (K.X n)
  comm₂₃ := by
    ext n : 1
    change
      (relativeCechPairBaseChangeNatTrans s b p g w U V).app (K.X n) ≫
          relativeCechFromPair g ((Scheme.Modules.pullback p).obj (K.X n))
            (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
        (Scheme.Modules.pullback b).map (relativeCechFromPair s (K.X n) U V) ≫
          (relativeOpenBaseChangeNatTrans s b p g w (U ⊓ V)).app (K.X n)
    exact relativeCechFromPair_baseChange s b p g w U V (K.X n)

/-- The morphism of relative Čech union complexes induced by a cochain map. -/
def relativeCechUnionComplexMVMap
    {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L)
    (s : X ⟶ S) (U V : X.Opens) :
    relativeCechUnionComplexMV K s U V ⟶ relativeCechUnionComplexMV L s U V where
  τ₁ := ((relativeOpenPushforward s (U ⊔ V)).mapHomologicalComplex (.up ℕ)).map φ
  τ₂ := ((relativeCechPairFunctor s U V).mapHomologicalComplex (.up ℕ)).map φ
  τ₃ := ((relativeOpenPushforward s (U ⊓ V)).mapHomologicalComplex (.up ℕ)).map φ
  comm₁₂ :=
    (NatTrans.mapHomologicalComplex (relativeCechUnionToPairNat s U V) _).naturality φ
  comm₂₃ :=
    (NatTrans.mapHomologicalComplex (relativeCechFromPairNat s U V) _).naturality φ

end GromovWitten.AlgebraicGeometry.Curves
