/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechBaseChange

/-!
# Base change for relative Čech complexes

The componentwise base-change maps for a relative two-open Čech complex assemble into a
morphism of short complexes of cochain complexes.  The construction records the canonical
base-change map on the pushforward term, the pair map, and the overlap map.
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

/-- The componentwise base-change morphism of relative Čech Mayer--Vietoris complexes. -/
def relativeCechComplexBaseChange
    (K : CochainComplex X.Modules ℕ) (s : X ⟶ S) (b : T ⟶ S)
    (p : Y ⟶ X) (g : Y ⟶ T) (h : IsPullback p g s b) (U V : X.Opens) :
    (relativeCechComplexMV K s U V).map
        ((Scheme.Modules.pullback b).mapHomologicalComplex (.up ℕ)) ⟶
      relativeCechComplexMV
        (((Scheme.Modules.pullback p).mapHomologicalComplex (.up ℕ)).obj K)
        g (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) where
  τ₁ :=
    (NatTrans.mapHomologicalComplex
      (modulePushforwardBaseChangeNatTrans s b p g h) (.up ℕ)).app K
  τ₂ :=
    (NatTrans.mapHomologicalComplex
      (relativeCechPairBaseChangeNatTrans s b p g h.w U V) (.up ℕ)).app K
  τ₃ :=
    (NatTrans.mapHomologicalComplex
      (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)) (.up ℕ)).app K
  comm₁₂ := by
    ext n : 1
    change
      (modulePushforwardBaseChangeNatTrans s b p g h).app (K.X n) ≫
          relativeCechToPair g ((Scheme.Modules.pullback p).obj (K.X n))
            (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
        (Scheme.Modules.pullback b).map (relativeCechToPair s (K.X n) U V) ≫
          (relativeCechPairBaseChangeNatTrans s b p g h.w U V).app (K.X n)
    exact relativeCechToPair_baseChange s b p g h U V (K.X n)
  comm₂₃ := by
    ext n : 1
    change
      (relativeCechPairBaseChangeNatTrans s b p g h.w U V).app (K.X n) ≫
          relativeCechFromPair g ((Scheme.Modules.pullback p).obj (K.X n))
            (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) =
        (Scheme.Modules.pullback b).map (relativeCechFromPair s (K.X n) U V) ≫
          (relativeOpenBaseChangeNatTrans s b p g h.w (U ⊓ V)).app (K.X n)
    exact relativeCechFromPair_baseChange s b p g h.w U V (K.X n)

end GromovWitten.AlgebraicGeometry.Curves
