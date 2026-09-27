/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness of bundles with finite affine-space charts

The augmented polynomial charts in `BundleData` suffice to prove smoothness of the
projection.  This argument does not require the transition maps to be linear.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace.BundleData

universe u

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-- A bundle with finitely many polynomial coordinates has smooth projection. -/
theorem smooth_proj [Finite ι] : Smooth 𝓔.proj := by
  let _ : IsZariskiLocalAtSource (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  let _ : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Smooth)
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (fun j ↦ (𝓔.chartι j).opensRange) 𝓔.iSup_opensRange_chartι
  intro j
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝓔.chartι j) (Scheme.Opens.ι _)
    (congr_arg TopologicalSpace.Opens.carrier
      (𝓔.chartι j).opensRange.opensRange_ι.symm), Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)]
  rw [← (𝓔.isPullback_chart j).w]
  let _ : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1))))) := by
    refine (HasRingHomProperty.Spec_iff (P := @Smooth) (Q := @RingHom.Smooth)).2 ?_
    exact RingHom.smooth_algebraMap.mpr
      { formallySmooth := inferInstance, finitePresentation := inferInstance }
  infer_instance

/-- The zero section makes the total-space projection surjective on points. -/
theorem surjective_proj : Function.Surjective 𝓔.proj := by
  intro x
  refine ⟨𝓔.zeroSection x, ?_⟩
  have h := congrArg (fun f : X ⟶ X ↦ f x) 𝓔.zeroSection_proj
  exact h

end GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace.BundleData
