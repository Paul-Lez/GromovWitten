/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.SheafHComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
/-!
# Flasque sheaves and cohomological dimension one

A map with flasque target, kernel and cokernel forces its source to have no
cohomology in degrees at least two. The proof applies the long exact Ext
sequence to the two short exact sequences through the image.
-/

open CategoryTheory Limits Abelian TopologicalSpace
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
universe u
noncomputable section
variable {X : TopCat.{u}}
/-- A flasque sheaf has no positive Ext-based sheaf cohomology. -/
lemma isZero_sheafH_of_isFlasque (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    IsZero (AddCommGrpCat.of (F.H (n + 1))) := by
  apply isZero_sheafH_of_isZero_rightDerivedSections n
  have h := TopCat.Sheaf.isZero_rightDerived_pushforward_of_isFlasque (toPoint X) F n
  exact IsZero.of_iso (PointSheaves.globalSections.{u}.map_isZero h)
    (derivedSectionsTopIso X F (n + 1))

private lemma isZero_sheafH_middle_of_shortExact
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    (h₁ : IsZero (AddCommGrpCat.of (S.X₁.H n)))
    (h₃ : IsZero (AddCommGrpCat.of (S.X₃.H n))) :
    IsZero (AddCommGrpCat.of (S.X₂.H n)) := by
  exact (Ext.covariant_sequence_exact₂' _ hS n).isZero_of_both_isZero h₁ h₃

private lemma isZero_sheafH_first_of_shortExact
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    (h₃ : IsZero (AddCommGrpCat.of (S.X₃.H n)))
    (h₂ : IsZero (AddCommGrpCat.of (S.X₂.H (n + 1)))) :
    IsZero (AddCommGrpCat.of (S.X₁.H (n + 1))) := by
  exact (Ext.covariant_sequence_exact₁' _ hS n (n + 1) rfl).isZero_of_both_isZero h₃ h₂

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf mapping to a flasque sheaf with flasque kernel and cokernel has
cohomological dimension at most one. -/
lemma isZero_sheafH_of_flasque_kernel_cokernel
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    [TopCat.Sheaf.IsFlasque G] [TopCat.Sheaf.IsFlasque (kernel f)]
    [TopCat.Sheaf.IsFlasque (cokernel f)] (n : ℕ) :
    IsZero (AddCommGrpCat.of (F.H (n + 2))) := by
  let S₁ : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) (by
      apply (cancel_mono (Abelian.image.ι f)).mp
      simp)
  have hS₁ : S₁.ShortExact := by
    have h : S₁.Exact := by
      let φ : S₁ ⟶ ShortComplex.kernelSequence f :=
        { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι f
          comm₂₃ := by change 𝟙 _ ≫ f = Abelian.factorThruImage f ≫ Abelian.image.ι f; simp }
      have : Epi φ.τ₁ := by dsimp only [φ]; infer_instance
      have : IsIso φ.τ₂ := by dsimp only [φ]; infer_instance
      have : Mono φ.τ₃ := by dsimp only [φ]; infer_instance
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
        (ShortComplex.kernelSequence_exact f)
    exact { exact := h
            mono_f := by dsimp [S₁]; infer_instance
            epi_g := by dsimp [S₁]; infer_instance }
  let S₂ : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    ShortComplex.kernelSequence (cokernel.π f)
  have hS₂ : S₂.ShortExact := {
    exact := ShortComplex.kernelSequence_exact _
    mono_f := by dsimp [S₂, ShortComplex.kernelSequence]; infer_instance
    epi_g := by dsimp [S₂, ShortComplex.kernelSequence]; infer_instance }
  have hI : IsZero (AddCommGrpCat.of ((Abelian.image f).H (n + 2))) :=
    isZero_sheafH_first_of_shortExact hS₂ (n + 1)
      (isZero_sheafH_of_isFlasque (X := X) (cokernel f) n)
      (isZero_sheafH_of_isFlasque (X := X) G (n + 1))
  exact isZero_sheafH_middle_of_shortExact hS₁ (n + 2)
    (isZero_sheafH_of_isFlasque (X := X) (kernel f) (n + 1)) hI
end
end GromovWitten.AlgebraicGeometry.SheafCohomology
