/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernel preservation and monomorphic postcomposition

A functor preserving the kernel of a map also preserves the kernel of its
composite with a monomorphism, provided the functor maps that monomorphism to one.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace CategoryTheory.Functor
/-- Kernel preservation is unchanged by a monomorphic postcomposition preserved by the functor. -/
lemma preservesKernel_comp_mono
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasKernels C] [HasKernels D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {A B E : C} (f : A ⟶ B) (g : B ⟶ E) [Mono g] [Mono (F.map g)]
    [PreservesLimit (parallelPair f 0) F] :
    PreservesLimit (parallelPair (f ≫ g) 0) F := by
  let e := kernelIsoOfEq (F.map_comp f g) ≪≫ kernelCompMono (F.map f) (F.map g)
  have h : kernelComparison (f ≫ g) F ≫ e.hom =
      F.map (kernelCompMono f g).hom ≫ kernelComparison f F := by
    apply (cancel_mono (kernel.ι (F.map f))).mp
    simp [e, Category.assoc, kernelCompMono]
  have : IsIso (kernelComparison (f ≫ g) F ≫ e.hom) := by
    rw [h]
    infer_instance
  have : IsIso (kernelComparison (f ≫ g) F) :=
    IsIso.of_isIso_comp_right _ e.hom
  exact PreservesKernel.of_iso_comparison F (f ≫ g)
end CategoryTheory.Functor
