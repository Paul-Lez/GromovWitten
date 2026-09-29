/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Boundary and homology short exact complexes

These constructions package the cycles, boundaries, and homology of a cochain
complex into the short exact complexes used by cohomology arguments.
-/

open CategoryTheory Limits
namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
noncomputable section
namespace CochainComplex

private lemma iCycles_factorThruImage_toCycles (K : CochainComplex C ℕ) (n : ℕ) :
    K.iCycles n ≫ Abelian.factorThruImage (K.toCycles n (n + 1)) = 0 := by
  rw [← cancel_mono (Abelian.image.ι (K.toCycles n (n + 1))),
    ← cancel_mono (K.iCycles (n + 1))]
  simp only [Category.assoc, Abelian.image.fac, HomologicalComplex.toCycles_i,
    HomologicalComplex.iCycles_d, zero_comp]

/-- The short complex from cycles to a term and then the following boundaries. -/
def cyclesBoundaryShortComplex (K : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles n) (Abelian.factorThruImage (K.toCycles n (n + 1)))
    (iCycles_factorThruImage_toCycles K n)

set_option backward.isDefEq.respectTransparency false in
lemma cyclesBoundaryShortComplex_shortExact (K : CochainComplex C ℕ) (n : ℕ) :
    (cyclesBoundaryShortComplex K n).ShortExact := by
  have hker : IsLimit (KernelFork.ofι (K.iCycles n)
      (iCycles_factorThruImage_toCycles K n)) :=
    isKernelOfComp (Abelian.image.ι (K.toCycles n (n + 1)) ≫ K.iCycles (n + 1))
      (K.d n (n + 1)) (K.cyclesIsKernel n (n + 1) (by simp))
      (iCycles_factorThruImage_toCycles K n)
      (by rw [← Category.assoc, Abelian.image.fac, HomologicalComplex.toCycles_i])
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hker
          mono_f := by change Mono (K.iCycles n); infer_instance
          epi_g := by
            change Epi (Abelian.factorThruImage (K.toCycles n (n + 1)))
            infer_instance }

/-- The short complex from boundaries to cycles and then homology. -/
def boundaryHomologyShortComplex (K : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (Abelian.image.ι (K.toCycles n (n + 1))) (K.homologyπ (n + 1))
    (Abelian.image_ι_comp_eq_zero (K.toCycles_comp_homologyπ n (n + 1)))

set_option backward.isDefEq.respectTransparency false in
lemma boundaryHomologyShortComplex_shortExact (K : CochainComplex C ℕ) (n : ℕ) :
    (boundaryHomologyShortComplex K n).ShortExact := by
  let S := ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
    (K.toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (K.homologyIsCokernel n (n + 1) (by simp))
  exact { exact := (S.exact_iff_exact_image_ι).mp hS
          mono_f := by
            change Mono (Abelian.image.ι (K.toCycles n (n + 1)))
            infer_instance
          epi_g := by change Epi (K.homologyπ (n + 1)); infer_instance }
end CochainComplex
end
end CategoryTheory
