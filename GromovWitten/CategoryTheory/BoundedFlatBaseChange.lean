/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.FiniteProjectiveCohomologyModel
import GromovWitten.CategoryTheory.PreserveKernelComposition

/-!
# Canonical degree-zero base change for bounded flat complexes

If a bounded flat complex is exact above degree one and its degree-one homology
is flat, its canonical degree-zero homology comparison is invertible under any
scalar extension. If the complex is also supported in nonnegative degrees, its
degree-zero homology is flat. No finite-generation or Noetherian hypothesis is needed.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
namespace CochainComplex
set_option backward.isDefEq.respectTransparency false in
/-- Flat degree-one homology makes the canonical degree-zero homology comparison invertible
for a bounded flat complex exact above degree one. -/
lemma bounded_int_zero_homologyComparison_isIso_of_flat_one
    {R T : Type u} [CommRing R] [CommRing T] (σ : R →+* T)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n)
    [Module.Flat R (K.homology 1)] :
    IsIso (K.homologyComparison (ModuleCat.extendScalars σ) (0 : ℤ)) := by
  let F := ModuleCat.extendScalars σ
  let d := ModuleCat.ofHom (bounded_int_flat_compression_d K)
  let i := ModuleCat.ofHom (LinearMap.ker (K.d 1 2).hom).subtype
  have : Module.Flat R (LinearMap.ker (K.d 1 2).hom) :=
    bounded_int_exact_flat_cycles_at K hflat N htail hexact 1 (by omega)
  have : Module.Flat R ((cokernel d : ModuleCat R) : Type u) :=
    Module.Flat.of_linearEquiv
      (bounded_int_flat_compression_cokernel_homology_iso K).toLinearEquiv
  have : PreservesLimit (parallelPair d 0) F :=
    ModuleCat.preservesKernel_extendScalars_of_flat_cokernel σ d
  have : IsIso (kernelComparison (K.d 1 2) F) := by
    rw [← bounded_int_d1_kernelComparisonIso_hom σ K hflat N htail hexact]
    infer_instance
  have hi : i = (ModuleCat.kernelIsoKer (K.d 1 2)).inv ≫ kernel.ι (K.d 1 2) := by
    simp [i]
  have hFi : F.map i = F.map (ModuleCat.kernelIsoKer (K.d 1 2)).inv ≫
      kernelComparison (K.d 1 2) F ≫ kernel.ι (F.map (K.d 1 2)) := by
    rw [hi, F.map_comp, kernelComparison_comp_ι]
  have : Mono i := by rw [hi]; infer_instance
  have : Mono (F.map i) := by rw [hFi]; infer_instance
  have hdi : d ≫ i = K.d 0 1 := by
    rfl
  have hp := F.preservesKernel_comp_mono d i
  have : PreservesLimit (parallelPair (K.d 0 1) 0) F := by
    rw [hdi] at hp
    exact hp
  have : PreservesLimit (parallelPair (K.sc (0 : ℤ)).g 0) F := by
    change PreservesLimit (parallelPair (K.d 0 ((ComplexShape.up ℤ).next 0)) 0) F
    have hn : (ComplexShape.up ℤ).next 0 = 1 := by
      apply (ComplexShape.up ℤ).next_eq'
      exact ComplexShape.up_mk _ _ (by norm_num)
    rw [hn]
    infer_instance
  exact (K.sc (0 : ℤ)).isIso_homologyComparison_of_preservesKernel F

/-- Flat degree-one homology forces flat degree-zero homology of a nonnegative bounded
flat complex exact above degree one. -/
lemma bounded_int_zero_homology_flat_of_flat_one
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [IsStrictlyGE K 0]
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n)
    [Module.Flat R (K.homology 1)] : Module.Flat R (K.homology 0) := by
  let d := bounded_int_flat_compression_d K
  let : Module.Flat R (K.X 0) := hflat 0
  let : Module.Flat R (LinearMap.ker (K.d 1 2).hom) :=
    bounded_int_exact_flat_cycles_at K hflat N htail hexact 1 (by omega)
  let : Module.Flat R (cokernel (ModuleCat.ofHom d) : ModuleCat R) :=
    Module.Flat.of_linearEquiv
      (bounded_int_flat_compression_cokernel_homology_iso K).toLinearEquiv
  let : Module.Flat R ((LinearMap.ker (K.d 1 2).hom) ⧸ LinearMap.range d) :=
    Module.Flat.of_linearEquiv (ModuleCat.cokernelIsoRangeQuotient
      (ModuleCat.ofHom d)).symm.toLinearEquiv
  let : Module.Flat R (LinearMap.ker d) :=
    d.kernel_flat_of_flat_source_of_flat_target_of_flat_cokernel
  exact Module.Flat.of_linearEquiv
    (bounded_int_flat_compression_kernel_homology_iso K).toLinearEquiv

end CochainComplex
