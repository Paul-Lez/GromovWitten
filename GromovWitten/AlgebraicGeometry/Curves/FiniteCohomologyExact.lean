/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.CohomologyExactSequence
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite cohomology in exact sequences

This file records the module-finiteness consequences of the long exact
cohomology sequence for a short exact sequence of module sheaves over a
Noetherian affine base.  The results use only the existing exactness API and
Noetherian module closure; they make no properness or coherence claim.
-/

open CategoryTheory Limits Abelian
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- The middle cohomology module is finite when the two outer modules in the
same degree are finite. -/
theorem finite_cohomology_middle_of_shortExact
    [IsNoetherianRing R] (s : X ⟶ Spec R) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ)
    [Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₁ n)]
    [Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₃ n)] :
    Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₂ n) := by
  have hExact : LinearMap.ker (cohomologyMapBaseLinear R s S.g n) =
      LinearMap.range (cohomologyMapBaseLinear R s S.f n) := by
    exact LinearMap.exact_iff.1 (cohomology_exact_at_X₂ hS n)
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₁ n) := inferInstance
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₃ n) := inferInstance
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₂ n) :=
    isNoetherian_of_range_eq_ker (cohomologyMapBaseLinear R s S.f n)
      (cohomologyMapBaseLinear R s S.g n) hExact.symm
  infer_instance

/-- The right cohomology module is finite when the middle module in degree `n`
and the left module in degree `n + 1` are finite. -/
theorem finite_cohomology_right_of_shortExact
    [IsNoetherianRing R] (s : X ⟶ Spec R) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ)
    [Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₂ n)]
    [Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₁ (n + 1))] :
    Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₃ n) := by
  have hExact : LinearMap.ker (cohomologyConnectingHomBaseLinear hS R s n) =
      LinearMap.range (cohomologyMapBaseLinear R s S.g n) := by
    exact LinearMap.exact_iff.1 (cohomology_exact_at_X₃ hS n)
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₂ n) := inferInstance
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₁ (n + 1)) := inferInstance
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₃ n) :=
    isNoetherian_of_range_eq_ker (cohomologyMapBaseLinear R s S.g n)
      (cohomologyConnectingHomBaseLinear hS R s n) hExact.symm
  infer_instance

/-- The left cohomology module in degree `n + 1` is finite when the right module
in degree `n` and the middle module in degree `n + 1` are finite. -/
theorem finite_cohomology_left_succ_of_shortExact
    [IsNoetherianRing R] (s : X ⟶ Spec R) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ)
    [Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₃ n)]
    [Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₂ (n + 1))] :
    Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₁ (n + 1)) := by
  let δₙ := cohomologyConnectingHomBaseLinear hS R s n
  have hExact : LinearMap.ker (cohomologyMapBaseLinear R s S.f (n + 1)) =
      LinearMap.range δₙ := by
    change LinearMap.ker (cohomologyMapBaseLinear R s S.f (n + 1)) =
      LinearMap.range (cohomologyConnectingHomBaseLinear hS R s n)
    exact LinearMap.exact_iff.1 (cohomology_exact_at_X₁ hS n)
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₃ n) := inferInstance
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₂ (n + 1)) := inferInstance
  let _ : IsNoetherian R (cohomologyModuleCat (R : Type u) s S.X₁ (n + 1)) :=
    isNoetherian_of_range_eq_ker δₙ
      (cohomologyMapBaseLinear R s S.f (n + 1)) hExact.symm
  infer_instance

/-- Degree-zero cohomology of the left term is finite whenever degree-zero
cohomology of the middle term is finite. -/
theorem finite_cohomology_zero_left_of_shortExact
    [IsNoetherianRing R] (s : X ⟶ Spec R) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₂ 0)] :
    Module.Finite R (cohomologyModuleCat (R : Type u) s S.X₁ 0) := by
  apply Module.Finite.of_injective (cohomologyMapBaseLinear R s S.f 0)
  change Function.Injective ((cohomologyFunctor X 0).map S.f).hom
  exact cohomology_zero_injective S hS

set_option backward.isDefEq.respectTransparency false in
/-- If the target, kernel, and cokernel have finite cohomology in every
degree, then the source has finite cohomology in every degree. -/
theorem finite_cohomology_of_finite_kernel_cokernel
    [IsNoetherianRing R] (s : X ⟶ Spec R) {M N : X.Modules} (φ : M ⟶ N)
    (hK : ∀ n, Module.Finite R (cohomologyModuleCat R s (kernel φ) n))
    (hN : ∀ n, Module.Finite R (cohomologyModuleCat R s N n))
    (hC : ∀ n, Module.Finite R (cohomologyModuleCat R s (cokernel φ) n))
    (n : ℕ) : Module.Finite R (cohomologyModuleCat R s M n) := by
  let S₁ : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ) (by
      apply (cancel_mono (Abelian.image.ι φ)).mp
      simp)
  have hS₁ : S₁.ShortExact := by
    have h : S₁.Exact := by
      let ψ : S₁ ⟶ ShortComplex.kernelSequence φ :=
        { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι φ
          comm₂₃ := by
            change 𝟙 _ ≫ φ = Abelian.factorThruImage φ ≫ Abelian.image.ι φ
            simp }
      have _ : Epi ψ.τ₁ := by dsimp only [ψ]; infer_instance
      have _ : IsIso ψ.τ₂ := by dsimp only [ψ]; infer_instance
      have _ : Mono ψ.τ₃ := by dsimp only [ψ]; infer_instance
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr
        (ShortComplex.kernelSequence_exact φ)
    exact { exact := h
            mono_f := by dsimp [S₁]; infer_instance
            epi_g := by dsimp [S₁]; infer_instance }
  let S₂ : ShortComplex X.Modules := ShortComplex.kernelSequence (cokernel.π φ)
  have hS₂ : S₂.ShortExact := {
    exact := ShortComplex.kernelSequence_exact _
    mono_f := by dsimp [S₂, ShortComplex.kernelSequence]; infer_instance
    epi_g := by dsimp [S₂, ShortComplex.kernelSequence]; infer_instance }
  have hI : Module.Finite R (cohomologyModuleCat R s (Abelian.image φ) n) := by
    cases n with
    | zero =>
      have _ : Module.Finite R (cohomologyModuleCat R s S₂.X₂ 0) := hN 0
      exact finite_cohomology_zero_left_of_shortExact s S₂ hS₂
    | succ m =>
      have _ : Module.Finite R (cohomologyModuleCat R s S₂.X₂ (m + 1)) := hN (m + 1)
      have _ : Module.Finite R (cohomologyModuleCat R s S₂.X₃ m) := hC m
      exact finite_cohomology_left_succ_of_shortExact s S₂ hS₂ m
  have _ : Module.Finite R (cohomologyModuleCat R s S₁.X₁ n) := hK n
  have _ : Module.Finite R (cohomologyModuleCat R s S₁.X₃ n) := hI
  exact finite_cohomology_middle_of_shortExact s S₁ hS₁ n

end

end GromovWitten.AlgebraicGeometry.Curves
