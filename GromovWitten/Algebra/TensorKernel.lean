/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.Flat.Equalizer

/-!
# Kernel preservation for scalar extension with flat target and cokernel

If the target and cokernel of a linear map are flat, its kernel is preserved by
tensoring with every algebra. The proof first shows that the image is flat and
then applies Mathlib's arbitrary-module kernel comparison for a surjection onto
a flat target.
-/

open TensorProduct
noncomputable section

namespace LinearMap

universe u v w

variable {R : Type u} [CommRing R]

section

variable {B C : Type v} [AddCommGroup B] [AddCommGroup C]
  [Module R B] [Module R C]

variable (g : B →ₗ[R] C)

/-- The image of a map is flat when its target and cokernel are flat. -/
lemma range_flat_of_flat_target_of_flat_cokernel
    [Module.Flat R C]
    [Module.Flat R (C ⧸ LinearMap.range g)] :
    Module.Flat R (LinearMap.range g) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ f hf
  let q : C →ₗ[R] (C ⧸ LinearMap.range g) := Submodule.mkQ _
  let i : LinearMap.range g →ₗ[R] C := (LinearMap.range g).subtype
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hi : Function.Injective i := (LinearMap.range g).injective_subtype
  have hqi : Function.Exact i q := LinearMap.exact_subtype_mkQ _
  have hiM : Function.Injective (i.lTensor M) :=
    LinearMap.lTensor_injective_of_exact_of_flat q hq i hi hqi M
  have hfC : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  intro x y hxy
  apply hiM
  apply hfC
  have hcomm : (f.rTensor C).comp (i.lTensor M) =
      (i.lTensor N).comp (f.rTensor (LinearMap.range g)) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hxy]
  exact (LinearMap.congr_fun hcomm y).symm

section Kernel

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Scalar extension preserves the kernel of a map whose target and cokernel are flat.

The map is the concrete kernel comparison from `Mathlib.RingTheory.Flat.Equalizer`; its
bijectivity is stated at the `AlgebraTensorModule` level used by `ModuleCat.extendScalars`.
-/
lemma tensorKer_bijective_of_target_flat_of_cokernel_flat
    [Module.Flat R C]
    [Module.Flat R (C ⧸ LinearMap.range g)] :
    Function.Bijective (LinearMap.tensorKer A A g) := by
  let I := LinearMap.range g
  let q : C →ₗ[R] (C ⧸ I) := Submodule.mkQ _
  let i : I →ₗ[R] C := I.subtype
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hi : Function.Injective i := I.injective_subtype
  have hqi : Function.Exact i q := LinearMap.exact_subtype_mkQ _
  have hiA : Function.Injective (i.lTensor A) :=
    LinearMap.lTensor_injective_of_exact_of_flat q hq i hi hqi A
  let _ : Module.Flat R I := range_flat_of_flat_target_of_flat_cokernel g
  let gi : B →ₗ[R] I := g.rangeRestrict
  have hgi : Function.Surjective gi := LinearMap.surjective_rangeRestrict _
  have hker : LinearMap.ker gi = LinearMap.ker g := by
    ext x
    simp [gi]
  let hgiA := LinearMap.kerLTensorEquivOfSurjective gi hgi A
  let ek : LinearMap.ker g ≃ₗ[R] LinearMap.ker gi := LinearEquiv.ofEq _ _ hker.symm
  let et : A ⊗[R] LinearMap.ker g ≃ₗ[R] A ⊗[R] LinearMap.ker gi :=
    TensorProduct.congr (LinearEquiv.refl R A) ek
  have hcomp : (i.lTensor A).comp (gi.lTensor A) = g.lTensor A := by
    rw [← LinearMap.lTensor_comp]
    rfl
  have hkerA : LinearMap.ker (gi.lTensor A) = LinearMap.ker (g.lTensor A) := by
    rw [← hcomp]
    exact (LinearMap.ker_comp_of_ker_eq_bot (gi.lTensor A)
      (LinearMap.ker_eq_bot.2 hiA)).symm
  let ea : LinearMap.ker (gi.lTensor A) ≃ₗ[R] LinearMap.ker (g.lTensor A) :=
    LinearEquiv.ofEq _ _ hkerA
  let e : A ⊗[R] LinearMap.ker g ≃ₗ[R] LinearMap.ker (g.lTensor A) :=
    et.trans (hgiA.symm.trans ea)
  have he (x : A ⊗[R] LinearMap.ker g) :
      (e x : A ⊗[R] B) = (LinearMap.tensorKer A A g x : A ⊗[R] B) := by
    induction x using TensorProduct.induction_on with
    | zero => simp [e]
    | add x y hx hy =>
      rw [map_add, map_add]
      change (e x : A ⊗[R] B) + (e y : A ⊗[R] B) =
        (LinearMap.tensorKer A A g x : A ⊗[R] B) +
          (LinearMap.tensorKer A A g y : A ⊗[R] B)
      rw [hx, hy]
    | tmul a x =>
      change ((hgiA.symm (a ⊗ₜ[R] ek x) : _) : A ⊗[R] B) = _
      have htmul :
          ((hgiA.symm (a ⊗ₜ[R] ek x) : _) : A ⊗[R] B) =
            a ⊗ₜ[R] (ek x : B) := by
        simpa only [hgiA] using
          (LinearMap.tensorKerEquivOfSurjective_symm_tmul gi hgi A a (ek x))
      rw [htmul]
      rfl
  constructor
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    rw [he x, he y]
    exact congrArg Subtype.val hxy
  · intro z
    obtain ⟨y, hy⟩ := e.surjective z
    refine ⟨y, ?_⟩
    apply Subtype.ext
    calc
      (LinearMap.tensorKer A A g y : A ⊗[R] B) = (e y : A ⊗[R] B) := (he y).symm
      _ = z := congrArg Subtype.val hy

end Kernel

end

end LinearMap
