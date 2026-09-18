/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.Algebra.TensorSubspaceDistrib
import GromovWitten.AlgebraicGeometry.Cones.AssociatedGradedGrading
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The lattice of tensor products of subspaces, second part

`GromovWitten/Algebra/TensorSubspaceDistrib.lean` proves the mixed distributivity law
`(A ⊗' ⊤) ⊓ (⊤ ⊗' B) = A ⊗' B` for subspaces of a tensor product of vector spaces.  This file
adds the remaining lattice identity needed for the product formula for normal cones, namely the
one-sided law

`(A₁ ⊗' ⊤) ⊓ (A₂ ⊗' ⊤) = (A₁ ⊓ A₂) ⊗' ⊤`   (`inf_tensorSub_top`),

which is flatness of the second factor rather than a statement about idempotents: over a field
every module is flat, so `- ⊗ W` is exact and `A ⊗' ⊤` is the kernel of `V ⊗ W → (V/A) ⊗ W`.

## Main results

* `range_tensorMap'`: the range of `e ⊗ f` is `range e ⊗' range f`, for arbitrary linear maps
  `e`, `f` (the version in `TensorSubspaceDistrib.lean` is for endomorphisms).
* `tensorSub_top_eq_range_rTensor`: `A ⊗' ⊤ = range (A.subtype ⊗ 1)`.
* `ker_rTensor_eq`: `ker (f ⊗ 1) = (ker f) ⊗' ⊤` for any linear map `f` out of `V`, by
  `Module.Flat.rTensor_exact`.
* `tensorSub_top_eq_ker_mkQ`: `A ⊗' ⊤ = ker (V ⊗ W → (V/A) ⊗ W)`.
* `rTensor_prod`: `(f.prod g) ⊗ 1` is `(f ⊗ 1).prod (g ⊗ 1)` up to the canonical isomorphism
  `(P × Q) ⊗ W ≅ (P ⊗ W) × (Q ⊗ W)`.
* `inf_tensorSub_top`: the one-sided distributivity law.
* `top_tensorSub_eq_range_lTensor`, `ker_lTensor_eq`, `top_tensorSub_eq_ker_mkQ`,
  `lTensor_prod`, `inf_top_tensorSub`: the right-hand analogues.
* `inf_tensorSub`: the two-sided consequence
  `(A₁ ⊗' B₁) ⊓ (A₂ ⊗' B₂) = (A₁ ⊓ A₂) ⊗' (B₁ ⊓ B₂)`, obtained by combining the two one-sided
  laws with `tensorSub_top_inf_top_tensorSub`.

## What is still missing for the injectivity of `grTensorToGr`

This file completes step (a) of the programme.  Steps (b), (c), (d) are **not** carried out:

* (b) the degreewise identification
  `J^n/J^(n+1) ≅ ⊕_{a+b=n} (I^a/I^(a+1)) ⊗_k (I'^b/I'^(b+1))`.  Note that `inf_tensorSub` gives
  only *binary* intersections; computing
  `(Σ_{a+b=n} I^a ⊗' I'^b) ⊓ (Σ_{c+d=n+1} I^c ⊗' I'^d)` termwise needs distributivity of `⊓`
  over the finite sums as well, for which the practical route is a splitting
  `I^a = I^(a+1) ⊕ C_a` of the finite part of the `I`-adic filtration, turning both sides into
  direct sums of the pieces `C_a ⊗' C'_b`;
* (c) the total-degree projections on `gr_I(R) ⊗[k] gr_{I'}(R')` and their intertwining with
  `GromovWitten.AlgebraicGeometry.AffineNormalCone.grProj`, which would then feed
  `AffineNormalCone.injective_of_degreewise`;
* (d) hence `grTensorEquiv` still carries its injectivity hypothesis, and the special case
  `gr_{(I,y)}(R[y]) ≃ gr_I(R) ⊗[k] gr_{(y)}(k[y])` is not proved.

Everything that *is* in this file is unconditional.
-/

open scoped TensorProduct

namespace GromovWitten.Algebra

universe u v

variable {k : Type u} [Field k] {V W P Q : Type v} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]

/-! ### `A ⊗' ⊤` as a range and as a kernel -/

/-- The range of a tensor product of two arbitrary linear maps is the tensor product of their
ranges.  (`range_tensorMap` of `TensorSubspaceDistrib.lean` is the case of endomorphisms.) -/
theorem range_tensorMap' {V' W' : Type v} [AddCommGroup V'] [Module k V'] [AddCommGroup W']
    [Module k W'] {A : Submodule k V} {B : Submodule k W} {e : V' →ₗ[k] V} {f : W' →ₗ[k] W}
    (hA : LinearMap.range e = A) (hB : LinearMap.range f = B) :
    LinearMap.range (TensorProduct.map e f) = tensorSub A B := by
  subst hA
  subst hB
  have key : TensorProduct.map (LinearMap.range e).subtype (LinearMap.range f).subtype ∘ₗ
      TensorProduct.map e.rangeRestrict f.rangeRestrict = TensorProduct.map e f := by
    rw [← TensorProduct.map_comp]
    congr 1
  rw [← key, LinearMap.range_comp, LinearMap.range_eq_top.mpr
    (TensorProduct.map_surjective (LinearMap.surjective_rangeRestrict e)
      (LinearMap.surjective_rangeRestrict f)),
    Submodule.map_top, tensorSub]

/-- `A ⊗' ⊤` is the image of `A ⊗[k] W` in `V ⊗[k] W`. -/
theorem tensorSub_top_eq_range_rTensor (A : Submodule k V) :
    tensorSub A (⊤ : Submodule k W) = LinearMap.range (LinearMap.rTensor W A.subtype) :=
  (range_tensorMap' (A.range_subtype) (LinearMap.range_id (M := W))).symm

/-- **Left exactness of `- ⊗ W` over a field**: the kernel of `f ⊗ 1` is `(ker f) ⊗' ⊤`. -/
theorem ker_rTensor_eq (f : V →ₗ[k] P) :
    LinearMap.ker (LinearMap.rTensor W f) =
      tensorSub (LinearMap.ker f) (⊤ : Submodule k W) := by
  have hex : Function.Exact (LinearMap.rTensor W (LinearMap.ker f).subtype)
      (LinearMap.rTensor W f) :=
    Module.Flat.rTensor_exact W (LinearMap.exact_subtype_ker_map f)
  rw [LinearMap.exact_iff] at hex
  rw [hex, tensorSub_top_eq_range_rTensor]

/-- `A ⊗' ⊤` is the kernel of `V ⊗ W → (V ⧸ A) ⊗ W`. -/
theorem tensorSub_top_eq_ker_mkQ (A : Submodule k V) :
    tensorSub A (⊤ : Submodule k W) = LinearMap.ker (LinearMap.rTensor W A.mkQ) := by
  rw [ker_rTensor_eq, Submodule.ker_mkQ]

/-! ### The one-sided distributivity law -/

/-- Tensoring a product of two maps with `W` is, up to the canonical isomorphism
`(P × Q) ⊗ W ≅ (P ⊗ W) × (Q ⊗ W)`, the product of the two tensored maps. -/
theorem rTensor_prod (f : V →ₗ[k] P) (g : V →ₗ[k] Q) :
    (TensorProduct.prodLeft k k P Q W).toLinearMap ∘ₗ LinearMap.rTensor W (f.prod g) =
      (LinearMap.rTensor W f).prod (LinearMap.rTensor W g) := by
  apply TensorProduct.ext'
  intro v w
  rfl

/-- **The one-sided distributivity law.**  For subspaces `A₁`, `A₂` of `V` and any vector space
`W` over the field `k`, `(A₁ ⊗ W) ⊓ (A₂ ⊗ W) = (A₁ ⊓ A₂) ⊗ W` inside `V ⊗[k] W`. -/
theorem inf_tensorSub_top (A₁ A₂ : Submodule k V) :
    tensorSub A₁ (⊤ : Submodule k W) ⊓ tensorSub A₂ (⊤ : Submodule k W)
      = tensorSub (A₁ ⊓ A₂) (⊤ : Submodule k W) := by
  have hker : LinearMap.ker (A₁.mkQ.prod A₂.mkQ) = A₁ ⊓ A₂ := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have h1 : tensorSub (A₁ ⊓ A₂) (⊤ : Submodule k W)
      = LinearMap.ker (LinearMap.rTensor W (A₁.mkQ.prod A₂.mkQ)) := by
    rw [ker_rTensor_eq, hker]
  have hinj : LinearMap.ker (LinearMap.rTensor W (A₁.mkQ.prod A₂.mkQ)) =
      LinearMap.ker ((TensorProduct.prodLeft k k (V ⧸ A₁) (V ⧸ A₂) W).toLinearMap ∘ₗ
        LinearMap.rTensor W (A₁.mkQ.prod A₂.mkQ)) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
  rw [h1, hinj, rTensor_prod, LinearMap.ker_prod, tensorSub_top_eq_ker_mkQ,
    tensorSub_top_eq_ker_mkQ]

/-! ### The right-hand analogues -/

/-- `⊤ ⊗' B` is the image of `V ⊗[k] B` in `V ⊗[k] W`. -/
theorem top_tensorSub_eq_range_lTensor (B : Submodule k W) :
    tensorSub (⊤ : Submodule k V) B = LinearMap.range (LinearMap.lTensor V B.subtype) :=
  (range_tensorMap' (LinearMap.range_id (M := V)) (B.range_subtype)).symm

/-- **Left exactness of `V ⊗ -` over a field**: the kernel of `1 ⊗ g` is `⊤ ⊗' (ker g)`. -/
theorem ker_lTensor_eq (g : W →ₗ[k] Q) :
    LinearMap.ker (LinearMap.lTensor V g) =
      tensorSub (⊤ : Submodule k V) (LinearMap.ker g) := by
  have hex : Function.Exact (LinearMap.lTensor V (LinearMap.ker g).subtype)
      (LinearMap.lTensor V g) :=
    Module.Flat.lTensor_exact V (LinearMap.exact_subtype_ker_map g)
  rw [LinearMap.exact_iff] at hex
  rw [hex, top_tensorSub_eq_range_lTensor]

/-- `⊤ ⊗' B` is the kernel of `V ⊗ W → V ⊗ (W ⧸ B)`. -/
theorem top_tensorSub_eq_ker_mkQ (B : Submodule k W) :
    tensorSub (⊤ : Submodule k V) B = LinearMap.ker (LinearMap.lTensor V B.mkQ) := by
  rw [ker_lTensor_eq, Submodule.ker_mkQ]

/-- The right-hand analogue of `rTensor_prod`. -/
theorem lTensor_prod (f : W →ₗ[k] P) (g : W →ₗ[k] Q) :
    (TensorProduct.prodRight k k V P Q).toLinearMap ∘ₗ LinearMap.lTensor V (f.prod g) =
      (LinearMap.lTensor V f).prod (LinearMap.lTensor V g) := by
  apply TensorProduct.ext'
  intro v w
  rfl

/-- The right-hand analogue of `inf_tensorSub_top`. -/
theorem inf_top_tensorSub (B₁ B₂ : Submodule k W) :
    tensorSub (⊤ : Submodule k V) B₁ ⊓ tensorSub (⊤ : Submodule k V) B₂
      = tensorSub (⊤ : Submodule k V) (B₁ ⊓ B₂) := by
  have hker : LinearMap.ker (B₁.mkQ.prod B₂.mkQ) = B₁ ⊓ B₂ := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have h1 : tensorSub (⊤ : Submodule k V) (B₁ ⊓ B₂)
      = LinearMap.ker (LinearMap.lTensor V (B₁.mkQ.prod B₂.mkQ)) := by
    rw [ker_lTensor_eq, hker]
  have hinj : LinearMap.ker (LinearMap.lTensor V (B₁.mkQ.prod B₂.mkQ)) =
      LinearMap.ker ((TensorProduct.prodRight k k V (W ⧸ B₁) (W ⧸ B₂)).toLinearMap ∘ₗ
        LinearMap.lTensor V (B₁.mkQ.prod B₂.mkQ)) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
  rw [h1, hinj, lTensor_prod, LinearMap.ker_prod, top_tensorSub_eq_ker_mkQ,
    top_tensorSub_eq_ker_mkQ]

/-- The two-sided form: `(A₁ ⊗' B₁) ⊓ (A₂ ⊗' B₂) = (A₁ ⊓ A₂) ⊗' (B₁ ⊓ B₂)`. -/
theorem inf_tensorSub (A₁ A₂ : Submodule k V) (B₁ B₂ : Submodule k W) :
    tensorSub A₁ B₁ ⊓ tensorSub A₂ B₂ = tensorSub (A₁ ⊓ A₂) (B₁ ⊓ B₂) := by
  rw [← tensorSub_top_inf_top_tensorSub A₁ B₁, ← tensorSub_top_inf_top_tensorSub A₂ B₂,
    ← tensorSub_top_inf_top_tensorSub (A₁ ⊓ A₂) (B₁ ⊓ B₂), ← inf_tensorSub_top,
    ← inf_top_tensorSub]
  ext x
  simp only [Submodule.mem_inf]
  tauto

end GromovWitten.Algebra
