/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Exact.Basic

/-!
# Effective flat descent of modules (cocycle form)

Let `A → B` be a map of commutative rings and `M` a `B`-module.  A *descent datum* on `M`
(in "`τ`-form") is an `A`-linear map `τ : M → B ⊗[A] M` which is semilinear for the left
`B`-action on `B ⊗[A] M`, satisfies the cocycle condition, and whose associated map
`φ : M ⊗[A] B → B ⊗[A] M`, `m ⊗ b ↦ (1 ⊗ b) · τ m`, is bijective.  This is the classical
cocycle formulation of Stacks, Section 35.3 ("Descent for modules"; the effectiveness theorem is
tag 023N), with `τ m = φ (m ⊗ 1)`.

The descended module is `descended τ = {m | τ m = 1 ⊗ m}`.  We prove that when `B` is flat over
`A` the natural map `B ⊗[A] descended τ → M` is a `B`-linear isomorphism.

The repository also contains the categorical (comonadic) form of faithfully flat descent of
modules, `GromovWitten/AlgebraicGeometry/Modules/AffineDescent.lean`, built on Mathlib's
`ModuleCat.comonadicExtendScalars`; it needs faithful flatness, and its descent data are
Eilenberg–Moore coalgebras.  The present file is the elementary cocycle form, needs only
flatness for effectiveness, and is the form used for descent of algebras in
`GromovWitten/Algebra/FlatDescentAlgebra.lean`.

## Main results

* `GromovWitten.Algebra.DescentDatum`: descent data on a `B`-module.
* `GromovWitten.Algebra.DescentDatum.canonical`: the canonical descent datum on `B ⊗[A] N`,
  `b ⊗ n ↦ b ⊗ (1 ⊗ n)`.
* `GromovWitten.Algebra.DescentDatum.descended`: the descended `A`-submodule of `M`.
* `GromovWitten.Algebra.DescentDatum.smul_tensor_eq_self`: `μ (τ m) = m` (no flatness).
* `GromovWitten.Algebra.DescentDatum.tau_injective`: `τ` is injective (no flatness).
* `GromovWitten.Algebra.DescentDatum.lTensor_subtype_injective`,
  `GromovWitten.Algebra.DescentDatum.range_lTensor_subtype_eq_ker`: flat base change of the
  equalizer defining `descended τ`.
* `GromovWitten.Algebra.DescentDatum.descentEquiv`: for `B` flat over `A`,
  `B ⊗[A] descended τ ≃ₗ[B] M`, `b ⊗ n ↦ b • n` (effective descent of modules).
* `GromovWitten.Algebra.DescentDatum.range_unitTensor_le_descended_canonical`: `N` (embedded by
  `n ↦ 1 ⊗ n`) lies in the descended module of the canonical datum on `B ⊗[A] N`.
* `GromovWitten.Algebra.DescentDatum.descended_canonical_eq_range`: for `B` faithfully flat
  over `A`, equality holds (exactness of the Amitsur complex `N → B ⊗ N ⇉ B ⊗ B ⊗ N`).
-/

open TensorProduct

namespace GromovWitten.Algebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- The `A`-linear map `B → B ⊗[A] B`, `b ↦ b ⊗ 1`. -/
noncomputable def descentInsLeft : B →ₗ[A] B ⊗[A] B :=
  (TensorProduct.mk A B B).flip 1

@[simp]
lemma descentInsLeft_apply (b : B) : descentInsLeft A B b = b ⊗ₜ[A] (1 : B) := rfl

variable (M : Type*) [AddCommGroup M] [Module A M]

/-- The `A`-linear map `ι : M → B ⊗[A] M`, `m ↦ 1 ⊗ m`. -/
noncomputable def descentUnitTensor : M →ₗ[A] B ⊗[A] M :=
  TensorProduct.mk A B M 1

@[simp]
lemma descentUnitTensor_apply (m : M) : descentUnitTensor A B M m = (1 : B) ⊗ₜ[A] m := rfl

variable [Module B M] [IsScalarTower A B M]

/-- The action of `B` on the right factor of `B ⊗[A] M`, `b ↦ (b' ⊗ m ↦ b' ⊗ b • m)`,
as an `A`-bilinear map. -/
noncomputable def descentRightSmul : B →ₗ[A] (B ⊗[A] M) →ₗ[A] (B ⊗[A] M) where
  toFun b := LinearMap.lTensor B ((LinearMap.lsmul B M b).restrictScalars A)
  map_add' b b' := by
    ext x m
    simp
  map_smul' a b := by
    ext x m
    simp

@[simp]
lemma descentRightSmul_tmul (b b' : B) (m : M) :
    descentRightSmul A B M b (b' ⊗ₜ[A] m) = b' ⊗ₜ[A] (b • m) := rfl

/-- The map `φ : M ⊗[A] B → B ⊗[A] M`, `m ⊗ b ↦ ρ b (τ m)`, associated with an `A`-linear
`τ : M → B ⊗[A] M`, where `ρ` is the right action `descentRightSmul`. -/
noncomputable def descentToPhi (τ : M →ₗ[A] B ⊗[A] M) : M ⊗[A] B →ₗ[A] B ⊗[A] M :=
  TensorProduct.lift ((descentRightSmul A B M).flip ∘ₗ τ)

@[simp]
lemma descentToPhi_tmul (τ : M →ₗ[A] B ⊗[A] M) (m : M) (b : B) :
    descentToPhi A B M τ (m ⊗ₜ[A] b) = descentRightSmul A B M b (τ m) := rfl

/-- A descent datum (in `τ`-form) on a `B`-module `M` relative to `A → B`: an `A`-linear map
`τ : M → B ⊗[A] M`, semilinear for the left `B`-action on `B ⊗[A] M`, satisfying the cocycle
condition `(B ⊗ τ) ∘ τ = assoc ∘ (descentInsLeft ⊗ M) ∘ τ`, and whose associated map
`descentToPhi τ : M ⊗[A] B → B ⊗[A] M` is bijective. -/
structure DescentDatum where
  /-- The coaction `τ : M → B ⊗[A] M`, i.e. `τ m = φ (m ⊗ 1)`. -/
  τ : M →ₗ[A] B ⊗[A] M
  /-- Semilinearity for the left `B`-action. -/
  τ_smul : ∀ (b : B) (m : M), τ (b • m) = b • τ m
  /-- The cocycle condition. -/
  cocycle : ∀ m : M, LinearMap.lTensor B τ (τ m) =
    TensorProduct.assoc A B B M (LinearMap.rTensor M (descentInsLeft A B) (τ m))
  /-- The associated map `M ⊗[A] B → B ⊗[A] M` is bijective. -/
  bijective : Function.Bijective (descentToPhi A B M τ)

namespace DescentDatum

variable {A B M}

/-- The descended `A`-submodule `{m | τ m = 1 ⊗ m}` of `M`. -/
noncomputable def descended (D : DescentDatum A B M) : Submodule A M :=
  LinearMap.ker (D.τ - descentUnitTensor A B M)

lemma mem_descended_iff (D : DescentDatum A B M) (m : M) :
    m ∈ D.descended ↔ D.τ m = (1 : B) ⊗ₜ[A] m := by
  simp [descended, sub_eq_zero]

variable (A B M) in
/-- The multiplication map `μ : B ⊗[A] M → M`, `b ⊗ m ↦ b • m`, as an `A`-linear map. -/
noncomputable def descentMul : B ⊗[A] M →ₗ[A] M :=
  (LinearMap.liftBaseChange B (LinearMap.id : M →ₗ[A] M)).restrictScalars A

@[simp]
lemma descentMul_tmul (b : B) (m : M) : descentMul A B M (b ⊗ₜ[A] m) = b • m := rfl

@[simp]
lemma descentRightSmul_one : descentRightSmul A B M 1 = LinearMap.id := by
  ext b m
  simp

@[simp]
lemma descentToPhi_tmul_one (τ : M →ₗ[A] B ⊗[A] M) (m : M) :
    descentToPhi A B M τ (m ⊗ₜ[A] (1 : B)) = τ m := by
  simp

variable (D : DescentDatum A B M)

/-- Applying the left multiplication `B ⊗ (B ⊗ M) → B ⊗ M` after `B ⊗ τ` is `τ ∘ μ`. -/
lemma descentMul_comp_lTensor_tau :
    descentMul A B (B ⊗[A] M) ∘ₗ LinearMap.lTensor B D.τ = D.τ ∘ₗ descentMul A B M := by
  ext b m
  simp [D.τ_smul]

omit [Module B M] [IsScalarTower A B M] in
/-- The left multiplication `B ⊗ (B ⊗ M) → B ⊗ M` is a retraction of
`assoc ∘ (ins₁ ⊗ M)`. -/
lemma descentMul_assoc_rTensor (x : B ⊗[A] M) :
    descentMul A B (B ⊗[A] M)
      (TensorProduct.assoc A B B M (LinearMap.rTensor M (descentInsLeft A B) x)) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy]

lemma tau_descentMul_tau (m : M) : D.τ (descentMul A B M (D.τ m)) = D.τ m := by
  have h := congrArg (descentMul A B (B ⊗[A] M)) (D.cocycle m)
  rw [descentMul_assoc_rTensor] at h
  calc D.τ (descentMul A B M (D.τ m))
      = descentMul A B (B ⊗[A] M) (LinearMap.lTensor B D.τ (D.τ m)) :=
        (LinearMap.congr_fun D.descentMul_comp_lTensor_tau (D.τ m)).symm
    _ = D.τ m := h

/-- The coaction `τ` of a descent datum is injective (no flatness needed): it factors as the
split injection `m ↦ m ⊗ 1` followed by the bijection `descentToPhi τ`. -/
theorem tau_injective : Function.Injective D.τ := by
  have h1 : Function.Injective (fun m : M => m ⊗ₜ[A] (1 : B)) := by
    intro m m' h
    have := congrArg (descentMul A B M ∘ TensorProduct.comm A M B) h
    simpa using this
  have : (D.τ : M → B ⊗[A] M) = descentToPhi A B M D.τ ∘ fun m => m ⊗ₜ[A] (1 : B) := by
    funext m
    simp
  rw [this]
  exact D.bijective.1.comp h1

/-- Lemma F1.a (unit law): `μ (τ m) = m`, where `μ : B ⊗[A] M → M` is `b ⊗ m ↦ b • m`.
No flatness is needed. -/
theorem smul_tensor_eq_self (m : M) : descentMul A B M (D.τ m) = m :=
  D.tau_injective (D.tau_descentMul_tau m)

omit [Module B M] [IsScalarTower A B M] in
lemma lTensor_descentUnitTensor_eq :
    LinearMap.lTensor B (descentUnitTensor A B M) =
      (TensorProduct.assoc A B B M).toLinearMap ∘ₗ
        LinearMap.rTensor M (descentInsLeft A B) := by
  ext b m
  simp

/-- Lemma F1.b: `τ` lands in the equalizer of `B ⊗ τ` and `B ⊗ ι`. -/
theorem tau_mem_ker (m : M) :
    D.τ m ∈ LinearMap.ker
      (LinearMap.lTensor B D.τ - LinearMap.lTensor B (descentUnitTensor A B M)) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, D.cocycle m,
    lTensor_descentUnitTensor_eq]
  rfl

lemma liftBaseChange_subtype_eq (x : B ⊗[A] D.descended) :
    LinearMap.liftBaseChange B D.descended.subtype x =
      descentMul A B M (LinearMap.lTensor B D.descended.subtype x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => simp
  | add x y hx hy => simp only [map_add, hx, hy]

lemma tau_liftBaseChange_subtype (x : B ⊗[A] D.descended) :
    D.τ (LinearMap.liftBaseChange B D.descended.subtype x) =
      LinearMap.lTensor B D.descended.subtype x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
    have hn := (D.mem_descended_iff n).1 n.2
    simp [D.τ_smul, hn, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy]

section Flat

variable [Module.Flat A B]

/-- Lemma F1.c (injectivity): for `B` flat over `A`, `B ⊗ descended τ → B ⊗ M` is injective. -/
theorem lTensor_subtype_injective :
    Function.Injective (LinearMap.lTensor B D.descended.subtype) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ D.descended.injective_subtype

/-- Lemma F1.c (exactness): for `B` flat over `A`, the image of `B ⊗ descended τ → B ⊗ M` is
the equalizer of `B ⊗ τ` and `B ⊗ ι`. -/
theorem range_lTensor_subtype_eq_ker :
    LinearMap.range (LinearMap.lTensor B D.descended.subtype) = LinearMap.ker
      (LinearMap.lTensor B D.τ - LinearMap.lTensor B (descentUnitTensor A B M)) := by
  have := Module.Flat.lTensor_exact B
    (LinearMap.exact_subtype_ker_map (D.τ - descentUnitTensor A B M))
  rw [LinearMap.lTensor_sub] at this
  exact this.linearMap_ker_eq.symm

/-- The inverse `δ : M → B ⊗[A] descended τ` of the descent isomorphism, characterised by
`(B ⊗ incl) (δ m) = τ m` (`lTensor_subtype_descentInv`). Needs `B` flat over `A`. -/
noncomputable def descentInv : M →ₗ[A] B ⊗[A] D.descended :=
  (LinearEquiv.ofInjective _ D.lTensor_subtype_injective).symm.toLinearMap ∘ₗ
    D.τ.codRestrict (LinearMap.range (LinearMap.lTensor B D.descended.subtype))
      (fun m => by rw [range_lTensor_subtype_eq_ker]; exact D.tau_mem_ker m)

@[simp]
lemma lTensor_subtype_descentInv (m : M) :
    LinearMap.lTensor B D.descended.subtype (D.descentInv m) = D.τ m := by
  simp [descentInv]

/-- **Theorem F1** (effective flat descent of modules). For `B` flat over `A` and a descent
datum `D` on the `B`-module `M`, the map `B ⊗[A] descended D → M`, `b ⊗ n ↦ b • n`, is a
`B`-linear isomorphism. -/
noncomputable def descentEquiv : B ⊗[A] D.descended ≃ₗ[B] M :=
  { LinearMap.liftBaseChange B D.descended.subtype with
    invFun := D.descentInv
    left_inv := fun x => by
      apply D.lTensor_subtype_injective
      change LinearMap.lTensor B D.descended.subtype
        (D.descentInv (LinearMap.liftBaseChange B D.descended.subtype x)) = _
      rw [lTensor_subtype_descentInv, tau_liftBaseChange_subtype]
    right_inv := fun m => by
      change LinearMap.liftBaseChange B D.descended.subtype (D.descentInv m) = m
      rw [liftBaseChange_subtype_eq, lTensor_subtype_descentInv, smul_tensor_eq_self] }

@[simp]
lemma descentEquiv_tmul (b : B) (n : D.descended) :
    D.descentEquiv (b ⊗ₜ[A] n) = b • (n : M) := rfl

lemma descentEquiv_symm_apply (m : M) : D.descentEquiv.symm m = D.descentInv m := rfl

@[simp]
lemma lTensor_subtype_descentEquiv_symm (m : M) :
    LinearMap.lTensor B D.descended.subtype (D.descentEquiv.symm m) = D.τ m :=
  D.lTensor_subtype_descentInv m

end Flat

section Canonical

variable (A B)
variable (N : Type*) [AddCommGroup N] [Module A N]

/-- The canonical descent datum on `B ⊗[A] N`: `τ (b ⊗ n) = b ⊗ (1 ⊗ n)`. Its associated map
`(B ⊗ N) ⊗ B → B ⊗ (B ⊗ N)` is the swap `(b ⊗ n) ⊗ b' ↦ b ⊗ (b' ⊗ n)`. -/
noncomputable def canonical : DescentDatum A B (B ⊗[A] N) where
  τ := LinearMap.lTensor B (descentUnitTensor A B N)
  τ_smul b x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b' n => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  cocycle x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b' n => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  bijective := by
    have : descentToPhi A B (B ⊗[A] N) (LinearMap.lTensor B (descentUnitTensor A B N)) =
        ((TensorProduct.assoc A B N B).trans
          (LinearEquiv.lTensor B (TensorProduct.comm A N B))).toLinearMap := by
      apply TensorProduct.ext_threefold
      intro b n b'
      simp [TensorProduct.smul_tmul']
    rw [this]
    exact LinearEquiv.bijective _

@[simp]
lemma canonical_τ_tmul (b : B) (n : N) :
    (canonical A B N).τ (b ⊗ₜ[A] n) = b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] n) := rfl

/-- `N`, embedded in `B ⊗[A] N` by `n ↦ 1 ⊗ n`, lies in the descended module of the canonical
datum. -/
theorem range_unitTensor_le_descended_canonical :
    LinearMap.range (descentUnitTensor A B N) ≤ (canonical A B N).descended := by
  rintro _ ⟨n, rfl⟩
  rw [mem_descended_iff]
  rfl

omit [Module B M] [IsScalarTower A B M] in
/-- The contracting homotopy for the Amitsur complex `N → B ⊗ N ⇉ B ⊗ (B ⊗ N)` after base
change along `A → B`. -/
lemma canonical_homotopy :
    LinearMap.lTensor B (descentUnitTensor A B N) ∘ₗ descentMul A B (B ⊗[A] N) -
      descentMul A B (B ⊗[A] (B ⊗[A] N)) ∘ₗ LinearMap.lTensor B
        ((canonical A B N).τ - descentUnitTensor A B (B ⊗[A] N)) = LinearMap.id := by
  apply TensorProduct.ext_threefold'
  intro b b' n
  simp [TensorProduct.smul_tmul', canonical]

omit [Module B M] [IsScalarTower A B M] in
/-- Corollary F1.d: for `B` faithfully flat over `A`, the descended module of the canonical
datum on `B ⊗[A] N` is exactly the image of `N` under `n ↦ 1 ⊗ n`. -/
theorem descended_canonical_eq_range [Module.FaithfullyFlat A B] :
    (canonical A B N).descended = LinearMap.range (descentUnitTensor A B N) := by
  have hex : Function.Exact (descentUnitTensor A B N)
      ((canonical A B N).τ - descentUnitTensor A B (B ⊗[A] N)) := by
    refine Module.FaithfullyFlat.lTensor_reflects_exact A B _ _ ?_
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      refine ⟨descentMul A B (B ⊗[A] N) x, ?_⟩
      have key := LinearMap.congr_fun (canonical_homotopy A B N) x
      rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.mem_ker.1 hx, map_zero, sub_zero] at key
      exact key
    · rintro _ ⟨y, rfl⟩
      have h0 : ((canonical A B N).τ - descentUnitTensor A B (B ⊗[A] N)) ∘ₗ
          descentUnitTensor A B N = 0 := by
        ext n
        simp [canonical]
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0]
      simp
  exact hex.linearMap_ker_eq

end Canonical

end DescentDatum

end GromovWitten.Algebra
