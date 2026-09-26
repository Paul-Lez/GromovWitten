/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.Clutching.AffineScheme
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Arbitrary coefficient base change for affine clutching

The affine pinching algebra commutes with arbitrary extension of the coefficient ring.  The
comparison map is written using the actual tensor products and its inverse is the branchwise
decomposition formula.  No flatness assumption on the coefficient extension is needed.
-/

open _root_.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace GromovWitten
namespace AlgebraicGeometry
namespace Curves
namespace Clutching

universe u

noncomputable section

variable {R S A B : Type u}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R S] [Algebra R A] [Algebra R B]

namespace fiberProduct

variable (εA : A →ₐ[R] R) (εB : B →ₐ[R] R)

local notation "P" => fiberProduct εA εB
local notation "AS" => S ⊗[R] A
local notation "BS" => S ⊗[R] B
local notation "PS" => S ⊗[R] P

/-- Extension of scalars of an algebra map, with the coefficient ring in the left tensor factor. -/
def baseChangeMap {C D : Type u} [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] (f : C →ₐ[R] D) :
    S ⊗[R] C →ₐ[S] S ⊗[R] D :=
  Algebra.TensorProduct.map (R := R) (S := S) (AlgHom.id S S) f

@[simp]
theorem baseChangeMap_tmul {C D : Type u} [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] (f : C →ₐ[R] D) (s : S) (c : C) :
    baseChangeMap (S := S) f (s ⊗ₜ[R] c) = s ⊗ₜ[R] f c := by
  simp [baseChangeMap]

/-- The augmentation after extension of scalars. -/
def baseChangeAugmentation : AS →ₐ[S] S :=
  Algebra.TensorProduct.lift (AlgHom.id S S) ((Algebra.ofId R S).comp εA)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem baseChangeAugmentation_tmul (s : S) (a : A) :
    baseChangeAugmentation (εA := εA) (s ⊗ₜ[R] a) = s * algebraMap R S (εA a) := by
  simp [baseChangeAugmentation]

@[simp]
theorem baseChangeAugmentation_includeRight (a : A) :
    baseChangeAugmentation (εA := εA) (Algebra.TensorProduct.includeRight a) =
      algebraMap R S (εA a) := by
  rw [Algebra.TensorProduct.includeRight_apply]
  simp [baseChangeAugmentation]

private def branchSectionA : A →ₐ[R] P where
  toFun a := ⟨(a, algebraMap R B (εA a)), by simp⟩
  map_one' := by apply Subtype.ext; ext <;> simp
  map_mul' a b := by apply Subtype.ext; ext <;> simp
  map_zero' := by apply Subtype.ext; ext <;> simp
  map_add' a b := by apply Subtype.ext; ext <;> simp
  commutes' r := by apply Subtype.ext; ext <;> simp

private def branchSectionB : B →ₐ[R] P where
  toFun b := ⟨(algebraMap R A (εB b), b), by simp⟩
  map_one' := by apply Subtype.ext; ext <;> simp
  map_mul' a b := by apply Subtype.ext; ext <;> simp
  map_zero' := by apply Subtype.ext; ext <;> simp
  map_add' a b := by apply Subtype.ext; ext <;> simp
  commutes' r := by apply Subtype.ext; ext <;> simp

private theorem branchSectionA_fst :
    (fst εA εB).comp (branchSectionA εA εB) = AlgHom.id R A := by
  ext a
  rfl

private theorem branchSectionA_snd : (snd εA εB).comp (branchSectionA εA εB) =
    (Algebra.ofId R B).comp εA := by
  ext a
  rfl

private theorem branchSectionB_fst : (fst εA εB).comp (branchSectionB εA εB) =
    (Algebra.ofId R A).comp εB := by
  ext b
  rfl

private theorem branchSectionB_snd :
    (snd εA εB).comp (branchSectionB εA εB) = AlgHom.id R B := by
  ext b
  rfl

private def branchSectionA_s : AS →ₐ[S] PS :=
  baseChangeMap (S := S) (branchSectionA εA εB)

private def branchSectionB_s : BS →ₐ[S] PS :=
  baseChangeMap (S := S) (branchSectionB εA εB)

private theorem branchSectionA_s_fst :
    (baseChangeMap (S := S) (fst εA εB)).comp (branchSectionA_s εA εB) = AlgHom.id S AS := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      change s ⊗ₜ[R] a = s ⊗ₜ[R] a
      rfl
  | add x y hx hy =>
      rw [map_add, hx, hy]
      simp

private theorem branchSectionA_s_snd :
    (baseChangeMap (S := S) (snd εA εB)).comp (branchSectionA_s εA εB) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := S) (A := S) (B := B)).comp
        (baseChangeAugmentation (εA := εA)) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      change s ⊗ₜ[R] algebraMap R B (εA a) =
        (s * algebraMap R S (εA a)) ⊗ₜ[R] 1
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
      simp [Algebra.smul_def, mul_comm]
  | add x y hx hy =>
      rw [map_add, hx, hy, map_add]

private theorem branchSectionB_s_fst :
    (baseChangeMap (S := S) (fst εA εB)).comp (branchSectionB_s εA εB) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := S) (A := S) (B := A)).comp
        (baseChangeAugmentation (εA := εB)) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
      change s ⊗ₜ[R] algebraMap R A (εB b) =
        (s * algebraMap R S (εB b)) ⊗ₜ[R] 1
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
      simp [Algebra.smul_def, mul_comm]
  | add x y hx hy =>
      rw [map_add, hx, hy, map_add]

private theorem branchSectionB_s_snd :
    (baseChangeMap (S := S) (snd εA εB)).comp (branchSectionB_s εA εB) = AlgHom.id S BS := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
      change s ⊗ₜ[R] b = s ⊗ₜ[R] b
      rfl
  | add x y hx hy =>
      rw [map_add, hx, hy]
      simp

private theorem baseChange_condition :
    (baseChangeAugmentation (εA := εA)).comp
        (baseChangeMap (S := S) (fst εA εB)) =
      (baseChangeAugmentation (εA := εB)).comp
        (baseChangeMap (S := S) (snd εA εB)) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s p =>
      change s * algebraMap R S (εA p.1.1) = s * algebraMap R S (εB p.1.2)
      have hp : εA p.1.1 = εB p.1.2 := by
        simpa only [fst_apply, snd_apply] using (condition εA εB p)
      rw [hp]
  | add x y hx hy =>
      rw [map_add, hx, hy]
      simp

/-- The scalar-extended fibre product of the two branches. -/
abbrev baseChangedFiberProduct : Subalgebra S (AS × BS) :=
  fiberProduct (baseChangeAugmentation (εA := εA))
    (baseChangeAugmentation (εA := εB))

local notation "P'" => baseChangedFiberProduct (S := S) εA εB

/-- The canonical comparison map from the scalar extension of the pinching algebra. -/
def comparison : PS →ₐ[S] P' :=
  fiberProduct.lift (R := S) (A := AS) (B := BS) (C := PS)
    (baseChangeAugmentation (εA := εA)) (baseChangeAugmentation (εA := εB))
    (baseChangeMap (S := S) (fst εA εB))
    (baseChangeMap (S := S) (snd εA εB))
    (baseChange_condition (S := S) εA εB)

@[simp]
theorem comparison_fst :
    (fst (baseChangeAugmentation (εA := εA))
      (baseChangeAugmentation (εA := εB))).comp (comparison (S := S) εA εB) =
      baseChangeMap (S := S) (fst εA εB) := by
  simpa only [comparison] using (fiberProduct.lift_fst (R := S) (A := AS) (B := BS) (C := PS)
    (baseChangeAugmentation (εA := εA)) (baseChangeAugmentation (εA := εB))
    (baseChangeMap (S := S) (fst εA εB)) (baseChangeMap (S := S) (snd εA εB))
    (baseChange_condition (S := S) εA εB))

@[simp]
theorem comparison_snd :
    (snd (baseChangeAugmentation (εA := εA))
      (baseChangeAugmentation (εA := εB))).comp (comparison (S := S) εA εB) =
      baseChangeMap (S := S) (snd εA εB) := by
  simpa only [comparison] using (fiberProduct.lift_snd (R := S) (A := AS) (B := BS) (C := PS)
    (baseChangeAugmentation (εA := εA)) (baseChangeAugmentation (εA := εB))
    (baseChangeMap (S := S) (fst εA εB)) (baseChangeMap (S := S) (snd εA εB))
    (baseChange_condition (S := S) εA εB))

@[simp]
theorem comparison_tmul (s : S) (p : P) :
    comparison (S := S) εA εB (s ⊗ₜ[R] p) =
      ⟨(s ⊗ₜ[R] fst εA εB p, s ⊗ₜ[R] snd εA εB p), by
        change s * algebraMap R S (εA p.1.1) = s * algebraMap R S (εB p.1.2)
        have hp : εA p.1.1 = εB p.1.2 := by
          simpa only [fst_apply, snd_apply] using (condition εA εB p)
        rw [hp]⟩ := by
  apply Subtype.ext
  rfl

private def comparisonInvFun : P' → PS := fun x =>
  branchSectionA_s εA εB x.1.1 + branchSectionB_s εA εB x.1.2 -
    algebraMap S PS (baseChangeAugmentation (εA := εA) x.1.1)

private theorem branch_decomposition (p : P) :
    branchSectionA εA εB p.1.1 + branchSectionB εA εB p.1.2 -
        algebraMap R P (εA p.1.1) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change p.1.1 + algebraMap R A (εB p.1.2) -
      algebraMap R A (εA p.1.1) = p.1.1
    have hp : εA p.1.1 = εB p.1.2 := by
      simpa only [fst_apply, snd_apply] using (condition εA εB p)
    rw [← hp]
    abel
  · change algebraMap R B (εA p.1.1) + p.1.2 -
      algebraMap R B (εA p.1.1) = p.1.2
    abel

private theorem comparisonInvFun_add (x y : P') :
    comparisonInvFun (S := S) εA εB (x + y) =
      comparisonInvFun (S := S) εA εB x + comparisonInvFun (S := S) εA εB y := by
  simp only [comparisonInvFun, map_add, Subalgebra.coe_add, Prod.fst_add, Prod.snd_add]
  abel

private theorem comparisonInvFun_tmul (s : S) (p : P) :
    comparisonInvFun (S := S) εA εB
        (comparison (S := S) εA εB (s ⊗ₜ[R] p)) = s ⊗ₜ[R] p := by
  rw [comparison_tmul]
  change
    (s ⊗ₜ[R] branchSectionA εA εB p.1.1) +
        (s ⊗ₜ[R] branchSectionB εA εB p.1.2) -
      algebraMap S PS (s * algebraMap R S (εA p.1.1)) = s ⊗ₜ[R] p
  rw [Algebra.TensorProduct.algebraMap_apply]
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  have hmul :
      (s * algebraMap R S (εA p.1.1)) ⊗ₜ[R] (1 : P) =
        (s ⊗ₜ[R] (1 : P)) *
          (algebraMap R S (εA p.1.1) ⊗ₜ[R] (1 : P)) := by
    symm
    convert Algebra.TensorProduct.tmul_mul_tmul (R := R) s
      (algebraMap R S (εA p.1.1)) (1 : P) (1 : P) using 1
    simp
  rw [hmul]
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_one, one_mul]
  rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub]
  exact congrArg (fun q : P => s ⊗ₜ[R] q) (branch_decomposition εA εB p)

private theorem comparisonInvFun_comparison (z : PS) :
    comparisonInvFun (S := S) εA εB (comparison (S := S) εA εB z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [comparisonInvFun]
  | tmul s p => exact comparisonInvFun_tmul (S := S) εA εB s p
  | add x y hx hy =>
      rw [map_add, comparisonInvFun_add, hx, hy]

private theorem comparison_comparisonInvFun (x : P') :
    comparison (S := S) εA εB (comparisonInvFun (S := S) εA εB x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · change
      (baseChangeMap (S := S) (fst εA εB))
          (branchSectionA_s εA εB x.1.1 + branchSectionB_s εA εB x.1.2 -
            algebraMap S PS (baseChangeAugmentation (εA := εA) x.1.1)) = x.1.1
    simp only [map_add, map_sub]
    have hA :
        (baseChangeMap (S := S) (fst εA εB))
            (branchSectionA_s εA εB x.1.1) = x.1.1 := by
      exact DFunLike.congr_fun (branchSectionA_s_fst (S := S) εA εB) x.1.1
    have hB :
        (baseChangeMap (S := S) (fst εA εB))
            (branchSectionB_s εA εB x.1.2) =
          (Algebra.TensorProduct.includeLeft (R := R) (S := S) (A := S) (B := A))
            (baseChangeAugmentation (εA := εB) x.1.2) := by
      exact DFunLike.congr_fun (branchSectionB_s_fst (S := S) εA εB) x.1.2
    have hc := (baseChangeMap (S := S) (fst εA εB)).commutes
      (baseChangeAugmentation (εA := εA) x.1.1)
    rw [hA, hB, hc]
    simp only [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    have hx := x.2
    change baseChangeAugmentation (εA := εA) x.1.1 =
      baseChangeAugmentation (εA := εB) x.1.2 at hx
    have hx' := congrArg (fun t : S => t ⊗ₜ[R] (1 : A)) hx
    change x.1.1 +
      (baseChangeAugmentation (εA := εB) x.1.2 ⊗ₜ[R] (1 : A)) -
        (baseChangeAugmentation (εA := εA) x.1.1 ⊗ₜ[R] (1 : A)) = x.1.1
    rw [hx']
    abel
  · change
      (baseChangeMap (S := S) (snd εA εB))
          (branchSectionA_s εA εB x.1.1 + branchSectionB_s εA εB x.1.2 -
            algebraMap S PS (baseChangeAugmentation (εA := εA) x.1.1)) = x.1.2
    simp only [map_add, map_sub]
    have hA :
        (baseChangeMap (S := S) (snd εA εB))
            (branchSectionA_s εA εB x.1.1) =
          (Algebra.TensorProduct.includeLeft (R := R) (S := S) (A := S) (B := B))
            (baseChangeAugmentation (εA := εA) x.1.1) := by
      exact DFunLike.congr_fun (branchSectionA_s_snd (S := S) εA εB) x.1.1
    have hB :
        (baseChangeMap (S := S) (snd εA εB))
            (branchSectionB_s εA εB x.1.2) = x.1.2 := by
      exact DFunLike.congr_fun (branchSectionB_s_snd (S := S) εA εB) x.1.2
    have hc := (baseChangeMap (S := S) (snd εA εB)).commutes
      (baseChangeAugmentation (εA := εA) x.1.1)
    rw [hA, hB, hc]
    simp only [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    have hx := x.2
    change baseChangeAugmentation (εA := εA) x.1.1 =
      baseChangeAugmentation (εA := εB) x.1.2 at hx
    have hx' := congrArg (fun t : S => t ⊗ₜ[R] (1 : B)) hx
    change
      (baseChangeAugmentation (εA := εA) x.1.1 ⊗ₜ[R] (1 : B)) + x.1.2 -
        (baseChangeAugmentation (εA := εA) x.1.1 ⊗ₜ[R] (1 : B)) = x.1.2
    rw [hx']
    abel

/-- Arbitrary coefficient base change preserves the affine pinching algebra. -/
def baseChangeEquiv : PS ≃ₐ[S] P' :=
  AlgEquiv.ofBijective (comparison (S := S) εA εB) (by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have := congrArg (comparisonInvFun (S := S) εA εB) hxy
      simpa only [comparisonInvFun_comparison] using this
    · intro y
      exact ⟨comparisonInvFun (S := S) εA εB y,
        comparison_comparisonInvFun (S := S) εA εB y⟩)

/-- The ring map induced by the canonical comparison after including the original pinching ring. -/
def baseChangeRingHom : P →+* P' :=
  (baseChangeEquiv (S := S) εA εB).toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : P →ₐ[R] PS).toRingHom

/-- The affine base-change square is a genuine pushout square of commutative rings. -/
theorem baseChange_isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap R P))
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (baseChangeRingHom (S := S) εA εB))
      (CommRingCat.ofHom (algebraMap S P')) := by
  refine (CommRingCat.isPushout_tensorProduct R S P).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (baseChangeEquiv (S := S) εA εB).toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    change baseChangeEquiv (S := S) εA εB (s ⊗ₜ[R] (1 : P)) =
      algebraMap S P' s
    have hs := (baseChangeEquiv (S := S) εA εB).commutes s
    rw [Algebra.TensorProduct.algebraMap_apply] at hs
    exact hs

/-- The corresponding affine schemes form a cartesian square. -/
theorem baseChange_isPullback :
    IsPullback
      (Scheme.Spec.map (CommRingCat.ofHom
        (baseChangeRingHom (S := S) εA εB)).op)
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap S P')).op)
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R P)).op)
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (baseChange_isPushout (S := S) εA εB)

@[simp]
theorem baseChangeEquiv_apply (z : PS) :
    baseChangeEquiv (S := S) εA εB z = comparison (S := S) εA εB z := rfl

@[simp]
theorem baseChangeEquiv_tmul (s : S) (p : P) :
    baseChangeEquiv (S := S) εA εB (s ⊗ₜ[R] p) =
      ⟨(s ⊗ₜ[R] fst εA εB p, s ⊗ₜ[R] snd εA εB p), by
        change s * algebraMap R S (εA p.1.1) = s * algebraMap R S (εB p.1.2)
        have hp : εA p.1.1 = εB p.1.2 := by
          simpa only [fst_apply, snd_apply] using (condition εA εB p)
        rw [hp]⟩ := by
  exact comparison_tmul (S := S) εA εB s p

end fiberProduct
end
end Clutching
end Curves
end AlgebraicGeometry
end GromovWitten
