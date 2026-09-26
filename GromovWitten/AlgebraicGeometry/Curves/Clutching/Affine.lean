/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Algebra.Subalgebra.Prod
import Mathlib.Algebra.Exact.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Flat.Basic

/-!
# Affine pinching along a common section

For two `R`-algebras equipped with augmentations to `R`, this file constructs the affine
pinching ring as the literal fibre product subalgebra of the product ring.  The construction is
independent of any scheme-level pushout assertion: the universal property proved here is the
algebraic one, for maps *into* the fibre product.
-/

open _root_.AlgebraicGeometry

namespace GromovWitten
namespace AlgebraicGeometry
namespace Curves
namespace Clutching

universe u

noncomputable section

variable {R A B C : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- The equaliser subalgebra of two augmentations `A →ₐ[R] R` and `B →ₐ[R] R`.

Its underlying ring is the actual subset of `A × B` cut out by the equality of the two
augmentation values. -/
abbrev fiberProduct (εA : A →ₐ[R] R) (εB : B →ₐ[R] R) : Subalgebra R (A × B) :=
  AlgHom.pullback εA εB

namespace fiberProduct

variable (εA : A →ₐ[R] R) (εB : B →ₐ[R] R)

/-- The two canonical algebra maps out of the affine fibre product. -/
def fst : fiberProduct εA εB →ₐ[R] A :=
  AlgHom.pullbackFst εA εB

def snd : fiberProduct εA εB →ₐ[R] B :=
  AlgHom.pullbackSnd εA εB

@[simp]
theorem fst_apply (p : fiberProduct εA εB) : fst εA εB p = p.1.1 := rfl

@[simp]
theorem snd_apply (p : fiberProduct εA εB) : snd εA εB p = p.1.2 := rfl

@[simp]
theorem condition (p : fiberProduct εA εB) : εA (fst εA εB p) = εB (snd εA εB p) :=
  p.2

/-- The universal map into the fibre product. -/
def lift (f : C →ₐ[R] A) (g : C →ₐ[R] B)
    (h : εA.comp f = εB.comp g) : C →ₐ[R] fiberProduct εA εB where
  toFun c := ⟨(f c, g c), by
    change εA (f c) = εB (g c)
    exact DFunLike.congr_fun h c⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp)

@[simp]
theorem lift_fst (f : C →ₐ[R] A) (g : C →ₐ[R] B)
    (h : εA.comp f = εB.comp g) : (fst εA εB).comp (lift εA εB f g h) = f := by
  ext c
  rfl

@[simp]
theorem lift_snd (f : C →ₐ[R] A) (g : C →ₐ[R] B)
    (h : εA.comp f = εB.comp g) : (snd εA εB).comp (lift εA εB f g h) = g := by
  ext c
  rfl

theorem lift_unique (f : C →ₐ[R] A) (g : C →ₐ[R] B)
    (h : εA.comp f = εB.comp g) (k : C →ₐ[R] fiberProduct εA εB)
    (hkf : (fst εA εB).comp k = f) (hkg : (snd εA εB).comp k = g) :
    k = lift εA εB f g h := by
  apply AlgHom.ext
  intro c
  apply Subtype.ext
  apply Prod.ext
  · exact DFunLike.congr_fun hkf c
  · exact DFunLike.congr_fun hkg c

theorem condition_hom : εA.comp (fst εA εB) = εB.comp (snd εA εB) := by
  ext p
  exact p.2

/-- Each projection is onto, using the constant algebra section of the other augmentation. -/
theorem fst_surjective : Function.Surjective (fst εA εB) := by
  intro a
  refine ⟨⟨(a, algebraMap R B (εA a)), ?_⟩, rfl⟩
  exact (εB.commutes (εA a)).symm

theorem snd_surjective : Function.Surjective (snd εA εB) := by
  intro b
  refine ⟨⟨(algebraMap R A (εB b), b), ?_⟩, rfl⟩
  exact εA.commutes (εB b)

/-- The linear map measuring the failure of a pair to satisfy the gluing equation. -/
def difference : A × B →ₗ[R] R :=
  LinearMap.coprod εA.toLinearMap (-εB.toLinearMap)

/-- The inclusion of the fibre product into the ambient product module. -/
def inclusion : fiberProduct εA εB →ₗ[R] A × B :=
  (fiberProduct εA εB).val.toLinearMap

@[simp]
theorem difference_apply (p : A × B) : difference εA εB p = εA p.1 - εB p.2 := by
  simp [difference, LinearMap.coprod_apply, sub_eq_add_neg]

theorem exact : Function.Exact (inclusion εA εB) (difference εA εB) := by
  intro p
  constructor
  · intro hp
    rw [difference_apply] at hp
    let q : fiberProduct εA εB := ⟨p, sub_eq_zero.mp hp⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    have hp' : εA p.1 - εB p.2 = 0 := by
      rw [← hq]
      exact sub_eq_zero.mpr (condition εA εB q)
    simpa only [difference_apply] using hp'

theorem inclusion_injective : Function.Injective (inclusion εA εB) :=
  Subtype.val_injective

theorem difference_surjective : Function.Surjective (difference εA εB) := by
  intro r
  refine ⟨(algebraMap R A r, 0), ?_⟩
  simp [difference]

/-- A section of the difference map, recording the split exact sequence. -/
def differenceSection (_εA : A →ₐ[R] R) (_εB : B →ₐ[R] R) : R →ₗ[R] A × B :=
  (LinearMap.inl R A B).comp (Algebra.ofId R A).toLinearMap

theorem difference_comp_section :
    (difference εA εB).comp (differenceSection εA εB) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  simp [difference, differenceSection]

private theorem moduleFlat_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ Q
  have hM : Function.Injective (LinearMap.lTensor M Q.subtype) :=
    (Module.Flat.iff_lTensor_injectiveₛ.mp (inferInstance : Module.Flat R M) Q)
  have hN : Function.Injective (LinearMap.lTensor N Q.subtype) :=
    (Module.Flat.iff_lTensor_injectiveₛ.mp (inferInstance : Module.Flat R N) Q)
  let eQ := TensorProduct.prodLeft R R M N (↥Q)
  let eP := TensorProduct.prodLeft R R M N P
  have hcomm :
      eP.toLinearMap.comp (LinearMap.lTensor (M × N) Q.subtype) =
        (LinearMap.prodMap (LinearMap.lTensor M Q.subtype)
          (LinearMap.lTensor N Q.subtype)).comp eQ.toLinearMap := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · change (0, 0) = (0, 0)
      rfl
    · intro x q
      dsimp [eQ, eP]
      change (x.1 ⊗ₜ[R] Q.subtype q, x.2 ⊗ₜ[R] Q.subtype q) =
        (x.1 ⊗ₜ[R] Q.subtype q, x.2 ⊗ₜ[R] Q.subtype q)
      rfl
    · intro x y hx hy
      simp only [map_add, LinearMap.comp_apply, LinearMap.prodMap_apply] at *
      rw [hx, hy]
  intro x y hxy
  apply eQ.injective
  have hxy' := congrArg eP.toLinearMap hxy
  change (eP.toLinearMap.comp (LinearMap.lTensor (M × N) Q.subtype)) x =
    (eP.toLinearMap.comp (LinearMap.lTensor (M × N) Q.subtype)) y at hxy'
  rw [hcomm] at hxy'
  apply Prod.ext
  · apply hM
    simpa using congrArg Prod.fst hxy'
  · apply hN
    simpa using congrArg Prod.snd hxy'

private def kernelProjection (ε : A →ₐ[R] R) : A →ₗ[R] LinearMap.ker ε.toLinearMap :=
  { toFun := fun a ↦ ⟨a - algebraMap R A (ε a), by
      change ε (a - algebraMap R A (ε a)) = 0
      simp [sub_eq_add_neg]⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      change (a + b) - algebraMap R A (ε (a + b)) =
        (a - algebraMap R A (ε a)) + (b - algebraMap R A (ε b))
      rw [map_add]
      simp only [map_add]
      abel
    map_smul' := by
      intro r a
      apply Subtype.ext
      change r • a - algebraMap R A (ε (r • a)) =
        r • (a - algebraMap R A (ε a))
      rw [map_smul]
      simp only [Algebra.smul_def, map_mul]
      rw [Algebra.algebraMap_self, RingHom.id_apply]
      rw [mul_sub]
    }

private theorem kernelProjection_comp_subtype (ε : A →ₐ[R] R) :
    (kernelProjection ε).comp (LinearMap.ker ε.toLinearMap).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change a - algebraMap R A (ε a) = a
  have ha := a.property
  change ε (a : A) = 0 at ha
  rw [ha]
  simp

private theorem flat_kernel (ε : A →ₐ[R] R) [Module.Flat R A] :
    Module.Flat R (LinearMap.ker ε.toLinearMap) := by
  apply Module.Flat.of_retract (LinearMap.ker ε.toLinearMap).subtype (kernelProjection ε)
  exact kernelProjection_comp_subtype ε

/-- Explicit decomposition of the pinching ring as the common constant and the two augmentation
kernels.  The subtraction terms are the unique representatives with augmentation zero. -/
def decompose : fiberProduct εA εB ≃ₗ[R]
    R × (LinearMap.ker εA.toLinearMap) × (LinearMap.ker εB.toLinearMap) where
  toFun p :=
    (εA p.1.1,
      (⟨p.1.1 - algebraMap R A (εA p.1.1), by
        change εA (p.1.1 - algebraMap R A (εA p.1.1)) = 0
        simp [sub_eq_add_neg]⟩,
       ⟨p.1.2 - algebraMap R B (εA p.1.1), by
        change εB (p.1.2 - algebraMap R B (εA p.1.1)) = 0
        have hp : εA p.1.1 = εB p.1.2 := by
          simpa [fst, snd] using condition εA εB p
        rw [map_sub, εB.commutes, hp]
        simp⟩))
  invFun x :=
    ⟨(algebraMap R A x.1 + x.2.1,
        algebraMap R B x.1 + x.2.2), by
      change εA (algebraMap R A x.1 + x.2.1) =
        εB (algebraMap R B x.1 + x.2.2)
      have hxA := x.2.1.2
      have hxB := x.2.2.2
      change εA.toLinearMap (x.2.1 : A) = 0 at hxA
      change εB.toLinearMap (x.2.2 : B) = 0 at hxB
      have hxA' : εA (x.2.1 : A) = 0 := hxA
      have hxB' : εB (x.2.2 : B) = 0 := hxB
      rw [map_add, map_add, εA.commutes, εB.commutes,
        hxA', hxB']
      ⟩
  map_add' p q := by
    apply Prod.ext
    · exact map_add εA p.1.1 q.1.1
    · apply Prod.ext
      · apply Subtype.ext
        change (p.1.1 + q.1.1) - algebraMap R A (εA (p.1.1 + q.1.1)) =
          (p.1.1 - algebraMap R A (εA p.1.1)) +
            (q.1.1 - algebraMap R A (εA q.1.1))
        rw [map_add]
        simp only [map_add]
        abel
      · apply Subtype.ext
        change (p.1.2 + q.1.2) - algebraMap R B (εA (p.1.1 + q.1.1)) =
          (p.1.2 - algebraMap R B (εA p.1.1)) +
            (q.1.2 - algebraMap R B (εA q.1.1))
        rw [map_add]
        simp only [map_add]
        abel
  map_smul' r p := by
    apply Prod.ext
    · exact map_smul εA r p.1.1
    · apply Prod.ext
      · apply Subtype.ext
        change r • p.1.1 - algebraMap R A (εA (r • p.1.1)) =
          r • (p.1.1 - algebraMap R A (εA p.1.1))
        rw [map_smul]
        simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
        rw [mul_sub]
      · apply Subtype.ext
        change r • p.1.2 - algebraMap R B (εA (r • p.1.1)) =
          r • (p.1.2 - algebraMap R B (εA p.1.1))
        rw [map_smul]
        simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
        rw [mul_sub]
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change algebraMap R A (εA p.1.1) +
        (p.1.1 - algebraMap R A (εA p.1.1)) = p.1.1
      abel
    · change algebraMap R B (εA p.1.1) +
        (p.1.2 - algebraMap R B (εA p.1.1)) = p.1.2
      abel
  right_inv x := by
    have hxA := x.2.1.2
    have hxB := x.2.2.2
    change εA.toLinearMap (x.2.1 : A) = 0 at hxA
    change εB.toLinearMap (x.2.2 : B) = 0 at hxB
    have hxA' : εA (x.2.1 : A) = 0 := hxA
    have hvalA : εA (algebraMap R A x.1 + x.2.1) = algebraMap R R x.1 := by
      rw [map_add, εA.commutes, hxA']
      simp
    apply Prod.ext
    · simpa [map_add, εA.commutes, hxA, Algebra.algebraMap_self]
    · apply Prod.ext
      · apply Subtype.ext
        change algebraMap R A x.1 + x.2.1 -
          algebraMap R A (εA (algebraMap R A x.1 + x.2.1)) = x.2.1
        rw [hvalA, Algebra.algebraMap_self, RingHom.id_apply]
        abel
      · apply Subtype.ext
        change algebraMap R B x.1 + x.2.2 -
          algebraMap R B (εA (algebraMap R A x.1 + x.2.1)) = x.2.2
        rw [hvalA, Algebra.algebraMap_self, RingHom.id_apply]
        abel

theorem decompose_apply (p : fiberProduct εA εB) :
    decompose εA εB p =
      (εA p.1.1,
        (⟨p.1.1 - algebraMap R A (εA p.1.1), by
          change εA (p.1.1 - algebraMap R A (εA p.1.1)) = 0
          simp [sub_eq_add_neg]⟩,
         ⟨p.1.2 - algebraMap R B (εA p.1.1), by
          change εB (p.1.2 - algebraMap R B (εA p.1.1)) = 0
          have hp : εA p.1.1 = εB p.1.2 := by
            simpa [fst, snd] using condition εA εB p
          rw [map_sub, εB.commutes, hp]
          simp⟩)) := rfl

theorem flat [Module.Flat R A] [Module.Flat R B] :
    Module.Flat R (fiberProduct εA εB) := by
  let _ : Module.Flat R (LinearMap.ker εA.toLinearMap) := flat_kernel εA
  let _ : Module.Flat R (LinearMap.ker εB.toLinearMap) := flat_kernel εB
  let _ : Module.Flat R (LinearMap.ker εA.toLinearMap × LinearMap.ker εB.toLinearMap) :=
    moduleFlat_prod
  let _ : Module.Flat R
      (R × (LinearMap.ker εA.toLinearMap × LinearMap.ker εB.toLinearMap)) :=
    moduleFlat_prod
  exact Module.Flat.of_linearEquiv (decompose εA εB)

theorem split_exact :
    List.TFAE [
      ∃ l, (difference εA εB) ∘ₗ l = LinearMap.id,
      ∃ l, l ∘ₗ (inclusion εA εB) = LinearMap.id,
      ∃ e : (A × B) ≃ₗ[R] (fiberProduct εA εB) × R,
        inclusion εA εB = e.symm.toLinearMap ∘ₗ LinearMap.inl R _ _ ∧
          difference εA εB = LinearMap.snd R _ _ ∘ₗ e.toLinearMap] := by
  exact Function.Exact.split_tfae (exact εA εB) (inclusion_injective εA εB)
    (difference_surjective εA εB)

/-- The affine closed immersion induced by the first projection. -/
def specFst : Spec (.of A) ⟶ Spec (.of (fiberProduct εA εB)) :=
  Scheme.Spec.map (CommRingCat.ofHom (fst εA εB).toRingHom).op

/-- The affine closed immersion induced by the second projection. -/
def specSnd : Spec (.of B) ⟶ Spec (.of (fiberProduct εA εB)) :=
  Scheme.Spec.map (CommRingCat.ofHom (snd εA εB).toRingHom).op

instance specFst_isClosedImmersion : IsClosedImmersion (specFst εA εB) :=
  IsClosedImmersion.spec_of_surjective _ (fst_surjective εA εB)

instance specSnd_isClosedImmersion : IsClosedImmersion (specSnd εA εB) :=
  IsClosedImmersion.spec_of_surjective _ (snd_surjective εA εB)

end fiberProduct
end

end Clutching
end Curves
end AlgebraicGeometry
end GromovWitten
