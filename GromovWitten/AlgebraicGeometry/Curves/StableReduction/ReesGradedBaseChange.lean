/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBlowupGlobal
import GromovWitten.AlgebraicGeometry.ProjBaseChange

/-!
# Graded Rees base change

The affine Rees algebra is graded by the powers of the center ideal.  This file supplies the
submodule-valued version of that grading required by relative `Proj`, identifies each homogeneous
piece with the corresponding ideal power, and proves the resulting graded base-change theorem
under flat scalar extension.
-/
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Polynomial
namespace GromovWitten.AlgebraicGeometry
open scoped DirectSum
open ReesBlowup
universe u
noncomputable section
variable {R : Type u} [CommRing R]
open ReesBlowup

def gradeSubmodule (I : Ideal R) (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := grade I n
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' := by
    intro a f hf
    rw [Algebra.smul_def]
    change ((algebraMap R (reesAlgebra I) a * f : reesAlgebra I) : R[X]) = _
    change C a * (f : R[X]) = _
    rw [hf]
    simp

def componentSubmodule (I : Ideal R) (f : reesAlgebra I) (n : ℕ) : gradeSubmodule I n :=
  ⟨component I f n, (component I f n).property⟩

noncomputable def decomposeFunSubmodule (I : Ideal R) (f : reesAlgebra I) :
    (⨁ n : ℕ, gradeSubmodule I n) :=
  DirectSum.mk (fun n : ℕ ↦ gradeSubmodule I n) (f : R[X]).support
    (fun n ↦ componentSubmodule I f n)

@[simp] theorem decomposeFunSubmodule_apply (I : Ideal R) (f : reesAlgebra I) (n : ℕ) :
    decomposeFunSubmodule I f n = componentSubmodule I f n := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  by_cases hn : n ∈ (f : R[X]).support
  · exact congr_arg (fun x : gradeSubmodule I n ↦ ((x : reesAlgebra I) : R[X])
      ) (DirectSum.mk_apply_of_mem hn)
  · unfold decomposeFunSubmodule
    rw [DirectSum.mk_apply_of_notMem hn]
    have hcoeff : (f : R[X]).coeff n = 0 := by
      simpa only [mem_support_iff, not_not] using hn
    simp [componentSubmodule, component, hcoeff]

noncomputable def decomposeAddHomSubmodule (I : Ideal R) :
    reesAlgebra I →+ (⨁ n : ℕ, gradeSubmodule I n) where
  toFun := decomposeFunSubmodule I
  map_zero' := by
    apply DFinsupp.ext
    intro n
    rw [decomposeFunSubmodule_apply]
    apply Subtype.ext
    apply Subtype.ext
    simp [componentSubmodule, component]
  map_add' f g := by
    apply DFinsupp.ext
    intro n
    rw [decomposeFunSubmodule_apply]
    rw [DFinsupp.add_apply, decomposeFunSubmodule_apply, decomposeFunSubmodule_apply]
    apply Subtype.ext
    apply Subtype.ext
    ext m
    simp [componentSubmodule, component, coeff_monomial]

@[simp] theorem coe_decomposeAddHomSubmodule_component (I : Ideal R) (f : reesAlgebra I) (n : ℕ) :
    (((decomposeAddHomSubmodule I f) n : gradeSubmodule I n) : reesAlgebra I) =
      component I f n := by
  exact congr_arg Subtype.val (decomposeFunSubmodule_apply I f n)

theorem recompose_decomposeAddHomSubmodule (I : Ideal R) :
    (DirectSum.coeAddMonoidHom (gradeSubmodule I)).comp (decomposeAddHomSubmodule I) =
      AddMonoidHom.id _ := by
  classical
  apply AddMonoidHom.ext
  intro f
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  apply Subtype.ext
  have hs : (decomposeAddHomSubmodule I f).support = (f : R[X]).support := by
    ext n
    rw [DFinsupp.mem_support_iff, mem_support_iff]
    have hz : (decomposeAddHomSubmodule I f) n = 0 ↔ (f : R[X]).coeff n = 0 := by
      rw [show (decomposeAddHomSubmodule I f) n = componentSubmodule I f n from
        decomposeFunSubmodule_apply I f n]
      constructor
      · intro h
        have h' := congr_arg
          (fun x : gradeSubmodule I n ↦ (((x : reesAlgebra I) : R[X]).coeff n)) h
        simpa [componentSubmodule, component] using h'
      · intro h
        apply Subtype.ext
        apply Subtype.ext
        simp [componentSubmodule, component, h]
    exact not_congr hz
  rw [DFinsupp.sum, hs]
  rw [AddSubmonoidClass.coe_finsetSum]
  simp_rw [coe_decomposeAddHomSubmodule_component, component_coe]
  exact (as_sum_support (f : R[X])).symm

theorem decomposeAddHomSubmodule_recompose (I : Ideal R) :
    (decomposeAddHomSubmodule I).comp (DirectSum.coeAddMonoidHom (gradeSubmodule I)) =
      AddMonoidHom.id _ := by
  apply DirectSum.addHom_ext'
  intro n
  apply AddMonoidHom.ext
  intro f
  simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
    AddMonoidHom.id_apply]
  apply DFinsupp.ext
  intro m
  change decomposeFunSubmodule I (f : reesAlgebra I) m =
    (DirectSum.of (fun i : ℕ ↦ gradeSubmodule I i) n f) m
  rw [decomposeFunSubmodule_apply]
  apply Subtype.ext
  apply Subtype.ext
  rw [componentSubmodule, component_coe, f.property]
  by_cases hmn : n = m
  · subst m
    rw [DirectSum.of_eq_same]
    simpa using f.property.symm
  · have hzero : (DirectSum.of (fun i : ℕ ↦ gradeSubmodule I i) n f) m = 0 :=
      DirectSum.of_eq_of_ne _ _ _ (fun h ↦ hmn h.symm)
    rw [hzero]
    rw [@coeff_monomial_of_ne R _ m n ((f : R[X]).coeff n) (fun h ↦ hmn h.symm)]
    simp

noncomputable instance decompositionSubmodule (I : Ideal R) :
    DirectSum.Decomposition (gradeSubmodule I) :=
  DirectSum.Decomposition.ofAddHom (gradeSubmodule I) (decomposeAddHomSubmodule I)
    (recompose_decomposeAddHomSubmodule I) (decomposeAddHomSubmodule_recompose I)

noncomputable instance gradedAlgebraSubmodule (I : Ideal R) :
    GradedAlgebra (gradeSubmodule I) where
  toGradedMonoid := {
    one_mem := by
      change (1 : reesAlgebra I) ∈ grade I 0
      exact (gradedMonoid I).one_mem
    mul_mem := by
      intro i j f g hf hg
      change f ∈ grade I i at hf
      change g ∈ grade I j at hg
      change f * g ∈ grade I (i + j)
      exact (gradedMonoid I).mul_mem hf hg }
  toDecomposition := decompositionSubmodule I

end
end GromovWitten.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.ReesBaseChange

universe u
variable {R : Type u} [CommRing R]

def gradeCoeffRaw (I : Ideal R) (n : ℕ) (f : gradeSubmodule I n) : R :=
  ((f : reesAlgebra I) : R[X]).coeff n

theorem gradeCoeffRaw_mem (I : Ideal R) (n : ℕ) (f : gradeSubmodule I n) :
    gradeCoeffRaw I n f ∈ I ^ n := by
  exact ((mem_reesAlgebra_iff I ((f : reesAlgebra I) : R[X])).mp
      (f : reesAlgebra I).property) n

noncomputable def homogeneousGradeRaw (I : Ideal R) (n : ℕ) (c : R) :
    gradeSubmodule I n :=
  ⟨AlgebraicGeometry.ReesBlowup.homogeneousMonomial I n c, by
    change AlgebraicGeometry.ReesBlowup.homogeneousMonomial I n c ∈
      AlgebraicGeometry.ReesBlowup.grade I n
    exact AlgebraicGeometry.ReesBlowup.homogeneousMonomial_mem_grade I n c⟩

theorem homogeneousGrade_gradeCoeff (I : Ideal R) (n : ℕ) (f : gradeSubmodule I n) :
    homogeneousGradeRaw I n (gradeCoeffRaw I n f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  change ((AlgebraicGeometry.ReesBlowup.homogeneousMonomial I n
      (gradeCoeffRaw I n f) : reesAlgebra I) : R[X]) =
    ((f : reesAlgebra I) : R[X])
  rw [AlgebraicGeometry.ReesBlowup.homogeneousMonomial_coe I n _
    (gradeCoeffRaw_mem I n f)]
  have hf := f.property
  change ((f : reesAlgebra I) : R[X]) =
    monomial n (((f : reesAlgebra I) : R[X]).coeff n) at hf
  exact hf.symm

theorem gradeCoeff_homogeneousGrade (I : Ideal R) (n : ℕ) (c : (I ^ n : Ideal R)) :
    gradeCoeffRaw I n (homogeneousGradeRaw I n c.1) = c.1 := by
  change ((homogeneousGradeRaw I n c.1 : reesAlgebra I) : R[X]).coeff n = c.1
  rw [homogeneousGradeRaw,
    AlgebraicGeometry.ReesBlowup.homogeneousMonomial_coe I n _ c.2]
  simp

noncomputable def gradeCoeffEquiv (I : Ideal R) (n : ℕ) :
    gradeSubmodule I n ≃ₗ[R] (I ^ n : Ideal R) where
  toFun f := ⟨gradeCoeffRaw I n f, gradeCoeffRaw_mem I n f⟩
  invFun c := homogeneousGradeRaw I n c.1
  left_inv f := homogeneousGrade_gradeCoeff I n f
  right_inv c := by
    apply Subtype.ext
    exact gradeCoeff_homogeneousGrade I n c
  map_add' f g := by
    apply Subtype.ext
    simp [gradeCoeffRaw]
  map_smul' a f := by
    apply Subtype.ext
    simp [gradeCoeffRaw, Algebra.smul_def]

end ReesBaseChange
end GromovWitten.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.ReesDegreeBaseChange

open scoped TensorProduct
open AlgebraicGeometry.ReesBlowup
universe u v
noncomputable section
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

theorem idealPowTensorEval_mul_left_exists (I : Ideal A) (n : ℕ) (c : B)
    (w : (I ^ n : Ideal A) ⊗[A] B) :
    ∃ w' : (I ^ n : Ideal A) ⊗[A] B,
      idealPowTensorEval I n w' = c * idealPowTensorEval I n w := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x b =>
      refine ⟨x ⊗ₜ[A] (c * b), ?_⟩
      rw [idealPowTensorEval_tmul, idealPowTensorEval_tmul]
      simp [mul_assoc, mul_comm]
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      refine ⟨x' + y', ?_⟩
      simp [hx', hy', mul_add]

theorem idealPowTensorEval_surjective_range (I : Ideal A) (n : ℕ)
    (b : B) (hb : b ∈ (I.map (algebraMap A B)) ^ n) :
    ∃ w : (I ^ n : Ideal A) ⊗[A] B, idealPowTensorEval I n w = b := by
  rw [← Ideal.map_pow] at hb
  refine Submodule.span_induction
    (p := fun b _ ↦ ∃ w : (I ^ n : Ideal A) ⊗[A] B,
      idealPowTensorEval I n w = b) ?_ ?_ ?_ ?_ hb
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := hb
    refine ⟨(⟨a, ha⟩ ⊗ₜ[A] (1 : B)), ?_⟩
    rw [idealPowTensorEval_tmul]
    change algebraMap A B a * 1 = algebraMap A B a
    simp
  · refine ⟨0, ?_⟩
    simp
  · intro x y _ _ ⟨wx, hx⟩ ⟨wy, hy⟩
    refine ⟨wx + wy, ?_⟩
    simp [hx, hy]
  · intro c x _ ⟨wx, hwx⟩
    obtain ⟨wx', hwx'⟩ := idealPowTensorEval_mul_left_exists I n c wx
    refine ⟨wx', ?_⟩
    rw [hwx', hwx]
    simp [smul_eq_mul]

end
end GromovWitten.AlgebraicGeometry.ReesDegreeBaseChange

namespace GromovWitten.AlgebraicGeometry.ReesGradedBaseChange

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Polynomial
open scoped TensorProduct
open AlgebraicGeometry.ReesBlowup
open GromovWitten.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.ReesBaseChange
universe u
noncomputable section
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

noncomputable def gradedMapSubmodule (I : Ideal A) (f : A →+* B) :
    gradeSubmodule I →+*ᵍ gradeSubmodule (I.map f) where
  toRingHom := reesMap I f
  map_mem := by
    intro n x hx
    change reesMap I f x ∈ grade (I.map f) n
    exact reesMap_mem_grade I f n x hx

noncomputable def gradedMapSubmoduleOfEq (I : Ideal A) (f : A →+* B)
    (J : Ideal B) (h : I.map f = J) :
    gradeSubmodule I →+*ᵍ gradeSubmodule J where
  toRingHom := ReesBlowupOfEq.reesMapOfEq I f J h
  map_mem := by
    intro n x hx
    change ReesBlowupOfEq.reesMapOfEq I f J h x ∈ ReesBlowup.grade J n
    exact ReesBlowupOfEq.reesMapOfEq_mem_grade I f J h n x hx

noncomputable def gradedMapOver (I : Ideal A) :
    ProjBaseChange.GradedHomOver (gradeSubmodule I)
      (gradeSubmodule (I.map (algebraMap A B))) where
  __ := gradedMapSubmodule I (algebraMap A B)
  commutes' := by
    intro a
    apply Subtype.ext
    simp [gradedMapSubmodule, reesMap, Polynomial.algebraMap_apply]

private def gradeTensorToRees (I : Ideal A) (n : ℕ) :
    (gradeSubmodule I n) ⊗[A] B →ₗ[A] reesAlgebra I ⊗[A] B :=
  LinearMap.rTensor B (gradeSubmodule I n).subtype

private theorem degreeMap_eq_reesBaseChange (I : Ideal A) (n : ℕ)
    (z : (gradeSubmodule I n) ⊗[A] B) :
    (gradedMapOver I).degreeMap n z =
      reesBaseChangeMap (B := B) I (gradeTensorToRees I n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      rw [ProjBaseChange.GradedHomOver.degreeMap_tmul]
      change _ = reesBaseChangeMap (B := B) I (x ⊗ₜ[A] b)
      rw [reesBaseChangeMap_tmul]
      simp [gradedMapOver, gradedMapSubmodule, mul_comm]
  | add x y hx hy => simp [hx, hy]

private theorem degreeMap_mem_grade (I : Ideal A) (n : ℕ)
    (z : (gradeSubmodule I n) ⊗[A] B) :
    (gradedMapOver (A := A) (B := B) I).degreeMap n z ∈
      gradeSubmodule (I.map (algebraMap A B)) n := by
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul x b =>
      rw [ProjBaseChange.GradedHomOver.degreeMap_tmul]
      change reesMap I (algebraMap A B) x *
        algebraMap B (reesAlgebra (I.map (algebraMap A B))) b ∈
          gradeSubmodule (I.map (algebraMap A B)) n
      simpa [Algebra.smul_def, smul_eq_mul, mul_comm] using
        (gradeSubmodule (I.map (algebraMap A B)) n).smul_mem b
          (reesMap_mem_grade I (algebraMap A B) n x x.property)
  | add x y hx hy =>
      rw [map_add]
      exact (gradeSubmodule (I.map (algebraMap A B)) n).add_mem hx hy

private def degreeMapToGrade (I : Ideal A) (n : ℕ) :
    (gradeSubmodule I n) ⊗[A] B →ₗ[A]
      gradeSubmodule (I.map (algebraMap A B)) n :=
  { toFun := fun z ↦
      ⟨(gradedMapOver (A := A) (B := B) I).degreeMap n z,
        degreeMap_mem_grade (B := B) I n z⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro a x
      apply Subtype.ext
      simp }

private theorem degreeMap_coeff (I : Ideal A) (n : ℕ)
    (z : (gradeSubmodule I n) ⊗[A] B) :
    gradeCoeffRaw (I.map (algebraMap A B)) n (degreeMapToGrade I n z) =
      idealPowTensorEval I n
        ((gradeCoeffEquiv I n).rTensor B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [degreeMapToGrade, gradeCoeffRaw, idealPowTensorEval]
  | tmul x b =>
      rw [LinearEquiv.rTensor_tmul]
      change ((((gradedMapOver (A := A) (B := B) I).degreeMap n
        (x ⊗ₜ[A] b) : reesAlgebra (I.map (algebraMap A B))) : B[X]).coeff n) = _
      rw [ProjBaseChange.GradedHomOver.degreeMap_tmul]
      change (((reesMap I (algebraMap A B) x :
        reesAlgebra (I.map (algebraMap A B))) : B[X]) * C b).coeff n = _
      rw [coeff_mul_C, reesMap_coe, coeff_map]
      simp [gradeCoeffRaw, gradeCoeffEquiv, idealPowTensorEval_tmul]
  | add x y hx hy =>
      change (((((gradedMapOver (A := A) (B := B) I).degreeMap n (x + y) :
        reesAlgebra (I.map (algebraMap A B))) : B[X]).coeff n)) = _
      rw [map_add, Subalgebra.coe_add, coeff_add]
      rw [map_add]
      rw [map_add, ← hx, ← hy]
      rfl

theorem isBaseChange (I : Ideal A) [Module.Flat A B] :
    (gradedMapOver (A := A) (B := B) I).IsBaseChange := by
  refine ⟨?_, ?_⟩
  · intro n x y hxy
    rw [degreeMap_eq_reesBaseChange I n x,
      degreeMap_eq_reesBaseChange I n y] at hxy
    have hmap := reesBaseChangeMap_injective (B := B) I hxy
    have htensor : Function.Injective (gradeTensorToRees (B := B) I n) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (Submodule.injective_subtype _)
    exact htensor hmap
  · intro n
    apply le_antisymm
    · intro y hy
      obtain ⟨z, rfl⟩ := hy
      exact degreeMap_mem_grade (B := B) I n z
    · intro y hy
      let yg : gradeSubmodule (I.map (algebraMap A B)) n := ⟨y, hy⟩
      let cVal : B := gradeCoeffRaw (I.map (algebraMap A B)) n yg
      have hcVal : cVal ∈ (I.map (algebraMap A B)) ^ n := by
        exact gradeCoeffRaw_mem (I.map (algebraMap A B)) n yg
      obtain ⟨w, hw⟩ := ReesDegreeBaseChange.idealPowTensorEval_surjective_range
        I n cVal hcVal
      let e := (gradeCoeffEquiv I n).rTensor B
      let z := e.symm w
      have hcoeff : gradeCoeffRaw (I.map (algebraMap A B)) n
          (degreeMapToGrade I n z) =
          gradeCoeffRaw (I.map (algebraMap A B)) n yg := by
        rw [degreeMap_coeff]
        change idealPowTensorEval I n (e z) = cVal
        rw [show e z = w from e.apply_symm_apply w, hw]
      have hgrade : degreeMapToGrade I n z = yg := by
        apply (gradeCoeffEquiv (I.map (algebraMap A B)) n).injective
        simpa [gradeCoeffEquiv] using hcoeff
      refine ⟨z, ?_⟩
      exact congrArg Subtype.val hgrade

end
end GromovWitten.AlgebraicGeometry.ReesGradedBaseChange
