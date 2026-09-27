/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.ProjBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Polynomial projective-bundle base change

The polynomial algebra on a free module is the symmetric algebra of that module.  This file
records the degreewise base-change calculation needed to use its homogeneous pieces as graded
data for `ProjBaseChange`: after extending scalars, each homogeneous piece is exactly the base
change of the original piece.  The proof uses the direct-sum decomposition of multivariate
polynomials and induction on homogeneous components, so it does not assume flatness of the
coefficient-ring map.
-/

open TensorProduct

namespace GromovWitten.AlgebraicGeometry.ProjBaseChange

universe u

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

namespace Polynomial

variable (σ : Type u)

local instance : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ A) :=
  MvPolynomial.gradedAlgebra

local instance : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ B) :=
  MvPolynomial.gradedAlgebra

/-- The coefficient extension map on homogeneous polynomial pieces. -/
def gradedMap : MvPolynomial.homogeneousSubmodule σ A →+*ᵍ
    MvPolynomial.homogeneousSubmodule σ B where
  __ := MvPolynomial.map (algebraMap A B)
  map_mem := by
    intro n x hx
    exact hx.map (algebraMap A B)

/-- The polynomial homogeneous map viewed as a graded map over `A → B`. -/
def gradedMapOver : GradedHomOver (MvPolynomial.homogeneousSubmodule σ A)
    (MvPolynomial.homogeneousSubmodule σ B) where
  __ := gradedMap σ
  commutes' := by
    intro a
    ext
    simp [gradedMap]

private abbrev degreeMap (n : ℕ) :
    TensorProduct A (MvPolynomial.homogeneousSubmodule σ A n) B →ₗ[A]
      MvPolynomial σ B :=
  @GradedHomOver.degreeMap A B _ _ _ (MvPolynomial σ A) (MvPolynomial σ B)
    _ _ _ _ _ _ (MvPolynomial.homogeneousSubmodule σ A)
    (MvPolynomial.homogeneousSubmodule σ B) (gradedMapOver σ) n

private theorem degreeMap_eq_polynomialTensor (n : ℕ)
    (z : TensorProduct A (MvPolynomial.homogeneousSubmodule σ A n) B) :
    (gradedMapOver σ).degreeMap n z =
      (MvPolynomial.algebraTensorAlgEquiv A B)
        ((TensorProduct.comm A (MvPolynomial σ A) B)
          ((MvPolynomial.homogeneousSubmodule σ A n).subtype.rTensor B z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp [GradedHomOver.degreeMap_tmul, gradedMapOver, gradedMap,
      MvPolynomial.algebraTensorAlgEquiv_tmul, Algebra.smul_def, mul_comm]
  | add z w hz hw => simp [hz, hw]

private theorem degreeMap_injective (n : ℕ) :
    Function.Injective (@degreeMap A B _ _ _ σ n) := by
  intro x y hxy
  apply (DirectSum.subtype_rTensor_injective
    (MvPolynomial.homogeneousSubmodule σ A) B n)
  have hfull :
      (MvPolynomial.algebraTensorAlgEquiv A B)
          ((TensorProduct.comm A (MvPolynomial σ A) B)
            ((MvPolynomial.homogeneousSubmodule σ A n).subtype.rTensor B x)) =
        (MvPolynomial.algebraTensorAlgEquiv A B)
          ((TensorProduct.comm A (MvPolynomial σ A) B)
            ((MvPolynomial.homogeneousSubmodule σ A n).subtype.rTensor B y)) := by
    rw [← degreeMap_eq_polynomialTensor σ n x, ← degreeMap_eq_polynomialTensor σ n y]
    exact hxy
  apply (TensorProduct.comm A (MvPolynomial σ A) B).injective
  exact (MvPolynomial.algebraTensorAlgEquiv A B).injective hfull

private theorem degreeMap_range_eq (n : ℕ) :
    LinearMap.range (degreeMap σ n) =
      (MvPolynomial.homogeneousSubmodule σ B n).restrictScalars A := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change MvPolynomial.IsHomogeneous _ n
    induction x using TensorProduct.induction_on with
    | zero => exact MvPolynomial.isHomogeneous_zero σ B n
    | tmul x b =>
      simpa only [GradedHomOver.degreeMap_tmul, gradedMapOver, gradedMap] using
        by simpa [Algebra.smul_def, mul_comm] using
          (x.property.map (algebraMap A B)).C_mul b
    | add x y hx hy =>
      simpa only [map_add] using hx.add hy
  · intro y hy
    change MvPolynomial.IsHomogeneous y n at hy
    have hcomp : ∀ z : MvPolynomial σ B, ∃ x,
        (@degreeMap A B _ _ _ σ n) x = MvPolynomial.homogeneousComponent n z := by
      intro z
      induction z using MvPolynomial.induction_on' with
      | monomial m b =>
        by_cases hdeg : m.degree = n
        · refine ⟨(⟨MvPolynomial.monomial m 1,
            MvPolynomial.isHomogeneous_monomial _ hdeg⟩ ⊗ₜ[A] b), ?_⟩
          rw [GradedHomOver.degreeMap_tmul]
          change (MvPolynomial.map (algebraMap A B) (MvPolynomial.monomial m 1)) *
            MvPolynomial.C b = MvPolynomial.homogeneousComponent n
              (MvPolynomial.monomial m b)
          rw [MvPolynomial.map_monomial]
          rw [MvPolynomial.homogeneousComponent_of_mem
            (MvPolynomial.isHomogeneous_monomial b rfl)]
          simp [hdeg, MvPolynomial.monomial_eq, mul_comm]
        · refine ⟨0, ?_⟩
          rw [MvPolynomial.homogeneousComponent_of_mem
            (MvPolynomial.isHomogeneous_monomial b rfl)]
          simp [Ne.symm hdeg]
      | add p q hp hq =>
        obtain ⟨xp, hp⟩ := hp
        obtain ⟨xq, hq⟩ := hq
        refine ⟨xp + xq, ?_⟩
        simp [hp, hq]
    obtain ⟨x, hx⟩ := hcomp y
    refine ⟨x, ?_⟩
    rw [hx, MvPolynomial.homogeneousComponent_eq_self hy]

/-- Homogeneous polynomial pieces commute with arbitrary scalar extension degree by degree. -/
theorem isBaseChange :
    @GradedHomOver.IsBaseChange A B _ _ _ (MvPolynomial σ A) (MvPolynomial σ B)
      _ _ _ _ _ _ (MvPolynomial.homogeneousSubmodule σ A)
      (MvPolynomial.homogeneousSubmodule σ B) (gradedMapOver σ) where
  injective := degreeMap_injective σ
  range_eq := degreeMap_range_eq σ

end Polynomial

end

end GromovWitten.AlgebraicGeometry.ProjBaseChange
