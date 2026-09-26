/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeBaseChange

/-!
# Unit-normalized charts for a DVR node

The quotient `LocalNode.Ring R a 1` is the general smoothing algebra
`R[x,y]/(xy-a)`.  If `a = u πⁿ` with `u` a unit, rescaling one branch gives an explicit
`R`-algebra equivalence with the standard chart `R[x,y]/(xy-πⁿ)`.  A DVR factors every
nonzero nonunit in this form, and the nonunit hypothesis is exactly what forces `n > 0`.

This file deliberately separates the algebraic normalization from the geometric etale-local
node theorem.  In particular, `AtWorstNodal` alone allows the persistent generic node `xy = 0`
and therefore cannot produce a positive thickness.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Polynomial

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u v

noncomputable section

/-- The explicit map from `R[x,y]/(xy-a)` to `R[x,y]/(xy-πⁿ)` when `a = uπⁿ`.

The first branch is rescaled by `u`; the second branch is unchanged. -/
def unitNormalizationMap {R : Type u} [CommRing R] (a π : R) (n : ℕ) (u : Rˣ)
    (h : a = (u : R) * π ^ n) :
    Ring R a 1 →ₐ[R] Ring R π n :=
  lift a 1
    (algebraMap R (Ring R π n) (u : R) * x R π n)
    (y R π n) (by
      calc
        algebraMap R (Ring R π n) (u : R) * x R π n * y R π n =
            algebraMap R (Ring R π n) (u : R) *
              algebraMap R (Ring R π n) (π ^ n) := by
          rw [mul_assoc, x_mul_y]
        _ = algebraMap R (Ring R π n) ((u : R) * π ^ n) := by
          rw [map_mul]
        _ = algebraMap R (Ring R π n) a := by rw [h]
        _ = algebraMap R (Ring R π n) (a ^ 1) := by simp)

/-- The inverse coordinate map for `unitNormalizationMap`. -/
def unitNormalizationInverseMap {R : Type u} [CommRing R] (a π : R) (n : ℕ) (u : Rˣ)
    (h : a = (u : R) * π ^ n) :
    Ring R π n →ₐ[R] Ring R a 1 :=
  lift π n
    (algebraMap R (Ring R a 1) (↑u⁻¹ : R) * x R a 1)
    (y R a 1) (by
      calc
        algebraMap R (Ring R a 1) (↑u⁻¹ : R) * x R a 1 * y R a 1 =
            algebraMap R (Ring R a 1) (↑u⁻¹ : R) *
              algebraMap R (Ring R a 1) (a ^ 1) := by
          rw [mul_assoc, x_mul_y]
        _ = algebraMap R (Ring R a 1) ((↑u⁻¹ : R) * a ^ 1) := by
          rw [map_mul]
        _ = algebraMap R (Ring R a 1) (π ^ n) := by
          rw [h]
          simp [pow_one])

@[simp] theorem unitNormalizationMap_x {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    unitNormalizationMap a π n u h (x R a 1) =
      algebraMap R (Ring R π n) (u : R) * x R π n := by
  change lift a 1
      (algebraMap R (Ring R π n) (u : R) * x R π n)
      (y R π n) _ (x R a 1) = _
  apply lift_x

@[simp] theorem unitNormalizationMap_y {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    unitNormalizationMap a π n u h (y R a 1) = y R π n := by
  change lift a 1
      (algebraMap R (Ring R π n) (u : R) * x R π n)
      (y R π n) _ (y R a 1) = _
  apply lift_y

@[simp] theorem unitNormalizationInverseMap_x {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    unitNormalizationInverseMap a π n u h (x R π n) =
      algebraMap R (Ring R a 1) (↑u⁻¹ : R) * x R a 1 := by
  change lift π n
      (algebraMap R (Ring R a 1) (↑u⁻¹ : R) * x R a 1)
      (y R a 1) _ (x R π n) = _
  apply lift_x

@[simp] theorem unitNormalizationInverseMap_y {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    unitNormalizationInverseMap a π n u h (y R π n) = y R a 1 := by
  change lift π n
      (algebraMap R (Ring R a 1) (↑u⁻¹ : R) * x R a 1)
      (y R a 1) _ (y R π n) = _
  apply lift_y

theorem unitNormalizationMap_comp_inverse {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    (unitNormalizationMap a π n u h).comp (unitNormalizationInverseMap a π n u h) =
      AlgHom.id R (Ring R π n) := by
  apply algHom_ext π n
  · simp only [AlgHom.coe_comp, Function.comp_apply, unitNormalizationInverseMap_x,
      map_mul, AlgHom.commutes, unitNormalizationMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul]
    simp
  · simp only [AlgHom.coe_comp, Function.comp_apply, unitNormalizationInverseMap_y,
      unitNormalizationMap_y, AlgHom.id_apply]

theorem unitNormalizationInverse_comp_map {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    (unitNormalizationInverseMap a π n u h).comp (unitNormalizationMap a π n u h) =
      AlgHom.id R (Ring R a 1) := by
  apply algHom_ext a 1
  · simp only [AlgHom.coe_comp, Function.comp_apply, unitNormalizationMap_x,
      map_mul, AlgHom.commutes, unitNormalizationInverseMap_x, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul]
    simp
  · simp only [AlgHom.coe_comp, Function.comp_apply, unitNormalizationMap_y,
      unitNormalizationInverseMap_y, AlgHom.id_apply]

/-- Unit normalization of the general smoothing algebra to a standard thickness chart. -/
def unitNormalizationEquiv {R : Type u} [CommRing R] (a π : R) (n : ℕ) (u : Rˣ)
    (h : a = (u : R) * π ^ n) : Ring R a 1 ≃ₐ[R] Ring R π n :=
  AlgEquiv.ofAlgHom (unitNormalizationMap a π n u h)
    (unitNormalizationInverseMap a π n u h)
    (unitNormalizationMap_comp_inverse a π n u h)
    (unitNormalizationInverse_comp_map a π n u h)

@[simp] theorem unitNormalizationEquiv_x {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    unitNormalizationEquiv a π n u h (x R a 1) =
      algebraMap R (Ring R π n) (u : R) * x R π n := by
  change unitNormalizationMap a π n u h (x R a 1) = _
  exact unitNormalizationMap_x a π n u h

@[simp] theorem unitNormalizationEquiv_y {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    unitNormalizationEquiv a π n u h (y R a 1) = y R π n := by
  change unitNormalizationMap a π n u h (y R a 1) = _
  exact unitNormalizationMap_y a π n u h

@[simp] theorem unitNormalizationEquiv_symm_x {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    (unitNormalizationEquiv a π n u h).symm (x R π n) =
      algebraMap R (Ring R a 1) (↑u⁻¹ : R) * x R a 1 := by
  change unitNormalizationInverseMap a π n u h (x R π n) = _
  exact unitNormalizationInverseMap_x a π n u h

@[simp] theorem unitNormalizationEquiv_symm_y {R : Type u} [CommRing R] (a π : R) (n : ℕ)
    (u : Rˣ) (h : a = (u : R) * π ^ n) :
    (unitNormalizationEquiv a π n u h).symm (y R π n) = y R a 1 := by
  change unitNormalizationInverseMap a π n u h (y R π n) = _
  exact unitNormalizationInverseMap_y a π n u h

/-- A nonzero nonunit in a DVR has positive valuation in a chosen uniformizer. -/
theorem dvr_factorization_pos {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha0 : a ≠ 0) (ha : ¬ IsUnit a)
    {π : R} (hπ : Irreducible π) :
    ∃ (n : ℕ) (u : Rˣ), 0 < n ∧ a = (u : R) * π ^ n := by
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  refine ⟨n, u, ?_, hu⟩
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  apply ha
  rw [hu, hn0, pow_zero, mul_one]
  exact u.isUnit

/-- Explicit standard chart data supplied by DVR factorization. -/
theorem dvr_standardChart {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha0 : a ≠ 0) (ha : ¬ IsUnit a)
    {π : R} (hπ : Irreducible π) :
    ∃ (n : ℕ) (u : Rˣ), 0 < n ∧ a = (u : R) * π ^ n ∧
      Nonempty (Ring R a 1 ≃ₐ[R] Ring R π n) := by
  obtain ⟨n, u, hn, hu⟩ := dvr_factorization_pos ha0 ha hπ
  exact ⟨n, u, hn, hu, ⟨unitNormalizationEquiv a π n u hu⟩⟩

/-- For a fixed uniformizer and exponent, the unit in a DVR factorization is unique. -/
theorem dvr_factorization_unit_unique {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a π : R} {n : ℕ} (hπ : Irreducible π)
    (u v : Rˣ) (hu : a = (u : R) * π ^ n) (hv : a = (v : R) * π ^ n) : u = v := by
  apply IsDiscreteValuationRing.unit_mul_pow_congr_unit hπ u v n n
  exact hu.symm.trans hv

/-- With a fixed irreducible uniformizer, both the exponent and unit in a nonzero DVR
factorization are unique. -/
theorem dvr_factorization_unique {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a π : R} {m n : ℕ} (hπ : Irreducible π)
    (u v : Rˣ) (hu : a = (u : R) * π ^ m) (hv : a = (v : R) * π ^ n) :
    m = n ∧ u = v := by
  have hmn : m = n := by
    apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ u v m n
    exact hu.symm.trans hv
  subst n
  exact ⟨rfl, dvr_factorization_unit_unique hπ u v hu hv⟩

/-- The normalization equivalence is independent of the chosen proof of the factorization and,
for a fixed uniformizer and exponent, of the unit representative as well. -/
theorem unitNormalizationEquiv_independent {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a π : R} {n : ℕ} (hπ : Irreducible π)
    {u v : Rˣ} (hu : a = (u : R) * π ^ n) (hv : a = (v : R) * π ^ n) :
    unitNormalizationEquiv a π n u hu = unitNormalizationEquiv a π n v hv := by
  have huv : u = v := dvr_factorization_unit_unique hπ u v hu hv
  subst v
  have huvproof : hu = hv := Subsingleton.elim _ _
  subst hv
  rfl

/-- Unit normalization commutes with coefficient extension.  This is the algebraic square used
by further DVR extensions: the coefficient maps send the two displayed coordinates to the same
rescaled coordinates. -/
private theorem coefficient_factorization_map
    (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (a π : R) (n : ℕ) (u : Rˣ) (h : a = (u : R) * π ^ n) :
    algebraMap R S a = (↑(Units.map (algebraMap R S).toMonoidHom u) : S) *
      (algebraMap R S π) ^ n := by
  rw [h, map_mul, map_pow]
  rfl

theorem unitNormalizationMap_coefficient_naturality
    (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (a π : R) (n : ℕ) (u : Rˣ) (h : a = (u : R) * π ^ n) :
    (coefficientAlgHom R S π n).comp (unitNormalizationMap a π n u h) =
    ((unitNormalizationMap (algebraMap R S a) (algebraMap R S π) n
        (Units.map (algebraMap R S) u)
          (coefficient_factorization_map R S a π n u h)).restrictScalars R).comp
      (coefficientAlgHom R S a 1) := by
  have hS :
      algebraMap R S a = (↑(Units.map (algebraMap R S).toMonoidHom u) : S) *
        (algebraMap R S π) ^ n :=
    coefficient_factorization_map R S a π n u h
  apply algHom_ext a 1
  · change _ =
      unitNormalizationMap (algebraMap R S a) (algebraMap R S π) n
        (Units.map (algebraMap R S).toMonoidHom u) hS
        (coefficientAlgHom R S a 1 (x R a 1))
    change coefficientAlgHom R S π n
        (unitNormalizationMap a π n u h (x R a 1)) = _
    rw [unitNormalizationMap_x a π n u h]
    simp only [coefficientAlgHom_x, map_mul, AlgHom.commutes]
    rw [unitNormalizationMap_x (algebraMap R S a) (algebraMap R S π) n
        (Units.map (algebraMap R S).toMonoidHom u) hS]
    have hu := IsScalarTower.algebraMap_apply R S (Ring S (algebraMap R S π) n) (u : R)
    rw [hu]
    simp only [Units.coe_map]
    rfl
  · change _ =
      unitNormalizationMap (algebraMap R S a) (algebraMap R S π) n
        (Units.map (algebraMap R S).toMonoidHom u) hS
        (coefficientAlgHom R S a 1 (y R a 1))
    change coefficientAlgHom R S π n
        (unitNormalizationMap a π n u h (y R a 1)) = _
    rw [unitNormalizationMap_y a π n u h]
    simp only [coefficientAlgHom_y]
    rw [unitNormalizationMap_y (algebraMap R S a) (algebraMap R S π) n
        (Units.map (algebraMap R S).toMonoidHom u) hS]
@[simp] theorem unitNormalizationEquiv_coefficient_naturality_x
    (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (a π : R) (n : ℕ) (u : Rˣ) (h : a = (u : R) * π ^ n) :
    coefficientAlgHom R S π n
        (unitNormalizationEquiv a π n u h (x R a 1)) =
      unitNormalizationEquiv (algebraMap R S a) (algebraMap R S π) n
        (Units.map (algebraMap R S) u)
          (coefficient_factorization_map R S a π n u h)
        (coefficientAlgHom R S a 1 (x R a 1)) := by
  have hS :
      algebraMap R S a = (↑(Units.map (algebraMap R S).toMonoidHom u) : S) *
        (algebraMap R S π) ^ n :=
    coefficient_factorization_map R S a π n u h
  change coefficientAlgHom R S π n
      (unitNormalizationMap a π n u h (x R a 1)) =
    (unitNormalizationMap (algebraMap R S a) (algebraMap R S π) n
      (Units.map (algebraMap R S).toMonoidHom u) hS).restrictScalars R
      (coefficientAlgHom R S a 1 (x R a 1))
  exact DFunLike.congr_fun
    (unitNormalizationMap_coefficient_naturality R S a π n u h) (x R a 1)

@[simp] theorem unitNormalizationEquiv_coefficient_naturality_y
    (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (a π : R) (n : ℕ) (u : Rˣ) (h : a = (u : R) * π ^ n) :
    coefficientAlgHom R S π n
        (unitNormalizationEquiv a π n u h (y R a 1)) =
      unitNormalizationEquiv (algebraMap R S a) (algebraMap R S π) n
        (Units.map (algebraMap R S) u)
          (coefficient_factorization_map R S a π n u h)
        (coefficientAlgHom R S a 1 (y R a 1)) := by
  have hS :
      algebraMap R S a = (↑(Units.map (algebraMap R S).toMonoidHom u) : S) *
        (algebraMap R S π) ^ n :=
    coefficient_factorization_map R S a π n u h
  change coefficientAlgHom R S π n
      (unitNormalizationMap a π n u h (y R a 1)) =
    (unitNormalizationMap (algebraMap R S a) (algebraMap R S π) n
      (Units.map (algebraMap R S).toMonoidHom u) hS).restrictScalars R
      (coefficientAlgHom R S a 1 (y R a 1))
  exact DFunLike.congr_fun
    (unitNormalizationMap_coefficient_naturality R S a π n u h) (y R a 1)

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
