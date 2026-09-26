/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ContinuousTorsionSplitting
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Explicit bounds for finite linear torsion representations

For a prime `l`, the automorphism group of an `n`-dimensional `ZMod l`-vector space has
cardinality

`∏ i : Fin n, (l ^ n - l ^ i)`.

This file applies that finite-group bound to the fixed field supplied by
`ContinuousFiniteRepresentation`.  The field itself is constructed in
`ContinuousTorsionSplitting`; this file only records its linear-algebraic degree bounds.  In
particular, the stable-reduction statement below takes the expected dimension `2 * g` as an
explicit hypothesis and does not assert a geometric construction of the Jacobian torsion module.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u v w

noncomputable section

open scoped IntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
variable [IsGalois K Ω]

namespace TorsionDegreeBound

variable (l n : ℕ)

/-- The cardinality bound for the general linear group of an `n`-dimensional vector space over
`ZMod l`.  The empty product makes this definition equal to `1` when `n = 0`. -/
def linearBound : ℕ := ∏ i : Fin n, (l ^ n - l ^ (i : ℕ))

section Prime

variable [Fact l.Prime]

theorem matrixGeneralLinearGroup_card :
    Nat.card (GL (Fin n) (ZMod l)) = linearBound l n := by
  rw [Matrix.card_GL_field]
  simp [linearBound, ZMod.card]

omit [Fact l.Prime] in
theorem linearBound_le_pow : linearBound l n ≤ l ^ (n * n) := by
  classical
  unfold linearBound
  calc
    ∏ i : Fin n, (l ^ n - l ^ (i : ℕ)) ≤ ∏ _i : Fin n, l ^ n := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        exact Nat.sub_le _ _
    _ = (l ^ n) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = l ^ (n * n) := by
      rw [← Nat.pow_mul]

end Prime

section Representation

variable {l : ℕ} [Fact l.Prime]
variable {V : Type w} [AddCommGroup V] [Module (ZMod l) V]
variable [FiniteDimensional (ZMod l) V]
variable [TopologicalSpace (LinearMap.GeneralLinearGroup (ZMod l) V)]
variable [DiscreteTopology (LinearMap.GeneralLinearGroup (ZMod l) V)]

/-- The finite linear representation group attached to a finite-dimensional `ZMod l`-module. -/
abbrev linearAutomorphisms := LinearMap.GeneralLinearGroup (ZMod l) V

/-- A continuous representation on a finite-dimensional `ZMod l`-module. -/
abbrev LinearRepresentation := Gal(Ω/K) →* linearAutomorphisms (V := V) (l := l)

/-- Choose finite coordinates for the linear automorphism group. -/
noncomputable def coordinateEquiv :
    GL (Fin (Module.finrank (ZMod l) V)) (ZMod l) ≃*
      linearAutomorphisms (V := V) (l := l) :=
  Matrix.GeneralLinearGroup.toLin' (Module.finBasis (ZMod l) V)

instance finiteLinearAutomorphisms : Finite (linearAutomorphisms (V := V) (l := l)) := by
  exact Finite.of_injective (coordinateEquiv (V := V) (l := l)).symm
    (coordinateEquiv (V := V) (l := l)).symm.injective

omit [TopologicalSpace (LinearMap.GeneralLinearGroup (ZMod l) V)]
    [DiscreteTopology (LinearMap.GeneralLinearGroup (ZMod l) V)] in
theorem linearAutomorphisms_card :
    Nat.card (linearAutomorphisms (V := V) (l := l)) =
      linearBound l (Module.finrank (ZMod l) V) := by
  let e := coordinateEquiv (V := V) (l := l)
  calc
    Nat.card (linearAutomorphisms (V := V) (l := l)) =
        Nat.card (GL (Fin (Module.finrank (ZMod l) V)) (ZMod l)) := by
      exact Nat.card_congr e.symm.toEquiv
    _ = linearBound l (Module.finrank (ZMod l) V) :=
      matrixGeneralLinearGroup_card l (Module.finrank (ZMod l) V)

variable (ρ : LinearRepresentation (K := K) (Ω := Ω) (V := V) (l := l))
variable (hρ : Continuous ρ)

/-- The fixed field cut out by a continuous linear torsion representation. -/
noncomputable abbrev splittingField : IntermediateField K Ω :=
  ContinuousFiniteRepresentation.fixedField ρ hρ

omit [FiniteDimensional (ZMod l) V] in
theorem splittingField_finiteDimensional :
    FiniteDimensional K (splittingField ρ hρ) :=
  ContinuousFiniteRepresentation.fixedField.finiteDimensional ρ hρ

omit [FiniteDimensional (ZMod l) V] in
theorem splittingField_isSeparable :
    Algebra.IsSeparable K (splittingField ρ hρ) :=
  ContinuousFiniteRepresentation.fixedField.isSeparable ρ hρ

omit [FiniteDimensional (ZMod l) V] in
theorem splittingField_isGalois : IsGalois K (splittingField ρ hρ) :=
  ContinuousFiniteRepresentation.fixedField.isGalois ρ hρ

omit [FiniteDimensional (ZMod l) V] in
theorem splittingField_representation_trivial
    (σ : Gal(Ω/splittingField ρ hρ)) : ρ
      (ContinuousFiniteRepresentation.restrictToBase ρ hρ σ) = 1 :=
  ContinuousFiniteRepresentation.restrictToBase_rho_eq_one ρ hρ σ

theorem splittingField_finrank_dvd_bound :
    Module.finrank K (splittingField ρ hρ) ∣
      linearBound l (Module.finrank (ZMod l) V) := by
  have hdiv : Module.finrank K (splittingField ρ hρ) ∣
      Nat.card (linearAutomorphisms (V := V) (l := l)) :=
    ContinuousFiniteRepresentation.fixedField.finrank_dvd_card ρ hρ
  rw [linearAutomorphisms_card (V := V) (l := l)] at hdiv
  exact hdiv

theorem splittingField_finrank_le_bound :
    Module.finrank K (splittingField ρ hρ) ≤
      linearBound l (Module.finrank (ZMod l) V) := by
  have hle : Module.finrank K (splittingField ρ hρ) ≤
      Nat.card (linearAutomorphisms (V := V) (l := l)) :=
    ContinuousFiniteRepresentation.fixedField.finrank_le_card ρ hρ
  rw [linearAutomorphisms_card (V := V) (l := l)] at hle
  exact hle

theorem splittingField_finrank_le_pow :
    Module.finrank K (splittingField ρ hρ) ≤
      l ^ (Module.finrank (ZMod l) V * Module.finrank (ZMod l) V) :=
  (splittingField_finrank_le_bound ρ hρ).trans
    (linearBound_le_pow l (Module.finrank (ZMod l) V))

end Representation

section StableReduction

variable {l : ℕ} [Fact l.Prime]
variable {V : Type w} [AddCommGroup V] [Module (ZMod l) V]
variable [FiniteDimensional (ZMod l) V]
variable [TopologicalSpace (LinearMap.GeneralLinearGroup (ZMod l) V)]
variable [DiscreteTopology (LinearMap.GeneralLinearGroup (ZMod l) V)]
variable (ρ : LinearRepresentation (K := K) (Ω := Ω) (V := V) (l := l))
variable (hρ : Continuous ρ)
variable (g : ℕ)

/-- The expected stable-reduction torsion bound, with `2 * g` substituted for the module rank. -/
def stableReductionBound : ℕ := linearBound l (2 * g)

theorem splittingField_finrank_le_stableReductionBound
    (hV : Module.finrank (ZMod l) V = 2 * g) :
    Module.finrank K (splittingField ρ hρ) ≤ stableReductionBound (l := l) g := by
  rw [stableReductionBound, ← hV]
  exact splittingField_finrank_le_bound ρ hρ

theorem splittingField_finrank_le_stableReductionPow
    (hV : Module.finrank (ZMod l) V = 2 * g) :
    Module.finrank K (splittingField ρ hρ) ≤ l ^ ((2 * g) * (2 * g)) := by
  rw [← hV]
  exact splittingField_finrank_le_pow ρ hρ

end StableReduction

end TorsionDegreeBound

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
