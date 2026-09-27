/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.PolynomialAutomorphisms
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Infinitesimal symmetries and the derivative criterion

In characteristic `p`, the substitution `X ↦ (1 + ε)X` preserves `X^p` over the dual
numbers. It reduces to the identity but is not the identity. Two distinct lifts of the same
point show that the affine-linear stabilizer's coordinate algebra is not formally unramified.
More generally, vanishing derivative gives an infinitesimal translation. Together with
square-zero rigidity, this proves that formal unramifiedness is equivalent to nonzero derivative.
No projective representability statement is assumed.
-/

namespace GromovWitten.AlgebraicGeometry.PolynomialAutomorphisms

open Polynomial
open scoped DualNumber

section Scale

variable (k : Type*) [CommRing k]

/-- The unit `1 + ε`, with inverse `1 - ε`. -/
def infinitesimalScale : (DualNumber k)ˣ :=
  Units.mkOfMulEqOne (1 + ε) (1 - ε) (by ext <;> simp)

@[simp] theorem infinitesimalScale_val :
    (infinitesimalScale k : DualNumber k) = 1 + ε := rfl

@[simp] theorem infinitesimalScale_fst :
    TrivSqZeroExt.fst (infinitesimalScale k : DualNumber k) = 1 := by
  simp

theorem infinitesimalScale_ne_one [Nontrivial k] : infinitesimalScale k ≠ 1 := by
  intro h
  have h' := congrArg (fun u : (DualNumber k)ˣ => TrivSqZeroExt.snd (u : DualNumber k)) h
  simp at h'

end Scale

variable (k : Type*) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem infinitesimalScale_pow_char : (infinitesimalScale k : DualNumber k) ^ p = 1 := by
  let : CharP (DualNumber k) p :=
    charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective p
  rw [infinitesimalScale_val, add_pow_char, one_pow,
    pow_eq_zero_of_le (Fact.out : p.Prime).two_le DualNumber.eps_pow_two, add_zero]

/-- A nontrivial infinitesimal affine-linear substitution preserving Frobenius. -/
def frobeniusInfinitesimalPoint : Point (X ^ p : k[X]) (DualNumber k) where
  scale := infinitesimalScale k
  translate := 0
  preserves := by
    simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.pow_comp,
      Polynomial.X_comp, Polynomial.C_0, add_zero, mul_pow,
      ← Polynomial.C_pow, infinitesimalScale_pow_char, Polynomial.C_1, one_mul]

/-- The corresponding polynomial automorphism preserves `X^p`. -/
theorem infinitesimalSubstitution_preserves_frobenius :
    substitutionAlgEquiv (infinitesimalScale k) 0 (X ^ p) =
      (X ^ p : (DualNumber k)[X]) := by
  rw [map_pow, substitutionAlgEquiv_apply_X]
  simp only [Polynomial.C_0, add_zero, mul_pow, ← Polynomial.C_pow,
    infinitesimalScale_pow_char, Polynomial.C_1, one_mul]

/-- Its reduction modulo `ε` is the identity on the affine coordinate. -/
theorem infinitesimalSubstitution_reduction_X :
    Polynomial.map (TrivSqZeroExt.fstHom k k k).toRingHom
      (substitutionAlgEquiv (infinitesimalScale k) 0 X) = (X : k[X]) := by
  simp [substitutionAlgEquiv_apply_X]

/-- Nevertheless the automorphism of the dual-number polynomial algebra is not the identity. -/
theorem infinitesimalSubstitution_ne_refl :
    substitutionAlgEquiv (infinitesimalScale k) 0 ≠ AlgEquiv.refl := by
  intro h
  have hX := congrArg (fun E : (DualNumber k)[X] ≃ₐ[DualNumber k] (DualNumber k)[X] =>
    TrivSqZeroExt.snd ((E X).coeff 1)) h
  simp at hX

private theorem not_formallyUnramified_of_dual_points {f : k[X]}
    (P Q : Point f (DualNumber k)) (hne : P ≠ Q)
    (hred : Point.map f (TrivSqZeroExt.fstHom k k k) P =
      Point.map f (TrivSqZeroExt.fstHom k k k) Q) :
    ¬ Algebra.FormallyUnramified k (CoordinateRing f) := by
  intro h
  let : Algebra.FormallyUnramified k (CoordinateRing f) := h
  let ρ := TrivSqZeroExt.fstHom k k k
  have hcomp : ρ.comp (pointToAlgHom f P) = ρ.comp (pointToAlgHom f Q) := by
    rw [← pointToAlgHom_map, ← pointToAlgHom_map, hred]
  have he := Algebra.FormallyUnramified.lift_unique' ρ
    (show IsNilpotent (RingHom.ker ρ.toRingHom) from
      ⟨2, TrivSqZeroExt.kerIdeal_sq k k⟩)
    (pointToAlgHom f P) (pointToAlgHom f Q) hcomp
  exact hne ((pointEquiv f).injective he)

/-- The affine-linear stabilizer of Frobenius fails infinitesimal uniqueness. -/
theorem not_formallyUnramified_frobenius :
    ¬ Algebra.FormallyUnramified k (CoordinateRing (X ^ p : k[X])) := by
  let P := frobeniusInfinitesimalPoint k p
  let Q : Point (X ^ p : k[X]) (DualNumber k) :=
    { scale := 1, translate := 0, preserves := by simp }
  apply not_formallyUnramified_of_dual_points k P Q
  · intro hPQ
    exact infinitesimalScale_ne_one k (congrArg Point.scale hPQ)
  · apply Point.ext
    · apply Units.ext
      simp [Point.map, P, Q, frobeniusInfinitesimalPoint]
    · rfl

/-- Vanishing derivative gives the infinitesimal translation `X ↦ X + ε`. -/
def infinitesimalTranslationPoint {f : k[X]} (hf : f.derivative = 0) :
    Point f (DualNumber k) where
  scale := 1
  translate := ε
  preserves := by
    have hsq : (C (ε : DualNumber k)) ^ 2 = 0 := by
      rw [← Polynomial.C_pow, DualNumber.eps_pow_two, Polynomial.C_0]
    have ht := Polynomial.aeval_add_of_sq_eq_zero
      (f.map (algebraMap k (DualNumber k))) X (C (ε : DualNumber k)) hsq
    change (f.map (algebraMap k (DualNumber k))).comp (X + C ε) =
      (f.map (algebraMap k (DualNumber k))).comp X +
        (f.map (algebraMap k (DualNumber k))).derivative.comp X * C ε at ht
    simpa [Polynomial.derivative_map, hf] using ht.symm

/-- A polynomial with zero derivative has a nontrivial infinitesimal affine-linear stabilizer. -/
theorem not_formallyUnramified_of_derivative_eq_zero {f : k[X]} (hf : f.derivative = 0) :
    ¬ Algebra.FormallyUnramified k (CoordinateRing f) := by
  let P := infinitesimalTranslationPoint k hf
  let Q : Point f (DualNumber k) := { scale := 1, translate := 0, preserves := by simp }
  apply not_formallyUnramified_of_dual_points k P Q
  · intro hPQ
    have he : (ε : DualNumber k) = 0 := congrArg Point.translate hPQ
    have hc := congrArg TrivSqZeroExt.snd he
    simp at hc
  · apply Point.ext
    · rfl
    · simp [Point.map, P, Q, infinitesimalTranslationPoint]

/-- The affine-linear stabilizer is formally unramified exactly when the derivative is nonzero.
This criterion includes constant polynomials and all characteristics. -/
theorem coordinateRing_formallyUnramified_iff (f : k[X]) :
    Algebra.FormallyUnramified k (CoordinateRing f) ↔ f.derivative ≠ 0 := by
  constructor
  · intro h hf
    exact not_formallyUnramified_of_derivative_eq_zero k hf h
  · exact coordinateRing_formallyUnramified

end GromovWitten.AlgebraicGeometry.PolynomialAutomorphisms
