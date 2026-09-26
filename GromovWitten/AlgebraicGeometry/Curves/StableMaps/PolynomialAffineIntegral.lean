/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Integral coordinates of a polynomial stabilizer

An affine-linear substitution preserving a nonconstant polynomial over a field has integral
scale and translation coordinates.  The target algebra may have zero divisors and nilpotents.
The leading coefficient gives the power relation on the scale, while the constant coefficient
gives a polynomial equation for the translation.
-/

namespace GromovWitten.AlgebraicGeometry.PolynomialAutomorphisms

open Polynomial

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]

/-- The top coefficient of an affine-linear substitution, without a domain hypothesis on the
coefficient algebra. -/
theorem coeff_affine_substitution [Nontrivial S] (f : k[X]) (a : Sˣ) (b : S) :
    ((f.map (algebraMap k S)).comp (C (a : S) * X + C b)).coeff f.natDegree =
      algebraMap k S f.leadingCoeff * (a : S) ^ f.natDegree := by
  have ha : (a : S) ≠ 0 := a.isUnit.ne_zero
  have hdeg : (C (a : S) * X + C b).natDegree = 1 := natDegree_linear ha
  have h := coeff_comp_degree_mul_degree
    (p := f.map (algebraMap k S)) (q := C (a : S) * X + C b)
    (by rw [hdeg]; exact one_ne_zero)
  simpa only [hdeg, mul_one, natDegree_map_eq_of_injective (algebraMap k S).injective,
    leadingCoeff_map_of_injective (algebraMap k S).injective, leadingCoeff_linear ha] using h

/-- A nonzero polynomial over the field retains a unit leading coefficient after an invertible
affine substitution, even over a coefficient algebra with nilpotents. -/
theorem isUnit_leadingCoeff_affine_substitution [Nontrivial S] {f : k[X]} (hf : f ≠ 0)
    (a : Sˣ) (b : S) :
    IsUnit ((f.map (algebraMap k S)).comp (C (a : S) * X + C b)).leadingCoeff := by
  have hlc : IsUnit (algebraMap k S f.leadingCoeff) :=
    (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf)).map (algebraMap k S)
  have hunit := hlc.mul (a.isUnit.pow f.natDegree)
  have hdeg : ((f.map (algebraMap k S)).comp
      (C (a : S) * X + C b)).natDegree = f.natDegree := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · calc
        _ ≤ (f.map (algebraMap k S)).natDegree *
            (C (a : S) * X + C b).natDegree := natDegree_comp_le
        _ = f.natDegree := by
          rw [natDegree_map_eq_of_injective (algebraMap k S).injective,
            natDegree_linear a.isUnit.ne_zero, mul_one]
    · rw [coeff_affine_substitution]
      exact hunit.ne_zero
  rw [Polynomial.leadingCoeff, hdeg, coeff_affine_substitution]
  exact hunit

/-- Preservation of a nonzero polynomial forces the scale raised to its degree to be one. -/
theorem scale_pow_eq_one_of_preserves [Nontrivial S] {f : k[X]} (hf : f ≠ 0)
    (a : Sˣ) (b : S)
    (hpres : (f.map (algebraMap k S)).comp (C (a : S) * X + C b) =
      f.map (algebraMap k S)) :
    (a : S) ^ f.natDegree = 1 := by
  have h := congrArg (fun p : S[X] => p.coeff f.natDegree) hpres
  rw [coeff_affine_substitution, coeff_map, coeff_natDegree] at h
  have hlc : IsUnit (algebraMap k S f.leadingCoeff) :=
    (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf)).map (algebraMap k S)
  apply hlc.mul_left_cancel
  simpa only [mul_one] using h

/-- The scale coordinate of a stabilizing affine substitution is integral. -/
theorem isIntegral_scale_of_preserves [Nontrivial S] {f : k[X]} (hf : 0 < f.natDegree)
    (a : Sˣ) (b : S)
    (hpres : (f.map (algebraMap k S)).comp (C (a : S) * X + C b) =
      f.map (algebraMap k S)) : IsIntegral k (a : S) := by
  refine ⟨X ^ f.natDegree - C 1, monic_X_pow_sub_C 1 hf.ne', ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, map_one,
    scale_pow_eq_one_of_preserves (ne_zero_of_natDegree_gt hf) a b hpres, sub_self]

/-- The inverse scale coordinate is integral as well: it satisfies the same power equation. -/
theorem isIntegral_inverse_scale_of_preserves [Nontrivial S] {f : k[X]}
    (hf : 0 < f.natDegree) (a : Sˣ) (b : S)
    (hpres : (f.map (algebraMap k S)).comp (C (a : S) * X + C b) =
      f.map (algebraMap k S)) : IsIntegral k (↑a⁻¹ : S) := by
  have ha := scale_pow_eq_one_of_preserves (ne_zero_of_natDegree_gt hf) a b hpres
  have hinv : (↑a⁻¹ : S) ^ f.natDegree = 1 := by
    have h : (↑a⁻¹ : S) ^ f.natDegree * (a : S) ^ f.natDegree = 1 := by
      rw [← mul_pow]
      simp
    simpa only [ha, mul_one] using h
  refine ⟨X ^ f.natDegree - C 1, monic_X_pow_sub_C 1 hf.ne', ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, map_one, hinv, sub_self]

/-- The constant coefficient of preservation is the equation `f(b) = f(0)`. -/
theorem aeval_translate_eq_of_preserves {f : k[X]} (a : Sˣ) (b : S)
    (hpres : (f.map (algebraMap k S)).comp (C (a : S) * X + C b) =
      f.map (algebraMap k S)) :
    aeval b f = algebraMap k S (f.coeff 0) := by
  have h := congrArg (fun p : S[X] => p.eval 0) hpres
  simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add,
    eval_map, eval₂_at_zero, aeval_def] using h

/-- The translation coordinate is integral by the nonzero equation `f(T)-f(0)`. -/
theorem isIntegral_translate_of_preserves {f : k[X]} (hf : 0 < f.natDegree)
    (a : Sˣ) (b : S)
    (hpres : (f.map (algebraMap k S)).comp (C (a : S) * X + C b) =
      f.map (algebraMap k S)) : IsIntegral k b := by
  apply IsAlgebraic.isIntegral
  refine ⟨f - C (f.coeff 0), ?_, ?_⟩
  · apply ne_zero_of_natDegree_gt
    simpa only [natDegree_sub_C] using hf
  · rw [map_sub, aeval_C, aeval_translate_eq_of_preserves a b hpres, sub_self]

end GromovWitten.AlgebraicGeometry.PolynomialAutomorphisms
