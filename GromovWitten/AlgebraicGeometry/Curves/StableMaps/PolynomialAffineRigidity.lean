/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.PolynomialAffineIntegral
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Ideal.Operations

/-!
# Infinitesimal rigidity of separable affine-linear substitutions

Two affine-linear substitutions preserving a polynomial with nonzero derivative agree if
their coordinates agree modulo a square-zero ideal. The test algebra may have nilpotents.
Taylor's formula reduces the assertion to cancellation of a polynomial with unit leading
coefficient.
-/

namespace GromovWitten.AlgebraicGeometry.PolynomialAutomorphisms

open Polynomial

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]

/-- Affine-linear symmetries of a polynomial with nonzero derivative have unique lifts through
arbitrary square-zero ideals of the coefficient algebra. -/
theorem affine_substitutions_eq_of_sq_zero {f : k[X]} (hf : f.derivative ≠ 0)
    (I : Ideal S) (hI : I ^ 2 = ⊥) (a a' : Sˣ) (b b' : S)
    (ha : (a' : S) - (a : S) ∈ I) (hb : b' - b ∈ I)
    (hpres : (f.map (algebraMap k S)).comp (C (a : S) * X + C b) =
      f.map (algebraMap k S))
    (hpres' : (f.map (algebraMap k S)).comp (C (a' : S) * X + C b') =
      f.map (algebraMap k S)) : a' = a ∧ b' = b := by
  nontriviality S
  have hmul {x y : S} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
    have h := Ideal.mul_mem_mul hx hy
    rw [← pow_two, hI, Ideal.mem_bot] at h
    exact h
  let z : S[X] := C (a : S) * X + C b
  let h : S[X] := C ((a' : S) - (a : S)) * X + C (b' - b)
  have hsq : h ^ 2 = 0 := by
    have haa := hmul ha ha
    have hab := hmul ha hb
    have hbb := hmul hb hb
    dsimp [h]
    calc
      _ = C (((a' : S) - (a : S)) * ((a' : S) - (a : S))) * X ^ 2 +
          C (2 * (((a' : S) - (a : S)) * (b' - b))) * X +
          C ((b' - b) * (b' - b)) := by simp only [map_mul, map_ofNat]; ring
      _ = 0 := by simp [haa, hab, hbb]
  have hzh : z + h = C (a' : S) * X + C b' := by
    dsimp [z, h]
    simp only [map_sub]
    ring
  have ht := Polynomial.aeval_add_of_sq_eq_zero (f.map (algebraMap k S)) z h hsq
  change (f.map (algebraMap k S)).comp (z + h) =
    (f.map (algebraMap k S)).comp z +
      (f.map (algebraMap k S)).derivative.comp z * h at ht
  rw [hzh, hpres', hpres, Polynomial.derivative_map] at ht
  have hprod : (f.derivative.map (algebraMap k S)).comp z * h = 0 := by
    exact add_left_cancel (show f.map (algebraMap k S) +
      (f.derivative.map (algebraMap k S)).comp z * h = f.map (algebraMap k S) + 0 by
        simpa only [add_zero] using ht.symm)
  have hz : IsUnit ((f.derivative.map (algebraMap k S)).comp z).leadingCoeff :=
    isUnit_leadingCoeff_affine_substitution hf a b
  have hh : h = 0 := (Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hz).mp hprod
  constructor
  · apply Units.ext
    have hx := congrArg (fun q : S[X] => q.coeff 1) hh
    simpa [h, sub_eq_zero] using hx
  · have hx := congrArg (fun q : S[X] => q.coeff 0) hh
    simpa [h, sub_eq_zero] using hx

end GromovWitten.AlgebraicGeometry.PolynomialAutomorphisms
