/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.SemilocalNormOrder
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Norm.Defs

/-!
# The order of an integral element of a fraction field

This file proves the algebraic input to Fulton's Proposition 1.4 / Stacks 42.20.3 needed for the
case where a rational function `φ` on the source of a dominant morphism `h : V ⟶ V'` of integral
schemes is algebraic over the function field `K` of `V'`: at a codimension-one point `x` of `V`
with `h x = η'` (the generic point of `V'`), the order of vanishing of `φ` at `x` is zero.

The geometric input is: `R := V.presheaf.stalk x` is a Noetherian local domain of Krull dimension
one with fraction field `L := K(V)`, and `φ` is algebraic over `K ⊆ L`, hence integral over `K`,
hence (being already a ratio of elements of the Noetherian domain `R`) integral over `R`; likewise
`φ⁻¹`. This file proves the corresponding purely algebraic statement:

* **Lemma A1** (`ordFrac_integral_eq_ofAdd_natCast`): for `R` a Noetherian local domain of Krull
  dimension `≤ 1` with fraction field `F`, every nonzero `y ∈ F` integral over `R` has
  `Ring.ordFrac R y = Multiplicative.ofAdd (n : ℤ)` for some `n : ℕ`, i.e. a non-negative order of
  vanishing. The proof applies `B := Algebra.adjoin R {y}` (a domain, module-finite over `R` by
  `Algebra.finite_adjoin_simple_of_isIntegral`, with fraction field `F` by Mathlib's
  `Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra`) to the
  semilocal norm formula `semilocal_length_quotient_span_eq_ordFrac_norm` of
  `GromovWitten/Algebra/SemilocalNormOrder.lean`, with `K = L = F` and the norm over the trivial
  extension `F/F` the identity on `F` (`Algebra.norm_algebraMap`, `Module.finrank_self`).
* **Lemma A1'** (`ordFrac_eq_one_of_integral_of_inv_integral`): if in addition `y⁻¹` is integral
  over `R`, then `Ring.ordFrac R y = 1`, i.e. the order of vanishing is exactly zero (the two
  non-negative orders of `y` and `y⁻¹` from Lemma A1 are negatives of each other, hence both zero).
* `ordFrac_eq_ofAdd_zero_of_integral_of_inv_integral`: the same fact restated as
  `Ring.ordFrac R y = Multiplicative.ofAdd (0 : ℤ)` (a convenience form; the geometric
  consumer `ProperPushforwardCurve.ord_eq_zero_of_isAlgebraic` uses Lemma A1' directly).

## Main results

* `GromovWitten.Algebra.ordFrac_integral_eq_ofAdd_natCast`
* `GromovWitten.Algebra.ordFrac_eq_one_of_integral_of_inv_integral`
* `GromovWitten.Algebra.ordFrac_eq_ofAdd_zero_of_integral_of_inv_integral`
-/

namespace GromovWitten.Algebra

section LemmaA1

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsLocalRing R]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- **Lemma A1.** `R` a Noetherian local domain with `Ring.KrullDimLE 1 R`, `F` a fraction field of
`R`, `y ∈ F` integral over `R` and nonzero. Then `Ring.ordFrac R y` is a non-negative integer
power `Multiplicative.ofAdd (n : ℤ)` of the generator. -/
theorem ordFrac_integral_eq_ofAdd_natCast [IsDomain R] {y : F} (hy : IsIntegral R y)
    (hy0 : y ≠ 0) : ∃ n : ℕ, Ring.ordFrac R y = Multiplicative.ofAdd (n : ℤ) := by
  set B : Subalgebra R F := Algebra.adjoin R {y} with hBdef
  have hyB : y ∈ B := Algebra.self_mem_adjoin_singleton R y
  have hfin : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hy
  have hfaithful : FaithfulSMul R B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a a' haa'
    apply FaithfulSMul.algebraMap_injective R F
    rw [IsScalarTower.algebraMap_apply R B F a, IsScalarTower.algebraMap_apply R B F a', haa']
  -- Mathlib: a subalgebra of a fraction field of `R` has the same fraction field.
  have hfracB : IsFractionRing B F := inferInstance
  set b : B := ⟨y, hyB⟩ with hbdef
  have hbne : b ≠ 0 := fun hcontra => hy0 (congrArg Subtype.val hcontra)
  have key := semilocal_length_quotient_span_eq_ordFrac_norm (A := R) (B := B) (K := F) (L := F)
    hbne
  have hbF : algebraMap B F b = y := by simp [hbdef]
  have hnorm : Algebra.norm F (algebraMap B F b) = y := by
    rw [hbF]
    have hnorm' : Algebra.norm F (algebraMap F F y) = y ^ Module.finrank F F :=
      Algebra.norm_algebraMap (R := F) (S := F) y
    rwa [Module.finrank_self, pow_one] at hnorm'
  exact ⟨(Module.length R (B ⧸ (Ideal.span {b} : Ideal B))).toNat, by rwa [hnorm] at key⟩

/-- **Lemma A1'.** Same hypotheses on `R`, `F`; `y ∈ F` with both `y` and `y⁻¹` integral over `R`.
Then `Ring.ordFrac R y = 1`. -/
theorem ordFrac_eq_one_of_integral_of_inv_integral [IsDomain R] {y : F} (hy : IsIntegral R y)
    (hy' : IsIntegral R y⁻¹) (hy0 : y ≠ 0) : Ring.ordFrac R y = 1 := by
  obtain ⟨n, hn⟩ := ordFrac_integral_eq_ofAdd_natCast R hy hy0
  obtain ⟨m, hm⟩ := ordFrac_integral_eq_ofAdd_natCast R hy' (inv_ne_zero hy0)
  have hmul : Ring.ordFrac R y * Ring.ordFrac R y⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
  rw [hn, hm, ← WithZero.coe_mul, ← ofAdd_add] at hmul
  have hsum : (n : ℤ) + (m : ℤ) = 0 := ofAdd_eq_one.mp (WithZero.coe_inj.mp hmul)
  have hn0 : n = 0 := by omega
  rw [hn, hn0]
  simp

/-- Lemma A1' restated with the right-hand side written as `Multiplicative.ofAdd (0 : ℤ)`, the
shape of the right-hand side of `AlgebraicGeometry.Scheme.ord_eq_iff` for `n = 0`. -/
theorem ordFrac_eq_ofAdd_zero_of_integral_of_inv_integral [IsDomain R] {y : F}
    (hy : IsIntegral R y) (hy' : IsIntegral R y⁻¹) (hy0 : y ≠ 0) :
    Ring.ordFrac R y = Multiplicative.ofAdd (0 : ℤ) :=
  (ordFrac_eq_one_of_integral_of_inv_integral R hy hy' hy0).trans (by simp)

end LemmaA1

end GromovWitten.Algebra
