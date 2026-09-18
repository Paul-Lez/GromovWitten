/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.Algebra.TensorSubspaceDistrib
import GromovWitten.AlgebraicGeometry.Cones.NormalConeProduct

/-!
# The filtration of the product ideal

This file collects the ideal-theoretic half of the computation of `gr_J(R ⊗[k] R')` for
`J = productIdeal k R R' I I'`, namely the exact description of the powers of `J`:

`J ^ n = Σ_{a + b = n} I^a · I'^b`   (`productIdeal_pow_eq`).

Together with the distributivity lemma `GromovWitten.Algebra.tensorSub_top_inf_top_tensorSub`
of `GromovWitten/Algebra/TensorSubspaceDistrib.lean`, this is the input for the identification

`J^n / J^(n+1) ≅ ⊕_{a + b = n} (I^a/I^(a+1)) ⊗_k (I'^b/I'^(b+1))`,

which would give injectivity of
`GromovWitten.AlgebraicGeometry.AffineNormalConeProduct.grTensorToGr` and hence discharge the
hypothesis of `grTensorEquiv`.

## Main results

* `Ideal.sup_pow_eq_sum`: in any commutative ring, `(I ⊔ J)^n = Σ_{a ≤ n} I^a · J^(n-a)`.  This
  is `add_pow` in the idempotent semiring of ideals, using that every positive natural number
  is `1` there (`natCast_eq_one_of_pos`).
* `productIdeal_pow_eq`: the resulting description of the powers of the product ideal, which
  upgrades the one-sided `le_productIdeal_pow` of `Cones/NormalConeProduct.lean` to an equality.

## What is *not* proved here

Injectivity of `grTensorToGr` is **not** discharged.  Two further steps are needed and are not
formalised:

1. the lattice identity for finite families, `(Σ_{a+b=n} I^a ⊗' I'^b) ⊓ (…)`, which needs
   `(A₁ ⊓ A₂) ⊗' ⊤ = (A₁ ⊗' ⊤) ⊓ (A₂ ⊗' ⊤)` in addition to
   `tensorSub_top_inf_top_tensorSub`, and then the degreewise isomorphism
   `J^n/J^(n+1) ≅ ⊕_{a+b=n} (I^a/I^(a+1)) ⊗_k (I'^b/I'^(b+1))`;
2. the passage from "injective in each degree" to "injective", which needs a grading on
   `AffineNormalCone.associatedGradedRing`; the repository currently defines it as a plain
   quotient `reesAlgebra I ⧸ I · reesAlgebra I` with no `GradedAlgebra` instance, so that
   grading would have to be constructed first.

Accordingly `grTensorEquiv` still carries its injectivity hypothesis.
-/

open scoped TensorProduct

namespace GromovWitten.Algebra

universe u

variable {S : Type u} [CommRing S]

/-- In the semiring of ideals, addition is idempotent, so every positive natural number casts
to the unit ideal. -/
theorem natCast_eq_one_of_pos {m : ℕ} (hm : 0 < m) : ((m : ℕ) : Ideal S) = 1 := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp
    · rw [Nat.cast_add, Nat.cast_one, ih h, Ideal.add_eq_sup, sup_idem]

/-- The binomial expansion for powers of a sum of two ideals: since addition of ideals is
idempotent, all binomial coefficients disappear. -/
theorem Ideal.sup_pow_eq_sum (I J : Ideal S) (n : ℕ) :
    (I ⊔ J) ^ n = ∑ a ∈ Finset.range (n + 1), I ^ a * J ^ (n - a) := by
  rw [← Ideal.add_eq_sup, add_pow]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at ha
  rw [natCast_eq_one_of_pos (Nat.choose_pos ha), mul_one]

end GromovWitten.Algebra

namespace GromovWitten.AlgebraicGeometry

namespace AffineNormalConeProduct

universe u

variable (k : Type u) [CommRing k] (R : Type u) [CommRing R] [Algebra k R]
  (R' : Type u) [CommRing R'] [Algebra k R'] (I : Ideal R) (I' : Ideal R')

/-- **The filtration of the product ideal.**  `J^n = Σ_{a + b = n} I^a · I'^b`, where `I^a` and
`I'^b` are extended to `R ⊗[k] R'` along the two inclusions.  This is the equality of which
`le_productIdeal_pow` is the easy inclusion. -/
theorem productIdeal_pow_eq (n : ℕ) :
    productIdeal k R R' I I' ^ n =
      ∑ a ∈ Finset.range (n + 1),
        Ideal.map (inl k R R') (I ^ a) * Ideal.map (inr k R R') (I' ^ (n - a)) := by
  rw [productIdeal, GromovWitten.Algebra.Ideal.sup_pow_eq_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Ideal.map_pow, Ideal.map_pow]

/-- Each summand of `productIdeal_pow_eq` is contained in the corresponding power, as already
recorded by `le_productIdeal_pow`; the two statements together say that the sum is exact. -/
theorem sum_le_productIdeal_pow (n : ℕ) :
    ∑ a ∈ Finset.range (n + 1),
        Ideal.map (inl k R R') (I ^ a) * Ideal.map (inr k R R') (I' ^ (n - a)) ≤
      productIdeal k R R' I I' ^ n :=
  le_of_eq (productIdeal_pow_eq k R R' I I' n).symm

end AffineNormalConeProduct

end GromovWitten.AlgebraicGeometry
