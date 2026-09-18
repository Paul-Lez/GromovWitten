/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DeformationSpace

/-!
# The grading of the affine normal cone

`AffineNormalCone.associatedGradedRing R I` is defined in `Cones/Affine.lean` as the quotient of
the Rees algebra `Rees_I(R) = ⊕_n I^n X^n ⊆ R[X]` by the ideal `I · Rees_I(R)`.  This file gives
it its `ℕ`-grading, in the form of a family of `R`-linear projections

`grProj R I n : gr_I(R) →ₗ[R] gr_I(R)`

onto the degree-`n` part, obtained from truncation of polynomials.  The essential input is the
coefficientwise description of the defining ideal,

`q ∈ I · Rees_I(R) ↔ ∀ m, (q : R[X]).coeff m ∈ I^(m+1)` (`mem_reesIdeal_iff`),

which combines `AffineNormalCone.coeff_mem_pow_succ_of_mem_map_rees` with
`AffineDeformationSpace.mem_map_of_forall_coeff_mem_pow_succ`.  It says exactly that the ideal
`I · Rees_I(R)` is homogeneous with degree-`m` part `I^(m+1) X^m`, so that the degree-`n` part of
the quotient is `I^n/I^(n+1)`.

## Main results

* `mem_reesIdeal_iff`: the defining ideal is homogeneous, described coefficientwise.
* `grProj`, `grProj_idem`, `grProj_comp_of_ne` (orthogonality) and `sum_grProj`
  (`x = Σ_{n < N} grProj n x` for `N` large): the degree decomposition.
* `grPiece n`, `mem_grPiece_iff`: the homogeneous parts.
* `eq_zero_of_forall_grProj_eq_zero` and `injective_of_degreewise`: a degree-preserving map that
  is injective on each homogeneous part is injective.  This is the form in which the grading is
  used to deduce injectivity of a comparison map from injectivity in each degree.
* `associatedGradedBaseRingHom_injective`: the degree-zero part really is `R ⧸ I`.
* `conormalToAssociatedGraded_injective`: the degree-one part really is the conormal module
  `I/I²`; equivalently the canonical map `N_{U/M} → C_{U/M}` is injective in degree one.

This file provides the grading as a family of orthogonal idempotent projections summing locally
finitely to the identity, rather than as a Mathlib `GradedAlgebra`/`DirectSum.Decomposition`
instance.  The two carry the same information, and the projection form is what the applications
(`injective_of_degreewise`) use; packaging it as a `DirectSum.Decomposition` would additionally
require choosing a degree bound for each element of the quotient and is not done here.
-/

open Polynomial

namespace GromovWitten.AlgebraicGeometry

namespace AffineNormalCone

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)

/-! ### The defining ideal is homogeneous -/

/-- **The ideal `I · Rees_I(R)` is homogeneous**, and is described coefficientwise: an element of
the Rees algebra lies in it exactly when its `m`-th coefficient already lies in `I^(m+1)`. -/
theorem mem_reesIdeal_iff (q : reesAlgebra I) :
    q ∈ Ideal.map (algebraMap R (reesAlgebra I)) I ↔
      ∀ m : ℕ, (q : Polynomial R).coeff m ∈ I ^ (m + 1) :=
  ⟨fun hq ↦ coeff_mem_pow_succ_of_mem_map_rees R I hq,
    AffineDeformationSpace.mem_map_of_forall_coeff_mem_pow_succ R I q⟩

/-! ### Truncation on the Rees algebra -/

/-- The degree-`n` monomial truncation of a Rees element stays in the Rees algebra. -/
theorem monomial_coeff_mem_reesAlgebra (n : ℕ) (p : reesAlgebra I) :
    (Polynomial.monomial n ((p : Polynomial R).coeff n)) ∈ reesAlgebra I :=
  reesAlgebra.monomial_mem.mpr ((mem_reesAlgebra_iff I _).mp p.2 n)

/-- Degree-`n` truncation, as an `R`-linear endomorphism of the Rees algebra. -/
noncomputable def reesProj (n : ℕ) : reesAlgebra I →ₗ[R] reesAlgebra I where
  toFun p := ⟨Polynomial.monomial n ((p : Polynomial R).coeff n),
    monomial_coeff_mem_reesAlgebra R I n p⟩
  map_add' p q := by
    apply Subtype.ext
    simp
  map_smul' r p := by
    apply Subtype.ext
    simp [Polynomial.smul_monomial]

@[simp]
theorem coe_reesProj (n : ℕ) (p : reesAlgebra I) :
    ((reesProj R I n p : reesAlgebra I) : Polynomial R) =
      Polynomial.monomial n ((p : Polynomial R).coeff n) := rfl

/-- A Rees element of degree `< N` is the sum of its truncations. -/
theorem sum_reesProj (p : reesAlgebra I) {N : ℕ} (hN : (p : Polynomial R).natDegree < N) :
    ∑ n ∈ Finset.range N, reesProj R I n p = p := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  exact (Polynomial.as_sum_range' (p : Polynomial R) N hN).symm

/-! ### The grading of the associated graded ring -/

/-- Truncation descends to the associated graded ring. -/
theorem reesProj_mem_reesIdeal (n : ℕ) {q : reesAlgebra I}
    (hq : q ∈ Ideal.map (algebraMap R (reesAlgebra I)) I) :
    reesProj R I n q ∈ Ideal.map (algebraMap R (reesAlgebra I)) I := by
  rw [mem_reesIdeal_iff] at hq ⊢
  intro m
  rw [coe_reesProj, Polynomial.coeff_monomial]
  split_ifs with h
  · subst h
    exact hq _
  · exact Ideal.zero_mem _

/-- The degree-`n` projection of the associated graded ring. -/
noncomputable def grProj (n : ℕ) :
    associatedGradedRing R I →ₗ[R] associatedGradedRing R I :=
  Submodule.liftQ ((Ideal.map (algebraMap R (reesAlgebra I)) I).restrictScalars R)
    (((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I)).toLinearMap).comp
      (reesProj R I n))
    (fun q hq ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (reesProj_mem_reesIdeal R I n hq))

@[simp]
theorem grProj_mk (n : ℕ) (p : reesAlgebra I) :
    grProj R I n (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I) p) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I) (reesProj R I n p) := rfl

/-- The projections are idempotent. -/
theorem grProj_idem (n : ℕ) (x : associatedGradedRing R I) :
    grProj R I n (grProj R I n x) = grProj R I n x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [grProj_mk, grProj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_reesProj, coe_reesProj, Polynomial.coeff_monomial, if_pos rfl]

/-- Projections in different degrees are orthogonal. -/
theorem grProj_comp_of_ne {m n : ℕ} (h : m ≠ n) (x : associatedGradedRing R I) :
    grProj R I m (grProj R I n x) = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [grProj_mk, grProj_mk]
  have hz : reesProj R I m (reesProj R I n p) = 0 := by
    apply Subtype.ext
    rw [coe_reesProj, coe_reesProj, Polynomial.coeff_monomial, if_neg (Ne.symm h)]
    simp
  rw [hz, map_zero]

/-- Every element of the associated graded ring is the sum of finitely many of its homogeneous
parts. -/
theorem sum_grProj (x : associatedGradedRing R I) :
    ∃ N : ℕ, ∑ n ∈ Finset.range N, grProj R I n x = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(p : Polynomial R).natDegree + 1, ?_⟩
  rw [Finset.sum_congr rfl fun n _ ↦ grProj_mk R I n p, ← map_sum,
    sum_reesProj R I p (Nat.lt_succ_self _)]

/-- If all homogeneous parts of an element vanish, the element vanishes. -/
theorem eq_zero_of_forall_grProj_eq_zero {x : associatedGradedRing R I}
    (h : ∀ n, grProj R I n x = 0) : x = 0 := by
  obtain ⟨N, hN⟩ := sum_grProj R I x
  rw [← hN, Finset.sum_congr rfl fun n _ ↦ h n, Finset.sum_const_zero]

/-- The degree-`n` homogeneous part of the associated graded ring. -/
noncomputable def grPiece (n : ℕ) : Submodule R (associatedGradedRing R I) :=
  LinearMap.range (grProj R I n)

/-- Membership in the degree-`n` part is the fixed-point condition for the `n`-th projection. -/
theorem mem_grPiece_iff (n : ℕ) (x : associatedGradedRing R I) :
    x ∈ grPiece R I n ↔ grProj R I n x = x := by
  rw [grPiece, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact grProj_idem R I n y
  · intro h
    exact ⟨x, h⟩

/-- The image of the `n`-th projection lies in the degree-`n` part. -/
theorem grProj_mem_grPiece (n : ℕ) (x : associatedGradedRing R I) :
    grProj R I n x ∈ grPiece R I n := by
  rw [grPiece, LinearMap.mem_range]
  exact ⟨x, rfl⟩

/-- **Degreewise injectivity implies injectivity.**  A linear map out of the associated graded
ring which intertwines the degree projections with a family of maps on the target, and which is
injective on each homogeneous part, is injective. -/
theorem injective_of_degreewise {M : Type u} [AddCommGroup M] [Module R M]
    (φ : associatedGradedRing R I →ₗ[R] M) (proj : ℕ → M →ₗ[R] M)
    (hcomm : ∀ (n : ℕ) (x : associatedGradedRing R I), φ (grProj R I n x) = proj n (φ x))
    (hinj : ∀ (n : ℕ) (x : associatedGradedRing R I), x ∈ grPiece R I n → φ x = 0 → x = 0) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_forall_grProj_eq_zero R I fun n ↦ ?_
  refine hinj n _ (grProj_mem_grPiece R I n x) ?_
  rw [hcomm n x, hx, map_zero]

/-! ### The homogeneous parts in degrees zero and one -/

/-- **The degree-zero part is `R ⧸ I`**: the structural map `R ⧸ I → gr_I(R)` is injective. -/
theorem associatedGradedBaseRingHom_injective :
    Function.Injective (associatedGradedBaseRingHom R I) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hmem : (algebraMap R (reesAlgebra I) a) ∈ Ideal.map (algebraMap R (reesAlgebra I)) I := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem]
  rw [mem_reesIdeal_iff] at hmem
  have h0 := hmem 0
  have hc : ((algebraMap R (reesAlgebra I) a : reesAlgebra I) : Polynomial R).coeff 0 = a := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hc, pow_one] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr h0

/-- **The degree-one part is the conormal module `I/I²`**: the canonical degree-one map
`I/I² → gr_I(R)` is injective.  Equivalently, the comparison `N_{U/M} → C_{U/M}` of
`AffineNormalCone.normalSheafCoordinateMap` is injective in degree one. -/
theorem conormalToAssociatedGraded_injective :
    Function.Injective (conormalToAssociatedGraded R I) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective z
  rw [conormalToAssociatedGraded_toCotangent, Ideal.Quotient.eq_zero_iff_mem,
    mem_reesIdeal_iff] at hz
  have h1 := hz 1
  rw [degreeOneRees_coe, Polynomial.coeff_monomial, if_pos rfl] at h1
  exact (I.toCotangent_eq_zero y).mpr h1

end AffineNormalCone

end GromovWitten.AlgebraicGeometry
