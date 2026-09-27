/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

/-!
# The explicit two-term dual complex of a nodal hypersurface

For the standard node `B = P/(xy - πⁿ)`, this file constructs the maps in the
displayed free resolution

`0 → P --(xy - πⁿ)→ P → B → 0`

and proves exactness.  Dualising the two free terms by `Hom_P(-, P)` leaves the
same multiplication map, so its degree-one cokernel is identified explicitly
with `B`.  This is the concrete local algebra behind the usual assertion
`Ext¹_P(B,P) ≅ B`; the latter derived-category notation is deliberately not
introduced here because this file records the finite projective complex and its
dual cokernel directly.
-/

open CategoryTheory Limits

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u

noncomputable section

variable (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ)

local notation "P" => MvPolynomial (Fin 2) R
local notation "B" => Ring R π n

/-! ### The free resolution and its exactness -/

/-- Multiplication by the node equation on the polynomial ring. -/
def hypersurfaceRelationMap : P →ₗ[P] P :=
  LinearMap.mulLeft P (equation R π n)

/-- The quotient map from the ambient polynomial ring to the node ring. -/
def hypersurfaceQuotientMap : P →ₗ[P] B :=
  (Ideal.Quotient.mkₐ P (relationIdeal R π n)).toLinearMap

omit [Nontrivial R] in
@[simp]
theorem hypersurfaceRelationMap_apply (p : P) :
    hypersurfaceRelationMap R π n p = p * equation R π n := by
  simp [hypersurfaceRelationMap, mul_comm]

omit [Nontrivial R] in
@[simp]
theorem hypersurfaceQuotientMap_apply (p : P) :
    hypersurfaceQuotientMap R π n p = Ideal.Quotient.mk (relationIdeal R π n) p := by
  simp [hypersurfaceQuotientMap]

theorem hypersurfaceRelationMap_injective :
    Function.Injective (hypersurfaceRelationMap R π n) := by
  intro p q hpq
  apply sub_eq_zero.mp
  have hzero : (p - q) * equation R π n = 0 := by
    simpa [sub_mul, hypersurfaceRelationMap_apply, mul_comm] using sub_eq_zero.mpr hpq
  have hreg := equation_isSMulRegular R π n
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg
  exact hreg (p - q) (by simpa [smul_eq_mul, mul_comm] using hzero)

omit [Nontrivial R] in
theorem hypersurfaceRelationMap_range :
    LinearMap.range (hypersurfaceRelationMap R π n) = relationIdeal R π n := by
  rw [hypersurfaceRelationMap, relationIdeal]
  exact Ideal.range_mul' (equation R π n)

omit [Nontrivial R] in
theorem hypersurfaceQuotientMap_ker :
    LinearMap.ker (hypersurfaceQuotientMap R π n) = relationIdeal R π n := by
  ext p
  rw [LinearMap.mem_ker]
  simp only [hypersurfaceQuotientMap]
  exact Ideal.Quotient.eq_zero_iff_mem

omit [Nontrivial R] in
theorem hypersurfaceQuotientMap_surjective :
    Function.Surjective (hypersurfaceQuotientMap R π n) := by
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨p, by simp [hypersurfaceQuotientMap]⟩

/- The displayed hypersurface sequence is exact at the middle term. -/
omit [Nontrivial R] in
theorem hypersurface_resolution_exact :
    Function.Exact (hypersurfaceRelationMap R π n) (hypersurfaceQuotientMap R π n) := by
  rw [LinearMap.exact_iff, hypersurfaceQuotientMap_ker, hypersurfaceRelationMap_range]

omit [Nontrivial R] in
/- The relation map lands in the kernel of the quotient map. -/
theorem hypersurface_resolution_comp_zero :
    (hypersurfaceQuotientMap R π n).comp (hypersurfaceRelationMap R π n) = 0 := by
  apply LinearMap.ext
  intro p
  exact (hypersurface_resolution_exact R π n).apply_apply_eq_zero p

/-! ### Dualising the displayed free resolution -/

/-- The degree-one dual differential, written as precomposition by the relation map.

Its source and target are the actual `P`-linear endomorphism modules
`Hom_P(P,P)`, rather than a free module chosen by hand. -/
def dualRelationMap : (P →ₗ[P] P) →ₗ[P] (P →ₗ[P] P) :=
  LinearMap.lcomp P P (hypersurfaceRelationMap R π n)

/-- Evaluation at `1` identifies `Hom_P(P,P)` with `P`. -/
noncomputable def endomorphismEvalEquiv (S : Type u) [CommRing S] :
    (MvPolynomial (Fin 2) S →ₗ[MvPolynomial (Fin 2) S] MvPolynomial (Fin 2) S) ≃ₗ[
      MvPolynomial (Fin 2) S] MvPolynomial (Fin 2) S :=
  { toFun := fun φ ↦ φ 1
    invFun := fun p ↦ LinearMap.mulLeft (MvPolynomial (Fin 2) S) p
    left_inv := by
      intro φ
      apply LinearMap.ext
      intro p
      simp only [LinearMap.mulLeft_apply]
      calc
        φ 1 * p = p * φ 1 := mul_comm _ _
        _ = φ p := by
          symm
          calc
            φ p = φ (p • (1 : MvPolynomial (Fin 2) S)) := by simp [smul_eq_mul]
            _ = p • φ 1 := map_smul φ p 1
            _ = p * φ 1 := by rfl
    right_inv := by
      intro p
      simp [LinearMap.mulLeft]
    map_add' := by
      intro φ ψ
      simp
    map_smul' := by
      intro p φ
      simp [smul_eq_mul] }

omit [Nontrivial R] in
theorem endomorphismEvalEquiv_apply (φ : P →ₗ[P] P) :
    endomorphismEvalEquiv R φ = φ 1 := rfl

omit [Nontrivial R] in
theorem endomorphismEvalEquiv_symm_apply (p : P) :
    (endomorphismEvalEquiv R).symm p = LinearMap.mulLeft P p := rfl

/- Evaluation at one turns precomposition by the relation into multiplication by the
hypersurface equation. -/
omit [Nontrivial R] in
theorem endomorphismEvalEquiv_dualRelationMap (φ : P →ₗ[P] P) :
    endomorphismEvalEquiv R (dualRelationMap R π n φ) =
      hypersurfaceRelationMap R π n (endomorphismEvalEquiv R φ) := by
  simp only [endomorphismEvalEquiv_apply, dualRelationMap, LinearMap.lcomp_apply,
    hypersurfaceRelationMap, LinearMap.mulLeft_apply]
  have hφ : ∀ z : P, φ z = z * φ 1 := by
    intro z
    calc
      φ z = φ (z • (1 : P)) := by simp [smul_eq_mul]
      _ = z • φ 1 := map_smul φ z 1
      _ = z * φ 1 := by rfl
  simpa using hφ (equation R π n)

/-- The quotient map in the dual complex is the quotient map after evaluation at one. -/
def dualQuotientMap : (P →ₗ[P] P) →ₗ[P] B :=
  (hypersurfaceQuotientMap R π n).comp (endomorphismEvalEquiv R).toLinearMap

omit [Nontrivial R] in
theorem dualQuotientMap_apply (φ : P →ₗ[P] P) :
    dualQuotientMap R π n φ =
      Ideal.Quotient.mk (relationIdeal R π n) (φ 1) := by
  simp [dualQuotientMap, hypersurfaceQuotientMap, endomorphismEvalEquiv]

omit [Nontrivial R] in
theorem dualRelationMap_range :
    LinearMap.range (dualRelationMap R π n) =
      (endomorphismEvalEquiv R).toLinearMap ⁻¹' (relationIdeal R π n) := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    change endomorphismEvalEquiv R (dualRelationMap R π n ψ) ∈ relationIdeal R π n
    rw [endomorphismEvalEquiv_dualRelationMap, ← hypersurfaceRelationMap_range]
    exact ⟨endomorphismEvalEquiv R ψ, rfl⟩
  · intro h
    let q : P := endomorphismEvalEquiv R φ
    have hq : q ∈ relationIdeal R π n := h
    rw [← hypersurfaceRelationMap_range R π n] at hq
    obtain ⟨p, hp⟩ := hq
    refine ⟨(endomorphismEvalEquiv R).symm p, ?_⟩
    apply (endomorphismEvalEquiv R).injective
    calc
      endomorphismEvalEquiv R
          (dualRelationMap R π n ((endomorphismEvalEquiv R).symm p)) =
          hypersurfaceRelationMap R π n p := by
            rw [endomorphismEvalEquiv_dualRelationMap]
            simp
      _ = endomorphismEvalEquiv R φ := by simpa [q] using hp

omit [Nontrivial R] in
theorem dualQuotientMap_ker :
    LinearMap.ker (dualQuotientMap R π n) = LinearMap.range (dualRelationMap R π n) := by
  ext φ
  constructor
  · intro h
    change dualQuotientMap R π n φ = 0 at h
    have hk : endomorphismEvalEquiv R φ ∈
        LinearMap.ker (hypersurfaceQuotientMap R π n) := by
      apply (LinearMap.mem_ker).2
      simpa [dualQuotientMap, endomorphismEvalEquiv] using h
    have hq : endomorphismEvalEquiv R φ ∈ relationIdeal R π n := by
      rw [← hypersurfaceQuotientMap_ker R π n]
      exact hk
    have hpre : φ ∈ (endomorphismEvalEquiv R).toLinearMap ⁻¹' (relationIdeal R π n) := hq
    have hmem := congrArg (fun N => φ ∈ N) (dualRelationMap_range R π n)
    exact hmem.mpr hpre
  · intro h
    rw [LinearMap.mem_ker]
    change dualQuotientMap R π n φ = 0
    change hypersurfaceQuotientMap R π n (endomorphismEvalEquiv R φ) = 0
    apply (LinearMap.mem_ker).1
    have hmem := congrArg (fun N => φ ∈ N) (dualRelationMap_range R π n)
    have hpre : φ ∈ (endomorphismEvalEquiv R).toLinearMap ⁻¹' (relationIdeal R π n) :=
      hmem.mp h
    have h' : endomorphismEvalEquiv R φ ∈ relationIdeal R π n := hpre
    exact (hypersurfaceQuotientMap_ker R π n).symm ▸ h'

omit [Nontrivial R] in
theorem dualQuotientMap_surjective :
    Function.Surjective (dualQuotientMap R π n) := by
  intro b
  obtain ⟨p, hp⟩ := hypersurfaceQuotientMap_surjective R π n b
  refine ⟨(endomorphismEvalEquiv R).symm p, ?_⟩
  simpa [dualQuotientMap, endomorphismEvalEquiv] using hp

/-! ### The explicit degree-one dual cokernel -/

/-- The cokernel of the dual differential, represented by the ordinary module quotient. -/
abbrev dualCokernel (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) : Type u :=
  (MvPolynomial (Fin 2) R →ₗ[MvPolynomial (Fin 2) R] MvPolynomial (Fin 2) R) ⧸
    LinearMap.range (dualRelationMap R π n)

instance dualCokernelModule : Module P (dualCokernel R π n) := inferInstance

/-- The degree-one dual cokernel of the free hypersurface complex is the node algebra. -/
noncomputable def dualCokernelEquiv :
    dualCokernel R π n ≃ₗ[P] B := by
  exact
    (Submodule.quotEquivOfEq (LinearMap.range (dualRelationMap R π n))
      (LinearMap.ker (dualQuotientMap R π n))
      (dualQuotientMap_ker R π n).symm).trans
      (LinearMap.quotKerEquivOfSurjective (dualQuotientMap R π n)
        (dualQuotientMap_surjective R π n))

@[simp]
theorem dualCokernelEquiv_apply_mk (p : P →ₗ[P] P) :
    dualCokernelEquiv R π n (Submodule.Quotient.mk p) =
      Ideal.Quotient.mk (relationIdeal R π n) (p 1) := by
  simp [dualCokernelEquiv, dualQuotientMap_apply]

@[simp]
theorem dualCokernelEquiv_symm_apply_quotient (p : P →ₗ[P] P) :
    (dualCokernelEquiv R π n).symm (Ideal.Quotient.mk (relationIdeal R π n) (p 1)) =
      Submodule.Quotient.mk p := by
  rw [LinearEquiv.symm_apply_eq]
  exact (dualCokernelEquiv_apply_mk R π n p).symm

/-- The node algebra is the actual cokernel of multiplication by its hypersurface equation. -/
theorem dualCokernel_is_nodeAlgebra :
    Nonempty (dualCokernel R π n ≃ₗ[P] B) :=
  ⟨dualCokernelEquiv R π n⟩

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
