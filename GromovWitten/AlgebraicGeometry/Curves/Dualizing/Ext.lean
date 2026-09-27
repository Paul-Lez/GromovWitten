/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.Dualizing.NodeHypersurface
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNodeBaseChange
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Genuine Ext for the standard nodal hypersurface

The two-term resolution from `NodeHypersurface` is packaged as a short exact
sequence in `ModuleCat`.  The connecting map in the actual long exact Ext
sequence identifies its degree-one Ext group with the cokernel of the dual
differential, and hence with the node algebra itself.
-/

open CategoryTheory Limits
open CategoryTheory Abelian
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u

noncomputable section

variable (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ)

local notation "P" => MvPolynomial (Fin 2) R
local notation "B" => Ring R π n

/-! ## The short exact sequence in `ModuleCat` -/

/-- The actual short complex associated to the node resolution. -/
abbrev nodeResolutionShortComplex : ShortComplex (ModuleCat P) :=
  ModuleCat.shortComplexOfCompEqZero (hypersurfaceRelationMap R π n)
    (hypersurfaceQuotientMap R π n) (hypersurface_resolution_comp_zero R π n)

omit [Nontrivial R] in
@[simp]
theorem nodeResolutionShortComplex_f :
    (nodeResolutionShortComplex R π n).f =
      ModuleCat.ofHom (hypersurfaceRelationMap R π n) := rfl

omit [Nontrivial R] in
@[simp]
theorem nodeResolutionShortComplex_g :
    (nodeResolutionShortComplex R π n).g =
      ModuleCat.ofHom (hypersurfaceQuotientMap R π n) := rfl

theorem nodeResolutionShortComplex_shortExact :
    (nodeResolutionShortComplex R π n).ShortExact := by
  refine ModuleCat.shortComplex_shortExact (nodeResolutionShortComplex R π n) ?_ ?_ ?_
  · change Function.Exact (hypersurfaceRelationMap R π n) (hypersurfaceQuotientMap R π n)
    exact hypersurface_resolution_exact R π n
  · change Function.Injective (hypersurfaceRelationMap R π n)
    exact hypersurfaceRelationMap_injective R π n
  · change Function.Surjective (hypersurfaceQuotientMap R π n)
    exact hypersurfaceQuotientMap_surjective R π n

/-! ## The actual Ext connecting map -/

abbrev nodeExtZero : Type u :=
  Abelian.Ext (ModuleCat.of P P) (ModuleCat.of P P) 0

abbrev nodeExtOne : Type u :=
  Abelian.Ext (ModuleCat.of P B) (ModuleCat.of P P) 1

/-- The map induced by precomposition with the first map of the resolution. -/
noncomputable def nodeExtDualDifferential : nodeExtZero R →ₗ[P] nodeExtZero R :=
  (Ext.mk₀ (nodeResolutionShortComplex R π n).f).precompOfLinear P
    (ModuleCat.of P P) (zero_add 0)

/-- The genuine connecting map `Hom_P(P,P) → Ext¹_P(B,P)`. -/
noncomputable def nodeExtConnecting : nodeExtZero R →ₗ[P] nodeExtOne R π n :=
  (nodeResolutionShortComplex_shortExact R π n).extClass.precompOfLinear P
    (ModuleCat.of P P) (add_comm 1 0)

theorem nodeExtDualDifferential_connecting_exact :
    Function.Exact (nodeExtDualDifferential R π n) (nodeExtConnecting R π n) := by
  have h := Ext.contravariant_sequence_exact₁'
    (nodeResolutionShortComplex_shortExact R π n) (ModuleCat.of P P) 0 1 (add_comm 1 0)
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  change Function.Exact
    ((Ext.mk₀ (nodeResolutionShortComplex R π n).f).precomp
      (ModuleCat.of P P) (zero_add 0))
    ((nodeResolutionShortComplex_shortExact R π n).extClass.precomp
      (ModuleCat.of P P) (add_comm 1 0))
  exact h

theorem nodeExtConnecting_surjective :
    Function.Surjective (nodeExtConnecting R π n) := by
  let _ : Projective (nodeResolutionShortComplex R π n).X₂ := by
    change Projective (ModuleCat.of P P)
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis P P)
  exact precomp_extClass_surjective_of_projective_X₂ (ModuleCat.of P P)
    (nodeResolutionShortComplex_shortExact R π n) 0

theorem nodeExtDualDifferential_range_eq_connecting_ker :
    LinearMap.range (nodeExtDualDifferential R π n) =
      LinearMap.ker (nodeExtConnecting R π n) := by
  exact (LinearMap.exact_iff.mp (nodeExtDualDifferential_connecting_exact R π n)).symm

/-- The quotient of the actual degree-zero Ext group by the dual differential is actual
`Ext¹_P(B,P)`, obtained from the connecting homomorphism in the long exact sequence. -/
noncomputable def nodeExtOneQuotientEquiv :
    (nodeExtZero R ⧸ LinearMap.range (nodeExtDualDifferential R π n)) ≃ₗ[P]
      nodeExtOne R π n := by
  exact
    (Submodule.quotEquivOfEq (LinearMap.range (nodeExtDualDifferential R π n))
      (LinearMap.ker (nodeExtConnecting R π n))
      (nodeExtDualDifferential_range_eq_connecting_ker R π n)).trans
      (LinearMap.quotKerEquivOfSurjective (nodeExtConnecting R π n)
        (nodeExtConnecting_surjective R π n))

/-! ## Comparison with the explicit dual complex -/

/-- The degree-zero Ext/Hom equivalence, followed by `ModuleCat`'s linear Hom equivalence. -/
noncomputable def nodeExtZeroToEnd : nodeExtZero R ≃ₗ[P]
    (P →ₗ[P] P) :=
  (Ext.linearEquiv₀ (R := P)).trans ModuleCat.homLinearEquiv

omit [Nontrivial R] in
theorem nodeExtZeroToEnd_apply (a : nodeExtZero R) :
    nodeExtZeroToEnd R a =
      (Ext.linearEquiv₀ (R := P) a).hom := by
  rfl

omit [Nontrivial R] in
theorem nodeExtZeroToEnd_mk
    (h : ModuleCat.of P P ⟶ ModuleCat.of P P) :
    nodeExtZeroToEnd R (Ext.mk₀ h) = h.hom := by
  rw [nodeExtZeroToEnd_apply]
  change (Ext.linearEquiv₀ (R := P) (Ext.mk₀ h)).hom = h.hom
  simp only [← Ext.linearEquiv₀_symm_apply (R := P) h,
    LinearEquiv.apply_symm_apply]

omit [Nontrivial R] in
theorem nodeExtDualDifferential_mk
    (h : ModuleCat.of P P ⟶ ModuleCat.of P P) :
    nodeExtDualDifferential R π n (Ext.mk₀ h) =
      Ext.mk₀ ((nodeResolutionShortComplex R π n).f ≫ h) := by
  change (Ext.mk₀ (nodeResolutionShortComplex R π n).f).comp
    (Ext.mk₀ h) (zero_add 0) = _
  rw [Ext.mk₀_comp_mk₀]

omit [Nontrivial R] in
theorem nodeExtZeroToEnd_dualDifferential (a : nodeExtZero R) :
    nodeExtZeroToEnd R (nodeExtDualDifferential R π n a) =
      dualRelationMap R π n (nodeExtZeroToEnd R a) := by
  rw [← Ext.mk₀_linearEquiv₀_apply (R := P) a]
  rw [nodeExtDualDifferential_mk]
  rw [nodeExtZeroToEnd_mk, nodeExtZeroToEnd_mk]
  apply (endomorphismEvalEquiv R).injective
  change ((Ext.linearEquiv₀ (R := P) a).hom.comp
      (hypersurfaceRelationMap R π n)) 1 =
    endomorphismEvalEquiv R
      (dualRelationMap R π n ((Ext.linearEquiv₀ (R := P) a).hom))
  rw [endomorphismEvalEquiv_dualRelationMap]
  simp only [LinearMap.comp_apply, hypersurfaceRelationMap_apply, one_mul,
    endomorphismEvalEquiv_apply]
  calc
    (Ext.linearEquiv₀ (R := P) a).hom (equation R π n) =
        equation R π n • (Ext.linearEquiv₀ (R := P) a).hom 1 := by
      calc
        (Ext.linearEquiv₀ (R := P) a).hom (equation R π n) =
            (Ext.linearEquiv₀ (R := P) a).hom
              (equation R π n • (1 : P)) := by
                simp [smul_eq_mul]
        _ = equation R π n • (Ext.linearEquiv₀ (R := P) a).hom 1 := by
          rw [map_smul]
    _ = equation R π n * (Ext.linearEquiv₀ (R := P) a).hom 1 := by
      rfl
    _ = (Ext.linearEquiv₀ (R := P) a).hom 1 * equation R π n := by
      rw [mul_comm]

omit [Nontrivial R] in
theorem nodeExtZeroToEnd_map_range :
    (LinearMap.range (nodeExtDualDifferential R π n)).map
        (nodeExtZeroToEnd R).toLinearMap =
      LinearMap.range (dualRelationMap R π n) := by
  apply le_antisymm
  · rintro z ⟨a, ⟨b, rfl⟩, rfl⟩
    refine ⟨nodeExtZeroToEnd R b, ?_⟩
    exact (nodeExtZeroToEnd_dualDifferential R π n b).symm
  · rintro z ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (nodeExtZeroToEnd R).surjective a
    refine ⟨nodeExtDualDifferential R π n b, ⟨b, rfl⟩, ?_⟩
    exact nodeExtZeroToEnd_dualDifferential R π n b

/-- The quotient in the genuine Ext calculation is the explicit degree-one dual cokernel. -/
noncomputable def nodeExtOneQuotientToDualCokernel :
      (nodeExtZero R ⧸ LinearMap.range (nodeExtDualDifferential R π n)) ≃ₗ[P]
      dualCokernel R π n := by
  exact Submodule.Quotient.equiv
    (LinearMap.range (nodeExtDualDifferential R π n))
    (LinearMap.range (dualRelationMap R π n))
    (nodeExtZeroToEnd R)
    (nodeExtZeroToEnd_map_range R π n)

/-- For the displayed hypersurface equation and its chosen free resolution, the actual derived
`Ext¹` group of the node is identified with the node algebra.  This is a presentation-relative
identification; it does not assert chart independence or a global dualizing sheaf. -/
noncomputable def nodeExtOneEquivNode : nodeExtOne R π n ≃ₗ[P] B :=
  (nodeExtOneQuotientEquiv R π n).symm.trans
    ((nodeExtOneQuotientToDualCokernel R π n).trans (dualCokernelEquiv R π n))

/-! ## Degree zero -/

/-- Every `P`-linear map from the node algebra to the ambient polynomial ring is zero. -/
theorem nodeHomNodeToAmbient_eq_zero
    (h : ModuleCat.of P B ⟶ ModuleCat.of P P) : h = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  let I := relationIdeal R π n
  have hmk_smul (q : P) : Ideal.Quotient.mk I q = q • (1 : B) := by
    have hm := (Ideal.Quotient.mkₐ P I).toLinearMap.map_smul q (1 : P)
    simpa [smul_eq_mul] using hm
  have heq_mem : equation R π n ∈ I :=
    Ideal.subset_span (Set.mem_singleton _)
  have hq : Ideal.Quotient.mk I (equation R π n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr heq_mem
  have hqsmul : equation R π n • (1 : B) = 0 := by
    rw [← hmk_smul (equation R π n)]
    exact hq
  have hone : h.hom 1 = 0 := by
    have hz : equation R π n • h.hom 1 = 0 := by
      rw [← map_smul, hqsmul, map_zero]
    have hreg := equation_isSMulRegular R π n
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg
    exact hreg _ hz
  rw [hmk_smul p, map_smul, hone, smul_zero]
  simp

/-- The degree-zero Ext group from the node to the ambient polynomial ring vanishes. -/
theorem nodeExtZeroNode_eq_zero
    (e : Abelian.Ext (ModuleCat.of P B) (ModuleCat.of P P) 0) : e = 0 := by
  apply (Ext.linearEquiv₀ (R := P)).injective
  simpa using nodeHomNodeToAmbient_eq_zero R π n (Ext.linearEquiv₀ (R := P) e)

/-! ## The projective-dimension boundary -/

/-- The node has projective dimension at most one, so its higher Ext groups vanish. -/
theorem nodeExt_eq_zero_of_two_le {i : ℕ} (hi : 2 ≤ i)
    (e : Abelian.Ext (ModuleCat.of P B) (ModuleCat.of P P) i) : e = 0 := by
  let h₁ : HasProjectiveDimensionLT (nodeResolutionShortComplex R π n).X₁ 1 := by
    change HasProjectiveDimensionLT (ModuleCat.of P P) 1
    infer_instance
  let h₂ : HasProjectiveDimensionLT (nodeResolutionShortComplex R π n).X₂ 2 := by
    change HasProjectiveDimensionLT (ModuleCat.of P P) 2
    infer_instance
  let _ : HasProjectiveDimensionLT (ModuleCat.of P B) 2 := by
    exact (nodeResolutionShortComplex_shortExact R π n).hasProjectiveDimensionLT_X₃ 1 h₁ h₂
  exact e.eq_zero_of_hasProjectiveDimensionLT 2 hi

/-! ## Arbitrary coefficient base change of the computed dual cokernel -/

section BaseChange

universe v

variable (S : Type v) [CommRing S] [Nontrivial S] [Algebra R S]

local notation "PS" => MvPolynomial (Fin 2) S

/-- Scalar extension of the actual polynomial endomorphism module, expressed through evaluation
at one.  This is the coefficient map on the Hom terms of the displayed resolution. -/
noncomputable def endomorphismBaseChangeEquiv :
    S ⊗[R] (MvPolynomial (Fin 2) R →ₗ[MvPolynomial (Fin 2) R]
      MvPolynomial (Fin 2) R) ≃ₗ[S]
      (MvPolynomial (Fin 2) S →ₗ[MvPolynomial (Fin 2) S]
        MvPolynomial (Fin 2) S) :=
  let e₁ :
      S ⊗[R] (MvPolynomial (Fin 2) R →ₗ[MvPolynomial (Fin 2) R]
        MvPolynomial (Fin 2) R) ≃ₗ[S] S ⊗[R] MvPolynomial (Fin 2) R :=
    LinearEquiv.baseChange R S _ _ ((endomorphismEvalEquiv R).restrictScalars R)
  let e₂ : S ⊗[R] MvPolynomial (Fin 2) R ≃ₗ[S] MvPolynomial (Fin 2) S :=
    (MvPolynomial.algebraTensorAlgEquiv R S).toLinearEquiv
  let e₃ : MvPolynomial (Fin 2) S ≃ₗ[S]
      (MvPolynomial (Fin 2) S →ₗ[MvPolynomial (Fin 2) S] MvPolynomial (Fin 2) S) :=
    (endomorphismEvalEquiv S).symm.restrictScalars S
  e₁.trans (e₂.trans e₃)

omit [Nontrivial R] [Nontrivial S] in
@[simp]
theorem endomorphismBaseChangeEquiv_tmul_apply_one
    (s : S) (φ : MvPolynomial (Fin 2) R →ₗ[MvPolynomial (Fin 2) R]
      MvPolynomial (Fin 2) R) :
    endomorphismBaseChangeEquiv R S (s ⊗ₜ[R] φ) 1 =
      s • MvPolynomial.map (algebraMap R S) (φ 1) := by
  simp [endomorphismBaseChangeEquiv, endomorphismEvalEquiv]

omit [Nontrivial R] [Nontrivial S] in
/-- Scalar extension commutes with the actual dual differential on the displayed two-term
resolution, on pure tensors. -/
theorem endomorphismBaseChangeEquiv_tmul_dualRelationMap
    (s : S) (φ : MvPolynomial (Fin 2) R →ₗ[MvPolynomial (Fin 2) R]
      MvPolynomial (Fin 2) R) :
    endomorphismBaseChangeEquiv R S
        (s ⊗ₜ[R] dualRelationMap R π n φ) =
      dualRelationMap S (algebraMap R S π) n
        (endomorphismBaseChangeEquiv R S (s ⊗ₜ[R] φ)) := by
  apply (endomorphismEvalEquiv S).injective
  simp only [endomorphismEvalEquiv_apply]
  rw [endomorphismBaseChangeEquiv_tmul_apply_one]
  conv_lhs => rw [← endomorphismEvalEquiv_apply]
  conv_rhs => rw [← endomorphismEvalEquiv_apply]
  rw [endomorphismEvalEquiv_dualRelationMap,
    endomorphismEvalEquiv_dualRelationMap]
  simp only [endomorphismEvalEquiv_apply]
  rw [endomorphismBaseChangeEquiv_tmul_apply_one]
  simp only [hypersurfaceRelationMap_apply]
  rw [map_mul, equation_map]
  rw [Algebra.smul_def, Algebra.smul_def]
  ac_rfl

/-- The canonical scalar extension of the explicit dual cokernel, transported through the
base-change equivalence for the node algebra.  This is an isomorphism of actual tensor products
and quotient modules; it does not assert a derived base-change theorem for `Ext`. -/
noncomputable def dualCokernelBaseChangeEquiv :
    S ⊗[R] dualCokernel R π n ≃ₗ[S] dualCokernel S (algebraMap R S π) n :=
  let e₁ : S ⊗[R] dualCokernel R π n ≃ₗ[S] S ⊗[R] Ring R π n :=
    LinearEquiv.baseChange R S _ _ ((dualCokernelEquiv R π n).restrictScalars R)
  let e₂ : S ⊗[R] Ring R π n ≃ₗ[S] Ring S (algebraMap R S π) n :=
    (baseChangeEquivLeft R S π n).toLinearEquiv
  let e₃ : Ring S (algebraMap R S π) n ≃ₗ[S]
      dualCokernel S (algebraMap R S π) n :=
    (dualCokernelEquiv S (algebraMap R S π) n).symm.restrictScalars S
  e₁.trans (e₂.trans e₃)

/-- On a quotient generator, scalar extension sends the represented endomorphism to the
coefficient-mapped quotient generator. -/
@[simp]
theorem dualCokernelBaseChangeEquiv_tmul_mk
    (s : S) (φ : MvPolynomial (Fin 2) R →ₗ[MvPolynomial (Fin 2) R]
      MvPolynomial (Fin 2) R) :
    dualCokernelBaseChangeEquiv R π n S
        (s ⊗ₜ[R] Submodule.Quotient.mk φ) =
      (dualCokernelEquiv S (algebraMap R S π) n).symm
        (Ideal.Quotient.mk (relationIdeal S (algebraMap R S π) n)
          (s • MvPolynomial.map (algebraMap R S) (φ 1))) := by
  change (dualCokernelEquiv S (algebraMap R S π) n).symm
    (baseChangeEquivLeft R S π n
      (s ⊗ₜ[R] dualCokernelEquiv R π n (Submodule.Quotient.mk φ))) = _
  rw [dualCokernelEquiv_apply_mk, baseChangeEquivLeft_tmul_mk]

/-- The same generator formula identifies the base-changed class with the class of the actual
coefficient-extended endomorphism on the dual Hom term. -/
theorem dualCokernelBaseChangeEquiv_tmul_mk_eq_quotient
    (s : S) (φ : MvPolynomial (Fin 2) R →ₗ[MvPolynomial (Fin 2) R]
      MvPolynomial (Fin 2) R) :
    dualCokernelBaseChangeEquiv R π n S
        (s ⊗ₜ[R] Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (endomorphismBaseChangeEquiv R S (s ⊗ₜ[R] φ)) := by
  rw [dualCokernelBaseChangeEquiv_tmul_mk,
    ← endomorphismBaseChangeEquiv_tmul_apply_one]
  exact dualCokernelEquiv_symm_apply_quotient S (algebraMap R S π) n
    (endomorphismBaseChangeEquiv R S (s ⊗ₜ[R] φ))

end BaseChange

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
