/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeDimension
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

/-!
# Base change for the local node smoothing

This file proves the canonical base-change presentation
`S ⊗[R] R[x,y]/(xy - πⁿ) ≃ S[x,y]/(xy - π_Sⁿ)`, together with its action on
pure tensors, the two distinguished coordinates, and the relative Jacobian ideal.  It also
identifies every scheme-theoretic fibre with a node over the corresponding residue field and
proves relative dimension at most one and pure relative dimension one.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Polynomial

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

universe u v

noncomputable section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- Mapping the coefficients of the node equation gives the node equation over the new base. -/
lemma equation_map (π : R) (n : ℕ) :
    MvPolynomial.map (algebraMap R S) (equation R π n) =
      equation S (algebraMap R S π) n := by
  simp [equation]

/-- Extension of the node relation ideal along a coefficient map is the node relation ideal over
the new coefficient ring. -/
lemma relationIdeal_map (π : R) (n : ℕ) :
    (relationIdeal R π n).map (MvPolynomial.map (algebraMap R S)) =
      relationIdeal S (algebraMap R S π) n := by
  rw [relationIdeal, relationIdeal, Ideal.map_span]
  simp [equation_map]

/-- After arbitrary base change to a nontrivial coefficient ring, the transported node
equation remains a regular singleton sequence.  No flatness, reducedness, or injectivity
hypothesis on the coefficient map is needed. -/
theorem equation_isRegular_baseChange [Nontrivial S] (π : R) (n : ℕ) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin 2) S)
      [MvPolynomial.map (algebraMap R S) (equation R π n)] := by
  rw [equation_map]
  exact equation_isRegular S (algebraMap R S π) n

/-- The node algebra obtained after arbitrary base change to a nontrivial coefficient ring
is itself nontrivial. -/
theorem baseChangedRing_nontrivial [Nontrivial S] (π : R) (n : ℕ) :
    Nontrivial (Ring S (algebraMap R S π) n) :=
  inferInstance

/-- The algebra obtained after arbitrary base change to a nontrivial coefficient ring has an
explicit finite complete-intersection presentation. -/
theorem baseChangedRing_isCompleteIntersection [Nontrivial S] (π : R) (n : ℕ) :
    Algebra.IsCompleteIntersection S (Ring S (algebraMap R S π) n) :=
  inferInstance

private lemma extendedRelationIdeal_map (π : R) (n : ℕ) :
    relationIdeal S (algebraMap R S π) n =
      ((relationIdeal R π n).map
        (Algebra.TensorProduct.includeRight :
          MvPolynomial (Fin 2) R →ₐ[R] S ⊗[R] MvPolynomial (Fin 2) R)).map
        (MvPolynomial.algebraTensorAlgEquiv R S) := by
  simp only [relationIdeal, Ideal.map_span]
  simp [equation, MvPolynomial.algebraTensorAlgEquiv_tmul]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def polynomialQuotientBaseChangeEquiv (π : R) (n : ℕ) :
    ((S ⊗[R] MvPolynomial (Fin 2) R) ⧸
        (relationIdeal R π n).map
          (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin 2) R →ₐ[R] S ⊗[R] MvPolynomial (Fin 2) R)) ≃ₐ[S]
      Ring S (algebraMap R S π) n :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
    (extendedRelationIdeal_map R S π n)

set_option backward.isDefEq.respectTransparency false in
@[simp] private theorem polynomialQuotientBaseChangeEquiv_mk
    (π : R) (n : ℕ) (z : S ⊗[R] MvPolynomial (Fin 2) R) :
    polynomialQuotientBaseChangeEquiv R S π n
        (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk (relationIdeal S (algebraMap R S π) n)
        (MvPolynomial.algebraTensorAlgEquiv R S z) := by
  apply Ideal.quotientEquivAlg_mk

set_option backward.isDefEq.respectTransparency false in
/-- Canonical base change of the node algebra, with the new coefficient ring as the left tensor
factor. -/
noncomputable def baseChangeEquivLeft (π : R) (n : ℕ) :
    S ⊗[R] Ring R π n ≃ₐ[S] Ring S (algebraMap R S π) n :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S
      (MvPolynomial (Fin 2) R) S (relationIdeal R π n)).trans
    (polynomialQuotientBaseChangeEquiv R S π n)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem baseChangeEquivLeft_tmul_mk (π : R) (n : ℕ)
    (s : S) (p : MvPolynomial (Fin 2) R) :
    baseChangeEquivLeft R S π n
        (s ⊗ₜ[R] Ideal.Quotient.mk (relationIdeal R π n) p) =
      Ideal.Quotient.mk (relationIdeal S (algebraMap R S π) n)
        (s • MvPolynomial.map (algebraMap R S) p) := by
  change polynomialQuotientBaseChangeEquiv R S π n
    (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S
      (MvPolynomial (Fin 2) R) S (relationIdeal R π n)
        (s ⊗ₜ[R] Ideal.Quotient.mk (relationIdeal R π n) p)) = _
  rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    polynomialQuotientBaseChangeEquiv_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem baseChangeEquivLeft_tmul_x (π : R) (n : ℕ) :
    baseChangeEquivLeft R S π n (1 ⊗ₜ[R] x R π n) =
      x S (algebraMap R S π) n := by
  change baseChangeEquivLeft R S π n
    (1 ⊗ₜ[R] Ideal.Quotient.mk (relationIdeal R π n) (MvPolynomial.X 0)) =
      Ideal.Quotient.mk (relationIdeal S (algebraMap R S π) n) (MvPolynomial.X 0)
  rw [baseChangeEquivLeft_tmul_mk]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem baseChangeEquivLeft_tmul_y (π : R) (n : ℕ) :
    baseChangeEquivLeft R S π n (1 ⊗ₜ[R] y R π n) =
      y S (algebraMap R S π) n := by
  change baseChangeEquivLeft R S π n
    (1 ⊗ₜ[R] Ideal.Quotient.mk (relationIdeal R π n) (MvPolynomial.X 1)) =
      Ideal.Quotient.mk (relationIdeal S (algebraMap R S π) n) (MvPolynomial.X 1)
  rw [baseChangeEquivLeft_tmul_mk]
  simp

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Canonical base change of the node algebra in the conventional right-tensor-factor
orientation. -/
noncomputable def baseChangeEquiv (π : R) (n : ℕ) :
    Ring R π n ⊗[R] S ≃ₐ[S] Ring S (algebraMap R S π) n :=
  (Algebra.TensorProduct.commRight R S (Ring R π n)).symm.trans
    (baseChangeEquivLeft R S π n)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp] theorem baseChangeEquiv_tmul_mk (π : R) (n : ℕ)
    (p : MvPolynomial (Fin 2) R) (s : S) :
    baseChangeEquiv R S π n
        (Ideal.Quotient.mk (relationIdeal R π n) p ⊗ₜ[R] s) =
      Ideal.Quotient.mk (relationIdeal S (algebraMap R S π) n)
        (s • MvPolynomial.map (algebraMap R S) p) := by
  change baseChangeEquivLeft R S π n
    ((Algebra.TensorProduct.commRight R S (Ring R π n)).symm
      (Ideal.Quotient.mk (relationIdeal R π n) p ⊗ₜ[R] s)) = _
  rw [Algebra.TensorProduct.commRight_symm_tmul,
    baseChangeEquivLeft_tmul_mk]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp] theorem baseChangeEquiv_tmul_x (π : R) (n : ℕ) :
    baseChangeEquiv R S π n (x R π n ⊗ₜ[R] 1) =
      x S (algebraMap R S π) n := by
  change baseChangeEquiv R S π n
    (Ideal.Quotient.mk (relationIdeal R π n) (MvPolynomial.X 0) ⊗ₜ[R] 1) = _
  rw [baseChangeEquiv_tmul_mk]
  simp [x]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp] theorem baseChangeEquiv_tmul_y (π : R) (n : ℕ) :
    baseChangeEquiv R S π n (y R π n ⊗ₜ[R] 1) =
      y S (algebraMap R S π) n := by
  change baseChangeEquiv R S π n
    (Ideal.Quotient.mk (relationIdeal R π n) (MvPolynomial.X 1) ⊗ₜ[R] 1) = _
  rw [baseChangeEquiv_tmul_mk]
  simp [y]

/-- Extension of the parameter-power ideal is the corresponding parameter-power ideal over the
new coefficient ring. -/
theorem parameterPowerIdeal_map (π : R) (n : ℕ) :
    (parameterPowerIdeal R π n).map (algebraMap R S) =
      parameterPowerIdeal S (algebraMap R S π) n := by
  rw [parameterPowerIdeal, parameterPowerIdeal, Ideal.map_span]
  simp

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The critical quotient commutes with arbitrary coefficient-ring base change. -/
noncomputable def criticalBaseChangeEquiv (π : R) (n : ℕ) :
    (R ⧸ parameterPowerIdeal R π n) ⊗[R] S ≃ₐ[S]
      S ⧸ parameterPowerIdeal S (algebraMap R S π) n :=
  (Algebra.TensorProduct.commRight R S (R ⧸ parameterPowerIdeal R π n)).symm.trans <|
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
      (parameterPowerIdeal R π n)).symm.trans <|
      Ideal.quotientEquivAlgOfEq S (parameterPowerIdeal_map R S π n)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The relative Jacobian ideal commutes with arbitrary coefficient-ring base change under the
canonical node-algebra equivalence. -/
theorem relativeJacobianIdeal_baseChange (π : R) (n : ℕ) :
    ((relativeJacobianIdeal R π n).map
        (Algebra.TensorProduct.includeLeft : Ring R π n →ₐ[R] Ring R π n ⊗[R] S)).map
      (baseChangeEquiv R S π n).toRingHom =
        relativeJacobianIdeal S (algebraMap R S π) n := by
  rw [relativeJacobianIdeal_eq, relativeJacobianIdeal_eq, Ideal.map_span, Ideal.map_span]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
    rcases hq with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · refine ⟨_, ⟨_, Or.inl rfl, rfl⟩, ?_⟩
      simp
    · refine ⟨_, ⟨_, Or.inr rfl, rfl⟩, ?_⟩
      simp

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- If the smoothing parameter becomes invertible after base change, the base-changed node
algebra is a Laurent polynomial algebra.  This is the algebraic generic-fibre normal form. -/
noncomputable def baseChangeEquivLaurentOfIsUnitImage (π : R) (n : ℕ)
    (hπ : IsUnit (algebraMap R S π)) :
    Ring R π n ⊗[R] S ≃ₐ[S] LaurentPolynomial S :=
  (baseChangeEquiv R S π n).trans
    (unitEquivLaurent S (algebraMap R S π) n hπ)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp] theorem baseChangeEquivLaurentOfIsUnitImage_tmul_x (π : R) (n : ℕ)
    (hπ : IsUnit (algebraMap R S π)) :
    baseChangeEquivLaurentOfIsUnitImage R S π n hπ (x R π n ⊗ₜ[R] 1) =
      LaurentPolynomial.T 1 := by
  simp [baseChangeEquivLaurentOfIsUnitImage]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp] theorem baseChangeEquivLaurentOfIsUnitImage_tmul_y (π : R) (n : ℕ)
    (hπ : IsUnit (algebraMap R S π)) :
    baseChangeEquivLaurentOfIsUnitImage R S π n hπ (y R π n ⊗ₜ[R] 1) =
      LaurentPolynomial.C ((algebraMap R S π) ^ n) * LaurentPolynomial.T (-1) := by
  simp [baseChangeEquivLaurentOfIsUnitImage]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Over a field, a nonzero image of the smoothing parameter is automatically invertible,
so the base-changed node algebra has Laurent form. -/
noncomputable def fieldBaseChangeEquivLaurent (F : Type v) [Field F] [Algebra R F]
    (π : R) (n : ℕ) (hπ : algebraMap R F π ≠ 0) :
    Ring R π n ⊗[R] F ≃ₐ[F] LaurentPolynomial F :=
  baseChangeEquivLaurentOfIsUnitImage R F π n (isUnit_iff_ne_zero.mpr hπ)

/-- A one-variable polynomial ring, presented with one generator and no relations. -/
private noncomputable def polynomialSubmersivePresentation (F : Type u) [CommRing F] :
    Algebra.SubmersivePresentation F F[X] Unit Empty := by
  let v : Empty → MvPolynomial Unit F := Empty.elim
  let P : Algebra.PreSubmersivePresentation F
      (MvPolynomial Unit F ⧸ Ideal.span (Set.range v)) Unit Empty :=
    Algebra.PreSubmersivePresentation.naive Empty.elim (fun x => x.elim)
  let Q : Algebra.SubmersivePresentation F
      (MvPolynomial Unit F ⧸ Ideal.span (Set.range v)) Unit Empty :=
    { toPreSubmersivePresentation := P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  let e : (MvPolynomial Unit F ⧸ Ideal.span (Set.range v)) ≃ₐ[F] F[X] :=
    (Ideal.quotientEquivAlgOfEq F (by simp [v])).trans
      ((AlgEquiv.quotientBot F (MvPolynomial Unit F)).trans
        (MvPolynomial.uniqueAlgEquiv F Unit))
  exact Q.ofAlgEquiv e

/-- The polynomial line has a standard-smooth presentation of relative dimension one. -/
theorem polynomial_standardSmoothOfRelativeDimension_one (F : Type u) [CommRing F] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 F F[X] := by
  apply (polynomialSubmersivePresentation F).isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension]

/-- The affine line is smooth of relative dimension one over any coefficient ring. -/
theorem affineLineToBaseSpec_smoothOfRelativeDimension_one
    (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (affineLineToBaseSpec R) := by
  rw [affineLineToBaseSpec]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
  exact polynomial_standardSmoothOfRelativeDimension_one R

/-- A Laurent polynomial algebra is standard smooth of relative dimension one over its
coefficient field. -/
theorem laurentPolynomial_standardSmoothOfRelativeDimension_one
    (F : Type u) [CommRing F] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 F (LaurentPolynomial F) := by
  let : IsScalarTower F F[X] (LaurentPolynomial F) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      simp [LaurentPolynomial.algebraMap_eq_toLaurent])
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 F F[X] :=
    polynomial_standardSmoothOfRelativeDimension_one F
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 F[X] (LaurentPolynomial F) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away Polynomial.X
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 F F[X] (LaurentPolynomial F)

/-- Laurent polynomial algebras over fields are smooth.  This is obtained by expressing
`F[T,T⁻¹]` as the localization of the smooth polynomial algebra `F[T]` at `T`. -/
theorem laurentPolynomial_smooth (F : Type u) [CommRing F] :
    Algebra.Smooth F (LaurentPolynomial F) := by
  let : IsScalarTower F F[X] (LaurentPolynomial F) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      simp [LaurentPolynomial.algebraMap_eq_toLaurent])
  have : Algebra.Smooth F F[X] := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth F[X] (LaurentPolynomial F) :=
    Algebra.Smooth.of_isLocalization_Away Polynomial.X
  exact Algebra.Smooth.comp F F[X] (LaurentPolynomial F)

/-- The spectrum of a Laurent polynomial algebra is smooth over its coefficient field. -/
theorem laurentSpec_smooth (F : Type u) [CommRing F] :
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap F (LaurentPolynomial F)))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.smooth_algebraMap.mpr
  exact laurentPolynomial_smooth F

/-- The punctured affine line is smooth of relative dimension one. -/
theorem laurentSpec_smoothOfRelativeDimension_one (F : Type u) [CommRing F] :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap F (LaurentPolynomial F)))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
  exact laurentPolynomial_standardSmoothOfRelativeDimension_one F

/-- Away from `x`, the local node algebra is standard smooth of relative dimension one over
the original coefficient ring. -/
theorem xAway_standardSmoothOfRelativeDimension_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R
      (Localization.Away (x R π n)) := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R (LaurentPolynomial R) :=
    laurentPolynomial_standardSmoothOfRelativeDimension_one R
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (xAwayEquivLaurent R π n).symm

/-- Away from `y`, the local node algebra is standard smooth of relative dimension one over
the original coefficient ring. -/
theorem yAway_standardSmoothOfRelativeDimension_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R
      (Localization.Away (y R π n)) := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R (LaurentPolynomial R) :=
    laurentPolynomial_standardSmoothOfRelativeDimension_one R
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (yAwayEquivLaurent R π n).symm

/-- The node algebra localized away from `x` is smooth over the coefficient ring. -/
theorem xAway_smooth (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.Smooth R (Localization.Away (x R π n)) := by
  have : Algebra.Smooth R (LaurentPolynomial R) := laurentPolynomial_smooth R
  exact Algebra.Smooth.of_equiv (xAwayEquivLaurent R π n).symm

/-- The node algebra localized away from `y` is smooth over the coefficient ring. -/
theorem yAway_smooth (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Algebra.Smooth R (Localization.Away (y R π n)) := by
  have : Algebra.Smooth R (LaurentPolynomial R) := laurentPolynomial_smooth R
  exact Algebra.Smooth.of_equiv (yAwayEquivLaurent R π n).symm

/-- The principal-open immersion obtained by inverting `x` in the node algebra. -/
def xAwaySpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (Localization.Away (x R π n))) ⟶ Spec (.of (Ring R π n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

/-- The structural morphism of the principal-open node chart where `x` is invertible. -/
def xAwayToBaseSpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (Localization.Away (x R π n))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R _))

/-- The principal-open immersion obtained by inverting `y` in the node algebra. -/
def yAwaySpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (Localization.Away (y R π n))) ⟶ Spec (.of (Ring R π n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

/-- The structural morphism of the principal-open node chart where `y` is invertible. -/
def yAwayToBaseSpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Spec (.of (Localization.Away (y R π n))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R _))

instance xAwaySpec_isOpenImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsOpenImmersion (xAwaySpec R π n) := by
  rw [xAwaySpec]
  infer_instance

instance yAwaySpec_isOpenImmersion
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    IsOpenImmersion (yAwaySpec R π n) := by
  rw [yAwaySpec]
  infer_instance

/-- The carrier of the `x`-away scheme chart is the basic open `D(x)`. -/
theorem range_xAwaySpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Set.range (xAwaySpec R π n) = (PrimeSpectrum.basicOpen (x R π n)).1 := by
  change Set.range (PrimeSpectrum.comap
    (algebraMap (Ring R π n) (Localization.Away (x R π n)))) = _
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- The carrier of the `y`-away scheme chart is the basic open `D(y)`. -/
theorem range_yAwaySpec (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Set.range (yAwaySpec R π n) = (PrimeSpectrum.basicOpen (y R π n)).1 := by
  change Set.range (PrimeSpectrum.comap
    (algebraMap (Ring R π n) (Localization.Away (y R π n)))) = _
  exact PrimeSpectrum.localization_away_comap_range _ _

@[reassoc (attr := simp)] theorem xAwaySpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    xAwaySpec R π n ≫ toBaseSpec R π n = xAwayToBaseSpec R π n := by
  rw [xAwaySpec, toBaseSpec, xAwayToBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => IsScalarTower.algebraMap_apply R (Ring R π n)
    (Localization.Away (x R π n)) r |>.symm

@[reassoc (attr := simp)] theorem yAwaySpec_toBaseSpec
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    yAwaySpec R π n ≫ toBaseSpec R π n = yAwayToBaseSpec R π n := by
  rw [yAwaySpec, toBaseSpec, yAwayToBaseSpec, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun r => IsScalarTower.algebraMap_apply R (Ring R π n)
    (Localization.Away (y R π n)) r |>.symm

/-- The structural morphism on `D(x)` is smooth of relative dimension one. -/
theorem xAwayToBaseSpec_smoothOfRelativeDimension_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    SmoothOfRelativeDimension 1 (xAwayToBaseSpec R π n) := by
  rw [xAwayToBaseSpec]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
  exact xAway_standardSmoothOfRelativeDimension_one R π n

/-- The structural morphism on `D(y)` is smooth of relative dimension one. -/
theorem yAwayToBaseSpec_smoothOfRelativeDimension_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    SmoothOfRelativeDimension 1 (yAwayToBaseSpec R π n) := by
  rw [yAwayToBaseSpec]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
  exact yAway_standardSmoothOfRelativeDimension_one R π n

/-- Every prime where `x` is nonzero belongs to the relative smooth locus. -/
theorem basicOpen_x_subset_smoothLocus
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    ↑(PrimeSpectrum.basicOpen (x R π n)) ⊆
      Algebra.smoothLocus R (Ring R π n) := by
  rw [Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  exact xAway_smooth R π n

/-- Every prime where `y` is nonzero belongs to the relative smooth locus. -/
theorem basicOpen_y_subset_smoothLocus
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    ↑(PrimeSpectrum.basicOpen (y R π n)) ⊆
      Algebra.smoothLocus R (Ring R π n) := by
  rw [Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  exact yAway_smooth R π n

/-- The union of the two smooth coordinate opens is exactly the complement of the relative
Jacobian zero locus. -/
theorem basicOpen_union_eq_compl_relativeJacobian_zeroLocus
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (↑(PrimeSpectrum.basicOpen (x R π n)) : Set (PrimeSpectrum (Ring R π n))) ∪
        ↑(PrimeSpectrum.basicOpen (y R π n)) =
      (PrimeSpectrum.zeroLocus (relativeJacobianIdeal R π n))ᶜ := by
  ext p
  simp only [Set.mem_union, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, relativeJacobianIdeal_eq]
  change x R π n ∉ p.asIdeal ∨ y R π n ∉ p.asIdeal ↔
    ¬ Ideal.span ({x R π n, y R π n} : Set (Ring R π n)) ≤ p.asIdeal
  constructor
  · rintro (hx | hy) hspan
    · exact hx (hspan (Ideal.subset_span (Set.mem_insert _ _)))
    · exact hy (hspan (Ideal.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  · intro hspan
    by_cases hx : x R π n ∈ p.asIdeal
    · right
      intro hy
      apply hspan
      rw [Ideal.span_le]
      intro z hz
      rcases hz with (rfl | hz)
      · exact hx
      · rw [Set.mem_singleton_iff] at hz
        subst z
        exact hy
    · exact Or.inl hx

/-- Scheme-theoretically, the two smooth principal-open immersions cover exactly the complement
of the relative Jacobian zero locus. -/
theorem range_xAwaySpec_union_range_yAwaySpec
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Set.range (xAwaySpec R π n) ∪ Set.range (yAwaySpec R π n) =
      (PrimeSpectrum.zeroLocus (relativeJacobianIdeal R π n))ᶜ := by
  rw [range_xAwaySpec, range_yAwaySpec]
  exact basicOpen_union_eq_compl_relativeJacobian_zeroLocus R π n

/-- The overlap of the two coordinate opens is exactly the basic open where `πⁿ` is
invertible. -/
theorem range_xAwaySpec_inter_range_yAwaySpec
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    Set.range (xAwaySpec R π n) ∩ Set.range (yAwaySpec R π n) =
      (PrimeSpectrum.basicOpen (algebraMap R (Ring R π n) (π ^ n))).1 := by
  rw [range_xAwaySpec, range_yAwaySpec]
  change ((PrimeSpectrum.basicOpen (x R π n) ⊓
    PrimeSpectrum.basicOpen (y R π n) :
      TopologicalSpace.Opens (PrimeSpectrum (Ring R π n))) :
        Set (PrimeSpectrum (Ring R π n))) = _
  rw [← PrimeSpectrum.basicOpen_mul, x_mul_y]
  rfl

/-- At positive thickness, the overlap of the two coordinate opens is the inverse-parameter
open `D(π)`. -/
theorem range_xAwaySpec_inter_range_yAwaySpec_of_pos
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hn : 0 < n) :
    Set.range (xAwaySpec R π n) ∩ Set.range (yAwaySpec R π n) =
      (PrimeSpectrum.basicOpen (algebraMap R (Ring R π n) π)).1 := by
  rw [range_xAwaySpec_inter_range_yAwaySpec, map_pow,
    PrimeSpectrum.basicOpen_pow _ n hn]

/-- The complement of the computed relative Jacobian locus is smooth over the base. -/
theorem compl_relativeJacobian_zeroLocus_subset_smoothLocus
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (PrimeSpectrum.zeroLocus (relativeJacobianIdeal R π n))ᶜ ⊆
      Algebra.smoothLocus R (Ring R π n) := by
  rw [← basicOpen_union_eq_compl_relativeJacobian_zeroLocus R π n]
  exact Set.union_subset (basicOpen_x_subset_smoothLocus R π n)
    (basicOpen_y_subset_smoothLocus R π n)

/-- The relative nonsmooth locus is contained in the computed Jacobian zero locus.  This is
the direction supplied by the two explicit smooth principal opens; the localized-presentation
argument needed for the reverse inclusion is not developed here. -/
theorem nonsmoothLocus_subset_relativeJacobian_zeroLocus
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    (Algebra.smoothLocus R (Ring R π n))ᶜ ⊆
      PrimeSpectrum.zeroLocus (relativeJacobianIdeal R π n) := by
  simpa using Set.compl_subset_compl.mpr
    (compl_relativeJacobian_zeroLocus_subset_smoothLocus R π n)

/-- If the smoothing parameter is a unit, the local-node algebra is standard smooth of
relative dimension one over its coefficient ring. -/
theorem ring_standardSmoothOfRelativeDimension_one_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Ring R π n) := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R (LaurentPolynomial R) :=
    laurentPolynomial_standardSmoothOfRelativeDimension_one R
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (unitEquivLaurent R π n hπ).symm

/-- A unit-parameter local-node chart is a smooth relative curve. -/
theorem toBaseSpec_smoothOfRelativeDimension_one_of_isUnit
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (hπ : IsUnit π) :
    SmoothOfRelativeDimension 1 (toBaseSpec R π n) := by
  rw [toBaseSpec]
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
  exact ring_standardSmoothOfRelativeDimension_one_of_isUnit R π n hπ

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The algebra obtained from the local-node presentation by a field base change on which the
smoothing parameter is nonzero is smooth over that field. -/
theorem fieldBaseChangeAlgebra_smooth
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (π : R) (n : ℕ) (hπ : algebraMap R F π ≠ 0) :
    Algebra.Smooth F (Ring R π n ⊗[R] F) := by
  have : Algebra.Smooth F (LaurentPolynomial F) := laurentPolynomial_smooth F
  exact Algebra.Smooth.of_equiv
    (fieldBaseChangeEquivLaurent R F π n hπ).symm

section SchemeBaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The coefficient-extension map between two local-node presentations. -/
noncomputable def coefficientMap (π : R) (n : ℕ) :
    Ring R π n →+* Ring T (algebraMap R T π) n :=
  (baseChangeEquiv R T π n).toRingEquiv.toRingHom.comp
    Algebra.TensorProduct.includeLeftRingHom

/-- Coefficient extension as a morphism of algebras over the original coefficient ring. -/
noncomputable def coefficientAlgHom (π : R) (n : ℕ) :
    Ring R π n →ₐ[R] Ring T (algebraMap R T π) n :=
  ((baseChangeEquiv R T π n).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeLeft

@[simp]
theorem coefficientAlgHom_toRingHom (π : R) (n : ℕ) :
    (coefficientAlgHom R T π n).toRingHom = coefficientMap R T π n :=
  rfl

/-- Coefficient extension of a local-node algebra is injective whenever the coefficient-ring
map is injective.  Flatness of the node algebra over its coefficient ring supplies the only
tensor-product input. -/
theorem coefficientMap_injective_of_injective (π : R) (n : ℕ)
    (h : Function.Injective (algebraMap R T)) :
    Function.Injective (coefficientMap R T π n) :=
  (baseChangeEquiv R T π n).injective.comp
    (Algebra.TensorProduct.includeLeft_injective
      (R := R) (S := R) (A := Ring R π n) (B := T) h)

@[simp] theorem coefficientMap_x (π : R) (n : ℕ) :
    coefficientMap R T π n (x R π n) =
      x T (algebraMap R T π) n := by
  exact baseChangeEquiv_tmul_x R T π n

@[simp] theorem coefficientAlgHom_x (π : R) (n : ℕ) :
    coefficientAlgHom R T π n (x R π n) =
      x T (algebraMap R T π) n := by
  change coefficientMap R T π n (x R π n) = _
  exact coefficientMap_x R T π n

@[simp] theorem coefficientMap_y (π : R) (n : ℕ) :
    coefficientMap R T π n (y R π n) =
      y T (algebraMap R T π) n := by
  exact baseChangeEquiv_tmul_y R T π n

@[simp] theorem coefficientAlgHom_y (π : R) (n : ℕ) :
    coefficientAlgHom R T π n (y R π n) =
      y T (algebraMap R T π) n := by
  change coefficientMap R T π n (y R π n) = _
  exact coefficientMap_y R T π n

/-- The scheme cut out by the base-changed node equation is canonically the fibre product
of the original affine node with the new affine base. -/
noncomputable def baseChangeSpecIso (π : R) (n : ℕ) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅
      Spec (.of (Ring T (algebraMap R T π) n)) :=
  pullbackSpecIso R (Ring R π n) T ≪≫
    (Scheme.Spec.mapIso
      (baseChangeEquiv R T π n).toRingEquiv.toCommRingCatIso.op).symm

@[reassoc (attr := simp)]
theorem baseChangeSpecIso_hom_coefficientMap (π : R) (n : ℕ) :
    (baseChangeSpecIso R T π n).hom ≫
        Spec.map (CommRingCat.ofHom (coefficientMap R T π n)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) := by
  simp only [baseChangeSpecIso, Iso.trans_hom, Category.assoc]
  rw [← pullbackSpecIso_hom_fst R (Ring R π n) T]
  rw [cancel_epi (pullbackSpecIso R (Ring R π n) T).hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, AlgebraicGeometry.Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (baseChangeEquiv R T π n).symm_apply_apply
    (Algebra.TensorProduct.includeLeftRingHom z)

@[reassoc (attr := simp)]
theorem baseChangeSpecIso_hom_toBaseSpec (π : R) (n : ℕ) :
    (baseChangeSpecIso R T π n).hom ≫ toBaseSpec T (algebraMap R T π) n =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) := by
  simp only [baseChangeSpecIso, Iso.trans_hom, Category.assoc]
  rw [← pullbackSpecIso_hom_snd R (Ring R π n) T]
  rw [cancel_epi (pullbackSpecIso R (Ring R π n) T).hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, AlgebraicGeometry.Spec.map_inj]
  ext t
  exact (baseChangeEquiv R T π n).symm.commutes t

/-- The affine fibre-product comparison as an isomorphism over the new base scheme. -/
noncomputable def baseChangeOverIso (π : R) (n : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).obj
        (Over.mk (toBaseSpec R π n)) ≅
      Over.mk (toBaseSpec T (algebraMap R T π) n) :=
  Over.isoMk (baseChangeSpecIso R T π n)
    (baseChangeSpecIso_hom_toBaseSpec R T π n)

@[simp]
theorem baseChangeOverIso_hom_left (π : R) (n : ℕ) :
    (baseChangeOverIso R T π n).hom.left = (baseChangeSpecIso R T π n).hom := rfl

/-! ## Base change of the relative critical locus -/

/-- The fibre product obtained by extending the coefficients of the relative critical locus. -/
noncomputable def baseChangedCriticalLocusSpec (π : R) (n : ℕ) : Scheme :=
  pullback (relativeCriticalLocusToBase R π n)
    (Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- The structural morphism from the base-changed critical locus to its new coefficient scheme. -/
def baseChangedCriticalLocusToBaseSpec (π : R) (n : ℕ) :
    baseChangedCriticalLocusSpec R T π n ⟶ Spec (.of T) := by
  dsimp [baseChangedCriticalLocusSpec]
  exact pullback.snd _ _

set_option backward.isDefEq.respectTransparency false in
/-- Unramifiedness of the critical locus is preserved by every coefficient base change. -/
instance baseChangedCriticalLocusToBaseSpec_unramified (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Unramified
      (baseChangedCriticalLocusToBaseSpec R T π n) := by
  change GromovWitten.AlgebraicGeometry.Unramified
    (pullback.snd (relativeCriticalLocusToBase R π n)
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  exact MorphismProperty.pullback_snd _ _
    (show GromovWitten.AlgebraicGeometry.Unramified
      (relativeCriticalLocusToBase R π n) from inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-- The base-changed critical locus is canonically the spectrum of the quotient by the
base-changed parameter power. -/
noncomputable def criticalBaseChangeSpecIso (π : R) (n : ℕ) :
    pullback (relativeCriticalLocusToBase R π n)
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅
      Spec (.of (T ⧸ parameterPowerIdeal T (algebraMap R T π) n)) :=
  pullbackSpecIso R (R ⧸ parameterPowerIdeal R π n) T ≪≫
    (Scheme.Spec.mapIso
      (criticalBaseChangeEquiv R T π n).toRingEquiv.toCommRingCatIso.op).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem criticalBaseChangeSpecIso_hom_toBaseSpec (π : R) (n : ℕ) :
    (criticalBaseChangeSpecIso R T π n).hom ≫
        relativeCriticalLocusToBase T (algebraMap R T π) n =
      pullback.snd (relativeCriticalLocusToBase R π n)
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) := by
  dsimp only [relativeCriticalLocusToBase]
  simp only [criticalBaseChangeSpecIso, Iso.trans_hom, Category.assoc]
  rw [← pullbackSpecIso_hom_snd R (R ⧸ parameterPowerIdeal R π n) T]
  rw [cancel_epi (pullbackSpecIso R (R ⧸ parameterPowerIdeal R π n) T).hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, AlgebraicGeometry.Spec.map_inj]
  ext t
  exact (criticalBaseChangeEquiv R T π n).symm.commutes t

/-- The critical-locus base-change comparison as an isomorphism over the new base scheme. -/
noncomputable def criticalBaseChangeOverIso (π : R) (n : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R T)))).obj
        (Over.mk (relativeCriticalLocusToBase R π n)) ≅
      Over.mk (relativeCriticalLocusToBase T (algebraMap R T π) n) :=
  Over.isoMk (criticalBaseChangeSpecIso R T π n)
    (criticalBaseChangeSpecIso_hom_toBaseSpec R T π n)

/-! ## Dimensions of the scheme-theoretic fibres -/

/-- A scheme-theoretic fibre of a local-node chart is homeomorphic to the prime spectrum of
the same node presentation over the corresponding residue field. -/
noncomputable def fiberHomeomorphNodeRing
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (p : PrimeSpectrum R) :
    (toBaseSpec R π n).fiber p ≃ₜ
      PrimeSpectrum
        (Ring p.asIdeal.ResidueField (algebraMap R p.asIdeal.ResidueField π) n) := by
  let e₂ := PrimeSpectrum.preimageHomeomorphFiber R (Ring R π n) p
  let e₃ : PrimeSpectrum (p.asIdeal.Fiber (Ring R π n)) ≃ₜ
      PrimeSpectrum
        (Ring p.asIdeal.ResidueField (algebraMap R p.asIdeal.ResidueField π) n) :=
    PrimeSpectrum.homeomorphOfRingEquiv
      (baseChangeEquivLeft R p.asIdeal.ResidueField π n).toRingEquiv
  refine ((toBaseSpec R π n).fiberHomeo p).trans ?_
  refine (Homeomorph.setCongr ?_).trans (e₂.trans e₃)
  ext q
  change PrimeSpectrum.comap (algebraMap R (Ring R π n)) q = p ↔
    PrimeSpectrum.comap (algebraMap R (Ring R π n)) q = p
  rfl

/-- Every scheme-theoretic fibre of a local-node chart has topological Krull dimension exactly
one.  The fibre is first identified with the prime spectrum of the residue-field tensor product,
then with the same node presentation over that residue field. -/
theorem fiber_topologicalKrullDim_eq_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (s : Spec (.of R)) :
    topologicalKrullDim ((toBaseSpec R π n).fiber s) = 1 := by
  let p : PrimeSpectrum R := s
  rw [(fiberHomeomorphNodeRing R π n p).isHomeomorph.topologicalKrullDim_eq,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_one]

/-- Every irreducible component of every scheme-theoretic fibre of a local-node chart has
topological Krull dimension one. -/
theorem fiber_component_topologicalKrullDim_eq_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) (s : Spec (.of R))
    (Z : Set ((toBaseSpec R π n).fiber s))
    (hZ : Z ∈ irreducibleComponents ((toBaseSpec R π n).fiber s)) :
    topologicalKrullDim Z = 1 := by
  let p : PrimeSpectrum R := s
  exact pureTopologicalDimensionOfHomeomorph
    (fiberHomeomorphNodeRing R π n p)
    (component_topologicalKrullDim_eq_one p.asIdeal.ResidueField
      (algebraMap R p.asIdeal.ResidueField π) n) Z hZ

/-- The structural morphism of every local-node presentation has relative dimension at most one
in the fibrewise topological-Krull-dimension sense used by the curve-family API. -/
theorem toBaseSpec_relativeDimensionLE_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.RelativeDimensionLE 1 (toBaseSpec R π n) := by
  constructor
  · infer_instance
  · intro s
    rw [fiber_topologicalKrullDim_eq_one R π n s]
    norm_num

/-- The structural morphism of every local-node presentation has pure relative dimension one. -/
theorem toBaseSpec_pureRelativeDimension_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.PureRelativeDimension 1 (toBaseSpec R π n) := by
  constructor
  · infer_instance
  · exact fiber_component_topologicalKrullDim_eq_one R π n

/-- The fibre-product scheme obtained by extending the coefficients of a local-node chart. -/
noncomputable def baseChangedNodeSpec (π : R) (n : ℕ) : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
    (Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- The canonical structural morphism from the coefficient-base-changed node to its new base. -/
def baseChangedNodeToBaseSpec (π : R) (n : ℕ) :
    baseChangedNodeSpec R T π n ⟶ Spec (.of T) := by
  dsimp [baseChangedNodeSpec]
  exact pullback.snd _ _

/-- An arbitrary coefficient base change of a local-node chart is affine. -/
instance baseChangedNodeToBaseSpec_isAffine (π : R) (n : ℕ) :
    IsAffineHom (baseChangedNodeToBaseSpec R T π n) := by
  change IsAffineHom
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  infer_instance

/-- An arbitrary coefficient base change of a local-node chart is quasi-compact. -/
instance baseChangedNodeToBaseSpec_quasiCompact (π : R) (n : ℕ) :
    QuasiCompact (baseChangedNodeToBaseSpec R T π n) := by
  change QuasiCompact
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  infer_instance

/-- Local finite presentation of the node chart is preserved by arbitrary coefficient base
change. -/
instance baseChangedNodeToBaseSpec_locallyOfFinitePresentation (π : R) (n : ℕ) :
    LocallyOfFinitePresentation (baseChangedNodeToBaseSpec R T π n) := by
  change LocallyOfFinitePresentation
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  exact locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (show LocallyOfFinitePresentation (toBaseSpec R π n) from inferInstance)

/-- Flatness of the node chart is preserved by every coefficient base change, with no
Noetherian, domain, or reducedness hypothesis on either coefficient ring. -/
instance baseChangedNodeToBaseSpec_flat (π : R) (n : ℕ) :
    Flat (baseChangedNodeToBaseSpec R T π n) := by
  change Flat
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  exact Flat.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (show Flat (toBaseSpec R π n) from inferInstance)

/-- Every coefficient base change to a nontrivial ring is syntomic.  The explicit affine
base-change isomorphism identifies it with the node chart over the new coefficient ring. -/
instance baseChangedNodeToBaseSpec_syntomic [Nontrivial T] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Syntomic
      (baseChangedNodeToBaseSpec R T π n) := by
  change GromovWitten.AlgebraicGeometry.Syntomic
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  rw [← baseChangeSpecIso_hom_toBaseSpec R T π n]
  exact GromovWitten.AlgebraicGeometry.Syntomic.precomp_iso
    (baseChangeSpecIso R T π n) (toBaseSpec T (algebraMap R T π) n) inferInstance

/-- Every coefficient base change of a local-node chart has relative dimension at most one. -/
theorem baseChangedNodeToBaseSpec_relativeDimensionLE_one (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.RelativeDimensionLE 1
      (baseChangedNodeToBaseSpec R T π n) := by
  change GromovWitten.AlgebraicGeometry.Curves.RelativeDimensionLE 1
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  rw [← baseChangeSpecIso_hom_toBaseSpec R T π n]
  exact GromovWitten.AlgebraicGeometry.Curves.RelativeDimensionLE.precomp_iso
    (baseChangeSpecIso R T π n) (toBaseSpec T (algebraMap R T π) n)
    (toBaseSpec_relativeDimensionLE_one T (algebraMap R T π) n)

/-- Every coefficient base change of a local-node chart has pure relative dimension one. -/
theorem baseChangedNodeToBaseSpec_pureRelativeDimension_one (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.PureRelativeDimension 1
      (baseChangedNodeToBaseSpec R T π n) := by
  change GromovWitten.AlgebraicGeometry.Curves.PureRelativeDimension 1
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))))
  rw [← baseChangeSpecIso_hom_toBaseSpec R T π n]
  exact GromovWitten.AlgebraicGeometry.Curves.PureRelativeDimension.precomp_iso
    (baseChangeSpecIso R T π n) (toBaseSpec T (algebraMap R T π) n)
    (toBaseSpec_pureRelativeDimension_one T (algebraMap R T π) n)

/-- Every local-node chart has geometric relative dimension at most one: the assertion is
checked after every field-valued coefficient extension, not only on residue-field fibres. -/
theorem toBaseSpec_geometricRelativeDimensionLE_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.GeometricRelativeDimensionLE 1
      (toBaseSpec R π n) := by
  constructor
  · infer_instance
  · rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    change GromovWitten.AlgebraicGeometry.Curves.TopologicalDimensionLE 1
      (baseChangedNodeSpec R K π n)
    change topologicalKrullDim (baseChangedNodeSpec R K π n) ≤ 1
    calc
      topologicalKrullDim (baseChangedNodeSpec R K π n) =
          topologicalKrullDim (Spec (.of (Ring K (algebraMap R K π) n))) :=
        (baseChangeSpecIso R K π n).schemeIsoToHomeo.isHomeomorph.topologicalKrullDim_eq
      _ = topologicalKrullDim
          (PrimeSpectrum (Ring K (algebraMap R K π) n)) := rfl
      _ = ringKrullDim (Ring K (algebraMap R K π) n) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
          (Ring K (algebraMap R K π) n)
      _ = 1 := ringKrullDim_eq_one K (algebraMap R K π) n
      _ ≤ 1 := le_rfl

/-- Every local-node chart has geometric pure relative dimension one after every
field-valued coefficient extension. -/
theorem toBaseSpec_geometricPureRelativeDimension_one
    (R : Type u) [CommRing R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.GeometricPureRelativeDimension 1
      (toBaseSpec R π n) := by
  constructor
  · infer_instance
  · rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    change GromovWitten.AlgebraicGeometry.Curves.PureTopologicalDimension 1
      (baseChangedNodeSpec R K π n)
    change ∀ Z ∈ irreducibleComponents (baseChangedNodeSpec R K π n),
      topologicalKrullDim Z = 1
    exact GromovWitten.AlgebraicGeometry.Curves.pureTopologicalDimensionOfHomeomorph
      (baseChangeSpecIso R K π n).schemeIsoToHomeo
      (component_topologicalKrullDim_eq_one K (algebraMap R K π) n)

/-- Over a nontrivial base, the local-node chart is syntomic of geometric pure relative
dimension one. -/
instance toBaseSpec_syntomicOfRelativeDimension_one
    (R : Type u) [CommRing R] [Nontrivial R] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.SyntomicOfRelativeDimension 1
      (toBaseSpec R π n) where
  syntomic := inferInstance
  geometricPureRelativeDimension := toBaseSpec_geometricPureRelativeDimension_one R π n

/-- Arbitrary coefficient base change preserves the node's geometric relative-dimension
bound. -/
theorem baseChangedNodeToBaseSpec_geometricRelativeDimensionLE_one (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.GeometricRelativeDimensionLE 1
      (baseChangedNodeToBaseSpec R T π n) := by
  exact GromovWitten.AlgebraicGeometry.Curves.GeometricRelativeDimensionLE.pullback_snd
    (toBaseSpec_geometricRelativeDimensionLE_one R π n)
    (Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- Arbitrary coefficient base change preserves geometric pure relative dimension one. -/
theorem baseChangedNodeToBaseSpec_geometricPureRelativeDimension_one (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.GeometricPureRelativeDimension 1
      (baseChangedNodeToBaseSpec R T π n) := by
  exact GromovWitten.AlgebraicGeometry.Curves.GeometricPureRelativeDimension.pullback_snd
    (toBaseSpec_geometricPureRelativeDimension_one R π n)
    (Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- Every coefficient base change to a nontrivial ring is syntomic of pure relative dimension
one. -/
instance baseChangedNodeToBaseSpec_syntomicOfRelativeDimension_one
    [Nontrivial T] (π : R) (n : ℕ) :
    GromovWitten.AlgebraicGeometry.Curves.SyntomicOfRelativeDimension 1
      (baseChangedNodeToBaseSpec R T π n) where
  syntomic := inferInstance
  geometricPureRelativeDimension :=
    baseChangedNodeToBaseSpec_geometricPureRelativeDimension_one R T π n

/-- When the smoothing parameter vanishes after coefficient extension, the actual
fibre product is isomorphic over `Spec T` to the positive special-fibre node chart `xy = 0`. -/
noncomputable def specialFiberOverIso (π : R) (n : ℕ)
    (hπ : algebraMap R T π = 0) :
    Over.mk (baseChangedNodeToBaseSpec R T π n) ≅ Over.mk (toBaseSpec T 0 n) := by
  rw [← hπ]
  exact baseChangeOverIso R T π n

/-- The underlying scheme isomorphism of the zero-parameter base-change comparison. -/
noncomputable def specialFiberSpecIso (π : R) (n : ℕ)
    (hπ : algebraMap R T π = 0) :
    baseChangedNodeSpec R T π n ≅ Spec (.of (Ring T 0 n)) :=
  (Over.forget (Spec (.of T))).mapIso (specialFiberOverIso R T π n hπ)

theorem specialFiberOverIso_inv_toBaseSpec (π : R) (n : ℕ)
    (hπ : algebraMap R T π = 0) :
    (specialFiberOverIso R T π n hπ).inv.left ≫ baseChangedNodeToBaseSpec R T π n =
      toBaseSpec T 0 n := by
  exact (specialFiberOverIso R T π n hπ).inv.w

/-- The closed `x`-axis inside a base-changed local-node chart where the parameter vanishes. -/
def specialFiberXBranch (π : R) (n : ℕ) (hn : n ≠ 0)
    (hπ : algebraMap R T π = 0) :
    Spec (.of T[X]) ⟶ baseChangedNodeSpec R T π n :=
  xBranchSpec T n hn ≫ (specialFiberOverIso R T π n hπ).inv.left

/-- The closed `y`-axis inside a base-changed local-node chart where the parameter vanishes. -/
def specialFiberYBranch (π : R) (n : ℕ) (hn : n ≠ 0)
    (hπ : algebraMap R T π = 0) :
    Spec (.of T[X]) ⟶ baseChangedNodeSpec R T π n :=
  yBranchSpec T n hn ≫ (specialFiberOverIso R T π n hπ).inv.left

/-- The common origin inside a base-changed local-node chart where the parameter vanishes. -/
def specialFiberNodeOrigin (π : R) (n : ℕ) (hn : n ≠ 0)
    (hπ : algebraMap R T π = 0) :
    Spec (.of T) ⟶ baseChangedNodeSpec R T π n :=
  nodeOriginSpec T n hn ≫ (specialFiberOverIso R T π n hπ).inv.left

instance specialFiberXBranch_isClosedImmersion (π : R) (n : ℕ) (hn : n ≠ 0)
    (hπ : algebraMap R T π = 0) :
    IsClosedImmersion (specialFiberXBranch R T π n hn hπ) := by
  dsimp [specialFiberXBranch]
  have : IsIso (specialFiberOverIso R T π n hπ).inv.left := by
    change IsIso ((Over.forget (Spec (.of T))).map
      (specialFiberOverIso R T π n hπ).inv)
    infer_instance
  infer_instance

instance specialFiberYBranch_isClosedImmersion (π : R) (n : ℕ) (hn : n ≠ 0)
    (hπ : algebraMap R T π = 0) :
    IsClosedImmersion (specialFiberYBranch R T π n hn hπ) := by
  dsimp [specialFiberYBranch]
  have : IsIso (specialFiberOverIso R T π n hπ).inv.left := by
    change IsIso ((Over.forget (Spec (.of T))).map
      (specialFiberOverIso R T π n hπ).inv)
    infer_instance
  infer_instance

instance specialFiberNodeOrigin_isClosedImmersion (π : R) (n : ℕ) (hn : n ≠ 0)
    (hπ : algebraMap R T π = 0) :
    IsClosedImmersion (specialFiberNodeOrigin R T π n hn hπ) := by
  dsimp [specialFiberNodeOrigin]
  have : IsIso (specialFiberOverIso R T π n hπ).inv.left := by
    change IsIso ((Over.forget (Spec (.of T))).map
      (specialFiberOverIso R T π n hπ).inv)
    infer_instance
  infer_instance

/-- Over a nontrivial coefficient ring, the two transported special-fibre branches remain
distinct. -/
theorem specialFiberXBranch_ne_specialFiberYBranch
    (π : R) (n : ℕ) [Nontrivial T] (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    specialFiberXBranch R T π n hn hπ ≠ specialFiberYBranch R T π n hn hπ := by
  intro h
  have : IsIso (specialFiberOverIso R T π n hπ).inv.left := by
    change IsIso ((Over.forget (Spec (.of T))).map
      (specialFiberOverIso R T π n hπ).inv)
    infer_instance
  apply xBranchSpec_ne_yBranchSpec T n hn
  rw [← cancel_mono (specialFiberOverIso R T π n hπ).inv.left]
  change xBranchSpec T n hn ≫ (specialFiberOverIso R T π n hπ).inv.left =
    yBranchSpec T n hn ≫ (specialFiberOverIso R T π n hπ).inv.left at h
  exact h

@[reassoc (attr := simp)]
theorem affineLineOriginSpec_specialFiberXBranch
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    affineLineOriginSpec T ≫ specialFiberXBranch R T π n hn hπ =
      specialFiberNodeOrigin R T π n hn hπ := by
  simp [specialFiberXBranch, specialFiberNodeOrigin]

@[reassoc (attr := simp)]
theorem affineLineOriginSpec_specialFiberYBranch
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    affineLineOriginSpec T ≫ specialFiberYBranch R T π n hn hπ =
      specialFiberNodeOrigin R T π n hn hπ := by
  simp [specialFiberYBranch, specialFiberNodeOrigin]

@[reassoc (attr := simp)]
theorem specialFiberXBranch_toBaseSpec
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    specialFiberXBranch R T π n hn hπ ≫ baseChangedNodeToBaseSpec R T π n =
      affineLineToBaseSpec T := by
  rw [specialFiberXBranch, Category.assoc, specialFiberOverIso_inv_toBaseSpec,
    xBranchSpec_toBaseSpec]

@[reassoc (attr := simp)]
theorem specialFiberYBranch_toBaseSpec
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    specialFiberYBranch R T π n hn hπ ≫ baseChangedNodeToBaseSpec R T π n =
      affineLineToBaseSpec T := by
  rw [specialFiberYBranch, Category.assoc, specialFiberOverIso_inv_toBaseSpec,
    yBranchSpec_toBaseSpec]

@[reassoc (attr := simp)]
theorem specialFiberNodeOrigin_toBaseSpec
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    specialFiberNodeOrigin R T π n hn hπ ≫ baseChangedNodeToBaseSpec R T π n =
      𝟙 (Spec (.of T)) := by
  rw [specialFiberNodeOrigin, Category.assoc, specialFiberOverIso_inv_toBaseSpec,
    nodeOriginSpec_toBaseSpec]

/-- Each displayed special-fibre branch is smooth of relative dimension one over the
coefficient ring. -/
theorem specialFiberXBranch_smoothOfRelativeDimension_one
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    SmoothOfRelativeDimension 1
      (specialFiberXBranch R T π n hn hπ ≫ baseChangedNodeToBaseSpec R T π n) := by
  rw [specialFiberXBranch_toBaseSpec]
  exact affineLineToBaseSpec_smoothOfRelativeDimension_one T

/-- The second displayed special-fibre branch is likewise smooth of relative dimension one. -/
theorem specialFiberYBranch_smoothOfRelativeDimension_one
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    SmoothOfRelativeDimension 1
      (specialFiberYBranch R T π n hn hπ ≫ baseChangedNodeToBaseSpec R T π n) := by
  rw [specialFiberYBranch_toBaseSpec]
  exact affineLineToBaseSpec_smoothOfRelativeDimension_one T

set_option backward.isDefEq.respectTransparency false in
private theorem IsPullback.postcomp_overIso
    {S P A B : Scheme} {X Y : Over S} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ Y.left} {g : B ⟶ Y.left} (h : IsPullback fst snd f g) (e : X ≅ Y) :
    IsPullback fst snd (f ≫ e.inv.left) (g ≫ e.inv.left) := by
  let e' := (Over.forget S).mapIso e
  apply h.of_iso (Iso.refl P) (Iso.refl A) (Iso.refl B) e'.symm
  · simp
  · simp
  · simp [e']
  · simp [e']

/-- Scheme-theoretically, the pullback of the two branches in the actual base-changed special
fibre is their common affine-line origin `Spec T`. -/
theorem specialFiberBranches_isPullback
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    IsPullback (affineLineOriginSpec T) (affineLineOriginSpec T)
      (specialFiberXBranch R T π n hn hπ) (specialFiberYBranch R T π n hn hπ) := by
  exact IsPullback.postcomp_overIso (affineLineOrigins_isPullback T n hn)
    (specialFiberOverIso R T π n hπ)

set_option backward.isDefEq.respectTransparency false in
private theorem range_union_postcomp_over_iso
    {S A B : Scheme} {X Y : Over S} (e : X ≅ Y) (f : A ⟶ Y.left) (g : B ⟶ Y.left)
    (h : Set.range f ∪ Set.range g = Set.univ) :
    Set.range (f ≫ e.inv.left) ∪ Set.range (g ≫ e.inv.left) = Set.univ := by
  let e' := (Over.forget S).mapIso e
  change Set.range ((Scheme.homeoOfIso e').symm ∘ f) ∪
    Set.range ((Scheme.homeoOfIso e').symm ∘ g) = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  have hx : Scheme.homeoOfIso e' x ∈ Set.range f ∪ Set.range g := by
    rw [h]
    trivial
  rcases hx with ⟨a, ha⟩ | ⟨b, hb⟩
  · left
    refine ⟨a, ?_⟩
    simp only [Function.comp_apply, ha, Homeomorph.symm_apply_apply]
  · right
    refine ⟨b, ?_⟩
    simp only [Function.comp_apply, hb, Homeomorph.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem range_inter_postcomp_over_iso
    {S A B C : Scheme} {X Y : Over S} (e : X ≅ Y)
    (f : A ⟶ Y.left) (g : B ⟶ Y.left) (k : C ⟶ Y.left)
    (h : Set.range f ∩ Set.range g = Set.range k) :
    Set.range (f ≫ e.inv.left) ∩ Set.range (g ≫ e.inv.left) =
      Set.range (k ≫ e.inv.left) := by
  let e' := (Over.forget S).mapIso e
  change Set.range ((Scheme.homeoOfIso e').symm ∘ f) ∩
      Set.range ((Scheme.homeoOfIso e').symm ∘ g) =
    Set.range ((Scheme.homeoOfIso e').symm ∘ k)
  rw [Set.range_comp, Set.range_comp, Set.range_comp,
    ← Set.image_inter (Scheme.homeoOfIso e').symm.injective, h]

/-- The two closed affine-line branches cover the actual base-changed special fibre. -/
theorem range_specialFiberXBranch_union_range_specialFiberYBranch
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    Set.range (specialFiberXBranch R T π n hn hπ) ∪
      Set.range (specialFiberYBranch R T π n hn hπ) = Set.univ := by
  exact range_union_postcomp_over_iso
    (specialFiberOverIso R T π n hπ)
    (xBranchSpec T n hn) (yBranchSpec T n hn)
    (range_xBranchSpec_union_range_yBranchSpec T n hn)

/-- The common-origin carrier is exactly the intersection of the two branches in the actual
base-changed special fibre. -/
theorem range_specialFiberXBranch_inter_range_specialFiberYBranch
    (π : R) (n : ℕ) (hn : n ≠ 0) (hπ : algebraMap R T π = 0) :
    Set.range (specialFiberXBranch R T π n hn hπ) ∩
      Set.range (specialFiberYBranch R T π n hn hπ) =
        Set.range (specialFiberNodeOrigin R T π n hn hπ) := by
  exact range_inter_postcomp_over_iso
    (specialFiberOverIso R T π n hπ)
    (xBranchSpec T n hn) (yBranchSpec T n hn) (nodeOriginSpec T n hn)
    (range_xBranchSpec_inter_range_yBranchSpec T n hn)

end SchemeBaseChange

section GenericFiber

variable (F : Type u) [Field F] [Algebra R F]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- When `π` has nonzero image in a field, the affine generic fibre of the local-node
presentation is explicitly the spectrum of a Laurent polynomial ring. -/
noncomputable def genericFiberSpecIso (π : R) (n : ℕ)
    (hπ : algebraMap R F π ≠ 0) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
        (Spec.map (CommRingCat.ofHom (algebraMap R F))) ≅
      Spec (.of (LaurentPolynomial F)) :=
  baseChangeSpecIso R F π n ≪≫
    (Scheme.Spec.mapIso
      (unitEquivLaurent F (algebraMap R F π) n
        (isUnit_iff_ne_zero.mpr hπ)).toRingEquiv.toCommRingCatIso.op).symm

@[reassoc (attr := simp)]
theorem genericFiberSpecIso_hom_toBaseSpec (π : R) (n : ℕ)
    (hπ : algebraMap R F π ≠ 0) :
    (genericFiberSpecIso R F π n hπ).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap F (LaurentPolynomial F))) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
        (Spec.map (CommRingCat.ofHom (algebraMap R F))) := by
  simp only [genericFiberSpecIso, Iso.trans_hom, Category.assoc]
  rw [← baseChangeSpecIso_hom_toBaseSpec R F π n]
  rw [cancel_epi (baseChangeSpecIso R F π n).hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, AlgebraicGeometry.Spec.map_inj]
  apply CommRingCat.hom_ext
  exact RingHom.ext fun a =>
    (unitEquivLaurent F (algebraMap R F π) n
      (isUnit_iff_ne_zero.mpr hπ)).symm.commutes a

/-- The generic-fibre projection of the affine local-node smoothing is smooth whenever the
smoothing parameter remains nonzero in the field. -/
theorem genericFiberProjection_smooth (π : R) (n : ℕ)
    (hπ : algebraMap R F π ≠ 0) :
    Smooth (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))) := by
  let : MorphismProperty.RespectsIso (@Smooth) := by
    rw [HasRingHomProperty.eq_affineLocally @Smooth]
    exact affineLocally_respectsIso _ RingHom.Smooth.propertyIsLocal.respectsIso
  rw [← genericFiberSpecIso_hom_toBaseSpec R F π n hπ]
  exact MorphismProperty.RespectsIso.precomp @Smooth
    (genericFiberSpecIso R F π n hπ).hom _ (laurentSpec_smooth F)

/-- The generic-fibre projection of the affine local-node smoothing is smooth of relative
dimension one whenever the smoothing parameter remains nonzero in the field. -/
theorem genericFiberProjection_smoothOfRelativeDimension_one (π : R) (n : ℕ)
    (hπ : algebraMap R F π ≠ 0) :
    SmoothOfRelativeDimension 1 (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R (Ring R π n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R F)))) := by
  let : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 1) := by
    rw [HasRingHomProperty.eq_affineLocally (@SmoothOfRelativeDimension 1)]
    exact affineLocally_respectsIso _
      (HasRingHomProperty.isLocal_ringHomProperty
        (@SmoothOfRelativeDimension 1)).respectsIso
  rw [← genericFiberSpecIso_hom_toBaseSpec R F π n hπ]
  exact MorphismProperty.RespectsIso.precomp (@SmoothOfRelativeDimension 1)
    (genericFiberSpecIso R F π n hπ).hom _
      (laurentSpec_smoothOfRelativeDimension_one F)

end GenericFiber

/-- On any positive-exponent fibre where `π` vanishes, the equation specializes to `xy = 0`. -/
theorem specialFiber_x_mul_y (π : R) (n : ℕ) (hn : n ≠ 0)
    (hπ : algebraMap R S π = 0) :
    x S (algebraMap R S π) n * y S (algebraMap R S π) n = 0 := by
  rw [x_mul_y]
  simp [hπ, hn]

/-- Over a nontrivial special-fibre ring, the positive-thickness fibre contains the two
displayed nonzero zero divisors and therefore is not a domain. -/
theorem specialFiber_not_isDomain (π : R) (n : ℕ) [Nontrivial S] (hn : n ≠ 0)
    (hπ : algebraMap R S π = 0) :
    ¬ IsDomain (Ring S (algebraMap R S π) n) := by
  rw [hπ]
  exact not_isDomain_zero_parameter S n hn

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode
