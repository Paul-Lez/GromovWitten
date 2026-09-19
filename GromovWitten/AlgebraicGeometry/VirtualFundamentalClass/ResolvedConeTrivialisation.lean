/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedConeDimension
import GromovWitten.AlgebraicGeometry.Cones.ConeTranslation

/-!
# Trivialisation of the tangent torsor over the resolved cone

In the polynomial model `R = k[x_i]_{i ∈ σ}` of the affine Behrend–Fantechi setting, the
projection `C ×_X E₀ → C(E)` from the product of the normal cone with the bundle `E₀` to the
resolved cone is a torsor under the restricted tangent bundle `T_M|_U = U × 𝔸^σ` of the ambient
affine space.  This file proves that this torsor is trivial, that is,
`ResolvedCone.IsPolynomialTrivialisation`, the one hypothesis left open in
`VirtualFundamentalClass/ResolvedConeDimension.lean`; the purity statements of that file thereby
become conditional only on the dimension formula for the extended Rees algebra of `I`.

The proof is the algebraic form of the geometric statement "a translation invariant closed
subscheme of an affine space over a base is extended from the base".  Concretely, writing
`S = R ⧸ I`, `gr = gr_I(R)` and `A = gr ⊗_S Sym_S(E⁰)` for the coordinate ring of `C ×_X E₀`:

* the tangent bundle coacts on `A`, by Vistoli's translation `ConeTranslation.coaction` on `gr`
  and by `φ.degreeOne` (with the opposite sign) on `Sym(E⁰)`; the resulting
  `ResolvedCone.productCoaction` fixes the image of `Sym(E⁻¹)`, because `coneBeta φ` kills the
  image of `coneAlpha φ`;
* a splitting of the mapping-cone surjection `coneBeta φ : L⁻¹ ⊕ E⁰ → L⁰`
  (`ResolvedCone.exists_rightInverse_coneBeta`) produces `|σ|` elements of `A` which the coaction
  translates by exactly the `|σ|` tangent parameters, the fibre coordinates of the torsor;
* the resulting comparison map `ring φ [t_σ] → A` is surjective (this is the exactness of the
  mapping-cone sequence) and equivariant, so its kernel is a translation invariant ideal, hence
  extended from `ring φ` by `ResolvedCone.eq_map_comap_C_of_translationCoaction` — and therefore
  zero, since `toProduct φ` is injective.

## Main definitions

* `ResolvedCone.tangentCoord`, `ResolvedCone.tangentBasis`: the identification of
  `L⁰ = S ⊗_R Ω[R⁄k]` with the free module on the differentials of the coordinates, and the
  coordinate map `1 ⊗ df ↦ Σ_i ε_i ∂_i f` which compares it with the Taylor derivation used by
  `Cones/ConeTranslation.lean`.
* `ResolvedCone.productCoaction`: the translation coaction of `T_M|_U` on `C ×_X E₀`.
* `ResolvedCone.coneLinear`: the linear map `(y, z) ↦ [y] ⊗ 1 - 1 ⊗ z` from `L⁻¹ ⊕ E⁰` to the
  coordinate ring of `C ×_X E₀`.
* `ResolvedCone.torsorCoord`, `ResolvedCone.torsorHom`: the fibre coordinates attached to a
  splitting of `coneBeta φ`, and the resulting comparison map `ring φ [t_σ] → gr ⊗ Sym(E⁰)`.

## Main results

* `ResolvedCone.productCoaction_coneLinear`: the coaction moves `coneLinear φ m` by the tangent
  coordinates of `coneBeta φ m`.
* `ResolvedCone.productCoaction_productMap`, `ResolvedCone.productCoaction_toProduct`: the
  resolved cone is invariant.
* `ResolvedCone.torsorHom_surjective`: the comparison map is surjective.
* `ResolvedCone.isPolynomialTrivialisation`: **the torsor is trivial**.
* `ResolvedCone.ringKrullDim_quotient_ring_eq'`, `ResolvedCone.dimension_eq_of_isMax'`,
  `ResolvedCone.dimension_toBundle_eq_of_isMax'`: the purity statements of
  `ResolvedConeDimension.lean` with the trivialisation hypothesis discharged.  They carry only
  `I ≠ ⊤`, the obstruction theory hypothesis on `φ`, and
  `HasDimensionFormula (extendedRees R I)`.
-/

universe u

-- The coordinate ring of `C ×_X E₀` is a tensor product whose left factor is itself a quotient
-- of a Rees algebra; synthesising `CommSemiring`/`CommRing` for it needs one more level of
-- pending instance problems than the default.
set_option maxSynthPendingDepth 5

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone

open CategoryTheory
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open scoped TensorProduct

section Trivialisation

variable (k : Type u) [Field k] (σ : Type u) (I : Ideal (MvPolynomial σ k))

/-! ### The tangent coordinates of the conormal complex -/

/-- The reduction modulo `I` of the Taylor derivation of the ambient polynomial ring:
`f ↦ Σ_i ε_i ∂_i f`, with coefficients in `S = R ⧸ I`. -/
noncomputable def taylorMod :
    Derivation k (MvPolynomial σ k) (MvPolynomial σ (MvPolynomial σ k ⧸ I)) :=
  (MvPolynomial.mapAlgHom
      (Algebra.ofId (MvPolynomial σ k) (MvPolynomial σ k ⧸ I))).toLinearMap.compDer
    (ConeTranslation.taylor k σ)

/-- The Taylor derivation modulo `I` is the reduction of the Taylor derivation. -/
theorem taylorMod_apply (f : MvPolynomial σ k) :
    taylorMod k σ I f =
      MvPolynomial.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ I))
        (ConeTranslation.taylor k σ f) :=
  rfl

/-- The **tangent coordinate map** of the polynomial model: the `S`-linear map
`L⁰ = S ⊗_R Ω[R⁄k] → S[ε_σ]` sending `1 ⊗ df` to `Σ_i ε_i ∂_i f`.  It is the coordinate form of
the identification of `L⁰` with the dual of the trivial tangent bundle `T_M|_U`. -/
noncomputable def tangentCoord :
    (MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k] →ₗ[MvPolynomial σ k ⧸ I]
      MvPolynomial σ (MvPolynomial σ k ⧸ I) :=
  LinearMap.liftBaseChange _ (taylorMod k σ I).liftKaehlerDifferential

/-- The tangent coordinate map on the differential of a polynomial. -/
@[simp]
theorem tangentCoord_one_tmul_D (f : MvPolynomial σ k) :
    tangentCoord k σ I (1 ⊗ₜ KaehlerDifferential.D k (MvPolynomial σ k) f) =
      MvPolynomial.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ I))
        (ConeTranslation.taylor k σ f) := by
  rw [tangentCoord, LinearMap.liftBaseChange_one_tmul,
    Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- The tangent coordinate map sends the differential of a coordinate to the corresponding
variable. -/
@[simp]
theorem tangentCoord_one_tmul_D_X (i : σ) :
    tangentCoord k σ I (1 ⊗ₜ KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i)) =
      MvPolynomial.X i := by
  rw [tangentCoord_one_tmul_D, ConeTranslation.taylor_X, MvPolynomial.map_X]

/-- The basis of `L⁰ = S ⊗_R Ω[R⁄k]` given by the differentials of the coordinates of the
ambient affine space. -/
noncomputable def tangentBasis :
    Module.Basis σ (MvPolynomial σ k ⧸ I)
      ((MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k]) :=
  (KaehlerDifferential.mvPolynomialBasis k σ).baseChange _

/-- The `i`-th element of the tangent basis is the differential of the `i`-th coordinate. -/
theorem tangentBasis_apply (i : σ) :
    tangentBasis k σ I i =
      1 ⊗ₜ KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) := by
  rw [tangentBasis, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]

end Trivialisation

section Coaction

variable {k : Type u} [Field k] {σ : Type u} {I : Ideal (MvPolynomial σ k)}
variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))

/-- The tangent coordinates, with values in the coordinate ring of `C ×_X E₀`. -/
noncomputable def tangentPoly :
    (MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k] →ₗ[MvPolynomial σ k ⧸ I]
      MvPolynomial σ (productRing φ) :=
  (MvPolynomial.mapAlgHom
      (Algebra.ofId (MvPolynomial σ k ⧸ I) (productRing φ))).toLinearMap ∘ₗ tangentCoord k σ I

/-- The tangent coordinates in the coordinate ring of `C ×_X E₀` are the reduction of the
tangent coordinates in `S`. -/
theorem tangentPoly_apply
    (v : (MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k]) :
    tangentPoly φ v =
      MvPolynomial.map (algebraMap (MvPolynomial σ k ⧸ I) (productRing φ))
        (tangentCoord k σ I v) :=
  rfl

/-- The tangent coordinates send the differential of the `i`-th coordinate to the `i`-th
variable. -/
@[simp]
theorem tangentPoly_tangentBasis (i : σ) :
    tangentPoly φ (tangentBasis k σ I i) = MvPolynomial.X i := by
  rw [tangentPoly_apply, tangentBasis_apply, tangentCoord_one_tmul_D_X, MvPolynomial.map_X]

/-- The translation coaction of the tangent bundle `T_M|_U` on the affine normal cone, with
values in polynomials over the coordinate ring of `C ×_X E₀`. -/
noncomputable def grCoaction :
    AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
      MvPolynomial σ (productRing φ) where
  toRingHom :=
    (MvPolynomial.mapAlgHom (Algebra.TensorProduct.includeLeft :
        AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
          productRing φ)).toRingHom.comp (ConeTranslation.coaction I).toRingHom
  commutes' := by
    intro s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h1 : algebraMap (MvPolynomial σ k ⧸ I)
        (AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) (Ideal.Quotient.mk I r) =
        algebraMap (MvPolynomial σ k)
          (AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) r :=
      (IsScalarTower.algebraMap_apply (MvPolynomial σ k) (MvPolynomial σ k ⧸ I) _ r).symm
    change (MvPolynomial.mapAlgHom _) (ConeTranslation.coaction I _) = _
    rw [h1, ConeTranslation.coaction_algebraMap, MvPolynomial.mapAlgHom_apply,
      MvPolynomial.map_C, MvPolynomial.algebraMap_apply, ← h1]
    exact congrArg MvPolynomial.C
      ((Algebra.TensorProduct.includeLeft :
        AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
          productRing φ).commutes _)

/-- The inclusion of the normal cone into `C ×_X E₀` is a map over the ambient polynomial
ring. -/
theorem includeLeft_comp_algebraMap :
    ((Algebra.TensorProduct.includeLeft :
        AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
          productRing φ) : _ →+* productRing φ).comp
        (algebraMap (MvPolynomial σ k)
          (AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I)) =
      (algebraMap (MvPolynomial σ k ⧸ I) (productRing φ)).comp
        (algebraMap (MvPolynomial σ k) (MvPolynomial σ k ⧸ I)) := by
  refine RingHom.ext fun r ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply (MvPolynomial σ k) (MvPolynomial σ k ⧸ I)
      (AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I)]
  exact (Algebra.TensorProduct.includeLeft :
    AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
      productRing φ).commutes _

/-- **The coaction on the degree-one part of the normal cone.**  The translation coaction moves
a degree-one class `[y]` to `[y] + Σ_i ε_i ∂_i y`, and the derivative term is exactly the
tangent coordinate of the conormal class of `y`. -/
theorem grCoaction_conormalToAssociatedGraded (y : I.Cotangent) :
    grCoaction φ (AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ k) I y) =
      MvPolynomial.C ((Algebra.TensorProduct.includeLeft :
          AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
            productRing φ)
          (AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ k) I y)) +
        tangentPoly φ (AffineNormalCone.conormalMap k (MvPolynomial σ k) I y) := by
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I y
  rw [AffineNormalCone.conormalToAssociatedGraded_toCotangent,
    AffineNormalCone.conormalMap_toCotangent, tangentPoly_apply, tangentCoord_one_tmul_D]
  change (MvPolynomial.mapAlgHom _) (ConeTranslation.coaction I _) = _
  rw [ConeTranslation.coaction_degreeOne, MvPolynomial.mapAlgHom_apply, map_add,
    MvPolynomial.map_C, MvPolynomial.map_map, MvPolynomial.map_map,
    includeLeft_comp_algebraMap φ]
  rfl

/-- The translation of the bundle `E₀` by a tangent vector, as a linear map `E⁰ → (C ×_X E₀)[ε]`:
the tangent bundle acts on `E₀` through `φ.degreeOne`, with the sign opposite to its action on
the normal cone, so that the two actions cancel along the map to `E₁`. -/
noncomputable def symCoactionLinear :
    E.degreeOne →ₗ[MvPolynomial σ k ⧸ I] MvPolynomial σ (productRing φ) :=
  ((IsScalarTower.toAlgHom (MvPolynomial σ k ⧸ I) (productRing φ)
        (MvPolynomial σ (productRing φ))).toLinearMap ∘ₗ
      ((Algebra.TensorProduct.includeRight :
          SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne →ₐ[MvPolynomial σ k ⧸ I]
            productRing φ).toLinearMap ∘ₗ
        SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeOne)) -
    (tangentPoly φ ∘ₗ φ.degreeOne)

/-- The value of the translation of `E₀` on a generator. -/
theorem symCoactionLinear_apply (z : E.degreeOne) :
    symCoactionLinear φ z =
      MvPolynomial.C
          ((1 : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) ⊗ₜ
            SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeOne z) -
        tangentPoly φ (φ.degreeOne z) :=
  rfl

/-- The translation coaction of the tangent bundle on the bundle `E₀`. -/
noncomputable def symCoaction :
    SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne →ₐ[MvPolynomial σ k ⧸ I]
      MvPolynomial σ (productRing φ) :=
  SymmetricAlgebra.lift (symCoactionLinear φ)

/-- **The translation coaction on `C ×_X E₀`.**  The tangent bundle `T_M|_U` acts diagonally, by
Vistoli's translation on the normal cone and by `φ.degreeOne` on `E₀`. -/
noncomputable def productCoaction :
    productRing φ →ₐ[MvPolynomial σ k ⧸ I] MvPolynomial σ (productRing φ) :=
  Algebra.TensorProduct.lift (grCoaction φ) (symCoaction φ) fun _ _ ↦ Commute.all _ _

/-- The coaction on the image of the normal cone. -/
@[simp]
theorem productCoaction_tmul_one
    (g : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) :
    productCoaction φ (g ⊗ₜ (1 : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)) =
      grCoaction φ g := by
  rw [productCoaction, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

/-- The coaction on the image of the bundle `E₀`. -/
@[simp]
theorem productCoaction_one_tmul (p : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne) :
    productCoaction φ
        ((1 : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) ⊗ₜ p) =
      symCoaction φ p := by
  rw [productCoaction, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- The `S`-linear map `L⁻¹ ⊕ E⁰ → gr ⊗ Sym(E⁰)` underlying the mapping cone: `(y, z)` goes to
`[y] ⊗ 1 - 1 ⊗ z`.  Composed with `coneAlpha φ` it is the defining map of the resolved cone,
and its coaction is measured by `coneBeta φ`. -/
noncomputable def coneLinear :
    (conormalComplex k (MvPolynomial σ k) I).degreeZero × E.degreeOne →ₗ[MvPolynomial σ k ⧸ I]
      productRing φ :=
  LinearMap.coprod
    ((Algebra.TensorProduct.includeLeft :
        AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
          productRing φ).toLinearMap ∘ₗ
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ k) I)
    (-((Algebra.TensorProduct.includeRight :
        SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne →ₐ[MvPolynomial σ k ⧸ I]
          productRing φ).toLinearMap ∘ₗ
      SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeOne))

/-- The value of `coneLinear`. -/
theorem coneLinear_apply
    (m : (conormalComplex k (MvPolynomial σ k) I).degreeZero × E.degreeOne) :
    coneLinear φ m =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ k) I m.1 ⊗ₜ 1 -
        (1 : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) ⊗ₜ
          SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeOne m.2 := by
  rw [coneLinear, LinearMap.coprod_apply]
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
  abel

set_option maxHeartbeats 1000000 in
-- The rewrites below all take place inside the tensor product `gr ⊗ Sym(E⁰)`, whose ring
-- instance is expensive to elaborate; the default heartbeat budget is not enough for the
-- dozen rewriting steps of this computation.
/-- **The infinitesimal action on the mapping cone.**  The translation coaction moves
`coneLinear φ m` by the tangent coordinates of `coneBeta φ m`; this is the identity which makes
the resolved cone invariant and `C ×_X E₀` a torsor over it. -/
theorem productCoaction_coneLinear
    (m : (conormalComplex k (MvPolynomial σ k) I).degreeZero × E.degreeOne) :
    productCoaction φ (coneLinear φ m) =
      MvPolynomial.C (coneLinear φ m) + tangentPoly φ (PicardCriteria.coneBeta φ m) := by
  rw [coneLinear_apply, map_sub, productCoaction_tmul_one, productCoaction_one_tmul,
    grCoaction_conormalToAssociatedGraded, symCoaction, SymmetricAlgebra.lift_ι_apply,
    symCoactionLinear_apply, Algebra.TensorProduct.includeLeft_apply,
    PicardCriteria.coneBeta_apply, conormalComplex_differential, map_add,
    map_sub (MvPolynomial.C : productRing φ →+* MvPolynomial σ (productRing φ))]
  abel

/-- The defining map of the resolved cone is `coneLinear` composed with the first map of the
mapping cone sequence. -/
theorem coneLinear_coneAlpha (x : E.degreeZero) :
    coneLinear φ (PicardCriteria.coneAlpha φ x) =
      productMap φ (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeZero x) := by
  rw [PicardCriteria.coneAlpha_apply, coneLinear_apply, productMap_ι]
  simp only [map_neg, TensorProduct.tmul_neg, sub_neg_eq_add]

/-- **The resolved cone is invariant under the translation coaction.**  The composite
`Sym(E⁻¹) → gr ⊗ Sym(E⁰)` is a map of coalgebra comodules with trivial coaction on the source:
the two translations cancel because `coneBeta φ ∘ coneAlpha φ = 0`. -/
theorem productCoaction_productMap (a : bundleRing φ) :
    productCoaction φ (productMap φ a) = MvPolynomial.C (productMap φ a) := by
  have key : (productCoaction φ).comp (productMap φ) =
      (IsScalarTower.toAlgHom (MvPolynomial σ k ⧸ I) (productRing φ)
        (MvPolynomial σ (productRing φ))).comp (productMap φ) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
    have hx : productCoaction φ
        (productMap φ (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeZero x)) =
        MvPolynomial.C
          (productMap φ (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeZero x)) := by
      rw [← coneLinear_coneAlpha, productCoaction_coneLinear, PicardCriteria.coneBeta_coneAlpha,
        map_zero, add_zero]
    exact hx
  exact DFunLike.congr_fun key a

/-- The coordinate ring of the resolved cone consists of invariants of the translation
coaction. -/
theorem productCoaction_toProduct (a : ring φ) :
    productCoaction φ (toProduct φ a) = MvPolynomial.C (toProduct φ a) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [toProduct_mk]
  exact productCoaction_productMap φ b

end Coaction

section Torsor

variable {k : Type u} [Field k] {σ : Type u} {I : Ideal (MvPolynomial σ k)}
variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
variable (s : (conormalComplex k (MvPolynomial σ k) I).degreeOne →ₗ[MvPolynomial σ k ⧸ I]
  (conormalComplex k (MvPolynomial σ k) I).degreeZero × E.degreeOne)

/-- The `σ` coordinates along the fibres of the torsor `C ×_X E₀ → C(E)`, attached to a
splitting `s` of the mapping-cone surjection `coneBeta φ`. -/
noncomputable def torsorCoord (i : σ) : productRing φ :=
  coneLinear φ (s (tangentBasis k σ I i))

/-- The torsor coordinates are affine coordinates for the translation coaction: the `i`-th one is
translated by exactly the `i`-th tangent parameter. -/
theorem productCoaction_torsorCoord
    (hs : (PicardCriteria.coneBeta φ) ∘ₗ s = LinearMap.id) (i : σ) :
    productCoaction φ (torsorCoord φ s i) =
      MvPolynomial.C (torsorCoord φ s i) + MvPolynomial.X i := by
  have hv : PicardCriteria.coneBeta φ (s (tangentBasis k σ I i)) = tangentBasis k σ I i :=
    DFunLike.congr_fun hs _
  rw [torsorCoord, productCoaction_coneLinear, hv, tangentPoly_tangentBasis]

/-- The **comparison map** `C(E) × 𝔸^σ → C ×_X E₀` attached to a splitting of the mapping-cone
surjection: it is the coordinate ring of the resolved cone together with the `σ` coordinates
along the fibres of the torsor. -/
noncomputable def torsorHom :
    MvPolynomial σ (ring φ) →ₐ[MvPolynomial σ k ⧸ I] productRing φ :=
  MvPolynomial.aevalTower (toProduct φ) (torsorCoord φ s)

/-- The comparison map restricted to the coordinate ring of the resolved cone. -/
@[simp]
theorem torsorHom_C (a : ring φ) : torsorHom φ s (MvPolynomial.C a) = toProduct φ a :=
  MvPolynomial.aevalTower_C _ _ a

/-- The comparison map on the fibre coordinates. -/
@[simp]
theorem torsorHom_X (i : σ) : torsorHom φ s (MvPolynomial.X i) = torsorCoord φ s i :=
  MvPolynomial.aevalTower_X _ _ i

/-- **The comparison map is equivariant.**  On `C(E) × 𝔸^σ` the tangent bundle acts by
translation of the second factor, which is the translation coaction of
`ResolvedConeDimension.lean`; on `C ×_X E₀` it acts by `productCoaction`. -/
theorem map_torsorHom_translationCoaction
    (hs : (PicardCriteria.coneBeta φ) ∘ₗ s = LinearMap.id) (f : MvPolynomial σ (ring φ)) :
    MvPolynomial.map ((torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ))
        (translationCoaction (ring φ) σ f) =
      productCoaction φ (torsorHom φ s f) := by
  have key : (MvPolynomial.map ((torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ))).comp
        (translationCoaction (ring φ) σ) =
      ((productCoaction φ : productRing φ →+* MvPolynomial σ (productRing φ))).comp
        (torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, translationCoaction_C, MvPolynomial.map_C]
      change MvPolynomial.C (torsorHom φ s (MvPolynomial.C a)) =
        productCoaction φ (torsorHom φ s (MvPolynomial.C a))
      rw [torsorHom_C, productCoaction_toProduct]
    · rw [RingHom.comp_apply, RingHom.comp_apply, translationCoaction_X, map_add,
        MvPolynomial.map_C, MvPolynomial.map_X]
      change MvPolynomial.C (torsorHom φ s (MvPolynomial.X i)) + MvPolynomial.X i =
        productCoaction φ (torsorHom φ s (MvPolynomial.X i))
      rw [torsorHom_X, productCoaction_torsorCoord φ s hs]
  exact DFunLike.congr_fun key f

/-- **Every mapping-cone element is in the image of the comparison map.**  The part of `(y, z)`
in the kernel of `coneBeta φ` comes from the resolved cone, by exactness of the mapping cone
sequence, and the rest is an `S`-combination of the fibre coordinates. -/
theorem coneLinear_mem_range (hs : (PicardCriteria.coneBeta φ) ∘ₗ s = LinearMap.id)
    (hobs : PicardCriteria.IsObstructionTheory φ)
    (m : (conormalComplex k (MvPolynomial σ k) I).degreeZero × E.degreeOne) :
    coneLinear φ m ∈ (torsorHom φ s).range := by
  have hsec : ∀ v, PicardCriteria.coneBeta φ (s v) = v := fun v ↦ DFunLike.congr_fun hs v
  have hfib : ∀ v, coneLinear φ (s v) ∈ (torsorHom φ s).range := by
    intro v
    have hle : (⊤ : Submodule (MvPolynomial σ k ⧸ I)
          (conormalComplex k (MvPolynomial σ k) I).degreeOne) ≤
        Submodule.comap ((coneLinear φ).comp s)
          (Subalgebra.toSubmodule (torsorHom φ s).range) := by
      rw [← (tangentBasis k σ I).span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Subalgebra.mem_toSubmodule]
      exact ⟨MvPolynomial.X i, torsorHom_X φ s i⟩
    exact hle Submodule.mem_top
  have hker : PicardCriteria.coneBeta φ (m - s (PicardCriteria.coneBeta φ m)) = 0 := by
    rw [map_sub, hsec, sub_self]
  obtain ⟨x, hx⟩ := (hobs.exact_cone.2 _).mp hker
  have hsplit : coneLinear φ m =
      productMap φ (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeZero x) +
        coneLinear φ (s (PicardCriteria.coneBeta φ m)) := by
    rw [← coneLinear_coneAlpha, ← map_add, hx]
    congr 1
    abel
  rw [hsplit]
  refine Subalgebra.add_mem _ ?_ (hfib _)
  exact ⟨MvPolynomial.C (Ideal.Quotient.mk (ideal φ)
    (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeZero x)), torsorHom_C φ s _⟩

/-- The image of the normal cone lies in the image of the comparison map. -/
theorem tmul_one_mem_range (hs : (PicardCriteria.coneBeta φ) ∘ₗ s = LinearMap.id)
    (hobs : PicardCriteria.IsObstructionTheory φ)
    (g : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) :
    (g ⊗ₜ (1 : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne) : productRing φ) ∈
      (torsorHom φ s).range := by
  have key : ∀ g : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I,
      g ∈ (torsorHom φ s).range.comap
        (Algebra.TensorProduct.includeLeft :
          AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I →ₐ[MvPolynomial σ k ⧸ I]
            productRing φ) := by
    intro g
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨t, rfl⟩ := AffineNormalCone.symToRees_surjective (MvPolynomial σ k) I p
    induction t using SymmetricAlgebra.induction with
    | algebraMap r =>
      have e : (AffineNormalCone.symToRees (MvPolynomial σ k) I) (algebraMap _ _ r) =
          algebraMap _ _ r := AlgHom.commutes _ r
      have e2 : Ideal.Quotient.mk
            (Ideal.map (algebraMap (MvPolynomial σ k) (reesAlgebra I)) I)
            (algebraMap (MvPolynomial σ k) (reesAlgebra I) r) =
          algebraMap (MvPolynomial σ k ⧸ I)
            (AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I)
            (Ideal.Quotient.mk I r) :=
        (IsScalarTower.algebraMap_apply (MvPolynomial σ k) (MvPolynomial σ k ⧸ I) _ r).symm
      rw [e, e2]
      exact Subalgebra.algebraMap_mem _ _
    | ι x =>
      rw [AffineNormalCone.symToRees_ι,
        ← AffineNormalCone.conormalToAssociatedGraded_toCotangent]
      have h := coneLinear_mem_range φ s hs hobs (Ideal.toCotangent I x, 0)
      rw [coneLinear_apply] at h
      simpa using h
    | mul a b ha hb => rw [map_mul, map_mul]; exact Subalgebra.mul_mem _ ha hb
    | add a b ha hb => rw [map_add, map_add]; exact Subalgebra.add_mem _ ha hb
  simpa using key g

/-- The image of the bundle `E₀` lies in the image of the comparison map. -/
theorem one_tmul_mem_range (hs : (PicardCriteria.coneBeta φ) ∘ₗ s = LinearMap.id)
    (hobs : PicardCriteria.IsObstructionTheory φ)
    (p : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne) :
    ((1 : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) ⊗ₜ p : productRing φ) ∈
      (torsorHom φ s).range := by
  have key : ∀ p : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne,
      p ∈ (torsorHom φ s).range.comap
        (Algebra.TensorProduct.includeRight :
          SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne →ₐ[MvPolynomial σ k ⧸ I]
            productRing φ) := by
    intro p
    induction p using SymmetricAlgebra.induction with
    | algebraMap r => exact Subalgebra.algebraMap_mem _ _
    | ι z =>
      have h := coneLinear_mem_range φ s hs hobs (0, z)
      rw [coneLinear_apply] at h
      simp only [map_zero, TensorProduct.zero_tmul, zero_sub] at h
      simpa using neg_mem h
    | mul a b ha hb => exact Subalgebra.mul_mem _ ha hb
    | add a b ha hb => exact Subalgebra.add_mem _ ha hb
  simpa using key p

/-- **The comparison map is surjective.** -/
theorem torsorHom_surjective (hs : (PicardCriteria.coneBeta φ) ∘ₗ s = LinearMap.id)
    (hobs : PicardCriteria.IsObstructionTheory φ) :
    Function.Surjective (torsorHom φ s) := by
  have key : ∀ a : productRing φ, a ∈ (torsorHom φ s).range := by
    intro a
    refine TensorProduct.induction_on a (zero_mem _) (fun g p ↦ ?_) (fun u v hu hv ↦ add_mem hu hv)
    have h : (g ⊗ₜ p : productRing φ) =
        (g ⊗ₜ (1 : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)) *
          ((1 : AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I) ⊗ₜ p) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    exact mul_mem (tmul_one_mem_range φ s hs hobs g) (one_tmul_mem_range φ s hs hobs p)
  intro a
  obtain ⟨f, hf⟩ := key a
  exact ⟨f, hf⟩

/-- If the coefficientwise extension of a ring map to polynomial rings kills a polynomial, then
that polynomial lies in the ideal generated by the kernel. -/
theorem mem_map_C_of_map_eq_zero {B A : Type u} [CommRing B] [CommRing A] (f : B →+* A)
    {τ : Type u} (g : MvPolynomial τ B) (hg : MvPolynomial.map f g = 0) :
    g ∈ (RingHom.ker f).map (MvPolynomial.C : B →+* MvPolynomial τ B) := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff g]
  refine Ideal.sum_mem _ fun m _ ↦ ?_
  have hc : MvPolynomial.coeff m g ∈ RingHom.ker f := by
    have h := congrArg (MvPolynomial.coeff m) hg
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h
  have hm : (MvPolynomial.monomial m (MvPolynomial.coeff m g) : MvPolynomial τ B) =
      MvPolynomial.C (MvPolynomial.coeff m g) * MvPolynomial.monomial m 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc)

/-- **The tangent torsor over the resolved cone is trivial.**  This is
`ResolvedCone.IsPolynomialTrivialisation`, the hypothesis left open in
`VirtualFundamentalClass/ResolvedConeDimension.lean`: the coordinate ring `gr_I(R) ⊗ Sym(E⁰)` of
`C ×_X E₀` is a polynomial ring in `|σ|` variables over the coordinate ring of `C(E)`,
compatibly with the inclusion `toProduct φ`.

The proof splits the mapping-cone surjection `coneBeta φ : L⁻¹ ⊕ E⁰ → L⁰`, uses the splitting to
produce `|σ|` fibre coordinates on `C ×_X E₀` on which the translation coaction acts by the
tangent parameters, checks that the comparison map `ring φ [t_σ] → gr_I(R) ⊗ Sym(E⁰)` is
surjective (exactness of the mapping cone) and equivariant, and concludes that its kernel is
extended from `ring φ` by the invariant ideal lemma — hence trivial, since `toProduct φ` is
injective. -/
theorem isPolynomialTrivialisation (hobs : PicardCriteria.IsObstructionTheory φ) :
    IsPolynomialTrivialisation φ := by
  obtain ⟨s, hs⟩ := exists_rightInverse_coneBeta φ hobs
  have hsurj := torsorHom_surjective φ s hs hobs
  have hinvariant : ∀ g ∈ RingHom.ker
      (torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ),
      translationCoaction (ring φ) σ g ∈
        (RingHom.ker (torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ)).map
          (MvPolynomial.C :
            MvPolynomial σ (ring φ) →+* MvPolynomial σ (MvPolynomial σ (ring φ))) := by
    intro g hg
    refine mem_map_C_of_map_eq_zero _ _ ?_
    rw [map_torsorHom_translationCoaction φ s hs g,
      show torsorHom φ s g = 0 from hg, map_zero]
  have hbot : RingHom.ker (torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ) = ⊥ := by
    have hcomap : (RingHom.ker (torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ)).comap
        (MvPolynomial.C : ring φ →+* MvPolynomial σ (ring φ)) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun a ha ↦ ?_
      have h1 : torsorHom φ s (MvPolynomial.C a) = 0 := ha
      rw [torsorHom_C] at h1
      exact toProduct_injective φ (h1.trans (map_zero (toProduct φ)).symm)
    rw [eq_map_comap_C_of_translationCoaction (ring φ) σ hinvariant, hcomap, Ideal.map_bot]
  have hinj : Function.Injective (torsorHom φ s :
      MvPolynomial σ (ring φ) →+* productRing φ) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hbot
  refine ⟨(RingEquiv.ofBijective
    (torsorHom φ s : MvPolynomial σ (ring φ) →+* productRing φ) ⟨hinj, hsurj⟩).symm, fun a ↦ ?_⟩
  rw [RingEquiv.symm_apply_eq]
  exact (torsorHom_C φ s a).symm

end Torsor

/-! ## Unconditional purity of the resolved cone -/

section Purity

open Order IntersectionTheory

attribute [local instance] specializationOrder

variable {k : Type u} [Field k] {σ : Type u} [Finite σ] {I : Ideal (MvPolynomial σ k)}
variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}
variable [Module.Free (MvPolynomial σ k ⧸ I) E.degreeZero]
variable [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeZero]
variable [Module.Free (MvPolynomial σ k ⧸ I) E.degreeOne]
variable [Module.Finite (MvPolynomial σ k ⧸ I) E.degreeOne]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))

/-- **Purity of the resolved cone, unconditionally on the trivialisation.**  Granting only the
dimension formula for the extended Rees algebra of `I`, every irreducible component of `C(E)`
has dimension `b = rank E⁰`. -/
theorem ringKrullDim_quotient_ring_eq' (hI : I ≠ ⊤)
    (hdf : HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I))
    (hobs : PicardCriteria.IsObstructionTheory φ)
    {q : Ideal (ring φ)} (hq : q ∈ minimalPrimes (ring φ)) :
    ringKrullDim (ring φ ⧸ q) =
      ((Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℕ∞)) :=
  ringKrullDim_quotient_ring_eq φ hI hdf (isPolynomialTrivialisation φ hobs) hq

/-- **Purity in the form used by the Chow groups, unconditionally on the trivialisation.** -/
theorem dimension_eq_of_isMax' (dimC : DimensionFunction (scheme φ)) (hI : I ≠ ⊤)
    (hdf : HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I))
    (hobs : PicardCriteria.IsObstructionTheory φ) (x : ↥(scheme φ)) (hx : IsMax x) :
    dimC x = (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) :=
  dimension_eq_of_isMax φ dimC hI hdf (isPolynomialTrivialisation φ hobs) x hx

/-- The same purity statement on the ambient bundle `E₁`, unconditionally on the
trivialisation. -/
theorem dimension_toBundle_eq_of_isMax' (dimC : DimensionFunction (scheme φ))
    (dimB : DimensionFunction (bundleSpace φ)) (hI : I ≠ ⊤)
    (hdf : HasDimensionFormula (AffineDeformationSpace.extendedRees (MvPolynomial σ k) I))
    (hobs : PicardCriteria.IsObstructionTheory φ) (x : ↥(scheme φ)) (hx : IsMax x) :
    dimB ((toBundle φ).base x) = (Module.finrank (MvPolynomial σ k ⧸ I) E.degreeOne : ℤ) :=
  dimension_toBundle_eq_of_isMax φ dimC dimB hI hdf (isPolynomialTrivialisation φ hobs) x hx

end Purity

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone
