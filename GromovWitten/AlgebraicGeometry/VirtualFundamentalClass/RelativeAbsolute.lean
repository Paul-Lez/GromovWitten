/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Cones.NormalConeAction
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Unconditional

/-!
# From a relative obstruction theory to an absolute one

Let `k` be a commutative ring, let `σ` and `τ` be finite index sets, let
`R = k[x_σ, y_τ] = MvPolynomial (σ ⊕ τ) k`, let `I ⊆ R` be an ideal and let `X = Spec (R ⧸ I)`.
The projection `Spec R → Y = Spec k[y_τ] = 𝔸^τ` makes `X` a closed subscheme of `𝔸^σ × Y`, so
`X → Y` has the *relative* conormal complex `[I/I² → ⊕_σ (R/I)·dx_s]`, in which only the
differentials of the `σ`-coordinates appear.

Behrend–Fantechi's passage from a relative obstruction theory to an absolute one adds the
differentials of the `τ`-coordinates back, both to the complex and to the bundle: a chain map
`φ : E ⟶ [I/I² → ⊕_σ (R/I)·dx_s]` is turned into the chain map
`absHom φ : absComplex φ ⟶ conormalComplex k R I` with
`(absComplex φ)⁰ = E⁰ ⊕ (τ → R/I)`.  The main theorem `ideal_absHom` says that this does not
change the resolved cone: the ideal of `C(absComplex φ)` inside `Sym(E⁻¹)` is the ideal `ideal'`
cut out by the *relative* datum.

## Main definitions

* `sigmaPart I`, `tauPart I`: the `σ`- and `τ`-coordinates of a tangent vector of the ambient
  affine space, and `sigmaLift I`, `tauLift I`, the corresponding coordinate embeddings.
* `relConormalComplex I`: the relative conormal complex `[I/I² → (σ → R/I)]`.
* `absComplex φ`, `absHom φ`: the absolute complex `[E⁻¹ → E⁰ ⊕ (τ → R/I)]` and the chain map to
  the absolute conormal complex attached to a relative datum `φ`.
* `relProductRing φ`, `relProductMap φ`, `ideal' φ`: the resolved-cone data of the relative
  datum, defined by the same formulas as in `VirtualFundamentalClass/ResolvedCone.lean`.
* `compareMap φ`: the algebra map `relProductRing φ → ResolvedCone.productRing (absHom φ)` built
  from the tangent coaction of `Cones/NormalConeAction.lean` in the `τ`-directions, and its
  retraction `compareRetraction φ`.
* `relConeCycle φ dimE d`, `relativeVirtualClass φ …`: the cycle of the relative resolved cone
  and the relative virtual class.

## Main results

* `sigmaLift_sigmaPart_add_tauLift_tauPart`: the decomposition of a tangent vector into its
  `σ`- and `τ`-parts.
* `sigmaPart_conormalMap_toCotangent`, `tauPart_conormalMap_toCotangent`: the coordinates of the
  conormal map are the partial derivatives.
* `compareMap_injective`, `productMap_absHom`: the comparison map is injective and identifies the
  coordinate-ring map of the absolute datum with that of the relative datum.
* `ideal_absHom : ResolvedCone.ideal (absHom φ) = ideal' φ`: **the main theorem**.
* `resolvedConeCycleAt_absHom`, `virtualClassAt_absHom`: the cycle-level and Chow-level
  consequences, the latter stating that the virtual class of the absolute obstruction theory is
  the relative virtual class, and `virtualDimension_absHom`, the shift of the virtual dimension
  by `#τ = dim Y`.
-/

universe u

-- The coordinate ring of `C ×_X E₀` is a tensor product whose left factor is a quotient of a
-- Rees algebra; synthesising `CommRing` for it, and for the tensor product itself, needs one
-- more level of pending instance problems than the default.
set_option maxSynthPendingDepth 5

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute

open scoped TensorProduct
open NormalConeAction ConeQuotient NormalSheafPicard
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {k : Type u} [CommRing k] {σ τ : Type u}

/-! ## The coordinates of a tangent vector -/

variable (I : Ideal (MvPolynomial (σ ⊕ τ) k))

/-- The `σ`-coordinates of a tangent vector of the ambient affine space `𝔸^{σ ⊔ τ}`, in the
basis of coordinate differentials. -/
noncomputable def sigmaPart : Tangent I →ₗ[Base I] (σ → Base I) :=
  LinearMap.pi fun s ↦ (tangentBasis I).coord (Sum.inl s)

/-- The `τ`-coordinates of a tangent vector of the ambient affine space `𝔸^{σ ⊔ τ}`, in the
basis of coordinate differentials. -/
noncomputable def tauPart : Tangent I →ₗ[Base I] (τ → Base I) :=
  LinearMap.pi fun t ↦ (tangentBasis I).coord (Sum.inr t)

@[simp]
theorem sigmaPart_apply (w : Tangent I) (s : σ) :
    sigmaPart I w s = (tangentBasis I).repr w (Sum.inl s) := rfl

@[simp]
theorem tauPart_apply (w : Tangent I) (t : τ) :
    tauPart I w t = (tangentBasis I).repr w (Sum.inr t) := rfl

/-- The `σ`-coordinates of the conormal class of `x ∈ I` are its partial derivatives in the
`σ`-directions. -/
theorem sigmaPart_conormalMap_toCotangent (x : I) (s : σ) :
    sigmaPart I (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I
        (Ideal.toCotangent I x)) s =
      Ideal.Quotient.mk I (MvPolynomial.pderiv (Sum.inl s) (x : MvPolynomial (σ ⊕ τ) k)) := by
  rw [sigmaPart_apply, AffineNormalCone.conormalMap_toCotangent]
  simp only [tangentBasis, Module.Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_apply]
  rw [Algebra.smul_def, mul_one]
  rfl

/-- The `τ`-coordinates of the conormal class of `x ∈ I` are its partial derivatives in the
`τ`-directions. -/
theorem tauPart_conormalMap_toCotangent (x : I) (t : τ) :
    tauPart I (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I
        (Ideal.toCotangent I x)) t =
      Ideal.Quotient.mk I (MvPolynomial.pderiv (Sum.inr t) (x : MvPolynomial (σ ⊕ τ) k)) := by
  rw [tauPart_apply, AffineNormalCone.conormalMap_toCotangent]
  simp only [tangentBasis, Module.Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_apply]
  rw [Algebra.smul_def, mul_one]
  rfl

section SigmaLift

variable [Fintype σ]

/-- The tangent vector with prescribed `σ`-coordinates and vanishing `τ`-coordinates. -/
noncomputable def sigmaLift : (σ → Base I) →ₗ[Base I] Tangent I :=
  Fintype.linearCombination (Base I) fun s ↦ tangentBasis I (Sum.inl s)

theorem sigmaLift_apply (f : σ → Base I) :
    sigmaLift I f = ∑ s : σ, f s • tangentBasis I (Sum.inl s) := rfl

end SigmaLift

section TauLift

variable [Fintype τ]

/-- The tangent vector with prescribed `τ`-coordinates and vanishing `σ`-coordinates. -/
noncomputable def tauLift : (τ → Base I) →ₗ[Base I] Tangent I :=
  Fintype.linearCombination (Base I) fun t ↦ tangentBasis I (Sum.inr t)

theorem tauLift_apply (f : τ → Base I) :
    tauLift I f = ∑ t : τ, f t • tangentBasis I (Sum.inr t) := rfl

end TauLift

/-! ## The relative conormal complex and the absolute complex -/

/-- **The relative conormal complex** of `X = Spec (R ⧸ I) ⊆ 𝔸^σ × 𝔸^τ` over `𝔸^τ`: the
conormal module in degree zero and the relative differentials `⊕_σ (R/I)·dx_s` in degree one. -/
noncomputable abbrev relConormalComplex : LinearTwoTermComplex (Base I) :=
  dualComplexOf ((sigmaPart I).comp
    (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I))

variable [Fintype σ] [Fintype τ]

/-- **The decomposition of a tangent vector** of `𝔸^{σ ⊔ τ}` into its `σ`- and `τ`-parts. -/
theorem sigmaLift_sigmaPart_add_tauLift_tauPart (w : Tangent I) :
    sigmaLift I (sigmaPart I w) + tauLift I (tauPart I w) = w := by
  have h := (tangentBasis I).sum_repr w
  rw [Fintype.sum_sum_type] at h
  exact h

variable {I}
variable {E : LinearTwoTermComplex (Base I)}

/-- **The absolute complex** attached to a relative obstruction datum `φ : E ⟶ L_{X/Y}`: the
degree-zero term is unchanged and the degree-one term acquires the `τ`-directions. -/
noncomputable abbrev absComplex (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    LinearTwoTermComplex (Base I) where
  degreeZero := E.degreeZero
  degreeOne := E.degreeOne × (τ → Base I)
  differential := E.differential.prod ((tauPart I).comp
    ((AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I).comp φ.degreeZero))

/-- The degree-one part of the absolute chain map: the `σ`-coordinates are those of the relative
chain map and the `τ`-coordinates are the new ones. -/
noncomputable def absHomOne (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    (absComplex φ).degreeOne →ₗ[Base I] (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I).degreeOne :=
  (sigmaLift I).comp (φ.degreeOne.comp (LinearMap.fst (Base I) E.degreeOne (τ → Base I))) +
    (tauLift I).comp (LinearMap.snd (Base I) E.degreeOne (τ → Base I))

@[simp]
theorem absHomOne_apply (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))
    (u : E.degreeOne) (w : τ → Base I) :
    absHomOne φ (u, w) = sigmaLift I (φ.degreeOne u) + tauLift I w := rfl

/-- **The absolute obstruction datum** attached to a relative one. -/
noncomputable def absHom (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    LinearTwoTermComplex.Hom (absComplex φ) (conormalComplex k (MvPolynomial (σ ⊕ τ) k) I) where
  degreeZero := φ.degreeZero
  degreeOne := absHomOne φ
  comm x := by
    have h : φ.degreeOne (E.differential x) =
        sigmaPart I (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I
          (φ.degreeZero x)) := φ.comm x
    have hx : absHomOne φ ((absComplex φ).differential x) =
        sigmaLift I (φ.degreeOne (E.differential x)) +
          tauLift I (tauPart I (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I
            (φ.degreeZero x))) := rfl
    rw [hx, h, sigmaLift_sigmaPart_add_tauLift_tauPart]

@[simp]
theorem absHom_degreeZero (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    (absHom φ).degreeZero = φ.degreeZero := rfl

@[simp]
theorem absHom_degreeOne (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    (absHom φ).degreeOne = absHomOne φ := rfl

/-! ## The resolved cone of the relative datum -/

open ConeTranslation (Gr)

/-- The coordinate ring `gr_I(R) ⊗_{R/I} Sym(E⁰)` of the product `C ×_X E₀` attached to a
relative obstruction datum: the same ring as for the absolute datum, but with the *relative*
degree-one term `E⁰`. -/
abbrev relProductRing (_φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) : Type u :=
  Gr I ⊗[Base I] SymmetricAlgebra (Base I) E.degreeOne

/-- The linear map classifying the morphism `C ×_X E₀ → E₁` of the relative datum: a generator
`x` of `E⁻¹` goes to `γ(φ⁻¹(x)) ⊗ 1 + 1 ⊗ ι(d x)`. -/
noncomputable def relProductLinear (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    E.degreeZero →ₗ[Base I] relProductRing φ :=
  ((TensorProduct.mk (Base I) (Gr I) (SymmetricAlgebra (Base I) E.degreeOne)).flip 1).comp
      ((AffineNormalCone.conormalToAssociatedGraded (MvPolynomial (σ ⊕ τ) k) I).comp
        φ.degreeZero) +
    (TensorProduct.mk (Base I) (Gr I) (SymmetricAlgebra (Base I) E.degreeOne) 1).comp
      ((SymmetricAlgebra.ι (Base I) E.degreeOne).comp E.differential)

/-- The coordinate-ring map of `C ×_X E₀ → E₁` for the relative datum. -/
noncomputable def relProductMap (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    SymmetricAlgebra (Base I) E.degreeZero →ₐ[Base I] relProductRing φ :=
  SymmetricAlgebra.lift (relProductLinear φ)

omit [Fintype σ] [Fintype τ] in
@[simp]
theorem relProductMap_ι (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))
    (x : E.degreeZero) :
    relProductMap φ (SymmetricAlgebra.ι (Base I) E.degreeZero x) =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial (σ ⊕ τ) k) I (φ.degreeZero x)
          ⊗ₜ[Base I] 1 +
        1 ⊗ₜ[Base I] SymmetricAlgebra.ι (Base I) E.degreeOne (E.differential x) := by
  rw [relProductMap, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- **The ideal of the resolved cone of the relative datum** inside `Sym(E⁻¹)`. -/
noncomputable def ideal' (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    Ideal (SymmetricAlgebra (Base I) E.degreeZero) :=
  RingHom.ker (relProductMap φ)

omit [Fintype σ] [Fintype τ] in
theorem mem_ideal'_iff {φ : LinearTwoTermComplex.Hom E (relConormalComplex I)}
    {a : SymmetricAlgebra (Base I) E.degreeZero} : a ∈ ideal' φ ↔ relProductMap φ a = 0 :=
  Iff.rfl

/-! ## The comparison map -/

/-- The `τ`-part of a tangent vector, viewed as a linear form on the absolute bundle
`E₀ × 𝔸^τ`. -/
noncomputable def tauTangent (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    Tangent I →ₗ[Base I] ResolvedCone.productRing (absHom φ) :=
  (TensorProduct.mk (Base I) (Gr I)
        (SymmetricAlgebra (Base I) (E.degreeOne × (τ → Base I))) 1).comp
    ((SymmetricAlgebra.ι (Base I) (E.degreeOne × (τ → Base I))).comp
      ((LinearMap.inr (Base I) E.degreeOne (τ → Base I)).comp (tauPart I)))

@[simp]
theorem tauTangent_apply (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))
    (w : Tangent I) :
    tauTangent φ w = 1 ⊗ₜ[Base I]
      SymmetricAlgebra.ι (Base I) (E.degreeOne × (τ → Base I)) (0, tauPart I w) := rfl

/-- **The comparison map** from the coordinate ring of `C ×_X E₀` for the relative datum to the
one for the absolute datum: on the normal-cone factor it is the tangent coaction translated by
the tautological `τ`-directions, and on the bundle factor it is the inclusion `E₀ ↪ E₀ × 𝔸^τ`. -/
noncomputable def compareMap (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    relProductRing φ →ₐ[Base I] ResolvedCone.productRing (absHom φ) :=
  Algebra.TensorProduct.lift
    (ConeQuotient.translate (act I) Algebra.TensorProduct.includeLeft (tauTangent φ))
    (Algebra.TensorProduct.includeRight.comp
      (symMap (LinearMap.inl (Base I) E.degreeOne (τ → Base I))))
    fun _ _ ↦ Commute.all _ _

/-- The retraction of the comparison map: it sets the `τ`-directions to zero. -/
noncomputable def compareRetraction (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    ResolvedCone.productRing (absHom φ) →ₐ[Base I] relProductRing φ :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.comp
      (symMap (LinearMap.fst (Base I) E.degreeOne (τ → Base I))))
    fun _ _ ↦ Commute.all _ _

theorem compareRetraction_tauTangent (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    (compareRetraction φ).toLinearMap.comp (tauTangent φ) = 0 := by
  refine LinearMap.ext fun w ↦ ?_
  change compareRetraction φ (1 ⊗ₜ[Base I] SymmetricAlgebra.ι (Base I) _ (0, tauPart I w)) = 0
  rw [compareRetraction, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply,
    symMap_ι]
  change Algebra.TensorProduct.includeRight
    (SymmetricAlgebra.ι (Base I) E.degreeOne (0 : E.degreeOne)) = 0
  rw [map_zero, map_zero]

/-- The retraction really is a retraction: the comparison map is a section of it. -/
theorem compareRetraction_comp_compareMap
    (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    (compareRetraction φ).comp (compareMap φ) = AlgHom.id (Base I) (relProductRing φ) := by
  have hincl : (compareRetraction φ).comp
      (Algebra.TensorProduct.includeLeft : Gr I →ₐ[Base I] _) =
      Algebra.TensorProduct.includeLeft :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hleft : (compareRetraction φ).comp
      (ConeQuotient.translate (act I) Algebra.TensorProduct.includeLeft (tauTangent φ)) =
      Algebra.TensorProduct.includeLeft := by
    rw [ConeQuotient.comp_translate, hincl, compareRetraction_tauTangent]
    exact act_zero _
  have hsym : (symMap (LinearMap.fst (Base I) E.degreeOne (τ → Base I))).comp
      (symMap (LinearMap.inl (Base I) E.degreeOne (τ → Base I))) =
      AlgHom.id (Base I) (SymmetricAlgebra (Base I) E.degreeOne) :=
    GradedCone.symMap_comp_symMap_of_comp_eq_id (Base I) E.degreeOne
      (LinearMap.fst_comp_inl _ _ _)
  refine Algebra.TensorProduct.ext' fun g s ↦ ?_
  have h1 : compareRetraction φ
      (ConeQuotient.translate (act I) Algebra.TensorProduct.includeLeft (tauTangent φ) g) =
      g ⊗ₜ[Base I] 1 := AlgHom.congr_fun hleft g
  have hs : symMap (LinearMap.fst (Base I) E.degreeOne (τ → Base I))
      (symMap (LinearMap.inl (Base I) E.degreeOne (τ → Base I)) s) = s :=
    AlgHom.congr_fun hsym s
  have h2 : compareRetraction φ ((Algebra.TensorProduct.includeRight.comp
      (symMap (LinearMap.inl (Base I) E.degreeOne (τ → Base I)))) s) = 1 ⊗ₜ[Base I] s := by
    change compareRetraction φ
      (1 ⊗ₜ[Base I] symMap (LinearMap.inl (Base I) E.degreeOne (τ → Base I)) s) = _
    rw [compareRetraction, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply,
      hs]
    rfl
  rw [AlgHom.comp_apply, compareMap, Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.id_apply,
    h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **The comparison map is injective.** -/
theorem compareMap_injective (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    Function.Injective (compareMap φ) := by
  have h : Function.LeftInverse (compareRetraction φ) (compareMap φ) := fun z ↦
    AlgHom.congr_fun (compareRetraction_comp_compareMap φ) z
  exact h.injective

/-! ## The ideal of the resolved cone of the absolute datum -/

omit [Fintype σ] [Fintype τ] in
/-- **The tangent coaction on a conormal class.**  Translating the degree-one class `γ(m)` of
`m ∈ I/I²` by a tangent vector adds the value of the conormal map on `m`.  This is
`NormalConeAction.map_comp_bundleTranslationCoaction` read on a generator. -/
theorem act_conormalToAssociatedGraded (m : I.Cotangent) :
    act I (AffineNormalCone.conormalToAssociatedGraded (MvPolynomial (σ ⊕ τ) k) I m) =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial (σ ⊕ τ) k) I m ⊗ₜ[Base I] 1 +
        (1 : Gr I) ⊗ₜ[Base I] SymmetricAlgebra.ι (Base I) (Tangent I)
          (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I m) := by
  have h := AlgHom.congr_fun (map_comp_bundleTranslationCoaction I)
    (SymmetricAlgebra.ι (Base I) I.Cotangent m)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, bundleTranslationCoaction_ι, map_add,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, nsToGrAlg_ι] at h
  simp only [symMap_id, AlgHom.id_apply, map_one] at h
  exact h.symm

theorem compareMap_tmul_one (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) (g : Gr I) :
    compareMap φ (g ⊗ₜ[Base I] 1) =
      ConeQuotient.translate (act I) Algebra.TensorProduct.includeLeft (tauTangent φ) g := by
  rw [compareMap, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

theorem compareMap_one_tmul (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))
    (s : SymmetricAlgebra (Base I) E.degreeOne) :
    compareMap φ (1 ⊗ₜ[Base I] s) =
      1 ⊗ₜ[Base I] symMap (LinearMap.inl (Base I) E.degreeOne (τ → Base I)) s := by
  rw [compareMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- **The comparison map on a conormal class**: the tangent coaction contributes exactly the
`τ`-coordinates of the conormal map. -/
theorem compareMap_conormal (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))
    (m : I.Cotangent) :
    compareMap φ
        (AffineNormalCone.conormalToAssociatedGraded (MvPolynomial (σ ⊕ τ) k) I m ⊗ₜ[Base I] 1) =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial (σ ⊕ τ) k) I m ⊗ₜ[Base I] 1 +
        1 ⊗ₜ[Base I] SymmetricAlgebra.ι (Base I) (E.degreeOne × (τ → Base I))
          (0, tauPart I (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I m)) := by
  rw [compareMap_tmul_one, ConeQuotient.translate, AlgHom.comp_apply,
    act_conormalToAssociatedGraded, map_add, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul, map_one, map_one, mul_one, one_mul,
    SymmetricAlgebra.lift_ι_apply, tauTangent_apply]
  rfl

/-- **The coordinate-ring map of the absolute datum factors through that of the relative one.** -/
theorem productMap_absHom (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    ResolvedCone.productMap (absHom φ) = (compareMap φ).comp (relProductMap φ) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
  have hpair : ((0 : E.degreeOne),
        tauPart I (AffineNormalCone.conormalMap k (MvPolynomial (σ ⊕ τ) k) I
          (φ.degreeZero x))) +
      LinearMap.inl (Base I) E.degreeOne (τ → Base I) (E.differential x) =
      (absComplex φ).differential x := by
    rw [LinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have hx : ResolvedCone.productMap (absHom φ) (SymmetricAlgebra.ι (Base I) E.degreeZero x) =
      ((compareMap φ).comp (relProductMap φ)) (SymmetricAlgebra.ι (Base I) E.degreeZero x) := by
    rw [ResolvedCone.productMap_ι, AlgHom.comp_apply, relProductMap_ι, map_add,
      compareMap_conormal, compareMap_one_tmul, symMap_ι, add_assoc, ← TensorProduct.tmul_add,
      ← map_add, hpair]
    rfl
  exact hx

/-- **The main theorem: passing from a relative obstruction theory to an absolute one does not
change the resolved cone.**  The ideal of the resolved cone of the absolute datum `absHom φ`
inside `Sym(E⁻¹)` is the ideal cut out by the relative datum `φ`. -/
theorem ideal_absHom (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    ResolvedCone.ideal (absHom φ) = ideal' φ := by
  refine Ideal.ext fun a ↦ ?_
  rw [ResolvedCone.mem_ideal_iff, mem_ideal'_iff, productMap_absHom, AlgHom.comp_apply]
  exact map_eq_zero_iff _ (compareMap_injective φ)

/-! ## The cycle and the virtual class of the absolute datum -/

section Cycle

open IntersectionTheory

variable [IsNoetherianRing k]
variable [Module.Free (Base I) E.degreeZero] [Module.Finite (Base I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (relConormalComplex I))

/-- **The cycle of the resolved cone of the relative datum** inside the bundle `E₁`, in the
degree `d`. -/
noncomputable def relConeCycle
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ))) (d : ℤ) :
    cyclesOfDimension (ResolvedCone.bundleSpace (absHom φ)) dimE d :=
  HomotopyInvariance.quotientCycle (ideal' φ) dimE d

/-- **The resolved-cone cycle of the absolute datum is the cycle of the relative datum.** -/
theorem resolvedConeCycleAt_absHom
    (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ))) (d : ℤ) :
    VirtualClass.resolvedConeCycleAt (absHom φ) dimE d = relConeCycle φ dimE d := by
  rw [HomotopyInvariance.resolvedConeCycleAt_eq_quotientCycle]
  exact HomotopyInvariance.quotientCycle_congr (ideal_absHom φ) dimE d

variable {ι : Type u} [Finite ι]
variable (e : ResolvedCone.bundleRing (absHom φ) ≃ₐ[Base I] MvPolynomial ι (Base I))
variable (dimX : DimensionFunction (_root_.AlgebraicGeometry.Spec (CommRingCat.of (Base I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace (absHom φ))) (i : ℤ)
variable (RX : RationalEquivalenceSystem
  (_root_.AlgebraicGeometry.Spec (CommRingCat.of (Base I))) dimX i)
variable (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace (absHom φ)) dimE
  (i + (Nat.card ι : ℤ)))

/-- **The relative virtual class** of a relative obstruction datum: the Gysin image of the class
of the resolved cone of the relative datum. -/
noncomputable def relativeVirtualClass
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (absHom φ)) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    RX.ChowGroup :=
  VectorBundle.zeroSectionGysin' e dimX dimE i RX RE hhom hinj
    (RE.quotientMap (relConeCycle φ dimE (i + (Nat.card ι : ℤ))))

/-- **The virtual class of the absolute obstruction theory is the relative virtual class.**
This is the affine model of Behrend–Fantechi's comparison of the virtual classes of a relative
and of the associated absolute obstruction theory. -/
theorem virtualClassAt_absHom
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (absHom φ)) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    VirtualClass.virtualClassAt (absHom φ) e dimX dimE i RX RE hhom hinj =
      relativeVirtualClass φ e dimX dimE i RX RE hhom hinj := by
  have h : VirtualClass.resolvedConeClassAt (absHom φ) dimE i RE =
      RE.quotientMap (relConeCycle φ dimE (i + (Nat.card ι : ℤ))) :=
    congrArg RE.quotientMap (resolvedConeCycleAt_absHom φ dimE (i + (Nat.card ι : ℤ)))
  exact congrArg _ h

end Cycle

/-- **The virtual dimension of the absolute obstruction theory** exceeds the relative one by the
dimension `#τ` of the base `Y = 𝔸^τ`. -/
theorem virtualDimension_absHom [Nontrivial (Base I)] [Module.Free (Base I) E.degreeOne]
    [Module.Finite (Base I) E.degreeOne]
    (φ : LinearTwoTermComplex.Hom E (relConormalComplex I)) :
    VirtualClass.virtualDimension (absHom φ) =
      ((Module.finrank (Base I) E.degreeOne : ℤ) -
        (Module.finrank (Base I) E.degreeZero : ℤ)) + (Nat.card τ : ℤ) := by
  have h : VirtualClass.virtualDimension (absHom φ) =
      (Module.finrank (Base I) (E.degreeOne × (τ → Base I)) : ℤ) -
        (Module.finrank (Base I) E.degreeZero : ℤ) := rfl
  rw [h, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  push_cast
  ring

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeAbsolute
