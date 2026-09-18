/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.ConeTranslation
import GromovWitten.AlgebraicGeometry.Cones.NormalConeRegular
import GromovWitten.AlgebraicGeometry.Cones.Products
import GromovWitten.AlgebraicGeometry.ObstructionTheory.AffineObstructionCone
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The tangent action on the affine normal cone as a cone action

`Cones/ConeTranslation.lean` constructs, in the polynomial model `M = 𝔸^σ_A = Spec R` with
`R = A[x_i]`, the coaction

`ConeTranslation.coaction : gr_I(R) →ₐ[R] gr_I(R)[ε_σ]`, `[f t] ↦ [f t] + Σ_i ε_i [∂_i f]`

of the translation action of `T_M|_U = U × 𝔸^σ` on the affine normal cone
`C_{U/M} = Spec gr_I(R)`, together with its unit and additivity laws on points
(`translatePoint_zero`, `translatePoint_add`) and its compatibility with the surjection
`Sym(I/I²) ↠ gr_I(R)`.  That coaction is written in the *polynomial* model and over the
*ambient* ring `R`, so it is not directly a `ConeQuotient.ConeAction`.

This file performs the two translations that are needed and packages the result.

## The bridge

The restricted tangent bundle is `T = Spec Sym_{R/I}(F)` with `F = (R/I) ⊗_R Ω[R⁄A]`, which is
exactly the bundle of `AffineNormalCone.normalSheafTangentAction`.  Since `R = A[x_i]`, the
module `Ω[R⁄A]` is free on the coordinate differentials, so `F` is free on
`NormalConeAction.tangentBasis`, and therefore

* `NormalConeAction.symEquiv : Sym_{R/I}(F) ≃ₐ[R/I] (R/I)[ε_σ]`
  (`SymmetricAlgebra.equivMvPolynomial`), and
* `NormalConeAction.tensorEquiv : gr_I(R) ⊗_{R/I} Sym_{R/I}(F) ≃ₐ[R/I] gr_I(R)[ε_σ]`
  (`MvPolynomial.algebraTensorAlgEquiv`).

Under `tensorEquiv`, `ConeTranslation.coaction` becomes an honest coaction
`NormalConeAction.act : gr_I(R) →ₐ[R/I] gr_I(R) ⊗_{R/I} Sym_{R/I}(F)`.

## Main results

* `NormalConeAction.normalConeAction : ConeQuotient.ConeAction (R/I) (gr_I(R)) F`: the tangent
  action on the affine normal cone, with all four `ConeAction` hypotheses proved.  The
  `𝔸¹`-contraction is `GradedCone.normalConeCoactionQuot` and the unit and associativity laws are
  `ConeTranslation.translatePoint_zero` and `translatePoint_add`, transported by
  `NormalConeAction.translate_act`.
* `NormalConeAction.map_comp_bundleTranslationCoaction` and
  `NormalConeAction.isEquivariant_nsToGrAlg`: the closed immersion `C_{U/M} ↪ N_{U/M}` is
  equivariant, i.e. `Sym(I/I²) ↠ gr_I(R)` intertwines the translation action of `T` on the
  normal sheaf with the action above.  This is the cone-action form of Vistoli's lemma, and it is
  what makes the quotient `[C_{U/M}/T_M|_U]` a closed substack of the intrinsic normal sheaf
  `[N_{U/M}/T_M|_U]`.  Its mathematical content is
  `NormalConeAction.tangentToPoly_conormalMap`: the conormal map `I/I² → (R/I) ⊗ Ω` is the Taylor
  derivation `f ↦ Σ_i ε_i ∂_i f` of `Cones/ConeTranslation.lean`.
* `NormalConeAction.normalConeObstructionCone`: the obstruction cone of `C_{U/M}` inside
  `h¹/h⁰(Eᵛ)` for an obstruction theory on the conormal complex, fully faithful and injective on
  isomorphism classes (`normalConeObstructionConeFullyFaithful`,
  `normalConeObstructionCone_injective_isoClass`), and its version
  `presentationNormalConeObstructionCone` for an obstruction theory on the two-term cotangent
  complex of the presentation `R → R/I`.
* `NormalConeAction.isEquivalence_quotientFunctor_of_bijective`: if the canonical map
  `Sym(I/I²) → gr_I(R)` is bijective — the lci case, provided by `Cones/RegularSequence.lean` —
  then `[C/T](B) ≌ [N/T](B)` for every test algebra: the intrinsic normal cone equals the
  intrinsic normal sheaf.
* `NormalConeAction.nonempty_hom_of_subsingleton` and
  `NormalConeAction.autEquivTangent_of_subsingleton`: when `I/I² = 0`, in particular for `I = ⊥`
  (the smooth case `U = M`), the cone is the zero cone and `[C/T](B)` is the classifying groupoid
  of `T_M(B)`: it has exactly one isomorphism class and the automorphism group of every object is
  `T_M(B) = Hom_{R/I}(F, B)`.

Nothing is assumed: all four `ConeAction` fields are theorems about the coaction constructed in
`Cones/ConeTranslation.lean`.
-/

open CategoryTheory TensorProduct

namespace GromovWitten.AlgebraicGeometry

namespace NormalConeAction

universe u

open ConeTranslation ConeQuotient GradedCone AffineNormalCone

variable {A : Type u} [CommRing A] {σ : Type u} (I : Ideal (MvPolynomial σ A))

/-- The base ring `R/I` of the affine normal cone, for `R = A[x_i]`. -/
abbrev Base : Type u := MvPolynomial σ A ⧸ I

/-- The module of the restricted tangent bundle `T_M|_U`, namely `(R/I) ⊗_R Ω[R⁄A]`.  This is
literally the bundle of `AffineNormalCone.normalSheafTangentAction`. -/
abbrev Tangent : Type u :=
  (MvPolynomial σ A ⧸ I) ⊗[MvPolynomial σ A] Ω[MvPolynomial σ A⁄A]

/-- **The coordinate differentials form a basis of the restricted tangent bundle.**  Over the
polynomial ring `R = A[x_i]` the module `Ω[R⁄A]` is free on `dx_i`, and freeness is preserved by
base change to `R/I`. -/
noncomputable def tangentBasis : Module.Basis σ (Base I) (Tangent I) :=
  (KaehlerDifferential.mvPolynomialBasis A σ).baseChange (MvPolynomial σ A ⧸ I)

@[simp]
theorem tangentBasis_apply (i : σ) :
    tangentBasis I i =
      (1 : Base I) ⊗ₜ[MvPolynomial σ A]
        KaehlerDifferential.D A (MvPolynomial σ A) (MvPolynomial.X i) := by
  change Module.Basis.baseChange _ (KaehlerDifferential.mvPolynomialBasis A σ) i = _
  rw [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]

/-- **The symmetric algebra of the restricted tangent bundle is a polynomial algebra.** -/
noncomputable def symEquiv :
    SymmetricAlgebra (Base I) (Tangent I) ≃ₐ[Base I] MvPolynomial σ (Base I) :=
  SymmetricAlgebra.equivMvPolynomial (tangentBasis I)

@[simp]
theorem symEquiv_ι (i : σ) :
    symEquiv I (SymmetricAlgebra.ι (Base I) (Tangent I) (tangentBasis I i)) =
      MvPolynomial.X i :=
  SymmetricAlgebra.equivMvPolynomial_ι_apply _ i

/-- **The coordinate algebra of `C_{U/M} ×_U T_M|_U` is `gr_I(R)[ε_σ]`.** -/
noncomputable def tensorEquiv :
    Gr I ⊗[Base I] SymmetricAlgebra (Base I) (Tangent I) ≃ₐ[Base I] MvPolynomial σ (Gr I) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Gr I ≃ₐ[Base I] Gr I) (symEquiv I)).trans
    (AlgEquiv.restrictScalars (Base I)
      (MvPolynomial.algebraTensorAlgEquiv (σ := σ) (Base I) (Gr I)))

/-- The comparison is the composite of the two bridging isomorphisms. -/
theorem tensorEquiv_apply (x : Gr I ⊗[Base I] SymmetricAlgebra (Base I) (Tangent I)) :
    tensorEquiv I x =
      MvPolynomial.algebraTensorAlgEquiv (σ := σ) (Base I) (Gr I)
        (Algebra.TensorProduct.congr (AlgEquiv.refl : Gr I ≃ₐ[Base I] Gr I) (symEquiv I) x) :=
  rfl

theorem tensorEquiv_tmul (g : Gr I) (s : SymmetricAlgebra (Base I) (Tangent I)) :
    tensorEquiv I (g ⊗ₜ[Base I] s) =
      g • MvPolynomial.map (algebraMap (Base I) (Gr I)) (symEquiv I s) := by
  rw [tensorEquiv_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  rfl

@[simp]
theorem tensorEquiv_left (g : Gr I) :
    tensorEquiv I (g ⊗ₜ[Base I] 1) = MvPolynomial.C g := by
  rw [tensorEquiv_tmul, map_one, map_one, MvPolynomial.smul_eq_C_mul, mul_one]

@[simp]
theorem tensorEquiv_right (i : σ) :
    tensorEquiv I ((1 : Gr I) ⊗ₜ[Base I]
        SymmetricAlgebra.ι (Base I) (Tangent I) (tangentBasis I i)) = MvPolynomial.X i := by
  rw [tensorEquiv_tmul, symEquiv_ι, MvPolynomial.map_X, one_smul]

/-! ## The coaction over the base `R/I` -/

/-- The tangent coaction of `Cones/ConeTranslation.lean`, read as a map of `R/I`-algebras.  The
underlying ring map is unchanged; only the base of the algebra structure is the degree-zero part
`R/I` of `gr_I(R)` rather than the ambient ring `R`. -/
noncomputable def coactionQ : Gr I →ₐ[Base I] MvPolynomial σ (Gr I) where
  toRingHom := (coaction I).toRingHom
  commutes' r := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hr : algebraMap (Base I) (Gr I) (Ideal.Quotient.mk I r) =
        algebraMap (MvPolynomial σ A) (Gr I) r :=
      (IsScalarTower.algebraMap_apply (MvPolynomial σ A) (Base I) (Gr I) r).symm
    have hp : algebraMap (Base I) (MvPolynomial σ (Gr I)) (Ideal.Quotient.mk I r) =
        MvPolynomial.C (algebraMap (MvPolynomial σ A) (Gr I) r) := by
      rw [MvPolynomial.algebraMap_apply, hr]
    change coaction I _ = _
    rw [hr, hp, coaction_algebraMap]

@[simp]
theorem coactionQ_apply (z : Gr I) : coactionQ I z = coaction I z := rfl

/-- **The tangent translation coaction of the affine normal cone.**  Under the identification
`gr_I(R) ⊗_{R/I} Sym(F) ≅ gr_I(R)[ε_σ]` it is the coaction `[f t] ↦ [f t] + Σ_i ε_i [∂_i f]` of
`Cones/ConeTranslation.lean`. -/
noncomputable def act :
    Gr I →ₐ[Base I] Gr I ⊗[Base I] SymmetricAlgebra (Base I) (Tangent I) :=
  ((tensorEquiv I).symm : _ →ₐ[Base I] _).comp (coactionQ I)

@[simp]
theorem tensorEquiv_act (z : Gr I) : tensorEquiv I (act I z) = coaction I z := by
  change tensorEquiv I ((tensorEquiv I).symm (coactionQ I z)) = _
  rw [AlgEquiv.apply_symm_apply, coactionQ_apply]

/-! ## The action on points -/

section Points

variable {I}
variable {B : Type u} [CommRing B] [Algebra (Base I) B]

/-- Composing the universal map out of `gr_I(R) ⊗ Sym(F)` with the comparison isomorphism gives
evaluation of the tangent coordinates at the vector `i ↦ l (dx_i)`. -/
theorem liftComp_tensorEquiv_symm (φ : Gr I →ₐ[Base I] B) (l : Tangent I →ₗ[Base I] B) :
    (Algebra.TensorProduct.lift φ (SymmetricAlgebra.lift l)
        (fun _ _ => Commute.all _ _)).toRingHom.comp
        ((tensorEquiv I).symm : _ →ₐ[Base I] _).toRingHom =
      MvPolynomial.eval₂Hom (φ : Gr I →+* B) (fun i => l (tangentBasis I i)) := by
  refine MvPolynomial.ringHom_ext (fun g => ?_) fun i => ?_
  · have hg : (tensorEquiv I).symm (MvPolynomial.C g) = g ⊗ₜ[Base I] 1 := by
      rw [AlgEquiv.symm_apply_eq, tensorEquiv_left]
    change Algebra.TensorProduct.lift φ (SymmetricAlgebra.lift l)
      (fun _ _ => Commute.all _ _) ((tensorEquiv I).symm (MvPolynomial.C g)) = _
    rw [hg, Algebra.TensorProduct.lift_tmul, map_one, mul_one, MvPolynomial.eval₂Hom_C]
    rfl
  · have hi : (tensorEquiv I).symm (MvPolynomial.X i) =
        (1 : Gr I) ⊗ₜ[Base I] SymmetricAlgebra.ι (Base I) (Tangent I) (tangentBasis I i) := by
      rw [AlgEquiv.symm_apply_eq, tensorEquiv_right]
    change Algebra.TensorProduct.lift φ (SymmetricAlgebra.lift l)
      (fun _ _ => Commute.all _ _) ((tensorEquiv I).symm (MvPolynomial.X i)) = _
    rw [hi, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
      SymmetricAlgebra.lift_ι_apply, MvPolynomial.eval₂Hom_X']

/-- **The action of the tangent bundle on the `B`-points of the affine normal cone** is the
translation `ConeTranslation.translatePoint` of the polynomial model. -/
theorem translate_act (φ : Gr I →ₐ[Base I] B) (l : Tangent I →ₗ[Base I] B) (z : Gr I) :
    translate (act I) φ l z =
      translatePoint I (φ : Gr I →+* B) (fun i => l (tangentBasis I i)) z :=
  RingHom.congr_fun (liftComp_tensorEquiv_symm φ l) (coaction I z)

/-- The action on points, as an equality of ring homomorphisms. -/
theorem translate_act_ringHom (φ : Gr I →ₐ[Base I] B) (l : Tangent I →ₗ[Base I] B) :
    ((translate (act I) φ l : Gr I →ₐ[Base I] B) : Gr I →+* B) =
      translatePoint I (φ : Gr I →+* B) (fun i => l (tangentBasis I i)) :=
  RingHom.ext (translate_act φ l)

/-- Translating by the zero tangent vector does nothing. -/
theorem act_zero (φ : Gr I →ₐ[Base I] B) : translate (act I) φ 0 = φ := by
  refine AlgHom.ext fun z => ?_
  rw [translate_act]
  have hv : (fun i => (0 : Tangent I →ₗ[Base I] B) (tangentBasis I i)) = 0 := by
    funext i
    rfl
  rw [hv, translatePoint_zero]
  rfl

/-- Translating twice is translating by the sum. -/
theorem act_add (φ : Gr I →ₐ[Base I] B) (l l' : Tangent I →ₗ[Base I] B) :
    translate (act I) (translate (act I) φ l) l' = translate (act I) φ (l + l') := by
  refine AlgHom.ext fun z => ?_
  rw [translate_act, translate_act_ringHom, translatePoint_add]
  have hv : (fun i => (l + l') (tangentBasis I i)) =
      (fun i => l (tangentBasis I i)) + fun i => l' (tangentBasis I i) := by
    funext i
    rfl
  rw [translate_act, hv]

end Points

/-! ## The conormal map is the Taylor derivation -/

/-- The `R/I`-linear map from the restricted tangent bundle to `gr_I(R)[ε_σ]` sending a tangent
vector to the corresponding linear form in the `ε`-coordinates. -/
noncomputable def tangentToPoly : Tangent I →ₗ[Base I] MvPolynomial σ (Gr I) :=
  (MvPolynomial.mapAlgHom (Algebra.ofId (Base I) (Gr I))).toLinearMap.comp
    ((symEquiv I).toLinearMap.comp (SymmetricAlgebra.ι (Base I) (Tangent I)))

theorem tangentToPoly_apply (v : Tangent I) :
    tangentToPoly I v =
      MvPolynomial.map (algebraMap (Base I) (Gr I))
        (symEquiv I (SymmetricAlgebra.ι (Base I) (Tangent I) v)) :=
  rfl

@[simp]
theorem tangentToPoly_basis (i : σ) : tangentToPoly I (tangentBasis I i) = MvPolynomial.X i := by
  rw [tangentToPoly_apply, symEquiv_ι, MvPolynomial.map_X]

/-- The Taylor derivation `f ↦ Σ_i ε_i ∂_i f` of `Cones/ConeTranslation.lean`, with values in
`gr_I(R)[ε_σ]`. -/
noncomputable def taylorDer : Derivation A (MvPolynomial σ A) (MvPolynomial σ (Gr I)) :=
  (MvPolynomial.mapAlgHom
    (Algebra.ofId (MvPolynomial σ A) (Gr I))).toLinearMap.compDer (taylor A σ)

/-- The universal derivation of `R = A[x_i]`, composed with the tangent comparison. -/
noncomputable def kaehlerDer : Derivation A (MvPolynomial σ A) (MvPolynomial σ (Gr I)) :=
  (((tangentToPoly I).restrictScalars (MvPolynomial σ A)).comp
    (TensorProduct.mk (MvPolynomial σ A) (Base I) Ω[MvPolynomial σ A⁄A] 1)).compDer
      (KaehlerDifferential.D A (MvPolynomial σ A))

/-- **The Taylor derivation is the universal derivation.**  Both are `A`-derivations of the
polynomial ring `R = A[x_i]` with values in `gr_I(R)[ε_σ]` sending `x_i` to `ε_i`, so they
agree. -/
theorem taylorDer_eq_kaehlerDer : taylorDer I = kaehlerDer I := by
  refine MvPolynomial.derivation_ext fun i => ?_
  change MvPolynomial.mapAlgHom (Algebra.ofId (MvPolynomial σ A) (Gr I))
    (taylor A σ (MvPolynomial.X i)) = _
  rw [taylor_X, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X]
  change _ = tangentToPoly I ((1 : Base I) ⊗ₜ[MvPolynomial σ A]
    KaehlerDifferential.D A (MvPolynomial σ A) (MvPolynomial.X i))
  rw [← tangentBasis_apply, tangentToPoly_basis]

/-- The Taylor expansion of a polynomial, read through the tangent comparison, is the image of
its universal differential. -/
theorem map_taylor_eq (x : MvPolynomial σ A) :
    MvPolynomial.map (algebraMap (MvPolynomial σ A) (Gr I)) (taylor A σ x) =
      tangentToPoly I ((1 : Base I) ⊗ₜ[MvPolynomial σ A]
        KaehlerDifferential.D A (MvPolynomial σ A) x) :=
  Derivation.congr_fun (taylorDer_eq_kaehlerDer I) x

/-- **The conormal map of `Cones/DeformationSpaceGeometry.lean` is the Taylor derivation.** -/
theorem tangentToPoly_conormalMap (x : I) :
    tangentToPoly I
        (AffineNormalCone.conormalMap A (MvPolynomial σ A) I (Ideal.toCotangent I x)) =
      MvPolynomial.map (algebraMap (MvPolynomial σ A) (Gr I)) (taylor A σ (x : MvPolynomial σ A)) :=
  by rw [AffineNormalCone.conormalMap_toCotangent, map_taylor_eq]

/-! ## Equivariance of the closed immersion `C_{U/M} ↪ N_{U/M}` -/

/-- The image of a pure tangent tensor under the comparison isomorphism. -/
@[simp]
theorem tensorEquiv_one_tmul_ι (v : Tangent I) :
    tensorEquiv I ((1 : Gr I) ⊗ₜ[Base I] SymmetricAlgebra.ι (Base I) (Tangent I) v) =
      tangentToPoly I v := by
  rw [tensorEquiv_tmul, one_smul, tangentToPoly_apply]

/-- The surjection `Sym_{R/I}(I/I²) ↠ gr_I(R)` of coordinate algebras, as a map of
`R/I`-algebras.  On spectra it is the closed immersion `C_{U/M} ↪ N_{U/M}` of the affine normal
cone into the affine normal sheaf. -/
noncomputable def nsToGrAlg :
    AffineNormalCone.normalSheafCoordinateRing (MvPolynomial σ A) I →ₐ[Base I] Gr I where
  toRingHom := AffineNormalCone.normalSheafCoordinateMap (MvPolynomial σ A) I
  commutes' r := AffineNormalCone.normalSheafCoordinateMap_base (MvPolynomial σ A) I r

theorem nsToGrAlg_surjective : Function.Surjective (nsToGrAlg I) :=
  AffineNormalCone.normalSheafCoordinateMap_surjective (MvPolynomial σ A) I

@[simp]
theorem nsToGrAlg_ι (m : I.Cotangent) :
    nsToGrAlg I (SymmetricAlgebra.ι (Base I) I.Cotangent m) =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ A) I m :=
  AffineNormalCone.normalSheafCoordinateMap_ι (MvPolynomial σ A) I m

-- The comparison `tensorEquiv` is a composite of several algebra equivalences, so unfolding the
-- `AlgHom.comp` applications in the last step exceeds the default recursion depth.
set_option maxRecDepth 8000 in
/-- **Vistoli's lemma in cone-action form.**  The closed immersion of the affine normal cone into
the affine normal sheaf intertwines the translation action of the restricted tangent bundle on
the normal sheaf with the tangent coaction of `Cones/ConeTranslation.lean` on the normal cone.

Both sides are algebra maps out of `Sym_{R/I}(I/I²)`, so it suffices to compare them on a
conormal generator `[x]`; there the statement is exactly `ConeTranslation.coaction_degreeOne`
together with the identification `NormalConeAction.tangentToPoly_conormalMap` of the conormal
map with the Taylor derivation. -/
theorem map_comp_bundleTranslationCoaction :
    (Algebra.TensorProduct.map (nsToGrAlg I)
        (symMap (LinearMap.id : Tangent I →ₗ[Base I] Tangent I))).comp
        (bundleTranslationCoaction
          (AffineNormalCone.conormalMap A (MvPolynomial σ A) I)) =
      (act I).comp (nsToGrAlg I) := by
  have key : ((tensorEquiv I).toAlgHom.comp
        ((Algebra.TensorProduct.map (nsToGrAlg I)
          (symMap (LinearMap.id : Tangent I →ₗ[Base I] Tangent I))).comp
          (bundleTranslationCoaction
            (AffineNormalCone.conormalMap A (MvPolynomial σ A) I)))) =
      ((tensorEquiv I).toAlgHom.comp ((act I).comp (nsToGrAlg I))) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I m
    have hL : (Algebra.TensorProduct.map (nsToGrAlg I)
          (symMap (LinearMap.id : Tangent I →ₗ[Base I] Tangent I)))
          (bundleTranslationCoaction (AffineNormalCone.conormalMap A (MvPolynomial σ A) I)
            (SymmetricAlgebra.ι (Base I) I.Cotangent (Ideal.toCotangent I x))) =
        nsToGrAlg I (SymmetricAlgebra.ι (Base I) I.Cotangent (Ideal.toCotangent I x))
            ⊗ₜ[Base I] 1 +
          (1 : Gr I) ⊗ₜ[Base I] SymmetricAlgebra.ι (Base I) (Tangent I)
            (AffineNormalCone.conormalMap A (MvPolynomial σ A) I (Ideal.toCotangent I x)) := by
      rw [bundleTranslationCoaction_ι, map_add, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul]
      simp only [symMap_id, AlgHom.id_apply, map_one]
    have hgoal : tensorEquiv I ((Algebra.TensorProduct.map (nsToGrAlg I)
          (symMap (LinearMap.id : Tangent I →ₗ[Base I] Tangent I)))
          (bundleTranslationCoaction (AffineNormalCone.conormalMap A (MvPolynomial σ A) I)
            (SymmetricAlgebra.ι (Base I) I.Cotangent (Ideal.toCotangent I x)))) =
        tensorEquiv I (act I (nsToGrAlg I
          (SymmetricAlgebra.ι (Base I) I.Cotangent (Ideal.toCotangent I x)))) := by
      rw [hL, map_add, tensorEquiv_left, tensorEquiv_one_tmul_ι, tensorEquiv_act, nsToGrAlg_ι,
        AffineNormalCone.conormalToAssociatedGraded_toCotangent, coaction_degreeOne,
        tangentToPoly_conormalMap]
    exact hgoal
  exact AlgHom.ext fun s => (tensorEquiv I).injective (AlgHom.congr_fun key s)

/-- The equivariance of the closed immersion, in the form required by
`ConeQuotient.IsEquivariant`, once the cone action has been packaged. -/
theorem isEquivariant_nsToGrAlg_aux :
    (Algebra.TensorProduct.map (nsToGrAlg I)
        (symMap (LinearMap.id : Tangent I →ₗ[Base I] Tangent I))).comp
        (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I).act =
      (act I).comp (nsToGrAlg I) :=
  map_comp_bundleTranslationCoaction I

/-! ## The cone action -/

/-- **The closed immersion `C_{U/M} ↪ N_{U/M}` is a morphism of cones.**  The conormal classes
are homogeneous of degree one in `gr_I(R)`, which is
`AffineNormalCone.conormal_mem_homogeneous_one`. -/
theorem isConeHom_nsToGrAlg :
    IsConeHom (symCoaction (Base I) I.Cotangent)
      (normalConeCoactionQuot (MvPolynomial σ A) I) (nsToGrAlg I) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  have hL : Polynomial.mapAlgHom (nsToGrAlg I)
        (symCoaction (Base I) I.Cotangent (SymmetricAlgebra.ι (Base I) I.Cotangent m)) =
      Polynomial.C (nsToGrAlg I (SymmetricAlgebra.ι (Base I) I.Cotangent m)) * Polynomial.X := by
    rw [symCoaction_ι, map_mul]
    simp
  have hR : normalConeCoactionQuot (MvPolynomial σ A) I
        (nsToGrAlg I (SymmetricAlgebra.ι (Base I) I.Cotangent m)) =
      Polynomial.C (nsToGrAlg I (SymmetricAlgebra.ι (Base I) I.Cotangent m)) * Polynomial.X := by
    rw [nsToGrAlg_ι]
    have h := GradedCone.mem_homogeneous.1
      (AffineNormalCone.conormal_mem_homogeneous_one (MvPolynomial σ A) I m)
    rw [pow_one] at h
    exact h
  exact hL.trans hR.symm

/-- **The tangent action commutes with the `𝔸¹`-contractions.**  This is the last `ConeAction`
axiom; it follows from the corresponding statement for the normal sheaf, because the closed
immersion `Sym(I/I²) ↠ gr_I(R)` is surjective, equivariant and a morphism of cones. -/
theorem conic_act :
    IsConeHom (normalConeCoactionQuot (MvPolynomial σ A) I)
      (tensorCoaction (normalConeCoactionQuot (MvPolynomial σ A) I)
        (symCoaction (Base I) (Tangent I))) (act I) := by
  have hmap : IsConeHom
      (tensorCoaction (symCoaction (Base I) I.Cotangent) (symCoaction (Base I) (Tangent I)))
      (tensorCoaction (normalConeCoactionQuot (MvPolynomial σ A) I)
        (symCoaction (Base I) (Tangent I)))
      (Algebra.TensorProduct.map (nsToGrAlg I)
        (symMap (LinearMap.id : Tangent I →ₗ[Base I] Tangent I))) := by
    rw [symMap_id]
    exact isConeHom_tensorMap (isConeHom_nsToGrAlg I)
      (isConeHom_id (symCoaction (Base I) (Tangent I)))
  have hbundle : IsConeHom (symCoaction (Base I) I.Cotangent)
      (tensorCoaction (symCoaction (Base I) I.Cotangent) (symCoaction (Base I) (Tangent I)))
      (bundleTranslationCoaction (AffineNormalCone.conormalMap A (MvPolynomial σ A) I)) :=
    (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I).conic
  have heq := map_comp_bundleTranslationCoaction I
  have hpsi := isConeHom_nsToGrAlg I
  have key : ((Polynomial.mapAlgHom (act I)).comp
        (normalConeCoactionQuot (MvPolynomial σ A) I)).comp (nsToGrAlg I) =
      ((tensorCoaction (normalConeCoactionQuot (MvPolynomial σ A) I)
        (symCoaction (Base I) (Tangent I))).comp (act I)).comp (nsToGrAlg I) := by
    rw [AlgHom.comp_assoc, ← hpsi, ← AlgHom.comp_assoc, mapAlgHom_comp, ← heq,
      ← mapAlgHom_comp, AlgHom.comp_assoc, hbundle, ← AlgHom.comp_assoc, hmap,
      AlgHom.comp_assoc, heq, ← AlgHom.comp_assoc]
  refine AlgHom.ext fun z => ?_
  obtain ⟨s, rfl⟩ := nsToGrAlg_surjective I z
  exact AlgHom.congr_fun key s

/-- **The tangent action of `T_M|_U = U × 𝔸^σ` on the affine normal cone `C_{U/M}`.**

The `𝔸¹`-contraction is the grading of `gr_I(R)` (`GradedCone.normalConeCoactionQuot`), the
coaction is the translation `[f t] ↦ [f t] + Σ_i ε_i [∂_i f]` of `Cones/ConeTranslation.lean`,
and all four `ConeAction` axioms are proved: the unit and associativity laws are
`ConeTranslation.translatePoint_zero` and `ConeTranslation.translatePoint_add`, and the
`𝔾ₘ`-equivariance is `NormalConeAction.conic_act`. -/
noncomputable def normalConeAction : ConeAction (Base I) (Gr I) (Tangent I) where
  coaction := normalConeCoactionQuot (MvPolynomial σ A) I
  isCone := isConeCoaction_normalConeCoactionQuot (MvPolynomial σ A) I
  act := act I
  act_zero φ := act_zero φ
  act_add φ l l' := act_add φ l l'
  conic := conic_act I

@[simp]
theorem normalConeAction_act : (normalConeAction I).act = act I := rfl

@[simp]
theorem normalConeAction_coaction :
    (normalConeAction I).coaction = normalConeCoactionQuot (MvPolynomial σ A) I := rfl

/-- **The closed immersion of the affine normal cone into the affine normal sheaf is
equivariant** for the tangent actions.  This is Vistoli's lemma: the translation action of
`T_M|_U` on `N_{U/M}` preserves the closed subcone `C_{U/M}`. -/
theorem isEquivariant_nsToGrAlg :
    IsEquivariant (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I)
      (normalConeAction I) (nsToGrAlg I) LinearMap.id :=
  map_comp_bundleTranslationCoaction I

/-! ## The obstruction cone of the affine intrinsic normal cone -/

section ObstructionCone

open PicardCriteria NormalSheafPicard NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {E : LinearTwoTermComplex (Base I)}

/-- **The obstruction cone of the affine intrinsic normal cone.**

For an obstruction theory `φ : E ⟶ [I/I² → (R/I) ⊗ Ω]` this is the morphism of cone stacks

`[C_{U/M}/T_M|_U](B) ⟶ h¹/h⁰(Eᵛ)(B)`

over every test algebra `B`, obtained by instantiating
`PicardCriteria.obstructionCone` with the equivariant closed immersion
`NormalConeAction.isEquivariant_nsToGrAlg` of the affine normal cone into the affine normal
sheaf. -/
noncomputable def normalConeObstructionCone
    (φ : LinearTwoTermComplex.Hom E (conormalComplex A (MvPolynomial σ A) I))
    (B : Type u) [CommRing B] [Algebra (Base I) B] :
    QuotientGroupoid (normalConeAction I) B ⥤ (dualPoints E B).quotient :=
  PicardCriteria.obstructionCone φ (isEquivariant_nsToGrAlg I) B

/-- **The obstruction cone of the normal cone is a closed immersion, first half.** -/
noncomputable def normalConeObstructionConeFullyFaithful
    {φ : LinearTwoTermComplex.Hom E (conormalComplex A (MvPolynomial σ A) I)}
    (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B] [Algebra (Base I) B] :
    (normalConeObstructionCone I φ B).FullyFaithful :=
  PicardCriteria.obstructionConeFullyFaithful hφ (isEquivariant_nsToGrAlg I)
    (nsToGrAlg_surjective I) B

/-- **The obstruction cone of the normal cone is a closed immersion, second half.** -/
theorem normalConeObstructionCone_injective_isoClass
    {φ : LinearTwoTermComplex.Hom E (conormalComplex A (MvPolynomial σ A) I)}
    (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B] [Algebra (Base I) B]
    {c c' : QuotientGroupoid (normalConeAction I) B}
    (hiso : Nonempty ((normalConeObstructionCone I φ B).obj c
      ≅ (normalConeObstructionCone I φ B).obj c')) :
    Nonempty (c ≅ c') :=
  PicardCriteria.obstructionCone_injective_isoClass hφ (isEquivariant_nsToGrAlg I)
    (nsToGrAlg_surjective I) B hiso

/-- **The obstruction cone of the normal cone for an obstruction theory on the presentation
cotangent complex** of `R → R/I`. -/
noncomputable def presentationNormalConeObstructionCone
    (φ : LinearTwoTermComplex.Hom E
      (CotangentComplex.AffinePresentation.twoTerm A (Base I)
        (quotientExtension A (MvPolynomial σ A) I)))
    (B : Type u) [CommRing B] [Algebra (Base I) B] :
    QuotientGroupoid (normalConeAction I) B ⥤ (dualPoints E B).quotient :=
  normalConeObstructionCone I (PicardCriteria.ofPresentation A (MvPolynomial σ A) I φ) B

/-- The obstruction cone attached to an obstruction theory on the presentation complex is fully
faithful. -/
noncomputable def presentationNormalConeObstructionConeFullyFaithful
    {φ : LinearTwoTermComplex.Hom E
      (CotangentComplex.AffinePresentation.twoTerm A (Base I)
        (quotientExtension A (MvPolynomial σ A) I))}
    (hφ : IsObstructionTheory φ) (B : Type u) [CommRing B] [Algebra (Base I) B] :
    (presentationNormalConeObstructionCone I φ B).FullyFaithful :=
  normalConeObstructionConeFullyFaithful I
    (PicardCriteria.isObstructionTheory_ofPresentation A (MvPolynomial σ A) I hφ) B

end ObstructionCone

/-! ## The local complete intersection case -/

/-- **If the normal cone is the normal sheaf, the two quotient stacks agree.**

When the canonical map `Sym_{R/I}(I/I²) → gr_I(R)` is bijective — which
`Cones/RegularSequence.lean` proves for an ideal generated by a regular sequence
(`AffineNormalCone.QuasiregularGenerators.normalSheafCoordinateMap_bijective`) — the inclusion
`[C_{U/M}/T_M|_U](B) ⥤ [N_{U/M}/T_M|_U](B)` is an equivalence for every test algebra `B`.  This
is the fibrewise statement `𝔠_{U/M} = 𝔑_{U/M}` for a local complete intersection. -/
theorem isEquivalence_quotientFunctor_of_bijective
    (hbij : Function.Bijective (AffineNormalCone.normalSheafCoordinateMap (MvPolynomial σ A) I))
    (B : Type u) [CommRing B] [Algebra (Base I) B] :
    (quotientFunctor (isEquivariant_nsToGrAlg I) B).IsEquivalence := by
  have hpsi : Function.Bijective (nsToGrAlg I) := hbij
  refine isEquivalence_quotientFunctor (isEquivariant_nsToGrAlg I) B (fun y => ?_)
    (fun _ _ l₁ l₂ _ _ hl => ?_) (fun x y l hxy => ?_)
  · refine ⟨y.comp ((AlgEquiv.ofBijective (nsToGrAlg I) hpsi).symm :
      Gr I →ₐ[Base I] _), 0, ?_⟩
    have hy : (y.comp ((AlgEquiv.ofBijective (nsToGrAlg I) hpsi).symm :
        Gr I →ₐ[Base I] _)).comp (nsToGrAlg I) = y :=
      AlgHom.ext fun t =>
        congrArg y ((AlgEquiv.ofBijective (nsToGrAlg I) hpsi).symm_apply_apply t)
    rw [hy]
    exact (AffineNormalCone.normalSheafTangentAction A (MvPolynomial σ A) I).act_zero y
  · simpa using hl
  · refine ⟨l, ?_, LinearMap.comp_id l⟩
    have hc := translate_comp (isEquivariant_nsToGrAlg I) x l
    rw [LinearMap.comp_id] at hc
    refine AlgHom.ext fun t => ?_
    obtain ⟨s, rfl⟩ := nsToGrAlg_surjective I t
    exact AlgHom.congr_fun (hc.trans hxy) s

/-! ## The smooth case -/

section Smooth

variable [Subsingleton I.Cotangent]

/-- **If the conormal module vanishes the normal cone is the zero cone**: every element of
`gr_I(R)` is a scalar, because `Sym_{R/I}(I/I²) = R/I` surjects onto it. -/
theorem algebraMap_surjective_of_subsingleton :
    Function.Surjective (algebraMap (Base I) (Gr I)) := by
  intro z
  obtain ⟨s, rfl⟩ := nsToGrAlg_surjective I z
  induction s using SymmetricAlgebra.induction with
  | algebraMap r => exact ⟨r, ((nsToGrAlg I).commutes r).symm⟩
  | ι m =>
    rw [Subsingleton.elim m 0, map_zero, map_zero]
    exact ⟨0, map_zero _⟩
  | mul a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    exact ⟨u * v, by rw [map_mul, map_mul, hu, hv]⟩
  | add a b ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    exact ⟨u + v, by rw [map_add, map_add, hu, hv]⟩

variable {B : Type u} [CommRing B] [Algebra (Base I) B]

/-- The zero cone has exactly one `B`-point. -/
theorem subsingleton_algHom_of_subsingleton : Subsingleton (Gr I →ₐ[Base I] B) := by
  refine ⟨fun f g => AlgHom.ext fun z => ?_⟩
  obtain ⟨r, rfl⟩ := algebraMap_surjective_of_subsingleton I z
  rw [AlgHom.commutes, AlgHom.commutes]

/-- **The quotient groupoid of the zero cone has a single object.** -/
theorem subsingleton_quotientGroupoid :
    Subsingleton (QuotientGroupoid (normalConeAction I) B) :=
  ⟨fun x y => QuotientGroupoid.ext
    ((subsingleton_algHom_of_subsingleton I).elim x.point y.point)⟩

/-- **The quotient groupoid of the zero cone has a single isomorphism class.** -/
theorem nonempty_hom_of_subsingleton (x y : QuotientGroupoid (normalConeAction I) B) :
    Nonempty (x ⟶ y) :=
  ⟨eqToHom ((subsingleton_quotientGroupoid I).elim x y)⟩

/-- **The automorphisms of the zero cone are the whole tangent bundle.**

For `I = ⊥` — the smooth case `U = M` — the quotient `[C_{U/M}/T_M|_U](B)` is the classifying
groupoid `B T_M(B)`: it has one isomorphism class (`nonempty_hom_of_subsingleton`) and the
automorphism group of every object is `T_M(B) = Hom_{R/I}(F, B)`. -/
noncomputable def autEquivTangent_of_subsingleton
    (x : QuotientGroupoid (normalConeAction I) B) :
    (x ⟶ x) ≃ (Tangent I →ₗ[Base I] B) :=
  have hs : Subsingleton (Gr I →ₐ[Base I] B) := subsingleton_algHom_of_subsingleton I
  (QuotientGroupoid.autEquivStabilizer x).trans
    (Equiv.subtypeUnivEquiv fun _ => hs.elim _ _)

end Smooth

/-- The conormal module of the zero ideal vanishes, so the results of the smooth case apply to
`I = ⊥`, i.e. to the identity closed immersion `U = M`. -/
instance : Subsingleton (⊥ : Ideal (MvPolynomial σ A)).Cotangent :=
  AffineNormalCone.conormalModuleBotSubsingleton (MvPolynomial σ A)

end NormalConeAction

end GromovWitten.AlgebraicGeometry
