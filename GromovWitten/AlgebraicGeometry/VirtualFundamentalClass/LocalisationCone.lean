/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeConeIdeal
import GromovWitten.AlgebraicGeometry.Cones.SmoothAmbient

/-!
# Flat formally étale base change of the resolved cone

Let `k` be a commutative ring, `R` a `k`-algebra, `I ⊆ R` an ideal and `B = R ⧸ I`.  Let `R'` be
a flat, formally étale `R`-algebra (the motivating example is a localisation
`R' = Localization.Away f`), put `I' = I·R'` and `B' = R' ⧸ I'`.  Geometrically `Spec B'` is a
basic open subscheme of `Spec B` in the localisation case, and an étale neighbourhood in general.

This file compares the affine obstruction datum over `Spec B` with its base change to `Spec B'`,
and the resolved cone of the one with the resolved cone of the other.  It is the "open/étale
restriction" companion of `VirtualFundamentalClass/BaseChangeCone.lean` and
`VirtualFundamentalClass/BaseChangeConeIdeal.lean`, which treat the polynomial base change
`Spec B × 𝔸^τ → Spec B`.

## Contents

* `LocalisationCone.extIdeal`, `LocalisationCone.baseExt`: the ideal `I'` and the ring `B'`, with
  `LocalisationCone.baseExtTensorEquiv : B' ≃ₐ[B] B ⊗[R] R'` and
  `LocalisationCone.flat_baseExt : Module.Flat B B'`.
* `LocalisationCone.cotangentComparison : B' ⊗[B] I/I² ≃ₗ[B'] I'/I'²`, the flat base change of
  the conormal module, and
  `LocalisationCone.kaehlerComparison : B' ⊗[B] (B ⊗[R] Ω[R⁄k]) ≃ₗ[B'] B' ⊗[R'] Ω[R'⁄k]`, the
  formally étale base change of the restricted cotangent bundle; they commute with the conormal
  maps (`LocalisationCone.kaehlerComparison_baseChange_conormalMap`).
* `LocalisationCone.baseChangeHom φ : Hom (E.baseChange B') (conormalComplex k R' I')`, the base
  change of an affine obstruction datum.
* `LocalisationCone.isPushoutBaseExt : Algebra.IsPushout R B R' B'`, and the localisation facts
  `LocalisationCone.flat_of_isLocalizationAway`,
  `LocalisationCone.formallyEtale_of_isLocalizationAway`,
  `LocalisationCone.isLocalization_away_baseExt`.
* `LocalisationCone.grBaseExtEquiv : B' ⊗[B] gr_I(R) ≃ₐ[B'] gr_{I'}(R')`, the flat base change of
  the associated graded ring.
* `LocalisationCone.bundleRingEquiv`, `LocalisationCone.productRingEquiv` and the commuting square
  `LocalisationCone.productRingEquiv_comp_productMap` for the two coordinate rings entering the
  resolved cone.
* `LocalisationCone.ideal_map_bundleRingEquiv` and
  `LocalisationCone.ringEquiv`, saying that `ResolvedCone.ring (baseChangeHom φ)` is
  `B' ⊗[B] ResolvedCone.ring φ`: the resolved cone commutes with the base change.
* `LocalisationCone.isLocalization_away_ring`: for `R'` a localisation of `R` away from `f`, the
  coordinate ring of the base-changed resolved cone is the localisation of `ResolvedCone.ring φ`
  away from the image of `f`.  This is the form needed to build an `AlgebraData` on `Spec B`.

## Implementation notes

All comparison maps are built from the heterobasic tensor-product equivalences
`TensorProduct.AlgebraTensorModule.cancelBaseChange` and `.congr`, from
`AffineNormalCone.quotTensorIdealEquiv` and `AffineNormalCone.idealTensorEquiv` (flat base change
of an ideal) of `Cones/NormalConeGlobal.lean`, and from
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.  As in round 16,
`LinearMap.liftBaseChange` is unusable here because the required `IsScalarTower` instances are
never found; every comparison is a composite of `LinearEquiv.trans`es instead.

The identification of the associated graded rings goes through `Algebra.IsPushout`: the square
`R → R'`, `B → B'` is a pushout (`isPushoutBaseExt`), so `Algebra.IsPushout.cancelBaseChangeAlg`
turns `B' ⊗[B] gr_I(R)` into `R' ⊗[R] gr_I(R)`, where `AffineNormalCone.grTensorEquiv` applies.
-/

-- Nested tensor products of a graded ring with a symmetric algebra need a deeper instance search.
set_option maxSynthPendingDepth 5

universe u

open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualClass.LocalisationCone

open GromovWitten.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (R' : Type u) [CommRing R'] [Algebra R R']

/-! ## The base ring of the base change -/

/-- The extension `I' = I·R'` of `I` to the flat formally étale `R`-algebra `R'`. -/
abbrev extIdeal : Ideal R' := I.map (algebraMap R R')

/-- The base ring `B' = R' ⧸ I'` of the base change. -/
abbrev baseExt : Type u := R' ⧸ extIdeal I R'

/-- The structure map `R → R'` carries `I` into `I'`. -/
theorem le_comap_extIdeal : I ≤ (extIdeal I R').comap (algebraMap R R') := fun _ hx =>
  Ideal.mem_map_of_mem _ hx

/-- The structure map of `B'` over `B` on a class `[r]`.  The `B`-algebra structure is Mathlib's
`Ideal.Quotient.algebraQuotientMapQuotient`, and the scalar tower over `R` is
`Ideal.Quotient.tower_quotient_map_quotient`. -/
@[simp]
theorem algebraMap_baseExt_mk (r : R) :
    algebraMap (R ⧸ I) (baseExt I R') (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk _ (algebraMap R R' r) :=
  rfl

/-- `B' ≃ₐ[B] B ⊗[R] R'`: the base ring of the base change is the base change of the base ring. -/
noncomputable def baseExtTensorEquiv : baseExt I R' ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] R' :=
  Algebra.TensorProduct.quotIdealMapEquivQuotTensor R' I

/-- `B'` is flat over `B` because `R'` is flat over `R`. -/
instance flat_baseExt [Module.Flat R R'] : Module.Flat (R ⧸ I) (baseExt I R') :=
  Module.Flat.of_linearEquiv (baseExtTensorEquiv I R').toLinearEquiv

/-! ## The pushout square, and the case of a localisation -/

/-- **The square `R → R'`, `B → B'` is a pushout**, i.e. `B' = R' ⊗[R] B`. -/
instance isPushoutBaseExt : Algebra.IsPushout R (R ⧸ I) R' (baseExt I R') :=
  ⟨IsBaseChange.of_equiv (baseExtTensorEquiv I R').symm.toLinearEquiv fun r' => by
    change (baseExtTensorEquiv I R').symm ((1 : R ⧸ I) ⊗ₜ r') = _
    rw [AlgEquiv.symm_apply_eq]
    rfl⟩

/-- The transposed pushout square, in the orientation needed by
`Algebra.IsPushout.cancelBaseChangeAlg`. -/
instance isPushoutBaseExt' : Algebra.IsPushout R R' (R ⧸ I) (baseExt I R') :=
  Algebra.IsPushout.symm inferInstance

/-- A localisation away from `f` is flat: one of the two instances this file assumes. -/
theorem flat_of_isLocalizationAway (f : R) [IsLocalization.Away f R'] : Module.Flat R R' :=
  IsLocalization.flat R' (Submonoid.powers f)

/-- A localisation away from `f` is formally étale: the other instance this file assumes. -/
theorem formallyEtale_of_isLocalizationAway (f : R) [IsLocalization.Away f R'] :
    Algebra.FormallyEtale R R' :=
  Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)

/-- **`B'` is the localisation of `B` away from the image of `f`** when `R'` is the localisation
of `R` away from `f`.  This is the ring-theoretic form of "`Spec B'` is the basic open subset
`D(f) ⊆ Spec B`". -/
theorem isLocalization_away_baseExt (f : R) [IsLocalization.Away f R'] :
    IsLocalization.Away (algebraMap R (R ⧸ I) f) (baseExt I R') := by
  have h : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers f))
      (baseExt I R') :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers f) R' (T := R ⧸ I)
      (B := baseExt I R')).mpr (isPushoutBaseExt I R')
  rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h

/-! ## The comparison of conormal modules -/

section Cotangent

variable [Module.Flat R R']

/-- **Flat base change of the conormal module**: `B' ⊗[B] I/I² ≃ I'/I'²`.  It is assembled from
`AffineNormalCone.quotTensorIdealEquiv` (`I/I² = B ⊗[R] I`) on both sides and the flat base
change `AffineNormalCone.idealTensorEquiv` of the ideal itself. -/
noncomputable def cotangentComparison :
    baseExt I R' ⊗[R ⧸ I] I.Cotangent ≃ₗ[baseExt I R'] (extIdeal I R').Cotangent :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (baseExt I R') (baseExt I R'))
      (AffineNormalCone.quotTensorIdealEquiv R I).symm).trans <|
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (baseExt I R')
        (baseExt I R') I).trans <|
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' (baseExt I R')
          (baseExt I R') I).symm).trans <|
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (baseExt I R') (baseExt I R'))
            (AffineNormalCone.idealTensorEquiv I (extIdeal I R') rfl)).trans
          (AffineNormalCone.quotTensorIdealEquiv R' (extIdeal I R'))

@[simp]
theorem cotangentComparison_tmul_toCotangent (b : baseExt I R') (x : I) :
    cotangentComparison I R' (b ⊗ₜ Ideal.toCotangent I x) =
      b • Ideal.toCotangent (extIdeal I R')
        ⟨algebraMap R R' (x : R), Ideal.mem_map_of_mem _ x.2⟩ := by
  have h1 : (AffineNormalCone.quotTensorIdealEquiv R I).symm (Ideal.toCotangent I x) =
      (1 : R ⧸ I) ⊗ₜ x := by
    rw [LinearEquiv.symm_apply_eq, AffineNormalCone.quotTensorIdealEquiv_one_tmul]
  have h2 : AffineNormalCone.idealTensorEquiv I (extIdeal I R') rfl ((1 : R') ⊗ₜ x) =
      ⟨algebraMap R R' (x : R), Ideal.mem_map_of_mem _ x.2⟩ := by
    rw [AffineNormalCone.idealTensorEquiv_one_tmul]
    rfl
  have h3 : AffineNormalCone.quotTensorIdealEquiv R' (extIdeal I R')
      (b ⊗ₜ (⟨algebraMap R R' (x : R), Ideal.mem_map_of_mem _ x.2⟩ : extIdeal I R')) =
      b • Ideal.toCotangent (extIdeal I R')
        ⟨algebraMap R R' (x : R), Ideal.mem_map_of_mem _ x.2⟩ := by
    rw [show (b ⊗ₜ (⟨algebraMap R R' (x : R), Ideal.mem_map_of_mem _ x.2⟩ : extIdeal I R')) =
        b • ((1 : baseExt I R') ⊗ₜ
          (⟨algebraMap R R' (x : R), Ideal.mem_map_of_mem _ x.2⟩ : extIdeal I R')) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
      AffineNormalCone.quotTensorIdealEquiv_one_tmul]
  change AffineNormalCone.quotTensorIdealEquiv R' (extIdeal I R')
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (baseExt I R') (baseExt I R'))
      (AffineNormalCone.idealTensorEquiv I (extIdeal I R') rfl)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' (baseExt I R')
          (baseExt I R') I).symm
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (baseExt I R')
            (baseExt I R') I
          (TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl (baseExt I R') (baseExt I R'))
            (AffineNormalCone.quotTensorIdealEquiv R I).symm (b ⊗ₜ Ideal.toCotangent I x))))) = _
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h1,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h2, h3]

end Cotangent

/-! ## The comparison of restricted cotangent bundles -/

section Kaehler

variable {k : Type u} [CommRing k] [Algebra k R] [Algebra k R'] [IsScalarTower k R R']
variable [Algebra.FormallyEtale R R']

/-- **Formally étale base change of the restricted cotangent bundle**:
`B' ⊗[B] (B ⊗[R] Ω[R⁄k]) ≃ B' ⊗[R'] Ω[R'⁄k]`.  The only non-formal ingredient is
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`. -/
noncomputable def kaehlerComparison :
    baseExt I R' ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] Ω[R⁄k]) ≃ₗ[baseExt I R']
      baseExt I R' ⊗[R'] Ω[R'⁄k] :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (baseExt I R') (baseExt I R')
      Ω[R⁄k]).trans <|
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' (baseExt I R') (baseExt I R')
        Ω[R⁄k]).symm).trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (baseExt I R') (baseExt I R'))
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R R'))

@[simp]
theorem kaehlerComparison_tmul_one_tmul (b : baseExt I R') (ω : Ω[R⁄k]) :
    kaehlerComparison I R' (b ⊗ₜ ((1 : R ⧸ I) ⊗ₜ ω)) =
      b ⊗ₜ KaehlerDifferential.map k k R R' ω := by
  change TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (baseExt I R') (baseExt I R'))
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R R')
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' (baseExt I R') (baseExt I R')
        Ω[R⁄k]).symm
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (baseExt I R')
        (baseExt I R') Ω[R⁄k] (b ⊗ₜ ((1 : R ⧸ I) ⊗ₜ ω)))) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul]

variable [Module.Flat R R']

/-- **Naturality of the conormal map under flat formally étale base change.** -/
theorem kaehlerComparison_baseChange_conormalMap (w : baseExt I R' ⊗[R ⧸ I] I.Cotangent) :
    kaehlerComparison I R'
        (LinearMap.baseChange (baseExt I R') (AffineNormalCone.conormalMap k R I) w) =
      AffineNormalCone.conormalMap k R' (extIdeal I R') (cotangentComparison I R' w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b y =>
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I y
    rw [LinearMap.baseChange_tmul, AffineNormalCone.conormalMap_toCotangent,
      kaehlerComparison_tmul_one_tmul, cotangentComparison_tmul_toCotangent, map_smul,
      AffineNormalCone.conormalMap_toCotangent, KaehlerDifferential.map_D,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

end Kaehler

/-! ## The base-changed obstruction datum -/

section BaseChangeHom

variable {k : Type u} [CommRing k] [Algebra k R] [Algebra k R'] [IsScalarTower k R R']
variable [Module.Flat R R'] [Algebra.FormallyEtale R R']
variable {E : LinearTwoTermComplex (R ⧸ I)}

/-- **The base change of an affine obstruction datum along a flat formally étale extension.** -/
noncomputable def baseChangeHom (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    LinearTwoTermComplex.Hom (E.baseChange (baseExt I R'))
      (conormalComplex k R' (extIdeal I R')) where
  degreeZero :=
    (cotangentComparison I R').toLinearMap ∘ₗ
      LinearMap.baseChange (baseExt I R') φ.degreeZero
  degreeOne :=
    (kaehlerComparison I R').toLinearMap ∘ₗ LinearMap.baseChange (baseExt I R') φ.degreeOne
  comm z := by
    have hcomm : LinearMap.baseChange (baseExt I R') φ.degreeOne
        (LinearMap.baseChange (baseExt I R') E.differential z) =
        LinearMap.baseChange (baseExt I R') (AffineNormalCone.conormalMap k R I)
          (LinearMap.baseChange (baseExt I R') φ.degreeZero z) := by
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero, map_zero]
      | tmul b e =>
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          LinearMap.baseChange_tmul]
        exact congrArg (b ⊗ₜ ·) (φ.comm e)
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    change kaehlerComparison I R' (LinearMap.baseChange (baseExt I R') φ.degreeOne
      (LinearMap.baseChange (baseExt I R') E.differential z)) = _
    rw [hcomm, kaehlerComparison_baseChange_conormalMap]
    rfl

@[simp]
theorem baseChangeHom_degreeZero (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    (baseChangeHom I R' φ).degreeZero =
      (cotangentComparison I R').toLinearMap ∘ₗ
        LinearMap.baseChange (baseExt I R') φ.degreeZero :=
  rfl

@[simp]
theorem baseChangeHom_degreeOne (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    (baseChangeHom I R' φ).degreeOne =
      (kaehlerComparison I R').toLinearMap ∘ₗ
        LinearMap.baseChange (baseExt I R') φ.degreeOne :=
  rfl

/-- The degree-zero component of the base-changed datum on a generator `1 ⊗ e`. -/
theorem baseChangeHom_degreeZero_one_tmul
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) (e : E.degreeZero) :
    (baseChangeHom I R' φ).degreeZero ((1 : baseExt I R') ⊗ₜ e) =
      cotangentComparison I R' ((1 : baseExt I R') ⊗ₜ φ.degreeZero e) := by
  change cotangentComparison I R'
    (LinearMap.baseChange (baseExt I R') φ.degreeZero ((1 : baseExt I R') ⊗ₜ e)) = _
  rw [LinearMap.baseChange_tmul]

end BaseChangeHom

/-! ## Flat base change of the associated graded ring -/

section Graded

variable [Module.Flat R R']

/-- The flat base change of the associated graded ring, as an `R'`-algebra isomorphism.  It is
`Algebra.IsPushout.cancelBaseChangeAlg` followed by `AffineNormalCone.grTensorEquiv`. -/
noncomputable def grBaseExtEquivAux :
    baseExt I R' ⊗[R ⧸ I] AffineNormalCone.associatedGradedRing R I ≃ₐ[R']
      AffineNormalCone.associatedGradedRing R' (extIdeal I R') :=
  (Algebra.IsPushout.cancelBaseChangeAlg R R' (R ⧸ I) (baseExt I R')
      (AffineNormalCone.associatedGradedRing R I)).trans
    (AffineNormalCone.grTensorEquiv I (extIdeal I R') rfl)

/-- The auxiliary comparison on a pure tensor `1 ⊗ z`. -/
theorem grBaseExtEquivAux_one_tmul (z : AffineNormalCone.associatedGradedRing R I) :
    grBaseExtEquivAux I R' ((1 : baseExt I R') ⊗ₜ z) =
      AffineNormalCone.grMapOfEq I (algebraMap R R') (extIdeal I R') rfl z := by
  rw [grBaseExtEquivAux, AlgEquiv.trans_apply, Algebra.IsPushout.cancelBaseChangeAlg_tmul,
    AffineNormalCone.grTensorEquiv_one_tmul]

/-- **Flat base change of the associated graded ring**: `B' ⊗[B] gr_I(R) ≃ₐ[B'] gr_{I'}(R')`. -/
noncomputable def grBaseExtEquiv :
    baseExt I R' ⊗[R ⧸ I] AffineNormalCone.associatedGradedRing R I ≃ₐ[baseExt I R']
      AffineNormalCone.associatedGradedRing R' (extIdeal I R') :=
  AlgEquiv.ofRingEquiv (f := (grBaseExtEquivAux I R').toRingEquiv) fun b => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : algebraMap (baseExt I R')
        (baseExt I R' ⊗[R ⧸ I] AffineNormalCone.associatedGradedRing R I)
        (Ideal.Quotient.mk _ r) = algebraMap R' _ r :=
      (IsScalarTower.algebraMap_apply R' (baseExt I R') _ r).symm
    have h2 : algebraMap (baseExt I R')
        (AffineNormalCone.associatedGradedRing R' (extIdeal I R'))
        (Ideal.Quotient.mk _ r) = algebraMap R' _ r :=
      (IsScalarTower.algebraMap_apply R' (baseExt I R') _ r).symm
    change grBaseExtEquivAux I R' _ = _
    rw [h1, h2, AlgEquiv.commutes]

@[simp]
theorem grBaseExtEquiv_one_tmul (z : AffineNormalCone.associatedGradedRing R I) :
    grBaseExtEquiv I R' ((1 : baseExt I R') ⊗ₜ z) =
      AffineNormalCone.grMapOfEq I (algebraMap R R') (extIdeal I R') rfl z :=
  grBaseExtEquivAux_one_tmul I R' z

/-- **Naturality of `I/I² → gr_I(R)` under the base change.** -/
theorem grMapOfEq_conormalToAssociatedGraded (y : I.Cotangent) :
    AffineNormalCone.grMapOfEq I (algebraMap R R') (extIdeal I R') rfl
        (AffineNormalCone.conormalToAssociatedGraded R I y) =
      AffineNormalCone.conormalToAssociatedGraded R' (extIdeal I R')
        (cotangentComparison I R' ((1 : baseExt I R') ⊗ₜ y)) := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
  rw [AffineNormalCone.conormalToAssociatedGraded_toCotangent,
    cotangentComparison_tmul_toCotangent, one_smul,
    AffineNormalCone.conormalToAssociatedGraded_toCotangent,
    AffineNormalCone.grMapOfEq_mk, AffineNormalCone.reesMapOfEq_degreeOneRees]

end Graded

/-! ## The resolved cone of the base-changed datum -/

section ResolvedConeBaseChange

variable {k : Type u} [CommRing k] [Algebra k R] [Algebra k R'] [IsScalarTower k R R']
variable [Module.Flat R R'] [Algebra.FormallyEtale R R']
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- **Base change of the vector bundle `E₁`**: the coordinate ring of `E₁` over `Spec B'` is the
base change along `B → B'` of the coordinate ring of `E₁` over `Spec B`. -/
noncomputable def bundleRingEquiv :
    ResolvedCone.bundleRing (baseChangeHom I R' φ) ≃ₐ[baseExt I R']
      baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ :=
  GradedCone.baseChangeEquiv (R ⧸ I) E.degreeZero (baseExt I R')

/-- The base change of `E₁` on a generator `1 ⊗ e`. -/
theorem bundleRingEquiv_ι_one_tmul (e : E.degreeZero) :
    bundleRingEquiv I R' φ
        (SymmetricAlgebra.ι (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeZero)
          ((1 : baseExt I R') ⊗ₜ e)) =
      (1 : baseExt I R') ⊗ₜ SymmetricAlgebra.ι (R ⧸ I) E.degreeZero e := by
  rw [show bundleRingEquiv I R' φ
      (SymmetricAlgebra.ι (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeZero)
        ((1 : baseExt I R') ⊗ₜ e)) =
      LinearMap.baseChange (baseExt I R') (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero)
        ((1 : baseExt I R') ⊗ₜ e) from SymmetricAlgebra.lift_ι_apply _ _,
    LinearMap.baseChange_tmul]

omit [Algebra k R'] [IsScalarTower k R R'] [Module.Flat R R'] [Algebra.FormallyEtale R R'] in
/-- The base change of the bundle `E₀` on a generator `1 ⊗ w`. -/
theorem symBaseChangeEquiv_ι_one_tmul (w : E.degreeOne) :
    GradedCone.baseChangeEquiv (R ⧸ I) E.degreeOne (baseExt I R')
        (SymmetricAlgebra.ι (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeOne)
          ((1 : baseExt I R') ⊗ₜ w)) =
      (1 : baseExt I R') ⊗ₜ SymmetricAlgebra.ι (R ⧸ I) E.degreeOne w := by
  rw [show GradedCone.baseChangeEquiv (R ⧸ I) E.degreeOne (baseExt I R')
      (SymmetricAlgebra.ι (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeOne)
        ((1 : baseExt I R') ⊗ₜ w)) =
      LinearMap.baseChange (baseExt I R') (SymmetricAlgebra.ι (R ⧸ I) E.degreeOne)
        ((1 : baseExt I R') ⊗ₜ w) from SymmetricAlgebra.lift_ι_apply _ _,
    LinearMap.baseChange_tmul]

/-- **Base change of the coordinate ring of `C ×_X E₀`**:
`gr_{I'}(R') ⊗_{B'} Sym_{B'}(B' ⊗_B E⁰) ≃ₐ[B'] B' ⊗_B (gr_I(R) ⊗_B Sym_B(E⁰))`. -/
noncomputable def productRingEquiv :
    ResolvedCone.productRing (baseChangeHom I R' φ) ≃ₐ[baseExt I R']
      baseExt I R' ⊗[R ⧸ I] ResolvedCone.productRing φ :=
  (Algebra.TensorProduct.congr (grBaseExtEquiv I R').symm
      (AlgEquiv.refl (R := baseExt I R')
        (A₁ := SymmetricAlgebra (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeOne)))).trans <|
    (Algebra.TensorProduct.congr
        (AlgEquiv.refl (R := baseExt I R')
          (A₁ := baseExt I R' ⊗[R ⧸ I] AffineNormalCone.associatedGradedRing R I))
        (GradedCone.baseChangeEquiv (R ⧸ I) E.degreeOne (baseExt I R'))).trans <|
      (Algebra.TensorProduct.cancelBaseChange (R ⧸ I) (baseExt I R') (baseExt I R')
          (baseExt I R' ⊗[R ⧸ I] AffineNormalCone.associatedGradedRing R I)
          (SymmetricAlgebra (R ⧸ I) E.degreeOne)).trans
        (Algebra.TensorProduct.assoc (R := R ⧸ I) (S := R ⧸ I) (T := baseExt I R')
          (A := baseExt I R') (C := AffineNormalCone.associatedGradedRing R I)
          (D := SymmetricAlgebra (R ⧸ I) E.degreeOne))

/-- The comparison of product rings on the image of `gr_I(R)`. -/
theorem productRingEquiv_grMapOfEq_tmul_one (z : AffineNormalCone.associatedGradedRing R I) :
    productRingEquiv I R' φ
        (AffineNormalCone.grMapOfEq I (algebraMap R R') (extIdeal I R') rfl z ⊗ₜ
          (1 : SymmetricAlgebra (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeOne))) =
      (1 : baseExt I R') ⊗ₜ (z ⊗ₜ (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) := by
  have hz : (grBaseExtEquiv I R').symm
      (AffineNormalCone.grMapOfEq I (algebraMap R R') (extIdeal I R') rfl z) =
      (1 : baseExt I R') ⊗ₜ z := by
    rw [AlgEquiv.symm_apply_eq, grBaseExtEquiv_one_tmul]
  rw [productRingEquiv]
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, hz, map_one]
  rw [Algebra.TensorProduct.one_def (A := baseExt I R')
      (B := SymmetricAlgebra (R ⧸ I) E.degreeOne),
    Algebra.TensorProduct.cancelBaseChange_tmul, one_smul, Algebra.TensorProduct.assoc_tmul]

/-- The comparison of product rings on the image of a generator of `Sym(E⁰)`. -/
theorem productRingEquiv_one_tmul_ι (w : E.degreeOne) :
    productRingEquiv I R' φ
        ((1 : AffineNormalCone.associatedGradedRing R' (extIdeal I R')) ⊗ₜ
          SymmetricAlgebra.ι (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeOne)
            ((1 : baseExt I R') ⊗ₜ w)) =
      (1 : baseExt I R') ⊗ₜ ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ
        SymmetricAlgebra.ι (R ⧸ I) E.degreeOne w) := by
  rw [productRingEquiv]
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, map_one,
    symBaseChangeEquiv_ι_one_tmul]
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul,
    Algebra.TensorProduct.one_def (A := baseExt I R')
      (B := AffineNormalCone.associatedGradedRing R I),
    Algebra.TensorProduct.assoc_tmul]

/-- The base-change square for the product maps, on a generator `1 ⊗ e`. -/
theorem productRingEquiv_productMap_ι_one_tmul (e : E.degreeZero) :
    productRingEquiv I R' φ (ResolvedCone.productMap (baseChangeHom I R' φ)
        (SymmetricAlgebra.ι (baseExt I R') (baseExt I R' ⊗[R ⧸ I] E.degreeZero)
          ((1 : baseExt I R') ⊗ₜ e))) =
      Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
          (ResolvedCone.productMap φ)
        (bundleRingEquiv I R' φ (SymmetricAlgebra.ι (baseExt I R')
          (baseExt I R' ⊗[R ⧸ I] E.degreeZero) ((1 : baseExt I R') ⊗ₜ e))) := by
  have hd : (E.baseChange (baseExt I R')).differential ((1 : baseExt I R') ⊗ₜ e) =
      (1 : baseExt I R') ⊗ₜ E.differential e := LinearMap.baseChange_tmul _ _ _
  rw [ResolvedCone.productMap_ι, bundleRingEquiv_ι_one_tmul, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, ResolvedCone.productMap_ι, baseChangeHom_degreeZero_one_tmul, hd,
    ← grMapOfEq_conormalToAssociatedGraded, map_add, productRingEquiv_grMapOfEq_tmul_one,
    productRingEquiv_one_tmul_ι, TensorProduct.tmul_add]

/-- **The commuting square of product maps**: the resolved cone of the base-changed datum sits
inside the base change of the bundle in the same way as the original resolved cone. -/
theorem productRingEquiv_comp_productMap :
    (productRingEquiv I R' φ).toAlgHom.comp (ResolvedCone.productMap (baseChangeHom I R' φ)) =
      (Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
        (ResolvedCone.productMap φ)).comp (bundleRingEquiv I R' φ).toAlgHom := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul b e =>
    have hb : (b ⊗ₜ e : baseExt I R' ⊗[R ⧸ I] E.degreeZero) =
        b • ((1 : baseExt I R') ⊗ₜ e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, map_smul, map_smul]
    exact congrArg (b • ·) (productRingEquiv_productMap_ι_one_tmul I R' φ e)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### The ideal and the coordinate ring of the base-changed resolved cone -/

/-- The base change of the quotient map `Sym_B(E⁰) → ResolvedCone.ring φ`. -/
noncomputable abbrev tensorQuotMap :
    baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ →ₐ[baseExt I R']
      baseExt I R' ⊗[R ⧸ I] ResolvedCone.ring φ :=
  Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
    (Ideal.Quotient.mkₐ (R ⧸ I) (ResolvedCone.ideal φ))

omit [Algebra k R'] [IsScalarTower k R R'] [Module.Flat R R'] [Algebra.FormallyEtale R R'] in
/-- The kernel of the base-changed quotient map is the extension of `ResolvedCone.ideal φ`.  This
is `Algebra.TensorProduct.lTensor_ker`, which needs only surjectivity. -/
theorem ker_tensorQuotMap :
    RingHom.ker (tensorQuotMap I R' φ) =
      Ideal.map (Algebra.TensorProduct.includeRight :
        ResolvedCone.bundleRing φ →ₐ[R ⧸ I] baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ)
        (ResolvedCone.ideal φ) := by
  have h := Algebra.TensorProduct.lTensor_ker (A := baseExt I R')
    (Ideal.Quotient.mkₐ (R ⧸ I) (ResolvedCone.ideal φ)) Ideal.Quotient.mk_surjective
  rw [show RingHom.ker (Ideal.Quotient.mkₐ (R ⧸ I) (ResolvedCone.ideal φ)) =
    ResolvedCone.ideal φ from Ideal.mk_ker] at h
  exact h

omit [Algebra k R'] [IsScalarTower k R R'] [Algebra.FormallyEtale R R'] in
/-- Because `B'` is flat over `B`, the base change of the product map has the same kernel as the
base change of the quotient map: they differ by the injective map `ResolvedCone.toProduct φ`. -/
theorem ker_map_productMap :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
        (ResolvedCone.productMap φ)) =
      RingHom.ker (tensorQuotMap I R' φ) := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
        (ResolvedCone.toProduct φ)) := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap
      (R := R ⧸ I) (M := baseExt I R') (ResolvedCone.toProduct φ).toLinearMap
      (ResolvedCone.toProduct_injective φ)
    exact fun x y hxy => h hxy
  have hcomp : ∀ x, Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
      (ResolvedCone.productMap φ) x =
      Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
        (ResolvedCone.toProduct φ) (tensorQuotMap I R' φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul b a =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  ext x
  simp only [RingHom.mem_ker, hcomp]
  exact ⟨fun h => hinj (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- **Membership in the ideal of the base-changed resolved cone.** -/
theorem mem_ideal_baseChangeHom_iff (a : ResolvedCone.bundleRing (baseChangeHom I R' φ)) :
    a ∈ ResolvedCone.ideal (baseChangeHom I R' φ) ↔
      bundleRingEquiv I R' φ a ∈
        Ideal.map (Algebra.TensorProduct.includeRight :
          ResolvedCone.bundleRing φ →ₐ[R ⧸ I] baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ)
          (ResolvedCone.ideal φ) := by
  have hsq : productRingEquiv I R' φ (ResolvedCone.productMap (baseChangeHom I R' φ) a) =
      Algebra.TensorProduct.map (AlgHom.id (baseExt I R') (baseExt I R'))
        (ResolvedCone.productMap φ) (bundleRingEquiv I R' φ a) :=
    AlgHom.congr_fun (productRingEquiv_comp_productMap I R' φ) a
  rw [ResolvedCone.mem_ideal_iff, ← ker_tensorQuotMap, ← ker_map_productMap, RingHom.mem_ker,
    ← hsq, map_eq_zero_iff _ (productRingEquiv I R' φ).injective]

/-- **The ideal of the base-changed resolved cone is the extension of the ideal of the resolved
cone.** -/
theorem ideal_map_bundleRingEquiv :
    Ideal.map (bundleRingEquiv I R' φ) (ResolvedCone.ideal (baseChangeHom I R' φ)) =
      Ideal.map (Algebra.TensorProduct.includeRight :
        ResolvedCone.bundleRing φ →ₐ[R ⧸ I] baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ)
        (ResolvedCone.ideal φ) := by
  refine le_antisymm ?_ fun y hy => ?_
  · rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => (mem_ideal_baseChangeHom_iff I R' φ a).1 ha
  · have h : bundleRingEquiv I R' φ ((bundleRingEquiv I R' φ).symm y) = y :=
      (bundleRingEquiv I R' φ).apply_symm_apply y
    have h2 : (bundleRingEquiv I R' φ).symm y ∈ ResolvedCone.ideal (baseChangeHom I R' φ) :=
      (mem_ideal_baseChangeHom_iff I R' φ _).2 (by rw [h]; exact hy)
    exact h ▸ Ideal.mem_map_of_mem _ h2

omit [Algebra k R'] [IsScalarTower k R R'] [Module.Flat R R'] [Algebra.FormallyEtale R R'] in
/-- The base change of a surjection is surjective. -/
theorem surjective_tensorQuotMap : Function.Surjective (tensorQuotMap I R' φ) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b c =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨b ⊗ₜ a, rfl⟩
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, map_add _ _ _⟩

/-- **The resolved cone commutes with flat formally étale base change**:
`ResolvedCone.ring (baseChangeHom φ) ≃ₐ[B'] B' ⊗_B ResolvedCone.ring φ`. -/
noncomputable def ringEquiv :
    ResolvedCone.ring (baseChangeHom I R' φ) ≃ₐ[baseExt I R']
      baseExt I R' ⊗[R ⧸ I] ResolvedCone.ring φ :=
  (Ideal.quotientEquivAlg (ResolvedCone.ideal (baseChangeHom I R' φ))
      (RingHom.ker (tensorQuotMap I R' φ)) (bundleRingEquiv I R' φ)
      (by rw [ker_tensorQuotMap]; exact (ideal_map_bundleRingEquiv I R' φ).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_tensorQuotMap I R' φ))

@[simp]
theorem ringEquiv_mk (a : ResolvedCone.bundleRing (baseChangeHom I R' φ)) :
    ringEquiv I R' φ (Ideal.Quotient.mk (ResolvedCone.ideal (baseChangeHom I R' φ)) a) =
      tensorQuotMap I R' φ (bundleRingEquiv I R' φ a) :=
  rfl

/-! ### Specialisation to a localisation -/

/-- The canonical `B`-algebra map from the coordinate ring of the resolved cone to the coordinate
ring of the base-changed resolved cone. -/
noncomputable def coneMap :
    ResolvedCone.ring φ →ₐ[R ⧸ I] ResolvedCone.ring (baseChangeHom I R' φ) :=
  ((ringEquiv I R' φ).symm.toAlgHom.restrictScalars (R ⧸ I)).comp
    Algebra.TensorProduct.includeRight

/-- The algebra structure on the base-changed resolved cone over the original resolved cone. -/
noncomputable abbrev coneAlgebra :
    Algebra (ResolvedCone.ring φ) (ResolvedCone.ring (baseChangeHom I R' φ)) :=
  (coneMap I R' φ).toRingHom.toAlgebra

attribute [local instance] coneAlgebra

/-- The structure map of the algebra above is `coneMap`. -/
theorem coneAlgebraMap_eq (x : ResolvedCone.ring φ) :
    algebraMap (ResolvedCone.ring φ) (ResolvedCone.ring (baseChangeHom I R' φ)) x =
      coneMap I R' φ x :=
  rfl

/-- The comparison map is a map of `B`-algebras. -/
instance isScalarTowerCone :
    IsScalarTower (R ⧸ I) (ResolvedCone.ring φ) (ResolvedCone.ring (baseChangeHom I R' φ)) :=
  IsScalarTower.of_algebraMap_eq fun x => ((coneMap I R' φ).commutes x).symm

/-- **The square of resolved cones is a pushout**: `C(E)' = B' ⊗_B C(E)`. -/
instance isPushoutCone :
    Algebra.IsPushout (R ⧸ I) (baseExt I R') (ResolvedCone.ring φ)
      (ResolvedCone.ring (baseChangeHom I R' φ)) :=
  ⟨IsBaseChange.of_equiv (ringEquiv I R' φ).symm.toLinearEquiv fun _ => rfl⟩

/-- **The coordinate ring of the base-changed resolved cone is a localisation.**  If `R'` is the
localisation of `R` away from `f`, then `ResolvedCone.ring (baseChangeHom φ)` is the localisation
of `ResolvedCone.ring φ` away from the image of `f`.  This is the form in which the resolved cone
is glued over a basic-open cover of `Spec B` in the next wave. -/
theorem isLocalization_away_ring (f : R) [IsLocalization.Away f R'] :
    IsLocalization.Away (algebraMap (R ⧸ I) (ResolvedCone.ring φ) (algebraMap R (R ⧸ I) f))
      (ResolvedCone.ring (baseChangeHom I R' φ)) := by
  have hb : IsLocalization.Away (algebraMap R (R ⧸ I) f) (baseExt I R') :=
    isLocalization_away_baseExt I R' f
  have h : IsLocalization (Algebra.algebraMapSubmonoid (ResolvedCone.ring φ)
      (Submonoid.powers (algebraMap R (R ⧸ I) f))) (ResolvedCone.ring (baseChangeHom I R' φ)) :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers (algebraMap R (R ⧸ I) f))
      (baseExt I R') (T := ResolvedCone.ring φ)
      (B := ResolvedCone.ring (baseChangeHom I R' φ))).mpr
      (Algebra.IsPushout.symm (isPushoutCone I R' φ))
  rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h

end ResolvedConeBaseChange

end GromovWitten.AlgebraicGeometry.VirtualClass.LocalisationCone
