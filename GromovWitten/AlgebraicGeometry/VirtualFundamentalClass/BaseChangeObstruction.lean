/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.LocalisationCone
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeCone
import GromovWitten.AlgebraicGeometry.ObstructionTheory.AffineCriterion

/-!
# Transfer of the obstruction-theory property along flat base change

`PicardCriteria.IsObstructionTheory φ` asks that `H⁰(φ)` be bijective and `H⁻¹(φ)` surjective.
`PicardCriteria.IsObstructionTheory.baseChange` already says that this property is preserved by
the degreewise base change `R' ⊗[R] φ` along an *arbitrary* `R`-algebra `R'`.  This file adds the
two pieces that the globalisation of the affine virtual class needs:

* the **converse** for a faithfully flat base change
  (`isObstructionTheory_of_baseChange`, `isObstructionTheory_baseChange_iff`);
* the identification of the geometric base changes
  `VirtualClass.LocalisationCone.baseChangeHom` (flat formally étale extension `R → R'`, e.g. a
  localisation `R' = Localization.Away f`) and
  `VirtualFundamentalClass.BaseChangeCone.baseChangeHom` (the polynomial extension modelling
  `Spec B × 𝔸^τ → Spec B`) with the degreewise base change, up to a *comparison chain map*
  of the two conormal complexes, so that the transfer applies to them.

## Main results

* `isObstructionTheory_of_comp_quasiIso`, `isObstructionTheory_of_quasiIso_comp`: being an
  obstruction theory is reflected by composition with a quasi-isomorphism (the converse of
  `PicardCriteria.IsObstructionTheory.comp_quasiIso` and `.quasiIso_comp`).
* `isObstructionTheory_baseChange_iff`: for `R'` a faithfully flat `R`-algebra,
  `IsObstructionTheory (φ.baseChange R') ↔ IsObstructionTheory φ`.
* `LocalisationCone.comparisonHom`, a quasi-isomorphism
  `(conormalComplex k R I).baseChange B' ⟶ conormalComplex k R' I'` whose two components are
  `LocalisationCone.cotangentComparison` and `LocalisationCone.kaehlerComparison`, and
  `LocalisationCone.baseChangeHom_eq_comp` saying that
  `LocalisationCone.baseChangeHom I R' φ` is `comparisonHom ∘ φ.baseChange B'`.
* `LocalisationCone.isObstructionTheory_baseChangeHom` and, for a faithfully flat `R → R'`,
  `LocalisationCone.isObstructionTheory_baseChangeHom_iff`.
* `Poly.baseChangeHom_eq_comp`, `Poly.isObstructionTheory_baseChangeHom` and
  `Poly.isObstructionTheory_baseChangeHom_iff`: the same for the polynomial base change
  `Spec B × 𝔸^τ → Spec B` of `VirtualFundamentalClass/BaseChangeCone.lean`.  Here the two
  comparison maps of round 16 are proved bijective: `Poly.bijective_baseChangeZero_id` is the
  flat base change `Poly.cotangentEquiv : B' ⊗[B] I/I² ≃ I'/I'²` of the conormal module, and
  `Poly.bijective_baseChangeOne_id` compares two free `B'`-modules on the `σ`-indexed basis of
  differentials of a polynomial ring (`KaehlerDifferential.mvPolynomialBasis`).  The converse
  direction assumes `[Nontrivial (MvPolynomial σ k ⧸ I)]`, which makes `B'` a nontrivial free,
  hence faithfully flat, `B`-module.

## Hypotheses

Every result is unconditional apart from the standing flatness/formal étaleness instances of
`VirtualFundamentalClass/LocalisationCone.lean`, the `Module.FaithfullyFlat` hypothesis in the
converse statements, and `[Nontrivial (MvPolynomial σ k ⧸ I)]` in the polynomial converse.  No
`sorry` and no new axioms.
-/

universe u

open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualClass.BaseChangeObstruction

open GromovWitten.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
open PicardCriteria LinearTwoTermComplex

/-! ## Reflection of the obstruction-theory property -/

section General

variable {R : Type u} [CommRing R] {E L : LinearTwoTermComplex R}

/-- **Composition with a quasi-isomorphism reflects the obstruction-theory property.**  This is
the converse of `PicardCriteria.IsObstructionTheory.comp_quasiIso`. -/
theorem isObstructionTheory_of_comp_quasiIso {L' : LinearTwoTermComplex R} {φ : Hom E L}
    {q : Hom L L'} (hq : q.IsQuasiIsomorphism) (h : IsObstructionTheory (q.comp φ)) :
    IsObstructionTheory φ := by
  obtain ⟨hcok, hker⟩ := h
  rw [Hom.cokernelMap_comp, LinearMap.coe_comp] at hcok
  rw [Hom.kernelMap_comp, LinearMap.coe_comp] at hker
  refine ⟨⟨fun a b hab => hcok.1 (congrArg q.cokernelMap hab), fun y => ?_⟩, fun y => ?_⟩
  · obtain ⟨x, hx⟩ := hcok.2 (q.cokernelMap y)
    exact ⟨x, hq.2.1 hx⟩
  · obtain ⟨x, hx⟩ := hker (q.kernelMap y)
    exact ⟨x, hq.1.1 hx⟩

/-- **Precomposition with a quasi-isomorphism reflects the obstruction-theory property.**  This
is the converse of `PicardCriteria.IsObstructionTheory.quasiIso_comp`. -/
theorem isObstructionTheory_of_quasiIso_comp {E' : LinearTwoTermComplex R} {φ : Hom E L}
    {q : Hom E' E} (hq : q.IsQuasiIsomorphism) (h : IsObstructionTheory (φ.comp q)) :
    IsObstructionTheory φ := by
  obtain ⟨hcok, hker⟩ := h
  rw [Hom.cokernelMap_comp, LinearMap.coe_comp] at hcok
  rw [Hom.kernelMap_comp, LinearMap.coe_comp] at hker
  refine ⟨⟨fun a b hab => ?_, fun y => ?_⟩, fun y => ?_⟩
  · obtain ⟨a', rfl⟩ := hq.2.2 a
    obtain ⟨b', rfl⟩ := hq.2.2 b
    exact congrArg q.cokernelMap (hcok.1 hab)
  · obtain ⟨x, hx⟩ := hcok.2 y
    exact ⟨q.cokernelMap x, hx⟩
  · obtain ⟨x, hx⟩ := hker y
    exact ⟨q.kernelMap x, hx⟩

/-- Two chain maps of two-term complexes with the same components are equal. -/
theorem hom_ext {F G : LinearTwoTermComplex R} {f g : Hom F G}
    (h0 : f.degreeZero = g.degreeZero) (h1 : f.degreeOne = g.degreeOne) : f = g := by
  cases f
  cases g
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

variable (R' : Type u) [CommRing R'] [Algebra R R']

/-- **A faithfully flat base change reflects the obstruction-theory property.**

The proof is the exact-sequence reformulation `PicardCriteria.isObstructionTheory_iff_exact_cone`
together with `Module.FaithfullyFlat.lTensor_exact_iff_exact`: a faithfully flat base change
reflects both the surjectivity of `coneBeta` and the exactness of the mapping-cone sequence. -/
theorem isObstructionTheory_of_baseChange [Module.FaithfullyFlat R R'] {φ : Hom E L}
    (h : IsObstructionTheory (φ.baseChange R')) : IsObstructionTheory φ := by
  obtain ⟨hsurj, hexact⟩ := h.exact_cone
  have hsurjT : Function.Surjective (LinearMap.lTensor R' (coneBeta φ)) := by
    intro z
    obtain ⟨w, hw⟩ := hsurj z
    refine ⟨(TensorProduct.prodRight R R' R' L.degreeZero E.degreeOne).symm w, ?_⟩
    rw [← coneBeta_baseChange R' φ, LinearEquiv.apply_symm_apply]
    exact hw
  have hexactT : Function.Exact (LinearMap.lTensor R' (coneAlpha φ))
      (LinearMap.lTensor R' (coneBeta φ)) := by
    intro z
    constructor
    · intro hz
      have hz' : coneBeta (φ.baseChange R')
          (TensorProduct.prodRight R R' R' L.degreeZero E.degreeOne z) = 0 := by
        rw [coneBeta_baseChange]
        exact hz
      obtain ⟨w, hw⟩ := (hexact _).1 hz'
      refine ⟨w, ?_⟩
      apply (TensorProduct.prodRight R R' R' L.degreeZero E.degreeOne).injective
      rw [← coneAlpha_baseChange]
      exact hw
    · rintro ⟨w, rfl⟩
      rw [← coneBeta_baseChange R' φ, ← coneAlpha_baseChange R' φ]
      exact (hexact _).2 ⟨w, rfl⟩
  exact isObstructionTheory_of_exact_cone
    ((Module.FaithfullyFlat.lTensor_surjective_iff_surjective R R' _).1 hsurjT)
    ((Module.FaithfullyFlat.lTensor_exact_iff_exact R R' _ _).1 hexactT)

/-- **Being an obstruction theory is invariant under faithfully flat base change.** -/
theorem isObstructionTheory_baseChange_iff [Module.FaithfullyFlat R R'] (φ : Hom E L) :
    IsObstructionTheory (φ.baseChange R') ↔ IsObstructionTheory φ :=
  ⟨isObstructionTheory_of_baseChange R', fun h => h.baseChange R'⟩

end General

/-! ## The flat formally étale base change of an affine obstruction datum -/

namespace LocalisationCone

open VirtualClass.LocalisationCone NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (R' : Type u) [CommRing R'] [Algebra R R']
variable {k : Type u} [CommRing k] [Algebra k R] [Algebra k R'] [IsScalarTower k R R']
variable [Algebra.FormallyEtale R R']

section Flat

variable [Module.Flat R R']

/-- **The comparison chain map** `(conormalComplex k R I).baseChange B' ⟶ conormalComplex k R' I'`
of a flat formally étale base change, with components
`VirtualClass.LocalisationCone.cotangentComparison` and
`VirtualClass.LocalisationCone.kaehlerComparison`.  It is a quasi-isomorphism because both
components are isomorphisms (`isQuasiIsomorphism_comparisonHom`). -/
noncomputable def comparisonHom :
    LinearTwoTermComplex.Hom ((conormalComplex k R I).baseChange (baseExt I R'))
      (conormalComplex k R' (extIdeal I R')) where
  degreeZero := (cotangentComparison I R').toLinearMap
  degreeOne := (kaehlerComparison I R').toLinearMap
  comm z := kaehlerComparison_baseChange_conormalMap I R' z

@[simp]
theorem comparisonHom_degreeZero :
    (comparisonHom I R' (k := k)).degreeZero = (cotangentComparison I R').toLinearMap :=
  rfl

@[simp]
theorem comparisonHom_degreeOne :
    (comparisonHom I R' (k := k)).degreeOne = (kaehlerComparison I R').toLinearMap :=
  rfl

/-- The comparison chain map is a quasi-isomorphism: both of its components are isomorphisms. -/
theorem isQuasiIsomorphism_comparisonHom :
    (comparisonHom I R' (k := k)).IsQuasiIsomorphism :=
  LinearTwoTermComplex.QuasiIsoSplitting.isQuasiIsomorphism_of_bijective
    (cotangentComparison I R').bijective (kaehlerComparison I R').bijective

variable {E : LinearTwoTermComplex (R ⧸ I)}

/-- **The base-changed obstruction datum is the degreewise base change followed by the
comparison quasi-isomorphism.** -/
theorem baseChangeHom_eq_comp (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    VirtualClass.LocalisationCone.baseChangeHom I R' φ =
      (comparisonHom I R').comp (φ.baseChange (baseExt I R')) :=
  rfl

/-- **The obstruction-theory property is preserved by a flat formally étale base change.** -/
theorem isObstructionTheory_baseChangeHom
    {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)} (h : IsObstructionTheory φ) :
    IsObstructionTheory (VirtualClass.LocalisationCone.baseChangeHom I R' φ) := by
  rw [baseChangeHom_eq_comp]
  exact (h.baseChange (baseExt I R')).comp_quasiIso (isQuasiIsomorphism_comparisonHom I R')

end Flat

section FaithfullyFlat

variable [Module.FaithfullyFlat R R']

/-- `B' = R' ⧸ I R'` is faithfully flat over `B = R ⧸ I` as soon as `R'` is faithfully flat over
`R`: it is the base change `B ⊗[R] R'` by
`VirtualClass.LocalisationCone.baseExtTensorEquiv`. -/
instance faithfullyFlat_baseExt :
    Module.FaithfullyFlat (R ⧸ I) (baseExt I R') :=
  Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) ((R ⧸ I) ⊗[R] R')
    (baseExtTensorEquiv I R').toLinearEquiv

variable {E : LinearTwoTermComplex (R ⧸ I)}

/-- **The converse for a faithfully flat base change.** -/
theorem isObstructionTheory_of_baseChangeHom
    {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
    (h : IsObstructionTheory (VirtualClass.LocalisationCone.baseChangeHom I R' φ)) :
    IsObstructionTheory φ := by
  rw [baseChangeHom_eq_comp] at h
  exact isObstructionTheory_of_baseChange (baseExt I R')
    (isObstructionTheory_of_comp_quasiIso (isQuasiIsomorphism_comparisonHom I R') h)

/-- **The obstruction-theory property is detected by a faithfully flat formally étale base
change.** -/
theorem isObstructionTheory_baseChangeHom_iff
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    IsObstructionTheory (VirtualClass.LocalisationCone.baseChangeHom I R' φ) ↔
      IsObstructionTheory φ :=
  ⟨isObstructionTheory_of_baseChangeHom I R', isObstructionTheory_baseChangeHom I R'⟩

end FaithfullyFlat

end LocalisationCone

/-! ## The polynomial base change of an affine obstruction datum -/

namespace Poly

open VirtualFundamentalClass.BaseChangeCone NormalSheafPicard.AffineIntrinsicNormalSheaf

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {k : Type u} [CommRing k] {σ : Type u} (τ : Type u) (I : Ideal (MvPolynomial σ k))

/-- **The comparison chain map of the polynomial base change**, the base change of the identity
of the conormal complex.  Its components are `BaseChangeCone.baseChangeZero τ I (Hom.id _)`,
that is `B' ⊗[B] I/I² → I'/I'²`, and `BaseChangeCone.baseChangeOne τ I (Hom.id _)`, that is
`B' ⊗[B] (B ⊗[R] Ω[R⁄k]) → B' ⊗[R'] Ω[R'⁄A']`. -/
noncomputable abbrev comparisonHom :
    LinearTwoTermComplex.Hom
      ((conormalComplex k (MvPolynomial σ k) I).baseChange (baseExt τ I))
      (conormalComplex (MvPolynomial τ k) (MvPolynomial σ (MvPolynomial τ k)) (extIdeal τ I)) :=
  VirtualFundamentalClass.BaseChangeCone.baseChangeHom τ I
    (LinearTwoTermComplex.Hom.id (conormalComplex k (MvPolynomial σ k) I))

variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}

/-- **The polynomially base-changed obstruction datum is the degreewise base change followed by
the comparison chain map.** -/
theorem baseChangeHom_eq_comp
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    VirtualFundamentalClass.BaseChangeCone.baseChangeHom τ I φ =
      (comparisonHom τ I).comp (φ.baseChange (baseExt τ I)) := by
  refine hom_ext (LinearMap.ext fun z => ?_) (LinearMap.ext fun z => ?_)
  · induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x e =>
      change baseChangeZero τ I φ (x ⊗ₜ e) =
        baseChangeZero τ I (LinearTwoTermComplex.Hom.id _)
          (LinearMap.baseChange (baseExt τ I) φ.degreeZero (x ⊗ₜ e))
      rw [LinearMap.baseChange_tmul, baseChangeZero_tmul, baseChangeZero_tmul]
      rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  · induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x e =>
      change baseChangeOne τ I φ (x ⊗ₜ e) =
        baseChangeOne τ I (LinearTwoTermComplex.Hom.id _)
          (LinearMap.baseChange (baseExt τ I) φ.degreeOne (x ⊗ₜ e))
      rw [LinearMap.baseChange_tmul, baseChangeOne_tmul, baseChangeOne_tmul]
      rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw]

/-! ### Bijectivity of the Kähler comparison -/

/-- The basis `{1 ⊗ dx_i}` of `B ⊗[R] Ω[R⁄k]`, coming from the basis of differentials of a
polynomial ring. -/
noncomputable def kaehlerBasisBase : Module.Basis σ (MvPolynomial σ k ⧸ I)
    ((MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k]) :=
  (KaehlerDifferential.mvPolynomialBasis k σ).baseChange _

/-- The basis `{1 ⊗ 1 ⊗ dx_i}` of the source `B' ⊗[B] (B ⊗[R] Ω[R⁄k])` of the Kähler
comparison. -/
noncomputable def kaehlerBasisSource : Module.Basis σ (baseExt τ I)
    (baseExt τ I ⊗[MvPolynomial σ k ⧸ I]
      ((MvPolynomial σ k ⧸ I) ⊗[MvPolynomial σ k] Ω[MvPolynomial σ k⁄k])) :=
  (kaehlerBasisBase I).baseChange _

/-- The basis `{1 ⊗ dx_i}` of the target `B' ⊗[R'] Ω[R'⁄A']` of the Kähler comparison. -/
noncomputable def kaehlerBasisTarget : Module.Basis σ (baseExt τ I) (kaehlerExt τ I) :=
  (KaehlerDifferential.mvPolynomialBasis (MvPolynomial τ k) σ).baseChange _

/-- **The Kähler comparison of the polynomial base change is bijective**: both sides are free
`B'`-modules on the `σ`-indexed basis of differentials, and the map matches the two bases. -/
theorem bijective_baseChangeOne_id :
    Function.Bijective (baseChangeOne τ I
      (LinearTwoTermComplex.Hom.id (conormalComplex k (MvPolynomial σ k) I))) := by
  have key : baseChangeOne τ I
      (LinearTwoTermComplex.Hom.id (conormalComplex k (MvPolynomial σ k) I)) =
      ((kaehlerBasisSource τ I).equiv (kaehlerBasisTarget τ I) (Equiv.refl σ)).toLinearMap := by
    refine (kaehlerBasisSource τ I).ext fun i => ?_
    have hs : kaehlerBasisSource τ I i =
        (1 : baseExt τ I) ⊗ₜ[MvPolynomial σ k ⧸ I] kaehlerBasisBase I i :=
      Module.Basis.baseChange_apply _ _ _
    have hb : kaehlerBasisBase I i = (1 : MvPolynomial σ k ⧸ I) ⊗ₜ[MvPolynomial σ k]
        KaehlerDifferential.mvPolynomialBasis k σ i :=
      Module.Basis.baseChange_apply _ _ _
    have ht : kaehlerBasisTarget τ I i = (1 : baseExt τ I) ⊗ₜ[MvPolynomial σ (MvPolynomial τ k)]
        KaehlerDifferential.mvPolynomialBasis (MvPolynomial τ k) σ i :=
      Module.Basis.baseChange_apply _ _ _
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, hs, hb, ht,
      baseChangeOne_tmul, one_smul]
    change kaehlerComparison τ I ((1 : MvPolynomial σ k ⧸ I) ⊗ₜ
      KaehlerDifferential.mvPolynomialBasis k σ i) = _
    rw [kaehlerComparison_one_tmul, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
    congr 2
    exact MvPolynomial.map_X _ i
  rw [key]
  exact ((kaehlerBasisSource τ I).equiv (kaehlerBasisTarget τ I) (Equiv.refl σ)).bijective

/-! ### Bijectivity of the conormal comparison -/

section Cotangent

/-- `R' = k[y_τ][x_σ]` is a flat `R = k[x_σ]`-module. -/
local instance flatAmbExt :
    Module.Flat (MvPolynomial σ k) (MvPolynomial σ (MvPolynomial τ k)) :=
  NormalConeBaseChange.flat_mvPolynomial (MvPolynomial τ k)

/-- The scalar tower `R → B → B'` for the polynomial base change. -/
instance isScalarTowerBaseExt :
    IsScalarTower (MvPolynomial σ k) (MvPolynomial σ k ⧸ I) (baseExt τ I) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The extension of `I` along the structure map `R → R'` is `BaseChangeCone.extIdeal`; the two
differ only by the unfolding of `NormalConeBaseChange.bcMap`. -/
theorem extIdeal_eq_map :
    Ideal.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ (MvPolynomial τ k))) I =
      extIdeal τ I := by
  rw [MvPolynomial.algebraMap_def]
  rfl

/-- **Flat base change of the conormal module along `R → R'`**: `B' ⊗[B] I/I² ≃ I'/I'²`.  This is
the polynomial-extension analogue of `VirtualClass.LocalisationCone.cotangentComparison`. -/
noncomputable def cotangentEquiv :
    baseExt τ I ⊗[MvPolynomial σ k ⧸ I] I.Cotangent ≃ₗ[baseExt τ I] (extIdeal τ I).Cotangent :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (baseExt τ I) (baseExt τ I))
      (AffineNormalCone.quotTensorIdealEquiv (MvPolynomial σ k) I).symm).trans <|
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (MvPolynomial σ k)
        (MvPolynomial σ k ⧸ I) (baseExt τ I) (baseExt τ I) I).trans <|
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (MvPolynomial σ k)
          (MvPolynomial σ (MvPolynomial τ k)) (baseExt τ I) (baseExt τ I) I).symm).trans <|
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (baseExt τ I) (baseExt τ I))
            (AffineNormalCone.idealTensorEquiv I (extIdeal τ I) (extIdeal_eq_map τ I))).trans
          (AffineNormalCone.quotTensorIdealEquiv (MvPolynomial σ (MvPolynomial τ k))
            (extIdeal τ I))

@[simp]
theorem cotangentEquiv_tmul_toCotangent (b : baseExt τ I) (x : I) :
    cotangentEquiv τ I (b ⊗ₜ Ideal.toCotangent I x) =
      b • Ideal.toCotangent (extIdeal τ I)
        ⟨NormalConeBaseChange.bcMap (MvPolynomial τ k) (x : MvPolynomial σ k),
          Ideal.mem_map_of_mem _ x.2⟩ := by
  have h1 : (AffineNormalCone.quotTensorIdealEquiv (MvPolynomial σ k) I).symm
      (Ideal.toCotangent I x) = (1 : MvPolynomial σ k ⧸ I) ⊗ₜ x := by
    rw [LinearEquiv.symm_apply_eq, AffineNormalCone.quotTensorIdealEquiv_one_tmul]
  have h2 : AffineNormalCone.idealTensorEquiv I (extIdeal τ I) (extIdeal_eq_map τ I)
      ((1 : MvPolynomial σ (MvPolynomial τ k)) ⊗ₜ x) =
      ⟨NormalConeBaseChange.bcMap (MvPolynomial τ k) (x : MvPolynomial σ k),
        Ideal.mem_map_of_mem _ x.2⟩ := by
    rw [AffineNormalCone.idealTensorEquiv_one_tmul]
    rfl
  have h3 : AffineNormalCone.quotTensorIdealEquiv (MvPolynomial σ (MvPolynomial τ k))
      (extIdeal τ I) (b ⊗ₜ (⟨NormalConeBaseChange.bcMap (MvPolynomial τ k)
        (x : MvPolynomial σ k), Ideal.mem_map_of_mem _ x.2⟩ : extIdeal τ I)) =
      b • Ideal.toCotangent (extIdeal τ I)
        ⟨NormalConeBaseChange.bcMap (MvPolynomial τ k) (x : MvPolynomial σ k),
          Ideal.mem_map_of_mem _ x.2⟩ := by
    rw [show (b ⊗ₜ (⟨NormalConeBaseChange.bcMap (MvPolynomial τ k) (x : MvPolynomial σ k),
          Ideal.mem_map_of_mem _ x.2⟩ : extIdeal τ I)) =
        b • ((1 : baseExt τ I) ⊗ₜ
          (⟨NormalConeBaseChange.bcMap (MvPolynomial τ k) (x : MvPolynomial σ k),
            Ideal.mem_map_of_mem _ x.2⟩ : extIdeal τ I)) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
      AffineNormalCone.quotTensorIdealEquiv_one_tmul]
  change AffineNormalCone.quotTensorIdealEquiv (MvPolynomial σ (MvPolynomial τ k)) (extIdeal τ I)
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (baseExt τ I) (baseExt τ I))
      (AffineNormalCone.idealTensorEquiv I (extIdeal τ I) (extIdeal_eq_map τ I))
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange (MvPolynomial σ k)
          (MvPolynomial σ (MvPolynomial τ k)) (baseExt τ I) (baseExt τ I) I).symm
        (TensorProduct.AlgebraTensorModule.cancelBaseChange (MvPolynomial σ k)
            (MvPolynomial σ k ⧸ I) (baseExt τ I) (baseExt τ I) I
          (TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl (baseExt τ I) (baseExt τ I))
            (AffineNormalCone.quotTensorIdealEquiv (MvPolynomial σ k) I).symm
            (b ⊗ₜ Ideal.toCotangent I x))))) = _
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h1,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h2, h3]

/-- **The conormal comparison of the polynomial base change is bijective**: it is the flat base
change `cotangentEquiv` of the conormal module. -/
theorem bijective_baseChangeZero_id :
    Function.Bijective (baseChangeZero τ I
      (LinearTwoTermComplex.Hom.id (conormalComplex k (MvPolynomial σ k) I))) := by
  have key : baseChangeZero τ I
      (LinearTwoTermComplex.Hom.id (conormalComplex k (MvPolynomial σ k) I)) =
      (cotangentEquiv τ I).toLinearMap := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul b y =>
      obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I y
      rw [baseChangeZero_tmul]
      change b • cotangentComparison τ I (Ideal.toCotangent I x) = _
      rw [cotangentComparison_toCotangent, LinearEquiv.coe_coe,
        cotangentEquiv_tmul_toCotangent]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  rw [key]
  exact (cotangentEquiv τ I).bijective

end Cotangent

/-- The comparison chain map of the polynomial base change is a quasi-isomorphism. -/
theorem isQuasiIsomorphism_comparisonHom : (comparisonHom τ I).IsQuasiIsomorphism :=
  LinearTwoTermComplex.QuasiIsoSplitting.isQuasiIsomorphism_of_bijective
    (bijective_baseChangeZero_id τ I) (bijective_baseChangeOne_id τ I)

/-- **Transfer of the obstruction-theory property to the polynomial base change.** -/
theorem isObstructionTheory_baseChangeHom
    {φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)}
    (h : IsObstructionTheory φ) :
    IsObstructionTheory (VirtualFundamentalClass.BaseChangeCone.baseChangeHom τ I φ) := by
  rw [baseChangeHom_eq_comp]
  exact (h.baseChange (baseExt τ I)).comp_quasiIso (isQuasiIsomorphism_comparisonHom τ I)

/-- `B' = R' ⧸ I R'` is nontrivial as soon as `B = R ⧸ I` is: it is the polynomial ring
`B[y_τ]` by `BaseChangeCone.baseAlgEquiv`. -/
instance nontrivial_baseExt [Nontrivial (MvPolynomial σ k ⧸ I)] : Nontrivial (baseExt τ I) :=
  (baseAlgEquiv τ I).toEquiv.nontrivial

/-- `B'` is faithfully flat over `B`: it is a nontrivial free `B`-module. -/
instance faithfullyFlat_baseExt [Nontrivial (MvPolynomial σ k ⧸ I)] :
    Module.FaithfullyFlat (MvPolynomial σ k ⧸ I) (baseExt τ I) :=
  inferInstance

/-- **The converse of `isObstructionTheory_baseChangeHom`.** -/
theorem isObstructionTheory_of_baseChangeHom [Nontrivial (MvPolynomial σ k ⧸ I)]
    {φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)}
    (h : IsObstructionTheory (VirtualFundamentalClass.BaseChangeCone.baseChangeHom τ I φ)) :
    IsObstructionTheory φ := by
  rw [baseChangeHom_eq_comp] at h
  exact isObstructionTheory_of_baseChange (baseExt τ I)
    (isObstructionTheory_of_comp_quasiIso (isQuasiIsomorphism_comparisonHom τ I) h)

/-- **The obstruction-theory property is detected by the polynomial base change.** -/
theorem isObstructionTheory_baseChangeHom_iff [Nontrivial (MvPolynomial σ k ⧸ I)]
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    IsObstructionTheory (VirtualFundamentalClass.BaseChangeCone.baseChangeHom τ I φ) ↔
      IsObstructionTheory φ :=
  ⟨isObstructionTheory_of_baseChangeHom τ I, isObstructionTheory_baseChangeHom τ I⟩

end Poly

end GromovWitten.AlgebraicGeometry.VirtualClass.BaseChangeObstruction

