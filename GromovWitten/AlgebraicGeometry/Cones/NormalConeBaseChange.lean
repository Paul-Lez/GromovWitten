/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.NormalConeAction
import GromovWitten.AlgebraicGeometry.Cones.NormalConeDimension
import GromovWitten.Algebra.DimensionFormula
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Scalar extension of the affine normal cone and of its tangent action

Let `A → A'` be a flat ring map — the case of interest is a field extension `k ⊆ k'` — let
`R = A[x_σ]`, `R' = A'[x_σ]`, let `I ⊆ R` be an ideal and let `I' = I R'` be its extension.  This
file proves that the affine local model of the intrinsic normal cone built in
`Cones/ConeTranslation.lean` and `Cones/NormalConeAction.lean` is unchanged by the scalar
extension.

## Contents

* `NormalConeBaseChange.flat_mvPolynomial`: `R'` is flat over `R` (base change of flatness along
  `A → R`, using Mathlib's pushout instance `Algebra.IsPushout A R A' R'`).
* `NormalConeBaseChange.grBaseChangeEquiv`: `gr_{I'}(R') ≃ₐ[R'] R' ⊗_R gr_I(R)`, an instance of
  `AffineNormalCone.grTensorEquiv`, with `grBaseChangeEquiv_one_tmul` identifying the induced map
  `NormalConeBaseChange.grMap` on the degree-zero and degree-one parts
  (`grMap_algebraMap`, `grMap_degreeOne`).
* `NormalConeBaseChange.taylor_map`: the Taylor derivation commutes with the extension of
  coefficients, whence `NormalConeBaseChange.coaction_comp_grMap`: **the tangent coaction of the
  affine normal cone is unchanged by scalar extension**.
* `NormalConeBaseChange.translatePoint_grMap`: consequently the action on `B`-points is
  unchanged: translating over `R'` and restricting along `gr_I(R) → gr_{I'}(R')` is translating
  over `R`, for the same tangent vector `v : σ → B`.
* `NormalConeBaseChange.pointEquiv` and `NormalConeBaseChange.pointEquiv_translatePoint`: the
  objects of the two quotient groupoids correspond (universal property of the base change), and
  the bijection intertwines the actions.  The arrows of either groupoid are tangent vectors
  `σ → B` with the translation law `ConeTranslation.translatePoint`
  (`NormalConeBaseChange.translatePoint_of_hom`, `NormalConeBaseChange.homOfTranslatePoint`,
  `NormalConeBaseChange.hom_ext_of_coords`), because the restricted tangent bundle is free on the
  coordinate differentials on both sides: Kähler differentials of polynomial rings commute with
  base change, and `NormalConeAction.tangentBasis` is the corresponding basis in both cases.

What is *not* packaged here is the assembly of these bijections into a functor
`[C'/T'](B) ⥤ [C/T](B)`: that requires an `R/I`-algebra structure on `R'/I'` and on `B` and the
corresponding scalar towers, plumbing which belongs with the global layer.  The compatibility of
the scalar extension with the closed immersions `Sym(I/I²) ↠ gr_I(R)` of
`Cones/NormalConeAction.lean` is likewise not recorded; `AffineNormalCone.nsToGr_naturality` in
`Cones/NormalConeGlobal.lean` is the corresponding statement for `normalSheafRing`.

## Dimensions

For `σ` finite and `A = k` a field, `NormalConeBaseChange.finrank_tangent` says that the
restricted tangent bundle is free of rank `#σ` over `R/I`, and
`NormalConeBaseChange.ringKrullDim_gr` that `dim gr_I(R) = #σ` for a proper ideal `I`
(`GromovWitten.Algebra.NormalCone.ringKrullDim_associatedGradedRing'` together with
`dim k[x_σ] = #σ`).  Hence `NormalConeBaseChange.normalCone_dim_sub_rank_eq_zero`: the two
numbers attached to the presentation `[C_{U/M}/T_M|_U]` — the dimension of the cone and the rank
of the acting bundle — differ by zero.  No new notion of stack dimension is introduced.
-/

open CategoryTheory TensorProduct

namespace GromovWitten.AlgebraicGeometry

namespace NormalConeBaseChange

universe u

open ConeTranslation ConeQuotient GradedCone AffineNormalCone NormalConeAction

variable {A : Type u} [CommRing A] {σ : Type u} (A' : Type u) [CommRing A'] [Algebra A A']

/-- The extension of coefficients `R = A[x_σ] → R' = A'[x_σ]`.  It is used as a plain ring
homomorphism: making it the structure map of an algebra requires the local instance
`MvPolynomial.algebraMvPolynomial`, which is only switched on in the last section, because it
would otherwise be selected for `Algebra R (MvPolynomial σ (gr_I R))` and clash with the instance
used in `Cones/ConeTranslation.lean`. -/
noncomputable def bcMap : MvPolynomial σ A →+* MvPolynomial σ A' :=
  MvPolynomial.map (algebraMap A A')

@[simp]
theorem bcMap_C (a : A) :
    bcMap (σ := σ) A' (MvPolynomial.C a) = MvPolynomial.C (algebraMap A A' a) :=
  MvPolynomial.map_C _ _

@[simp]
theorem bcMap_X (i : σ) : bcMap A' (MvPolynomial.X i : MvPolynomial σ A) = MvPolynomial.X i :=
  MvPolynomial.map_X _ _

variable (I : Ideal (MvPolynomial σ A))

/-- The extension `I R'` of `I` to the polynomial ring over `A'`. -/
noncomputable abbrev extIdeal : Ideal (MvPolynomial σ A') := I.map (bcMap A')

/-! ## Base change of the associated graded ring -/

/-- The map `gr_I(R) → gr_{I'}(R')` induced by the coefficient extension. -/
noncomputable def grMap : Gr I →+* Gr (extIdeal A' I) :=
  AffineNormalCone.grMapOfEq I (bcMap A') (extIdeal A' I) rfl

@[simp]
theorem grMap_algebraMap (r : MvPolynomial σ A) :
    grMap A' I (algebraMap (MvPolynomial σ A) (Gr I) r) =
      algebraMap (MvPolynomial σ A') (Gr (extIdeal A' I)) (bcMap A' r) :=
  AffineNormalCone.grMapOfEq_algebraMap I (bcMap A') (extIdeal A' I) rfl r

@[simp]
theorem grMap_degreeOne (x : I) :
    grMap A' I (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (MvPolynomial σ A) I x)) =
      Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (MvPolynomial σ A') (extIdeal A' I)
        ⟨bcMap A' (x : MvPolynomial σ A), Ideal.mem_map_of_mem _ x.2⟩) := by
  change AffineNormalCone.grMapOfEq I (bcMap A') (extIdeal A' I) rfl
      (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (MvPolynomial σ A) I x)) = _
  rw [AffineNormalCone.grMapOfEq_mk, AffineNormalCone.reesMapOfEq_degreeOneRees]

/-! ## Base change of the Taylor derivation and of the tangent coaction -/

/-- **The Taylor derivation commutes with the extension of coefficients.**  Both sides are
computed from the coordinate partial derivatives, which do not see the coefficient ring. -/
theorem taylor_map (x : MvPolynomial σ A) :
    taylor A' σ (bcMap A' x) = MvPolynomial.map (bcMap A') (taylor A σ x) := by
  induction x using MvPolynomial.induction_on with
  | C a => rw [bcMap_C, taylor_C, taylor_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, bcMap_X, taylor_mul, taylor_mul, map_add, map_mul, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_C, taylor_X, taylor_X, MvPolynomial.map_X, hp, bcMap_X]

/-- **The tangent coaction of the affine normal cone is unchanged by scalar extension.**

The coaction `[f t] ↦ [f t] + Σ_i ε_i [∂_i f]` of `Cones/ConeTranslation.lean` commutes with the
map `gr_I(R) → gr_{I'}(R')`, because the Taylor derivation does. -/
theorem coaction_comp_grMap (z : Gr I) :
    coaction (extIdeal A' I) (grMap A' I z) =
      MvPolynomial.map (grMap A' I) (coaction I z) := by
  have halg : ((algebraMap (MvPolynomial σ A') (Gr (extIdeal A' I))).comp (bcMap A') :
        MvPolynomial σ A →+* Gr (extIdeal A' I)) =
      (grMap A' I).comp (algebraMap (MvPolynomial σ A) (Gr I)) :=
    RingHom.ext fun r => (grMap_algebraMap A' I r).symm
  have key : ((coaction (extIdeal A' I)).toRingHom.comp (grMap A' I) :
        Gr I →+* MvPolynomial σ (Gr (extIdeal A' I))) =
      (MvPolynomial.map (grMap A' I)).comp (coaction I).toRingHom := by
    refine gr_ringHom_ext I (fun r => ?_) fun x => ?_
    · change coaction (extIdeal A' I) (grMap A' I (algebraMap (MvPolynomial σ A) (Gr I) r)) =
        MvPolynomial.map (grMap A' I) (coaction I (algebraMap (MvPolynomial σ A) (Gr I) r))
      rw [grMap_algebraMap, coaction_algebraMap, coaction_algebraMap, MvPolynomial.map_C,
        grMap_algebraMap]
    · change coaction (extIdeal A' I) (grMap A' I
          (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (MvPolynomial σ A) I x))) =
        MvPolynomial.map (grMap A' I) (coaction I
          (Ideal.Quotient.mk _ (AffineNormalCone.degreeOneRees (MvPolynomial σ A) I x)))
      rw [grMap_degreeOne, coaction_degreeOne, coaction_degreeOne, map_add, MvPolynomial.map_C,
        grMap_degreeOne, MvPolynomial.map_map, taylor_map, MvPolynomial.map_map, halg]
  exact RingHom.congr_fun key z

/-- **The action on points is unchanged by scalar extension.**  Translating a `B`-point of the
normal cone over `R'` by a tangent vector `v` and restricting it along `gr_I(R) → gr_{I'}(R')` is
translating the restricted point by the same `v`. -/
theorem translatePoint_grMap {B : Type u} [CommRing B] (φ : Gr (extIdeal A' I) →+* B)
    (v : σ → B) :
    (translatePoint (extIdeal A' I) φ v).comp (grMap A' I) =
      translatePoint I (φ.comp (grMap A' I)) v := by
  refine RingHom.ext fun z => ?_
  change MvPolynomial.eval₂Hom φ v (coaction (extIdeal A' I) (grMap A' I z)) =
    MvPolynomial.eval₂Hom (φ.comp (grMap A' I)) v (coaction I z)
  rw [coaction_comp_grMap, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_map]

/-! ## Flat base change of the associated graded ring -/

section Flat

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **Flatness lifts to the polynomial rings.**  `A'[x_σ]` is the base change of `A'` along
`A → A[x_σ]`, so it is flat over `A[x_σ]` as soon as `A'` is flat over `A`. -/
theorem flat_mvPolynomial [Module.Flat A A'] :
    Module.Flat (MvPolynomial σ A) (MvPolynomial σ A') :=
  Module.Flat.isBaseChange A (MvPolynomial σ A) A' (MvPolynomial σ A')
    (Algebra.IsPushout.out (R := A) (S := MvPolynomial σ A) (R' := A') (S' := MvPolynomial σ A'))

/-- **Scalar extension of the affine normal cone.**  For a flat extension of coefficients,
`gr_{I'}(R')` is the base change of `gr_I(R)` along `R → R'`; this is
`AffineNormalCone.grTensorEquiv`, whose proof is that the Rees algebra commutes with flat base
change. -/
noncomputable def grBaseChangeEquiv [Module.Flat (MvPolynomial σ A) (MvPolynomial σ A')] :
    MvPolynomial σ A' ⊗[MvPolynomial σ A] Gr I ≃ₐ[MvPolynomial σ A'] Gr (extIdeal A' I) :=
  AffineNormalCone.grTensorEquiv I (extIdeal A' I) rfl

/-- The comparison isomorphism restricts on `1 ⊗ -` to the map `NormalConeBaseChange.grMap`. -/
theorem grBaseChangeEquiv_one_tmul
    [Module.Flat (MvPolynomial σ A) (MvPolynomial σ A')] (z : Gr I) :
    grBaseChangeEquiv A' I ((1 : MvPolynomial σ A') ⊗ₜ[MvPolynomial σ A] z) = grMap A' I z :=
  AffineNormalCone.grTensorEquiv_one_tmul I (extIdeal A' I) rfl z

/-- The comparison isomorphism on a general pure tensor. -/
theorem grBaseChangeEquiv_tmul [Module.Flat (MvPolynomial σ A) (MvPolynomial σ A')]
    (b : MvPolynomial σ A') (z : Gr I) :
    grBaseChangeEquiv A' I (b ⊗ₜ[MvPolynomial σ A] z) =
      algebraMap (MvPolynomial σ A') (Gr (extIdeal A' I)) b * grMap A' I z := by
  have h : (b ⊗ₜ[MvPolynomial σ A] z : MvPolynomial σ A' ⊗[MvPolynomial σ A] Gr I) =
      (b ⊗ₜ[MvPolynomial σ A] (1 : Gr I)) *
        ((1 : MvPolynomial σ A') ⊗ₜ[MvPolynomial σ A] z) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hb : algebraMap (MvPolynomial σ A') (MvPolynomial σ A' ⊗[MvPolynomial σ A] Gr I) b =
      b ⊗ₜ[MvPolynomial σ A] (1 : Gr I) := rfl
  rw [h, map_mul, grBaseChangeEquiv_one_tmul, ← hb, AlgEquiv.commutes]

/-- **Objects of the two quotient groupoids correspond.**

By the universal property of the base change `gr_{I'}(R') = R' ⊗_R gr_I(R)`, restriction along
`NormalConeBaseChange.grMap` is a bijection from the `R'`-algebra maps out of `gr_{I'}(R')` to
the `R`-algebra maps out of `gr_I(R)`.  Since `R ↠ R/I` and `R' ↠ R'/I'` are surjective, these
are exactly the objects of the two quotient groupoids `[C/T](B)` and `[C'/T'](B)`. -/
noncomputable def pointEquiv [Module.Flat (MvPolynomial σ A) (MvPolynomial σ A')]
    (B : Type u) [CommRing B] [Algebra (MvPolynomial σ A) B] [Algebra (MvPolynomial σ A') B]
    [IsScalarTower (MvPolynomial σ A) (MvPolynomial σ A') B] :
    (Gr (extIdeal A' I) →ₐ[MvPolynomial σ A'] B) ≃ (Gr I →ₐ[MvPolynomial σ A] B) where
  toFun f :=
    { toRingHom := (f : Gr (extIdeal A' I) →+* B).comp (grMap A' I)
      commutes' := fun r => by
        change f (grMap A' I (algebraMap (MvPolynomial σ A) (Gr I) r)) = _
        rw [grMap_algebraMap, f.commutes]
        exact (IsScalarTower.algebraMap_apply (MvPolynomial σ A) (MvPolynomial σ A') B r).symm }
  invFun g :=
    (Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ A') B) g
      fun _ _ => Commute.all _ _).comp (grBaseChangeEquiv A' I).symm.toAlgHom
  left_inv f := by
    refine AlgHom.ext fun w => ?_
    obtain ⟨u, rfl⟩ := (grBaseChangeEquiv A' I).surjective w
    change Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ A') B) _
      (fun _ _ => Commute.all _ _) ((grBaseChangeEquiv A' I).symm
        (grBaseChangeEquiv A' I u)) = _
    rw [AlgEquiv.symm_apply_apply]
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul b z =>
      rw [Algebra.TensorProduct.lift_tmul, grBaseChangeEquiv_tmul, map_mul, AlgHom.commutes]
      rfl
    | add x y hx hy =>
      have he : grBaseChangeEquiv A' I (x + y) =
          grBaseChangeEquiv A' I x + grBaseChangeEquiv A' I y :=
        (grBaseChangeEquiv A' I).map_add x y
      rw [map_add, hx, hy, he, map_add]
  right_inv g := by
    refine AlgHom.ext fun z => ?_
    change Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ A') B) g
      (fun _ _ => Commute.all _ _) ((grBaseChangeEquiv A' I).symm (grMap A' I z)) = _
    have hz : (grBaseChangeEquiv A' I).symm (grMap A' I z) =
        (1 : MvPolynomial σ A') ⊗ₜ[MvPolynomial σ A] z := by
      rw [AlgEquiv.symm_apply_eq, grBaseChangeEquiv_one_tmul]
    rw [hz, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- **The bijection of objects intertwines the tangent actions.**  Together with
`NormalConeBaseChange.translatePoint_of_hom` and `NormalConeBaseChange.homOfTranslatePoint` —
which describe the arrows of either quotient groupoid as tangent vectors `σ → B` — this says that
the two quotient groupoids `[C'/T'](B)` and `[C/T](B)` have the same objects, the same arrows and
the same translation law. -/
theorem pointEquiv_translatePoint [Module.Flat (MvPolynomial σ A) (MvPolynomial σ A')]
    (B : Type u) [CommRing B] [Algebra (MvPolynomial σ A) B] [Algebra (MvPolynomial σ A') B]
    [IsScalarTower (MvPolynomial σ A) (MvPolynomial σ A') B]
    (f : Gr (extIdeal A' I) →ₐ[MvPolynomial σ A'] B) (v : σ → B) :
    translatePoint I ((pointEquiv A' I B f : Gr I →ₐ[MvPolynomial σ A] B) : Gr I →+* B) v =
      (translatePoint (extIdeal A' I) (f : Gr (extIdeal A' I) →+* B) v).comp (grMap A' I) :=
  (translatePoint_grMap A' I (f : Gr (extIdeal A' I) →+* B) v).symm

/-- The bijection of objects is restriction along `gr_I(R) → gr_{I'}(R')`. -/
theorem pointEquiv_apply [Module.Flat (MvPolynomial σ A) (MvPolynomial σ A')]
    (B : Type u) [CommRing B] [Algebra (MvPolynomial σ A) B] [Algebra (MvPolynomial σ A') B]
    [IsScalarTower (MvPolynomial σ A) (MvPolynomial σ A') B]
    (f : Gr (extIdeal A' I) →ₐ[MvPolynomial σ A'] B) (z : Gr I) :
    pointEquiv A' I B f z = f (grMap A' I z) :=
  rfl

end Flat

/-! ## Arrows of the quotient groupoid are tangent vectors -/

section Arrows

variable {A₀ : Type u} [CommRing A₀] {σ₀ : Type u} (J : Ideal (MvPolynomial σ₀ A₀))
  {B : Type u} [CommRing B] [Algebra (Base J) B]

/-- **An arrow of `[C_{U/M}/T_M|_U](B)` is a tangent vector `σ → B`**, and its translation law is
`ConeTranslation.translatePoint`.  Together with
`NormalConeBaseChange.translatePoint_grMap` this says that the groupoid data over `R` and over
`R'` is literally the same: the same index set `σ` of tangent coordinates and the same
translation law. -/
theorem translatePoint_of_hom {x y : QuotientGroupoid (normalConeAction J) B} (f : x ⟶ y) :
    translatePoint J (x.point : Gr J →+* B) (fun i => f.val (tangentBasis J i)) =
      (y.point : Gr J →+* B) := by
  rw [← translate_act_ringHom]
  exact congrArg (fun z : Gr J →ₐ[Base J] B => (z : Gr J →+* B)) f.translate_eq

/-- Conversely, a tangent vector satisfying the translation law is an arrow. -/
noncomputable def homOfTranslatePoint {x y : QuotientGroupoid (normalConeAction J) B}
    (v : σ₀ → B)
    (hv : translatePoint J (x.point : Gr J →+* B) v = (y.point : Gr J →+* B)) : x ⟶ y where
  val := (tangentBasis J).constr B v
  translate_eq := by
    refine AlgHom.ext fun z => ?_
    have hval : (fun i => ((tangentBasis J).constr B v) (tangentBasis J i)) = v := by
      funext i
      rw [Module.Basis.constr_basis]
    have h := translate_act_ringHom (I := J) x.point ((tangentBasis J).constr B v)
    rw [hval] at h
    exact RingHom.congr_fun (h.trans hv) z

/-- The tangent-coordinate description of an arrow is faithful. -/
theorem hom_ext_of_coords {x y : QuotientGroupoid (normalConeAction J) B} (f g : x ⟶ y)
    (h : ∀ i, f.val (tangentBasis J i) = g.val (tangentBasis J i)) : f = g :=
  QuotientGroupoid.Hom.ext ((tangentBasis J).ext h)

end Arrows

/-! ## Dimensions in the polynomial model over a field -/

section Dimension

variable {k : Type u} [Field k] {τ : Type u} [Fintype τ] (J : Ideal (MvPolynomial τ k))

/-- **The restricted tangent bundle is free of rank `#σ`** over `R/I`: it has the basis
`NormalConeAction.tangentBasis` of coordinate differentials. -/
theorem finrank_tangent (hJ : J ≠ ⊤) :
    Module.finrank (Base J) (Tangent J) = Fintype.card τ := by
  have _ : Nontrivial (Base J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  exact Module.finrank_eq_card_basis (tangentBasis J)

/-- The polynomial ring in `#σ` variables over a field has Krull dimension `#σ`. -/
theorem ringKrullDim_mvPolynomial :
    ringKrullDim (MvPolynomial τ k) = (Fintype.card τ : ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- **The affine normal cone of a proper ideal of `k[x_σ]` has Krull dimension `#σ`.**  This is
`GromovWitten.Algebra.ringKrullDim_associatedGradedRing'` applied to the polynomial
ring, whose dimension is `#σ`. -/
theorem ringKrullDim_gr (hJ : J ≠ ⊤) :
    ringKrullDim (Gr J) = (Fintype.card τ : ℕ∞) :=
  GromovWitten.Algebra.ringKrullDim_associatedGradedRing' k J hJ _
    (ringKrullDim_mvPolynomial (k := k) (τ := τ))

/-- **The presentation `[C_{U/M}/T_M|_U]` has dimension zero.**

The affine normal cone has Krull dimension `#σ` (`ringKrullDim_gr`) and the acting tangent bundle
has rank `#σ` (`finrank_tangent`), so the difference of the two numbers attached to the
presentation — the dimension of the cone minus the rank of the bundle — is zero.  No new notion
of stack dimension is introduced: this is a statement about those two integers. -/
theorem normalCone_dim_sub_rank_eq_zero (hJ : J ≠ ⊤) :
    (Fintype.card τ : ℤ) - (Module.finrank (Base J) (Tangent J) : ℤ) = 0 := by
  rw [finrank_tangent J hJ, sub_self]

end Dimension

end NormalConeBaseChange

end GromovWitten.AlgebraicGeometry
