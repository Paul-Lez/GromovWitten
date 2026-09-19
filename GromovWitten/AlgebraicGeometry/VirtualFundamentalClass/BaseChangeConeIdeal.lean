/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeCone

/-!
# The ideal of the resolved cone after base change along `X × 𝔸^τ → X`

This file continues `VirtualFundamentalClass/BaseChangeCone.lean`.  With the notation of that
file (`R = k[x_σ]`, `A' = k[y_τ]`, `R' = A'[x_σ]`, `I ⊆ R`, `I' = I·R'`, `B = R/I`, `B' = R'/I'`)
it identifies the resolved cone of the base-changed obstruction datum `baseChangeHom τ I φ` with
the polynomial extension of the resolved cone of `φ`.

## Contents

* `BaseChangeCone.grPolyEquiv : gr_{I'}(R') ≃+* (gr_I R)[y_τ]` and its `B`-algebra form
  `BaseChangeCone.grPolyTensorEquiv : gr_{I'}(R') ≃ₐ[B] gr_I(R) ⊗_B B[y_τ]`, the trivialised base
  change of the associated graded ring, obtained from `NormalConeBaseChange.grBaseChangeEquiv`,
  `MvPolynomial.commAlgEquiv` and `MvPolynomial.algebraTensorAlgEquiv`.
* `BaseChangeCone.productRingEquiv`: the coordinate ring `gr_{I'}(R') ⊗_{B'} Sym_{B'}(E⁰ ⊗ B')`
  of `C ×_X E₀` after base change is the polynomial ring in `τ` variables over the coordinate
  ring `gr_I(R) ⊗_B Sym_B(E⁰)` of `C ×_X E₀`.
* `BaseChangeCone.productRingEquiv_productMap`: the commuting square relating the two product
  maps; consequently `BaseChangeCone.ideal_map_polyBundleRingEquiv` and
  `BaseChangeCone.ideal_map_bundleRingEquiv` compute the ideal of the base-changed resolved cone.
* `BaseChangeCone.ringEquiv : ResolvedCone.ring (baseChangeHom τ I φ) ≃+*
  MvPolynomial τ (ResolvedCone.ring φ)`, compatible with the quotient maps
  (`BaseChangeCone.ringEquiv_mk`, `BaseChangeCone.ringEquiv_comp_mk`); this is the ring-level
  form of the commuting square of closed immersions `C(E)' ↪ E₁'` and `C(E) ↪ E₁`.

Everything is stated for an arbitrary index type `τ : Type u`; finiteness is never used.
-/

universe u

set_option maxSynthPendingDepth 5
-- Tensor products of a graded ring with a symmetric algebra need a deeper instance search.

open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeCone

open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {k : Type u} [CommRing k] {σ : Type u} (τ : Type u) (I : Ideal (MvPolynomial σ k))

/-! ## The associated graded ring of the base change -/

section GradedBaseChange

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- `A' = k[y_τ]` is a flat `k`-module. -/
local instance flatCoeffExt : Module.Flat k (MvPolynomial τ k) := Module.Flat.of_free

/-- `R' = k[y_τ][x_σ]` is a flat `R = k[x_σ]`-module. -/
local instance flatAmbExt :
    Module.Flat (MvPolynomial σ k) (MvPolynomial σ (MvPolynomial τ k)) :=
  NormalConeBaseChange.flat_mvPolynomial (MvPolynomial τ k)

/-- The associated graded ring `gr_I(R)`. -/
abbrev grBase : Type u := AffineNormalCone.associatedGradedRing (MvPolynomial σ k) I

/-- The associated graded ring `gr_{I'}(R')` of the base change. -/
abbrev grExt : Type u :=
  AffineNormalCone.associatedGradedRing (MvPolynomial σ (MvPolynomial τ k)) (extIdeal τ I)

/-- The variable swap `R' = k[y_τ][x_σ] ≃ R[y_τ]`, as an `R`-algebra equivalence. -/
noncomputable def commAlgEquivAmb :
    MvPolynomial σ (MvPolynomial τ k) ≃ₐ[MvPolynomial σ k] MvPolynomial τ (MvPolynomial σ k) :=
  AlgEquiv.ofRingEquiv (f := (MvPolynomial.commAlgEquiv k σ τ).toRingEquiv)
    (fun p => commAlgEquiv_bcMap τ p)

/-- **The associated graded ring of the base change is a polynomial ring.** -/
noncomputable def grPolyEquiv : grExt τ I ≃+* MvPolynomial τ (grBase I) :=
  (NormalConeBaseChange.grBaseChangeEquiv (MvPolynomial τ k) I).symm.toRingEquiv.trans
    ((Algebra.TensorProduct.congr (commAlgEquivAmb τ)
        (AlgEquiv.refl (R := MvPolynomial σ k) (A₁ := grBase I))).toRingEquiv.trans
      ((Algebra.TensorProduct.comm (MvPolynomial σ k) (MvPolynomial τ (MvPolynomial σ k))
          (grBase I)).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k) (grBase I)).toRingEquiv))

/-- The trivialisation carries the comparison map `gr_I(R) → gr_{I'}(R')` to the constants. -/
theorem grPolyEquiv_grMap (z : grBase I) :
    grPolyEquiv τ I (NormalConeBaseChange.grMap (MvPolynomial τ k) I z) = MvPolynomial.C z := by
  have h : (NormalConeBaseChange.grBaseChangeEquiv (MvPolynomial τ k) I).symm
      (NormalConeBaseChange.grMap (MvPolynomial τ k) I z) =
      (1 : MvPolynomial σ (MvPolynomial τ k)) ⊗ₜ[MvPolynomial σ k] z := by
    rw [AlgEquiv.symm_apply_eq, NormalConeBaseChange.grBaseChangeEquiv_one_tmul]
  change (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k) (grBase I))
      ((Algebra.TensorProduct.comm _ _ _)
        ((Algebra.TensorProduct.congr (commAlgEquivAmb τ) (AlgEquiv.refl))
          ((NormalConeBaseChange.grBaseChangeEquiv (MvPolynomial τ k) I).symm _))) = _
  rw [h, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
    Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, map_one,
    Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]
  rfl

/-- The trivialisation on the image of the structure map of `R'`. -/
theorem grPolyEquiv_algebraMap (p : MvPolynomial σ (MvPolynomial τ k)) :
    grPolyEquiv τ I (algebraMap (MvPolynomial σ (MvPolynomial τ k)) (grExt τ I) p) =
      MvPolynomial.map (algebraMap (MvPolynomial σ k) (grBase I))
        (MvPolynomial.commAlgEquiv k σ τ p) := by
  have h : (NormalConeBaseChange.grBaseChangeEquiv (MvPolynomial τ k) I).symm
      (algebraMap (MvPolynomial σ (MvPolynomial τ k)) (grExt τ I) p) =
      p ⊗ₜ[MvPolynomial σ k] (1 : grBase I) := by
    rw [AlgEquiv.symm_apply_eq]
    exact ((NormalConeBaseChange.grBaseChangeEquiv (MvPolynomial τ k) I).commutes p).symm
  change (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k) (grBase I))
      ((Algebra.TensorProduct.comm _ _ _)
        ((Algebra.TensorProduct.congr (commAlgEquivAmb τ) (AlgEquiv.refl))
          ((NormalConeBaseChange.grBaseChangeEquiv (MvPolynomial τ k) I).symm _))) = _
  rw [h, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
    Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  rfl

/-- `gr_{I'}(R')` is an algebra over `B = R/I`, through the structure map `B → B'`. -/
noncomputable local instance algebraBaseGrExt :
    Algebra (MvPolynomial σ k ⧸ I) (grExt τ I) :=
  ((algebraMap (baseExt τ I) (grExt τ I)).comp
    (algebraMap (MvPolynomial σ k ⧸ I) (baseExt τ I))).toAlgebra

/-- The `B`-algebra structure on `gr_{I'}(R')` is the one induced from `B'`. -/
local instance isScalarTowerBaseGrExt :
    IsScalarTower (MvPolynomial σ k ⧸ I) (baseExt τ I) (grExt τ I) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The structure map of `gr_{I'}(R')` over `B'` on the class of a polynomial. -/
theorem algebraMap_grExt_mk (p : MvPolynomial σ (MvPolynomial τ k)) :
    algebraMap (baseExt τ I) (grExt τ I) (Ideal.Quotient.mk _ p) =
      algebraMap (MvPolynomial σ (MvPolynomial τ k)) (grExt τ I) p :=
  rfl

/-- Mathlib's isomorphism `(A/J)[y_τ] ≃ A[y_τ]/J·A[y_τ]` inverts the coefficientwise
projection. -/
theorem quotientEquivQuotientMvPolynomial_symm_mk {A : Type u} [CommRing A] (J : Ideal A)
    (q : MvPolynomial τ A) :
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) J).symm
        (Ideal.Quotient.mk _ q) = MvPolynomial.map (Ideal.Quotient.mk J) q := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

/-- The trivialisation `B' ≃ B[y_τ]` is the coefficientwise projection after the variable swap. -/
theorem baseRingEquiv_mk_map (p : MvPolynomial σ (MvPolynomial τ k)) :
    baseRingEquiv τ I (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (Ideal.Quotient.mk I) (MvPolynomial.commAlgEquiv k σ τ p) := by
  rw [baseRingEquiv_mk, quotientEquivQuotientMvPolynomial_symm_mk τ I]

/-- The trivialisation of `gr_{I'}(R')` is compatible with the trivialisation of `B'`. -/
theorem grPolyEquiv_algebraMap_baseExt (b : baseExt τ I) :
    grPolyEquiv τ I (algebraMap (baseExt τ I) (grExt τ I) b) =
      MvPolynomial.map (algebraMap (MvPolynomial σ k ⧸ I) (grBase I)) (baseRingEquiv τ I b) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [algebraMap_grExt_mk, grPolyEquiv_algebraMap, baseRingEquiv_mk_map, MvPolynomial.map_map]
  congr 1

/-- **The trivialisation of `gr_{I'}(R')` as a `B`-algebra equivalence** onto the base change
`gr_I(R) ⊗_B B[y_τ]`. -/
noncomputable def grPolyTensorEquiv :
    grExt τ I ≃ₐ[MvPolynomial σ k ⧸ I]
      grBase I ⊗[MvPolynomial σ k ⧸ I] MvPolynomial τ (MvPolynomial σ k ⧸ I) :=
  AlgEquiv.ofRingEquiv (f := (grPolyEquiv τ I).trans
      (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I) (grBase I)).symm.toRingEquiv)
    (by
      intro b
      change (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I) (grBase I)).symm
        (grPolyEquiv τ I (algebraMap (baseExt τ I) (grExt τ I)
          (algebraMap (MvPolynomial σ k ⧸ I) (baseExt τ I) b))) = _
      rw [grPolyEquiv_algebraMap_baseExt, baseRingEquiv_algebraMap, MvPolynomial.algebraMap_eq,
        MvPolynomial.map_C, AlgEquiv.symm_apply_eq, Algebra.TensorProduct.algebraMap_apply,
        MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, Algebra.smul_def, mul_one,
        MvPolynomial.algebraMap_eq])

/-- The trivialisation of `gr_{I'}(R')` on the image of `gr_I(R)`. -/
theorem grPolyTensorEquiv_grMap (z : grBase I) :
    grPolyTensorEquiv τ I (NormalConeBaseChange.grMap (MvPolynomial τ k) I z) =
      z ⊗ₜ[MvPolynomial σ k ⧸ I] 1 := by
  change (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I) (grBase I)).symm
    (grPolyEquiv τ I _) = _
  rw [grPolyEquiv_grMap, AlgEquiv.symm_apply_eq, MvPolynomial.algebraTensorAlgEquiv_tmul,
    map_one, Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]

/-- The trivialisation of `gr_{I'}(R')` on the image of `B'`. -/
theorem grPolyTensorEquiv_algebraMap (b : baseExt τ I) :
    grPolyTensorEquiv τ I (algebraMap (baseExt τ I) (grExt τ I) b) =
      (1 : grBase I) ⊗ₜ[MvPolynomial σ k ⧸ I] baseRingEquiv τ I b := by
  change (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I) (grBase I)).symm
    (grPolyEquiv τ I _) = _
  rw [grPolyEquiv_algebraMap_baseExt, AlgEquiv.symm_apply_eq,
    MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-! ## The coordinate ring of `C ×_X E₀` after base change -/

variable {E : LinearTwoTermComplex (MvPolynomial σ k ⧸ I)}

/-- Rearrangement of the base change of `gr_I(R) ⊗_B Sym_B(E⁰)`:
`(gr_I(R) ⊗_B B[y_τ]) ⊗_B Sym_B(E⁰) ≃ (gr_I(R) ⊗_B Sym_B(E⁰))[y_τ]`. -/
noncomputable def polyTensorRearrange :
    (grBase I ⊗[MvPolynomial σ k ⧸ I] MvPolynomial τ (MvPolynomial σ k ⧸ I))
        ⊗[MvPolynomial σ k ⧸ I] SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne
      ≃+*
      MvPolynomial τ (grBase I ⊗[MvPolynomial σ k ⧸ I]
        SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne) :=
  (Algebra.TensorProduct.assoc (R := MvPolynomial σ k ⧸ I) (S := MvPolynomial σ k ⧸ I)
      (A := grBase I) (MvPolynomial σ k ⧸ I) (MvPolynomial τ (MvPolynomial σ k ⧸ I))
      (SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)).toRingEquiv.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := MvPolynomial σ k ⧸ I) (A₁ := grBase I))
        (Algebra.TensorProduct.comm (MvPolynomial σ k ⧸ I)
          (MvPolynomial τ (MvPolynomial σ k ⧸ I))
          (SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne))).toRingEquiv.trans
      ((Algebra.TensorProduct.assoc (R := MvPolynomial σ k ⧸ I) (S := MvPolynomial σ k ⧸ I)
          (A := grBase I) (MvPolynomial σ k ⧸ I)
          (SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)
          (MvPolynomial τ (MvPolynomial σ k ⧸ I))).symm.toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I)
          (grBase I ⊗[MvPolynomial σ k ⧸ I]
            SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)).toRingEquiv))

/-- The rearrangement on a triple tensor. -/
theorem polyTensorRearrange_tmul (z : grBase I) (q : MvPolynomial τ (MvPolynomial σ k ⧸ I))
    (s : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne) :
    polyTensorRearrange τ I (E := E) ((z ⊗ₜ[MvPolynomial σ k ⧸ I] q) ⊗ₜ[MvPolynomial σ k ⧸ I] s) =
      (z ⊗ₜ[MvPolynomial σ k ⧸ I] s) •
        MvPolynomial.map (algebraMap (MvPolynomial σ k ⧸ I)
          (grBase I ⊗[MvPolynomial σ k ⧸ I]
            SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)) q := by
  change (MvPolynomial.algebraTensorAlgEquiv (MvPolynomial σ k ⧸ I) _)
    ((Algebra.TensorProduct.assoc (R := MvPolynomial σ k ⧸ I) (S := MvPolynomial σ k ⧸ I)
        (A := grBase I) (MvPolynomial σ k ⧸ I)
        (SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)
        (MvPolynomial τ (MvPolynomial σ k ⧸ I))).symm
      (z ⊗ₜ[MvPolynomial σ k ⧸ I] (s ⊗ₜ[MvPolynomial σ k ⧸ I] q))) = _
  rw [Algebra.TensorProduct.assoc_symm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- **The coordinate ring of `C ×_X E₀` after base change** is the polynomial ring in `τ`
variables over the coordinate ring of `C ×_X E₀`. -/
noncomputable def productRingEquiv
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    ResolvedCone.productRing (baseChangeHom τ I φ) ≃+*
      MvPolynomial τ (ResolvedCone.productRing φ) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := baseExt τ I) (A₁ := grExt τ I))
      (GradedCone.baseChangeEquiv (MvPolynomial σ k ⧸ I) E.degreeOne
        (baseExt τ I))).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange (R := MvPolynomial σ k ⧸ I) (S := baseExt τ I)
        (T := grExt τ I) (A := grExt τ I)
        (B := SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (grPolyTensorEquiv τ I)
          (AlgEquiv.refl (R := MvPolynomial σ k ⧸ I)
            (A₁ := SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne))).toRingEquiv.trans
        (polyTensorRearrange τ I (E := E))))

/-- The base change of the bundle `E₀` on a generator of the symmetric algebra. -/
theorem baseChangeEquiv_ι_one_tmul (w : E.degreeOne) :
    GradedCone.baseChangeEquiv (MvPolynomial σ k ⧸ I) E.degreeOne (baseExt τ I)
        (SymmetricAlgebra.ι (baseExt τ I)
          (baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeOne) ((1 : baseExt τ I) ⊗ₜ w)) =
      (1 : baseExt τ I) ⊗ₜ[MvPolynomial σ k ⧸ I]
        SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeOne w := by
  rw [show GradedCone.baseChangeEquiv (MvPolynomial σ k ⧸ I) E.degreeOne (baseExt τ I)
      (SymmetricAlgebra.ι (baseExt τ I)
        (baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeOne) ((1 : baseExt τ I) ⊗ₜ w)) =
      LinearMap.baseChange (baseExt τ I)
        (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeOne) ((1 : baseExt τ I) ⊗ₜ w) from
    SymmetricAlgebra.lift_ι_apply _ _, LinearMap.baseChange_tmul]

/-- The base change of the bundle `E₀` preserves the unit, written as a pure tensor. -/
theorem baseChangeEquiv_one :
    GradedCone.baseChangeEquiv (MvPolynomial σ k ⧸ I) E.degreeOne (baseExt τ I) 1 =
      (1 : baseExt τ I) ⊗ₜ[MvPolynomial σ k ⧸ I]
        (1 : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne) := by
  rw [map_one, Algebra.TensorProduct.one_def]

set_option maxHeartbeats 1000000 in
-- Tensor products of a graded ring with a symmetric algebra make the unifier work hard here.
/-- **The trivialisation of the coordinate ring of `C ×_X E₀` on a pure tensor.** -/
theorem productRingEquiv_tmul
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (g : grExt τ I)
    (t : SymmetricAlgebra (baseExt τ I) (baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeOne))
    (z : grBase I) (q : MvPolynomial τ (MvPolynomial σ k ⧸ I))
    (s : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)
    (ht : GradedCone.baseChangeEquiv (MvPolynomial σ k ⧸ I) E.degreeOne (baseExt τ I) t =
      (1 : baseExt τ I) ⊗ₜ[MvPolynomial σ k ⧸ I] s)
    (hg : grPolyTensorEquiv τ I g = z ⊗ₜ[MvPolynomial σ k ⧸ I] q) :
    productRingEquiv τ I φ (g ⊗ₜ[baseExt τ I] t) =
      (z ⊗ₜ[MvPolynomial σ k ⧸ I] s) •
        MvPolynomial.map (algebraMap (MvPolynomial σ k ⧸ I)
          (grBase I ⊗[MvPolynomial σ k ⧸ I]
            SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)) q := by
  have h1 : productRingEquiv τ I φ (g ⊗ₜ[baseExt τ I] t) =
      polyTensorRearrange τ I (E := E)
        ((Algebra.TensorProduct.congr (grPolyTensorEquiv τ I)
            (AlgEquiv.refl (R := MvPolynomial σ k ⧸ I)
              (A₁ := SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)))
          ((Algebra.TensorProduct.cancelBaseChange (R := MvPolynomial σ k ⧸ I)
              (S := baseExt τ I) (T := grExt τ I) (A := grExt τ I)
              (B := SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne))
            (g ⊗ₜ[baseExt τ I]
              (GradedCone.baseChangeEquiv (MvPolynomial σ k ⧸ I) E.degreeOne (baseExt τ I) t)))) :=
    rfl
  rw [h1, ht, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul,
    Algebra.TensorProduct.congr_apply]
  rw [Algebra.TensorProduct.map_tmul]
  rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, hg,
    polyTensorRearrange_tmul]

/-- The trivialisation on the image of `gr_I(R)`. -/
theorem productRingEquiv_grMap_tmul_one
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) (z : grBase I) :
    productRingEquiv τ I φ
        (NormalConeBaseChange.grMap (MvPolynomial τ k) I z ⊗ₜ[baseExt τ I] 1) =
      MvPolynomial.C (z ⊗ₜ[MvPolynomial σ k ⧸ I]
        (1 : SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne)) := by
  rw [productRingEquiv_tmul τ I φ _ _ z 1 1 (baseChangeEquiv_one τ I)
      (grPolyTensorEquiv_grMap τ I z), map_one, Algebra.smul_def, mul_one,
    MvPolynomial.algebraMap_eq]

/-- The trivialisation on a generator of the symmetric algebra of `E₀`. -/
theorem productRingEquiv_one_tmul_ι
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) (w : E.degreeOne) :
    productRingEquiv τ I φ
        ((1 : grExt τ I) ⊗ₜ[baseExt τ I]
          SymmetricAlgebra.ι (baseExt τ I)
            (baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeOne) ((1 : baseExt τ I) ⊗ₜ w)) =
      MvPolynomial.C ((1 : grBase I) ⊗ₜ[MvPolynomial σ k ⧸ I]
        SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeOne w) := by
  have hg : grPolyTensorEquiv τ I (1 : grExt τ I) =
      (1 : grBase I) ⊗ₜ[MvPolynomial σ k ⧸ I]
        (1 : MvPolynomial τ (MvPolynomial σ k ⧸ I)) := by
    rw [map_one, Algebra.TensorProduct.one_def]
  rw [productRingEquiv_tmul τ I φ _ _ 1 1 _ (baseChangeEquiv_ι_one_tmul τ I w) hg, map_one,
    Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]

/-- The trivialisation is compatible with the trivialisation `B' ≃ B[y_τ]` of the base. -/
theorem productRingEquiv_algebraMap
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (b : baseExt τ I) :
    productRingEquiv τ I φ
        (algebraMap (baseExt τ I) (ResolvedCone.productRing (baseChangeHom τ I φ)) b) =
      MvPolynomial.map (algebraMap (MvPolynomial σ k ⧸ I)
          (grBase I ⊗[MvPolynomial σ k ⧸ I]
            SymmetricAlgebra (MvPolynomial σ k ⧸ I) E.degreeOne))
        (baseRingEquiv τ I b) := by
  rw [Algebra.TensorProduct.algebraMap_apply,
    productRingEquiv_tmul τ I φ _ _ 1 (baseRingEquiv τ I b) 1 (baseChangeEquiv_one τ I)
      (grPolyTensorEquiv_algebraMap τ I b), Algebra.smul_def,
    ← Algebra.TensorProduct.one_def, map_one, one_mul]

/-! ## The commuting square of product maps -/

/-- **Naturality of the degree-one comparison map.**  The map `I/I² → gr_I(R)` commutes with the
base change of the conormal module and of the associated graded ring. -/
theorem grMap_conormalToAssociatedGraded (y : I.Cotangent) :
    NormalConeBaseChange.grMap (MvPolynomial τ k) I
        (AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ k) I y) =
      AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ (MvPolynomial τ k))
        (extIdeal τ I) (cotangentComparison τ I y) := by
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
  rw [AffineNormalCone.conormalToAssociatedGraded_toCotangent, cotangentComparison_toCotangent,
    AffineNormalCone.conormalToAssociatedGraded_toCotangent,
    NormalConeBaseChange.grMap_degreeOne]

/-- The product map of the base-changed datum on a generator `1 ⊗ x`. -/
theorem productMap_baseChangeHom_ι_one_tmul
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (e : E.degreeZero) :
    ResolvedCone.productMap (baseChangeHom τ I φ)
        (SymmetricAlgebra.ι (baseExt τ I)
          (baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeZero)
          ((1 : baseExt τ I) ⊗ₜ e)) =
      NormalConeBaseChange.grMap (MvPolynomial τ k) I
            (AffineNormalCone.conormalToAssociatedGraded (MvPolynomial σ k) I
              (φ.degreeZero e)) ⊗ₜ[baseExt τ I] 1 +
        (1 : grExt τ I) ⊗ₜ[baseExt τ I]
          SymmetricAlgebra.ι (baseExt τ I)
            (baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeOne)
            ((1 : baseExt τ I) ⊗ₜ E.differential e) := by
  have h0 : (baseChangeHom τ I φ).degreeZero ((1 : baseExt τ I) ⊗ₜ e) =
      cotangentComparison τ I (φ.degreeZero e) := by
    change baseChangeZero τ I φ ((1 : baseExt τ I) ⊗ₜ e) = _
    rw [baseChangeZero_tmul, one_smul]
  have h1 : (E.baseChange (baseExt τ I)).differential ((1 : baseExt τ I) ⊗ₜ e) =
      (1 : baseExt τ I) ⊗ₜ E.differential e := by
    rw [LinearTwoTermComplex.baseChange_differential, LinearMap.baseChange_tmul]
  rw [ResolvedCone.productMap_ι, h0, h1, ← grMap_conormalToAssociatedGraded]

/-- The trivialisation of the product ring carries the base-changed product map of a generator
to the constant polynomial with value the product map of the generator. -/
theorem productRingEquiv_productMap_ι_one_tmul
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (e : E.degreeZero) :
    productRingEquiv τ I φ
        (ResolvedCone.productMap (baseChangeHom τ I φ)
          (SymmetricAlgebra.ι (baseExt τ I)
            (baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeZero)
            ((1 : baseExt τ I) ⊗ₜ e))) =
      MvPolynomial.C (ResolvedCone.productMap φ
        (SymmetricAlgebra.ι (MvPolynomial σ k ⧸ I) E.degreeZero e)) := by
  rw [productMap_baseChangeHom_ι_one_tmul, map_add, productRingEquiv_grMap_tmul_one,
    productRingEquiv_one_tmul_ι, ← map_add, ResolvedCone.productMap_ι]

/-- The trivialisation of the bundle ring is compatible with the trivialisation `B' ≃ B[y_τ]`. -/
theorem polyBundleRingEquiv_algebraMap
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (b : baseExt τ I) :
    polyBundleRingEquiv τ I φ
        (algebraMap (baseExt τ I) (ResolvedCone.bundleRing (baseChangeHom τ I φ)) b) =
      MvPolynomial.map (algebraMap (MvPolynomial σ k ⧸ I) (ResolvedCone.bundleRing φ))
        (baseRingEquiv τ I b) := by
  have hb : bundleRingEquiv τ I φ
      (algebraMap (baseExt τ I) (ResolvedCone.bundleRing (baseChangeHom τ I φ)) b) =
      b ⊗ₜ[MvPolynomial σ k ⧸ I] (1 : ResolvedCone.bundleRing φ) :=
    (bundleRingEquiv τ I φ).commutes b
  change (MvPolynomial.algebraTensorAlgEquiv (σ := τ) (MvPolynomial σ k ⧸ I)
      (ResolvedCone.bundleRing φ))
      ((Algebra.TensorProduct.comm _ _ _)
        ((Algebra.TensorProduct.congr (baseAlgEquiv τ I) (AlgEquiv.refl))
          (bundleRingEquiv τ I φ _))) = _
  rw [hb, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
    Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  rfl

/-- The commuting square on the image of the base ring `B'`. -/
theorem productRingEquiv_productMap_algebraMap
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (b : baseExt τ I) :
    productRingEquiv τ I φ
        (ResolvedCone.productMap (baseChangeHom τ I φ)
          (algebraMap (baseExt τ I) (ResolvedCone.bundleRing (baseChangeHom τ I φ)) b)) =
      MvPolynomial.map (ResolvedCone.productMap φ).toRingHom
        (polyBundleRingEquiv τ I φ
          (algebraMap (baseExt τ I) (ResolvedCone.bundleRing (baseChangeHom τ I φ)) b)) := by
  have hcomp : (ResolvedCone.productMap φ).toRingHom.comp
      (algebraMap (MvPolynomial σ k ⧸ I) (ResolvedCone.bundleRing φ)) =
      algebraMap (MvPolynomial σ k ⧸ I) (ResolvedCone.productRing φ) :=
    (ResolvedCone.productMap φ).comp_algebraMap
  rw [AlgHom.commutes, productRingEquiv_algebraMap, polyBundleRingEquiv_algebraMap,
    MvPolynomial.map_map, hcomp]

/-- **The commuting square of product maps.**  Under the trivialisations of the bundle ring and
of the product ring, the product map of the base-changed obstruction datum is the coefficientwise
extension of the product map of `φ`. -/
theorem productRingEquiv_productMap
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (a : ResolvedCone.bundleRing (baseChangeHom τ I φ)) :
    productRingEquiv τ I φ (ResolvedCone.productMap (baseChangeHom τ I φ) a) =
      MvPolynomial.map (ResolvedCone.productMap φ).toRingHom (polyBundleRingEquiv τ I φ a) := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap b => exact productRingEquiv_productMap_algebraMap τ I φ b
  | ι x =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b e =>
      have hx : (b ⊗ₜ[MvPolynomial σ k ⧸ I] e :
          baseExt τ I ⊗[MvPolynomial σ k ⧸ I] E.degreeZero) =
          b • ((1 : baseExt τ I) ⊗ₜ[MvPolynomial σ k ⧸ I] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hx, map_smul, Algebra.smul_def]
      simp only [map_mul]
      rw [productRingEquiv_productMap_ι_one_tmul, productRingEquiv_productMap_algebraMap τ I φ b,
        polyBundleRingEquiv_ι_one_tmul, MvPolynomial.map_C]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-! ## The ideal of the resolved cone after base change -/

/-- Membership in the ideal of the base-changed resolved cone is detected, through the
trivialisation of the bundle ring, by the extended ideal of the resolved cone of `φ`. -/
theorem mem_ideal_baseChangeHom_iff
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (a : ResolvedCone.bundleRing (baseChangeHom τ I φ)) :
    a ∈ ResolvedCone.ideal (baseChangeHom τ I φ) ↔
      polyBundleRingEquiv τ I φ a ∈
        Ideal.map (MvPolynomial.C : ResolvedCone.bundleRing φ →+* _)
          (ResolvedCone.ideal φ) := by
  have hker : Ideal.map (MvPolynomial.C : ResolvedCone.bundleRing φ →+* _)
      (ResolvedCone.ideal φ) =
      RingHom.ker (MvPolynomial.map (σ := τ) (ResolvedCone.productMap φ).toRingHom) :=
    (MvPolynomial.ker_map _).symm
  rw [hker, RingHom.mem_ker, ← productRingEquiv_productMap, ResolvedCone.mem_ideal_iff]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (productRingEquiv τ I φ).injective (by rw [h, map_zero])

/-- **The ideal of the base-changed resolved cone is the extension of the ideal of the resolved
cone of `φ`**, under the trivialisation `Sym_{B'}(B' ⊗_B E⁻¹) ≃ Sym_B(E⁻¹)[y_τ]`. -/
theorem ideal_map_polyBundleRingEquiv
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    Ideal.map ((polyBundleRingEquiv τ I φ : ResolvedCone.bundleRing (baseChangeHom τ I φ) →+*
          MvPolynomial τ (ResolvedCone.bundleRing φ)))
        (ResolvedCone.ideal (baseChangeHom τ I φ)) =
      Ideal.map (MvPolynomial.C : ResolvedCone.bundleRing φ →+* _) (ResolvedCone.ideal φ) := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => (mem_ideal_baseChangeHom_iff τ I φ a).1 ha
  · intro x hx
    obtain ⟨a, rfl⟩ := (polyBundleRingEquiv τ I φ).surjective x
    exact Ideal.mem_map_of_mem _ ((mem_ideal_baseChangeHom_iff τ I φ a).2 hx)

/-- The tail of the trivialisation `polyBundleRingEquiv`: the base change of the bundle ring is
a polynomial ring over the bundle ring. -/
noncomputable def bundleTensorPolyEquiv
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ ≃+*
      MvPolynomial τ (ResolvedCone.bundleRing φ) :=
  (Algebra.TensorProduct.congr (baseAlgEquiv τ I)
      (AlgEquiv.refl (R := MvPolynomial σ k ⧸ I)
        (A₁ := ResolvedCone.bundleRing φ))).toRingEquiv.trans
    ((Algebra.TensorProduct.comm (MvPolynomial σ k ⧸ I)
        (MvPolynomial τ (MvPolynomial σ k ⧸ I)) (ResolvedCone.bundleRing φ)).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := τ) (MvPolynomial σ k ⧸ I)
        (ResolvedCone.bundleRing φ)).toRingEquiv)

/-- `polyBundleRingEquiv` factors through the base change of the bundle ring. -/
theorem polyBundleRingEquiv_eq
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    polyBundleRingEquiv τ I φ =
      (bundleRingEquiv τ I φ).toRingEquiv.trans (bundleTensorPolyEquiv τ I φ) :=
  rfl

/-- The tail of the trivialisation carries `1 ⊗ y` to the constant `y`. -/
theorem bundleTensorPolyEquiv_one_tmul
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (y : ResolvedCone.bundleRing φ) :
    bundleTensorPolyEquiv τ I φ ((1 : baseExt τ I) ⊗ₜ[MvPolynomial σ k ⧸ I] y) =
      MvPolynomial.C y := by
  change (MvPolynomial.algebraTensorAlgEquiv (σ := τ) (MvPolynomial σ k ⧸ I)
      (ResolvedCone.bundleRing φ))
      ((Algebra.TensorProduct.comm _ _ _)
        ((Algebra.TensorProduct.congr (baseAlgEquiv τ I) (AlgEquiv.refl)) _)) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
    Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, map_one,
    Algebra.smul_def, mul_one, MvPolynomial.algebraMap_eq]
  rfl

/-- **The ideal of the base-changed resolved cone is the extension of the ideal of the resolved
cone of `φ`**, in the tensor-product form `Sym_{B'}(B' ⊗_B E⁻¹) ≃ B' ⊗_B Sym_B(E⁻¹)`. -/
theorem ideal_map_bundleRingEquiv
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    Ideal.map ((bundleRingEquiv τ I φ : ResolvedCone.bundleRing (baseChangeHom τ I φ) →+*
          baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ))
        (ResolvedCone.ideal (baseChangeHom τ I φ)) =
      Ideal.map (Algebra.TensorProduct.includeRight :
          ResolvedCone.bundleRing φ →ₐ[MvPolynomial σ k ⧸ I]
            baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ).toRingHom
        (ResolvedCone.ideal φ) := by
  have hsymm : ((bundleTensorPolyEquiv τ I φ).symm :
        MvPolynomial τ (ResolvedCone.bundleRing φ) →+*
          baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ).comp
      ((bundleTensorPolyEquiv τ I φ :
        baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ →+*
          MvPolynomial τ (ResolvedCone.bundleRing φ))) = RingHom.id _ :=
    RingHom.ext fun x => (bundleTensorPolyEquiv τ I φ).symm_apply_apply x
  have hcomp : ((bundleTensorPolyEquiv τ I φ :
        baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ →+*
          MvPolynomial τ (ResolvedCone.bundleRing φ))).comp
      (Algebra.TensorProduct.includeRight :
        ResolvedCone.bundleRing φ →ₐ[MvPolynomial σ k ⧸ I]
          baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ).toRingHom =
      (MvPolynomial.C : ResolvedCone.bundleRing φ →+* _) :=
    RingHom.ext fun y => bundleTensorPolyEquiv_one_tmul τ I φ y
  have key : Ideal.map (bundleTensorPolyEquiv τ I φ :
          baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ →+*
            MvPolynomial τ (ResolvedCone.bundleRing φ))
        (Ideal.map ((bundleRingEquiv τ I φ : ResolvedCone.bundleRing (baseChangeHom τ I φ) →+*
            baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ))
          (ResolvedCone.ideal (baseChangeHom τ I φ))) =
      Ideal.map (bundleTensorPolyEquiv τ I φ :
          baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ →+*
            MvPolynomial τ (ResolvedCone.bundleRing φ))
        (Ideal.map (Algebra.TensorProduct.includeRight :
            ResolvedCone.bundleRing φ →ₐ[MvPolynomial σ k ⧸ I]
              baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ).toRingHom
          (ResolvedCone.ideal φ)) := by
    rw [Ideal.map_map, Ideal.map_map, hcomp, ← ideal_map_polyBundleRingEquiv τ I φ]
    rfl
  have h := congrArg (Ideal.map ((bundleTensorPolyEquiv τ I φ).symm :
    MvPolynomial τ (ResolvedCone.bundleRing φ) →+*
      baseExt τ I ⊗[MvPolynomial σ k ⧸ I] ResolvedCone.bundleRing φ)) key
  simp only [Ideal.map_map, ← RingHom.comp_assoc, hsymm, RingHom.id_comp] at h
  exact h

/-! ## The coordinate ring of the base-changed resolved cone -/

/-- **The coordinate ring of the resolved cone of the base change** is the polynomial ring in `τ`
variables over the coordinate ring of the resolved cone of `φ`. -/
noncomputable def ringEquiv
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    ResolvedCone.ring (baseChangeHom τ I φ) ≃+* MvPolynomial τ (ResolvedCone.ring φ) :=
  (Ideal.quotientEquiv (ResolvedCone.ideal (baseChangeHom τ I φ))
      (Ideal.map (MvPolynomial.C : ResolvedCone.bundleRing φ →+* _) (ResolvedCone.ideal φ))
      (polyBundleRingEquiv τ I φ) (ideal_map_polyBundleRingEquiv τ I φ).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ)
      (ResolvedCone.ideal φ)).symm.toRingEquiv

/-- **The closed immersion `C(E)' ↪ E₁'` is the polynomial extension of `C(E) ↪ E₁`.**  On
coordinate rings: the trivialisation of the coordinate ring of the resolved cone of the base
change is compatible with the trivialisation of the coordinate ring of the bundle. -/
theorem ringEquiv_mk
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I))
    (a : ResolvedCone.bundleRing (baseChangeHom τ I φ)) :
    ringEquiv τ I φ (Ideal.Quotient.mk (ResolvedCone.ideal (baseChangeHom τ I φ)) a) =
      MvPolynomial.map (Ideal.Quotient.mk (ResolvedCone.ideal φ))
        (polyBundleRingEquiv τ I φ a) := by
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := τ) (ResolvedCone.ideal φ)).symm
      (Ideal.Quotient.mk _ (polyBundleRingEquiv τ I φ a)) = _
  rw [quotientEquivQuotientMvPolynomial_symm_mk]

/-- The commuting square of the two closed immersions, as an equality of ring maps. -/
theorem ringEquiv_comp_mk
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k (MvPolynomial σ k) I)) :
    (ringEquiv τ I φ).toRingHom.comp
        (Ideal.Quotient.mk (ResolvedCone.ideal (baseChangeHom τ I φ))) =
      (MvPolynomial.map (Ideal.Quotient.mk (ResolvedCone.ideal φ))).comp
        (polyBundleRingEquiv τ I φ).toRingHom :=
  RingHom.ext fun a => ringEquiv_mk τ I φ a

end GradedBaseChange

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.BaseChangeCone
