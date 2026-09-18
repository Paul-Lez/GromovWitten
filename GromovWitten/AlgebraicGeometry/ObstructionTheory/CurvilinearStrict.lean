/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.Curvilinear

/-!
# The strict curvilinear obstruction cone

`ObstructionTheory/Curvilinear.lean` constructs the curvilinear extensions
`κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)` but cannot feed them to the obstruction machinery: applying the
square-zero deformation API of `CotangentComplex/SquareZero.lean` to the *concrete* iterated
quotient `κ[t]/(tⁿ⁺¹)` runs into a typeclass diamond, because `Semiring` and `SMul` on a quotient
ring have several non-reducibly-equal instance paths while the API instantiates a `[CommRing B]`
variable.

This file removes the obstacle in the standard way: the ambient ring stays a **variable** `B`, and
being curvilinear is a *property with data* recorded by the class `SquareZero.IsCurvilinear`, an
isomorphism `B ≃ₐ[κ] κ[t]/(tⁿ⁺¹)` carrying `M` onto `(tⁿ)/(tⁿ⁺¹)`.  Every instance then comes from
the variables exactly as in `SquareZero.lean`, so `Lift R M P.Ring`, `obstructionE` and
`SquareZero.curvilinearObstructionAt` elaborate.

## Contents

* `SquareZero.IsCurvilinear κ M`: the curvilinear structure, with its order (`SquareZero.curvOrder`)
  and its identification with the model (`SquareZero.curvEquiv`).
* Transport along the identification: `SquareZero.isSquareZero_of_isCurvilinear`,
  `SquareZero.curvCoeffEquiv`, **`SquareZero.curvilinearTrivialisation : Coeff M ≃ₗ[κ] κ`** (the
  kernel is a line) and `SquareZero.curvilinearQuotEquiv : B ⧸ M ≃ₐ[κ] κ[t]/(tⁿ)`.
* `SquareZero.curvilinearAug`, `SquareZero.curvilinearAug_mul_eq_zero`: the augmentation ideal and
  the fact that it annihilates the kernel.
* `SquareZero.IsJetOver κ M A`: the `A`-algebra structure of `B ⧸ M` is a jet at the point, i.e.
  reduces to `x` modulo `t`; `SquareZero.isScalarTower_coeff_of_isJetOver` is the instance it
  buys, namely that `A` acts on the kernel through the point.
* **`SquareZero.CurvilinearObstructions'`**: the set of curvilinear obstructions in the strict
  sense — the obstructions of the extensions `κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)`, over all `n ≥ 1`, all
  curvilinear extensions, all jets at the point and all trivialisations of the kernel — with
  * `SquareZero.curvilinearObstructions'_subset`: it is contained in the set
    `SquareZero.CurvilinearObstructionsAt` of all obstructions at the point;
  * `SquareZero.smul_mem_curvilinearObstructions'`: **it is stable under `κˣ`**;
  * `SquareZero.zero_mem_curvilinearObstructions'`: **it contains the origin**, because the
    constant `1`-jet extends to `κ[t]/(t²)`.

  Together the last two say that the strict curvilinear obstructions form a cone in `Ob(x)`.
* `SquareZero.jetOneEquivTangent`: the lifts of the point to `κ[ε] = κ[t]/(t²)` — the first-order
  jets at `x` — are the tangent vectors `Der_R(A, κ)`.

## Which `κˣ`-action

The scaling is by rescaling the trivialisation of the kernel, which is the reason the set is
defined quantifying over all trivialisations.  This is equivalent to the reparametrisation
`t ↦ ct` only up to the `n`-th power: an automorphism of `κ[t]/(tⁿ⁺¹)` with `t ↦ ct` multiplies
the generator `tⁿ` of the kernel by `cⁿ`, so reparametrisation alone would give stability under
`n`-th powers of `κˣ` and not under all of `κˣ`.  Since the kernel is one-dimensional, the two
descriptions agree after `SquareZero.exists_units_smul_trivialisation`: any two trivialisations of
the kernel differ by a unit, so quantifying over trivialisations is the same as quantifying over
the `κˣ`-orbit of the canonical one determined by the identification with the model.

There are no `sorry`s and no new axioms; the fields of `SquareZero.IsCurvilinear` and
`SquareZero.IsJetOver` are their defining data and conditions, not supplied conclusions.
-/

namespace GromovWitten.AlgebraicGeometry

namespace CotangentComplex

namespace SquareZero

open PicardCriteria LinearTwoTermComplex Polynomial
open scoped TensorProduct

universe u v

/-! ## Curvilinear extensions with an abstract ambient ring -/

section Model

variable {B : Type v} [CommRing B] (κ : Type v) [Field κ] [Algebra κ B] (M : Ideal B)

/-- The `κ`-action on the kernel of a square-zero extension is multiplication by the image of the
scalar. -/
theorem coeff_smul_val [IsSquareZero M] (c : κ) (m : Coeff M) :
    (c • m).val = algebraMap κ B c * m.val :=
  Coeff.val_smul M c (algebraMap κ B c) rfl m

/-- **`M ⊆ B` is a curvilinear extension over `κ`**: the ambient ring is identified with a
truncated polynomial algebra `κ[t]/(tⁿ⁺¹)` in such a way that `M` becomes `(tⁿ)/(tⁿ⁺¹)`, for some
`n ≥ 1`.  The order `n` is part of the data; the two fields are the identification and its
defining property, not supplied conclusions. -/
class IsCurvilinear : Type v where
  /-- The order of the curvilinear extension. -/
  order : ℕ
  /-- The order is at least one, so that the ideal is square zero. -/
  [order_ne_zero : NeZero order]
  /-- The identification of the ambient ring with the truncated polynomial algebra. -/
  equiv : B ≃ₐ[κ] curvRing κ order
  /-- The identification carries the ideal onto the kernel of the model. -/
  map_equiv_eq : Ideal.map (equiv : B →+* curvRing κ order) M = curvIdeal κ order

attribute [instance] IsCurvilinear.order_ne_zero

variable [hcurv : IsCurvilinear κ M]

/-- The order of a curvilinear extension. -/
abbrev curvOrder : ℕ := IsCurvilinear.order (κ := κ) (M := M)

/-- The identification of the ambient ring of a curvilinear extension with `κ[t]/(tⁿ⁺¹)`. -/
noncomputable abbrev curvEquiv : B ≃ₐ[κ] curvRing κ (curvOrder κ M) :=
  IsCurvilinear.equiv (κ := κ) (M := M)

/-- The identification carries the kernel into the kernel of the model. -/
theorem curvEquiv_mem {x : B} (hx : x ∈ M) : curvEquiv κ M x ∈ curvIdeal κ (curvOrder κ M) := by
  rw [← IsCurvilinear.map_equiv_eq (κ := κ) (M := M)]
  exact Ideal.mem_map_of_mem _ hx

/-- The identification reflects membership in the kernel. -/
theorem mem_of_curvEquiv_mem {x : B} (hx : curvEquiv κ M x ∈ curvIdeal κ (curvOrder κ M)) :
    x ∈ M := by
  rw [← IsCurvilinear.map_equiv_eq (κ := κ) (M := M)] at hx
  obtain ⟨y, hy, hxy⟩ :=
    (Ideal.mem_map_iff_of_surjective _ (curvEquiv κ M).surjective).1 hx
  rwa [← (curvEquiv κ M).injective hxy]

include hcurv in
/-- **The kernel of a curvilinear extension is square zero.** -/
theorem isSquareZero_of_isCurvilinear : IsSquareZero M := by
  refine ⟨?_⟩
  rw [pow_two, ← le_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  have hxy : curvEquiv κ M (x * y) = 0 := by
    rw [map_mul]
    exact mul_eq_zero_of_mem (curvIdeal κ (curvOrder κ M)) (curvEquiv_mem κ M hx)
      (curvEquiv_mem κ M hy)
  have : x * y = 0 := (curvEquiv κ M).injective (by rw [hxy, map_zero])
  rw [Ideal.mem_bot]
  exact this

variable [IsSquareZero M]

/-- **The kernel of a curvilinear extension, identified with the kernel of the model.** -/
noncomputable def curvCoeffEquiv : Coeff M ≃ₗ[κ] Coeff (curvIdeal κ (curvOrder κ M)) where
  toFun m := Coeff.mk _ (curvEquiv κ M m.val) (curvEquiv_mem κ M m.val_mem)
  invFun m := Coeff.mk _ ((curvEquiv κ M).symm m.val) (by
    refine mem_of_curvEquiv_mem κ M ?_
    rw [AlgEquiv.apply_symm_apply]
    exact m.val_mem)
  left_inv m := Coeff.ext M (by
    change (curvEquiv κ M).symm (curvEquiv κ M m.val) = m.val
    rw [AlgEquiv.symm_apply_apply])
  right_inv m := Coeff.ext _ (by
    change curvEquiv κ M ((curvEquiv κ M).symm m.val) = m.val
    rw [AlgEquiv.apply_symm_apply])
  map_add' m m' := Coeff.ext _ (by
    change curvEquiv κ M (m.val + m'.val) = curvEquiv κ M m.val + curvEquiv κ M m'.val
    rw [map_add])
  map_smul' c m := Coeff.ext _ (by
    change curvEquiv κ M ((c • m).val)
      = algebraMap κ (curvRing κ (curvOrder κ M)) c * curvEquiv κ M m.val
    rw [coeff_smul_val κ M c m, map_mul, AlgEquiv.commutes])

/-- **The kernel of a curvilinear extension is a `κ`-line**: the identification with the model
carries it onto the line spanned by the class of `tⁿ`. -/
noncomputable def curvilinearTrivialisation : Coeff M ≃ₗ[κ] κ :=
  (curvCoeffEquiv κ M).trans (curvTrivialisation κ (curvOrder κ M))

end Model

section Quot

variable {B : Type v} [CommRing B] (κ : Type v) [Field κ] [Algebra κ B] (M : Ideal B)
variable [IsCurvilinear κ M]

/-- **The quotient of a curvilinear extension is the truncated algebra of one order less.** -/
noncomputable def curvilinearQuotEquiv :
    (B ⧸ M) ≃ₐ[κ] Polynomial κ ⧸ powIdeal κ (curvOrder κ M) :=
  (Ideal.quotientEquivAlg M (curvIdeal κ (curvOrder κ M)) (curvEquiv κ M)
    (IsCurvilinear.map_equiv_eq (κ := κ) (M := M)).symm).trans (curvQuotEquiv κ (curvOrder κ M))

/-- The augmentation ideal `(t)` of a curvilinear extension. -/
noncomputable def curvilinearAug : Ideal B :=
  (Ideal.span {curvParam κ (curvOrder κ M)}).comap (curvEquiv κ M)

/-- **The augmentation ideal annihilates the kernel** of a curvilinear extension: this is
`t · tⁿ = 0` transported along the identification. -/
theorem curvilinearAug_mul_eq_zero {u w : B} (hu : u ∈ curvilinearAug κ M) (hw : w ∈ M) :
    u * w = 0 := by
  refine (curvEquiv κ M).injective ?_
  rw [map_mul, map_zero]
  exact mul_eq_zero_of_mem_span_curvParam κ (curvOrder κ M) (Ideal.mem_comap.1 hu)
    (curvEquiv_mem κ M hw)

end Quot

/-! ## Jets over a curvilinear extension -/

section Jet

variable {B : Type v} [CommRing B] (κ : Type v) [Field κ] [Algebra κ B] (M : Ideal B)
variable [IsCurvilinear κ M] (A : Type v) [CommRing A] [Algebra A κ] [Algebra A (B ⧸ M)]

/-- **A jet at the point over a curvilinear extension**: the `A`-algebra structure of the quotient
`B ⧸ M ≃ κ[t]/(tⁿ)` reduces to the point modulo `t`.  The field is the defining condition, not a
supplied conclusion. -/
class IsJetOver : Prop where
  /-- A jet reduces to the point modulo `t`. -/
  reduces : ∀ a : A, algebraMap A (B ⧸ M) a - algebraMap κ (B ⧸ M) (algebraMap A κ a)
    ∈ (curvilinearAug κ M).map (Ideal.Quotient.mk M)

/-- **The `A`-action on the kernel of a curvilinear extension factors through the point**, for
every jet: the kernel is annihilated by the augmentation ideal, so only the value of the jet at
`t = 0` acts on it. -/
instance isScalarTower_coeff_of_isJetOver [IsSquareZero M] [IsJetOver κ M A] :
    IsScalarTower A κ (Coeff M) := by
  refine ⟨fun a c m => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A (B ⧸ M) a)
  obtain ⟨u, hu, hmk⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk M) Ideal.Quotient.mk_surjective).1
      (IsJetOver.reduces (κ := κ) (M := M) (A := A) a)
  have hw : algebraMap κ B c * m.val ∈ M := Ideal.mul_mem_left _ _ m.val_mem
  have hd : b - algebraMap κ B (algebraMap A κ a) - u ∈ M := by
    rw [← Ideal.Quotient.eq, map_sub, hb, hmk]
    rfl
  have hzero : (b - algebraMap κ B (algebraMap A κ a)) * (algebraMap κ B c * m.val) = 0 := by
    have hsplit : b - algebraMap κ B (algebraMap A κ a)
        = u + (b - algebraMap κ B (algebraMap A κ a) - u) := by ring
    rw [hsplit, add_mul, curvilinearAug_mul_eq_zero κ M hu hw, mul_eq_zero_of_mem M hd hw,
      add_zero]
  have hbw : b * (algebraMap κ B c * m.val)
      = algebraMap κ B (algebraMap A κ a) * (algebraMap κ B c * m.val) := by
    rw [← sub_eq_zero, ← sub_mul]
    exact hzero
  refine Coeff.ext _ ?_
  rw [coeff_smul_val, Coeff.val_smul M a b hb, coeff_smul_val, Algebra.smul_def, map_mul,
    mul_assoc]
  exact hbw.symm

end Jet

/-! ## The strict curvilinear obstruction cone -/

section TheSet

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (P : Algebra.Extension.{v} R A) (κ : Type v) [Field κ] [Algebra A κ]
variable {E : LinearTwoTermComplex A} [Module.Finite A E.degreeZero]
  [Module.Finite A E.degreeOne] (φ : Hom E (presComplex P))

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- **The set of curvilinear obstructions at the point, in the strict sense**: the obstructions of
the curvilinear extensions `κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)`, over all `n ≥ 1`, all ambient rings
identified with the model, all jets at the point, and all trivialisations of the kernel.
Quantifying over the trivialisations is what makes the set a cone; by
`SquareZero.curvilinearTrivialisation` the kernel is a `κ`-line, so a trivialisation always
exists. -/
def CurvilinearObstructions' : Set (ObSpace κ E) :=
  {v | ∃ (B' : Type v) (_ : CommRing B') (_ : Algebra R B') (_ : Algebra κ B') (M' : Ideal B')
    (_ : IsCurvilinear κ M') (_ : IsSquareZero M') (_ : Algebra A (B' ⧸ M'))
    (_ : IsScalarTower R A (B' ⧸ M')) (_ : IsJetOver κ M' A)
    (_ : Nonempty (Lift R M' P.Ring)) (β : Coeff M' ≃ₗ[κ] κ),
    curvilinearObstructionAt M' P κ φ β = v}

/-- **The strict curvilinear obstructions are obstructions at the point.** -/
theorem curvilinearObstructions'_subset :
    CurvilinearObstructions' P κ φ ⊆ CurvilinearObstructionsAt P κ φ := by
  rintro v ⟨B', hB, hRB, hκB, M', hcurv, hsq, hAM, hRAM, hjet, hne, β, rfl⟩
  exact ⟨B', hB, hRB, M', hsq, hAM, hRAM, inferInstance, inferInstance, hne, β, rfl⟩

/-- **The set of strict curvilinear obstructions is stable under `κˣ`**: rescaling the
trivialisation of the kernel rescales the obstruction. -/
theorem smul_mem_curvilinearObstructions' (c : κˣ) {v : ObSpace κ E}
    (hv : v ∈ CurvilinearObstructions' P κ φ) :
    (c : κ) • v ∈ CurvilinearObstructions' P κ φ := by
  obtain ⟨B', hB, hRB, hκB, M', hcurv, hsq, hAM, hRAM, hjet, hne, β, rfl⟩ := hv
  exact ⟨B', hB, hRB, hκB, M', hcurv, hsq, hAM, hRAM, hjet, hne,
    β.trans (LinearEquiv.smulOfUnit c), curvilinearObstructionAt_smulOfUnit M' P κ φ β c⟩

/-! ### The origin is a curvilinear obstruction -/

variable [Algebra R κ] [IsScalarTower R A κ]

/-- **The origin is a strict curvilinear obstruction.**  The first curvilinear extension
`κ[t]/(t²) → κ` with the constant `1`-jet — the point itself — is unobstructed, because the point
lifts to `κ[t]/(t²)` as a constant. -/
theorem zero_mem_curvilinearObstructions' (h : IsObstructionTheory φ) :
    (0 : ObSpace κ E) ∈ CurvilinearObstructions' P κ φ := by
  have hcurv : IsCurvilinear κ (curvIdeal κ 1) :=
    ⟨1, AlgEquiv.refl, le_antisymm (Ideal.map_le_iff_le_comap.2 fun _ hx => hx)
      fun _ hx => Ideal.mem_map_of_mem _ hx⟩
  have hjet : IsJetOver κ (curvIdeal κ 1) A :=
    ⟨fun a => by
      have hs : algebraMap A (curvRing κ 1 ⧸ curvIdeal κ 1) a
          = algebraMap κ (curvRing κ 1 ⧸ curvIdeal κ 1) (algebraMap A κ a) :=
        IsScalarTower.algebraMap_apply A κ (curvRing κ 1 ⧸ curvIdeal κ 1) a
      rw [hs, sub_self]
      exact Ideal.zero_mem _⟩
  have hne : Nonempty _ := ⟨liftToRing (curvIdeal κ 1) P (constLift κ 1)⟩
  have hzero : curvilinearObstructionAt (curvIdeal κ 1) P κ φ (curvTrivialisation κ 1) = 0 :=
    (curvilinearObstructionAt_eq_zero_iff (curvIdeal κ 1) P κ φ h _).2 ⟨constLift κ 1⟩
  exact ⟨curvRing κ 1, inferInstance, inferInstance, inferInstance, curvIdeal κ 1, hcurv,
    inferInstance, inferInstance, inferInstance, hjet, hne, curvTrivialisation κ 1, hzero⟩

/-- **Any two trivialisations of a line differ by a unit.**  Together with
`SquareZero.smul_mem_curvilinearObstructions'` this says that quantifying over all trivialisations
of the kernel is the same as taking the `κˣ`-orbit of the canonical trivialisation
`SquareZero.curvilinearTrivialisation` determined by the identification with the model. -/
theorem exists_units_smul_trivialisation {N : Type v} [AddCommGroup N] [Module κ N]
    (β β' : N ≃ₗ[κ] κ) : ∃ c : κˣ, β' = β.trans (LinearEquiv.smulOfUnit c) := by
  have hu : β' (β.symm 1) ≠ 0 := by
    intro h
    have h0 : β.symm 1 = 0 := by
      have := congrArg β'.symm h
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    have h1 : (1 : κ) = 0 := by
      have := congrArg β h0
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    exact one_ne_zero h1
  refine ⟨Units.mk0 _ hu, LinearEquiv.ext fun m => ?_⟩
  have hm : (β m) • β.symm 1 = m := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  calc β' m = β' ((β m) • β.symm 1) := by rw [hm]
    _ = (β m) • β' (β.symm 1) := by rw [map_smul]
    _ = β' (β.symm 1) • β m := by rw [smul_eq_mul, smul_eq_mul, mul_comm]
    _ = (β.trans (LinearEquiv.smulOfUnit (Units.mk0 _ hu))) m := rfl

end TheSet

/-! ## First-order jets and the tangent space -/

section JetOne

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (κ : Type v) [Field κ] [Algebra R κ] [Algebra A κ] [IsScalarTower R A κ]

/-- **The lifts of the point to `κ[ε] = κ[t]/(t²)` are the tangent vectors at the point.**  A
solution of the lifting problem for the first curvilinear extension is a first-order deformation
of the point, and these form the module of `R`-derivations `A → κ`. -/
noncomputable def jetOneEquivTangent : Lift R (curvIdeal κ 1) A ≃ Derivation R A κ :=
  (Lift.equivDerivation (constLift κ 1)).trans
    (LinearEquiv.compDer (LinearEquiv.restrictScalars A (curvTrivialisation κ 1))).toEquiv

end JetOne

end SquareZero

end CotangentComplex

end GromovWitten.AlgebraicGeometry
