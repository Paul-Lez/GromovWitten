/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.PointObstruction

/-!
# Curvilinear extensions and obstructions

`ObstructionTheory/PointObstruction.lean` shows that the coarse obstruction space `Ob(x)` at a
`κ`-point `x : A → κ` is a universal obstruction space, and studies square-zero extensions whose
kernel is a line abstractly.  This file constructs the *curvilinear* extensions

`κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)`,

the jets that live over them, and the form of the obstruction theory that applies to them.

## The truncated polynomial algebras

* `SquareZero.curvRing κ n = κ[t]/(tⁿ⁺¹)` (`Polynomial κ ⧸ (tⁿ⁺¹)`), with the classes
  `SquareZero.curvParam` of `t` and `SquareZero.curvGen` of `tⁿ`.
* `SquareZero.curvIdeal κ n = (tⁿ)/(tⁿ⁺¹)`, the kernel of the extension, and
  `SquareZero.isSquareZero_curvIdeal`: **it is square zero**, because `2n ≥ n + 1` for `n ≥ 1`
  (the hypothesis `n ≥ 1` is carried as `[NeZero n]`).
* `SquareZero.curvQuotEquiv : (curvRing κ n ⧸ curvIdeal κ n) ≃ₐ[κ] κ[t]/(tⁿ)`: the quotient is
  the truncated algebra of one order less, so this really is the extension of the statement.
* `SquareZero.curvGen_ne_zero`, `SquareZero.exists_eq_smul_curvCoeffGen`,
  `SquareZero.curvTrivialisation : Coeff (curvIdeal κ n) ≃ₗ[κ] κ`: **the kernel is a line**,
  spanned by the class of `tⁿ`, which is nonzero by a degree argument and generates because
  `p · tⁿ ≡ p(0) · tⁿ` modulo `tⁿ⁺¹`.

## Jets

* `SquareZero.curvAug`: the augmentation ideal `(t)` of `κ[t]/(tⁿ)`.
* `SquareZero.IsJet κ n A`: the `A`-algebra structure of `κ[t]/(tⁿ)` is an `n`-jet at the point,
  i.e. it reduces to `x` modulo `t`.  The field is the defining condition, not a conclusion.
* `SquareZero.isScalarTowerCoeff`: **the `A`-action on the kernel of a curvilinear extension
  factors through the point**, for every jet.  This is the whole point of the jet condition: the
  kernel `(tⁿ)/(tⁿ⁺¹)` is killed by `t`, so only the value of the jet at `t = 0` acts on it, and
  the obstruction of a jet therefore lives in `Ob(x) ⊗[κ] (tⁿ)/(tⁿ⁺¹)`.
* `SquareZero.constIsJet`, `SquareZero.constLift`: the constant jet — the canonical `A`-algebra
  structure of `κ[t]/(tⁿ)`, the one factoring through `x` — is a jet, and it always extends, so
  its curvilinear obstruction vanishes.

## The obstruction at a point, with the correct hypotheses on the coefficients

`PointObstruction.lean` states its results under `[Algebra κ (B ⧸ M)]` and
`[IsScalarTower A κ (B ⧸ M)]`, which say that the *whole* extension lies over the point.  That is
too strong for a jet of order `≥ 2`: the `A`-algebra structure of `κ[t]/(tⁿ)` is the jet itself
and does not factor through `κ`.  What the obstruction machinery actually uses is only
`[Module κ (Coeff M)]` and `[IsScalarTower A κ (Coeff M)]` — the *kernel* is a `κ`-vector space on
which `A` acts through `x` — which is exactly what `SquareZero.isScalarTowerCoeff` provides.  This
file therefore repeats under those weaker hypotheses the small part of `PointObstruction.lean`
that mentions them:

* `SquareZero.pointObstructionAt`, `SquareZero.pointObstructionAt_eq_zero_iff`,
  `SquareZero.trivialiseTensorAt`, `SquareZero.curvilinearObstructionAt`,
  `SquareZero.curvilinearObstructionAt_eq_zero_iff`,
  `SquareZero.curvilinearObstructionAt_smulOfUnit`;
* `SquareZero.CurvilinearObstructionsAt`, the set of obstructions at the point of all square-zero
  extensions whose kernel is a trivialised `κ`-line, with
  `SquareZero.smul_mem_curvilinearObstructionsAt` (it is a `κˣ`-stable cone) and
  `SquareZero.curvilinearObstructions_subset` (the set of `PointObstruction.lean` is contained in
  it, so nothing is lost).

Everything above is built with `SquareZero.extOneEquivObTensor`, which already has exactly the
right hypotheses.

## What is missing, and why

The set `CurvilinearObstructions'` of obstructions of the truncated-polynomial extensions
themselves — over all `n`, all jets and all trivialisations — is **not** defined here, and neither
are the two statements about it that were the goal (that it is contained in
`CurvilinearObstructionsAt`, and that it is a `κˣ`-stable cone containing the origin).  The
obstacle is a typeclass diamond, not mathematics:

* for the concrete iterated quotient `B = κ[t]/(tⁿ⁺¹)`, `Semiring B` and `SMul A (B ⧸ M)` each
  have two instance paths — the dedicated quotient instances (`Ideal.Quotient.semiring`,
  `Submodule.Quotient.instSMul'`) and the ones coming from the `CommRing`/`Algebra` structures —
  and instance search picks different ones in this file and in
  `CotangentComplex/SquareZero.lean`, where the ambient ring is a variable carrying `[CommRing B]`
  and `[Algebra A (B ⧸ M)]`.  The two are propositionally but not reducibly equal, so
  `SquareZero.ringAlgebra` and `SquareZero.isScalarTower_base` cannot be applied and the type
  `Lift R (curvIdeal κ n) P.Ring` — which every obstruction statement mentions — does not
  elaborate;
* on top of that, `κ[t]/(tⁿ)` already carries a canonical `A`-algebra structure through the point,
  which competes with the jet for `SMul A (B ⧸ M)`, so making a nonconstant jet *the* instance is
  fragile.

Two ways out, neither attempted here: state the curvilinear extensions with an abstract ambient
ring `B` plus an isomorphism `B ≃ₐ[κ] κ[t]/(tⁿ⁺¹)` carrying `M` to `(tⁿ)/(tⁿ⁺¹)` (so that all
instances come from variables), or give `curvRing` its own `CommRing`/`Algebra` instances as
`@[instance_reducible]` shortcuts so that only one path exists.  All the mathematical input for
the missing statements is present in this file: the extension, its square-zero kernel, the
trivialisation of that kernel, the jet condition and its consequence
`SquareZero.isScalarTowerCoeff`, the scaling law `curvilinearObstructionAt_smulOfUnit`, and the
unobstructedness of the constant jet (`SquareZero.constLift`).

There are no `sorry`s and no new axioms; nothing is supplied as a structure field carrying a
conclusion (the field of `SquareZero.IsJet` is its defining condition).
-/

namespace GromovWitten.AlgebraicGeometry

namespace CotangentComplex

namespace SquareZero

open PicardCriteria LinearTwoTermComplex Polynomial
open scoped TensorProduct

universe u v

/-! ## The truncated polynomial algebras -/

section Truncated

variable (κ : Type v) [Field κ] (n : ℕ)

/-- The ideal `(tᵏ)` of the polynomial ring `κ[t]`. -/
noncomputable abbrev powIdeal (k : ℕ) : Ideal (Polynomial κ) := Ideal.span {(X : Polynomial κ) ^ k}

/-- The ambient ring `κ[t]/(tⁿ⁺¹)` of the `n`-th curvilinear extension. -/
noncomputable abbrev curvRing : Type v := Polynomial κ ⧸ powIdeal κ (n + 1)

/-- The class of `t` in `κ[t]/(tⁿ⁺¹)`. -/
noncomputable def curvParam : curvRing κ n := Ideal.Quotient.mk _ (X : Polynomial κ)

/-- The class of `tⁿ` in `κ[t]/(tⁿ⁺¹)`: the generator of the kernel of the curvilinear
extension. -/
noncomputable def curvGen : curvRing κ n := Ideal.Quotient.mk _ ((X : Polynomial κ) ^ n)

/-- **The kernel `(tⁿ)/(tⁿ⁺¹)` of the `n`-th curvilinear extension.** -/
noncomputable def curvIdeal : Ideal (curvRing κ n) := Ideal.span {curvGen κ n}

/-- The kernel is the image of the ideal `(tⁿ)` of the polynomial ring. -/
theorem curvIdeal_eq_map :
    curvIdeal κ n = (powIdeal κ n).map (Ideal.Quotient.mk (powIdeal κ (n + 1))) := by
  rw [curvIdeal, Ideal.map_span, Set.image_singleton]
  rfl

/-- The generator of the kernel lies in it. -/
theorem curvGen_mem : curvGen κ n ∈ curvIdeal κ n :=
  Ideal.mem_span_singleton_self _

/-- `t · tⁿ = 0` in `κ[t]/(tⁿ⁺¹)`. -/
theorem curvParam_mul_curvGen : curvParam κ n * curvGen κ n = 0 := by
  rw [curvParam, curvGen, ← map_mul, ← pow_succ']
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-- The augmentation ideal `(t)` annihilates the kernel. -/
theorem mul_eq_zero_of_mem_span_curvParam {u w : curvRing κ n}
    (hu : u ∈ Ideal.span {curvParam κ n}) (hw : w ∈ curvIdeal κ n) : u * w = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨b, rfl⟩ :=
    Ideal.mem_span_singleton'.1 (show w ∈ Ideal.span {curvGen κ n} from hw)
  have h : a * curvParam κ n * (b * curvGen κ n)
      = a * b * (curvParam κ n * curvGen κ n) := by ring
  rw [h, curvParam_mul_curvGen, mul_zero]

/-- **The kernel of the curvilinear extension is square zero**, because `2n ≥ n + 1`. -/
instance isSquareZero_curvIdeal [NeZero n] : IsSquareZero (curvIdeal κ n) := by
  refine ⟨?_⟩
  rw [pow_two, curvIdeal, Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_bot,
    curvGen, ← map_mul, ← pow_add, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hn := NeZero.ne n
  exact pow_dvd_pow _ (by omega)

/-- The class of `tⁿ` is nonzero in `κ[t]/(tⁿ⁺¹)`. -/
theorem curvGen_ne_zero : curvGen κ n ≠ 0 := by
  intro h
  rw [curvGen, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  have hne : ((X : Polynomial κ) ^ n) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hle := Polynomial.natDegree_le_of_dvd h hne
  rw [natDegree_X_pow, natDegree_X_pow] at hle
  omega

/-- **The quotient of the ambient ring by the kernel is the truncated algebra `κ[t]/(tⁿ)`**:
the `n`-th curvilinear extension really is `κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)`. -/
noncomputable def curvQuotEquiv :
    (curvRing κ n ⧸ curvIdeal κ n) ≃ₐ[κ] Polynomial κ ⧸ powIdeal κ n :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (curvIdeal_eq_map κ n)).trans
    (DoubleQuot.quotQuotEquivQuotOfLE
      (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n)))))
    fun _ => rfl

end Truncated

/-! ### The kernel of a curvilinear extension is a line -/

section CurvCoeff

variable (κ : Type v) [Field κ] (n : ℕ) [NeZero n]

/-- The class of `tⁿ`, as an element of the kernel. -/
noncomputable def curvCoeffGen : Coeff (curvIdeal κ n) :=
  Coeff.mk _ (curvGen κ n) (curvGen_mem κ n)

omit [NeZero n] in
@[simp]
theorem curvCoeffGen_val : (curvCoeffGen κ n).val = curvGen κ n :=
  rfl

/-- The `κ`-action on the kernel is multiplication by the image of the scalar. -/
theorem curvCoeff_smul_val (c : κ) (m : Coeff (curvIdeal κ n)) :
    (c • m).val = algebraMap κ (curvRing κ n) c * m.val :=
  Coeff.val_smul (curvIdeal κ n) c (algebraMap κ (curvRing κ n) c) rfl m

/-- **The class of `tⁿ` generates the kernel over `κ`.** -/
theorem exists_eq_smul_curvCoeffGen (m : Coeff (curvIdeal κ n)) :
    ∃ c : κ, m = c • curvCoeffGen κ n := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1
    (show m.val ∈ Ideal.span {curvGen κ n} from m.val_mem)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨p.coeff 0, Coeff.ext _ ?_⟩
  rw [curvCoeff_smul_val, curvCoeffGen_val, ← hy]
  have h1 : (Ideal.Quotient.mk (powIdeal κ (n + 1)) (X * p.divX)) * curvGen κ n = 0 :=
    mul_eq_zero_of_mem_span_curvParam κ n
      (Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ p.divX, by
        rw [curvParam, ← map_mul, mul_comm]⟩)
      (curvGen_mem κ n)
  conv_lhs => rw [← Polynomial.X_mul_divX_add p]
  rw [map_add, add_mul, h1, zero_add]
  rfl

omit [NeZero n] in
/-- The class of `tⁿ` is a nonzero element of the kernel. -/
theorem curvCoeffGen_ne_zero : curvCoeffGen κ n ≠ 0 := by
  intro h
  refine curvGen_ne_zero κ n ?_
  rw [← curvCoeffGen_val κ n, h]
  rfl

/-- The line spanned by the class of `tⁿ` inside the kernel. -/
noncomputable def curvLine : κ →ₗ[κ] Coeff (curvIdeal κ n) where
  toFun c := c • curvCoeffGen κ n
  map_add' c d := add_smul c d _
  map_smul' c d := by
    change (c * d) • curvCoeffGen κ n = c • d • curvCoeffGen κ n
    rw [mul_smul]

theorem curvLine_bijective : Function.Bijective (curvLine κ n) := by
  constructor
  · intro c d hcd
    by_contra hne
    have hsub : c - d ≠ 0 := sub_ne_zero.2 hne
    have h0 : (c - d) • curvCoeffGen κ n = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hcd
    refine curvCoeffGen_ne_zero κ n ?_
    calc curvCoeffGen κ n = ((c - d)⁻¹ * (c - d)) • curvCoeffGen κ n := by
          rw [inv_mul_cancel₀ hsub, one_smul]
      _ = (c - d)⁻¹ • ((c - d) • curvCoeffGen κ n) := by rw [mul_smul]
      _ = 0 := by rw [h0, smul_zero]
  · intro m
    obtain ⟨c, rfl⟩ := exists_eq_smul_curvCoeffGen κ n m
    exact ⟨c, rfl⟩

/-- **The kernel of the `n`-th curvilinear extension is one-dimensional**, trivialised by the
class of `tⁿ`. -/
noncomputable def curvTrivialisation : Coeff (curvIdeal κ n) ≃ₗ[κ] κ :=
  (LinearEquiv.ofBijective (curvLine κ n) (curvLine_bijective κ n)).symm

end CurvCoeff

/-! ## The obstruction at a point, with the correct hypotheses on the coefficients -/

section AtPoint

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B] (M : Ideal B)
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{v} R A)
variable (κ : Type v) [Field κ] [Algebra A κ]

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

section Weak

variable [Module κ (Coeff M)] [IsScalarTower A κ (Coeff M)]
variable {E : LinearTwoTermComplex A} [Module.Finite A E.degreeZero]
  [Module.Finite A E.degreeOne] (φ : Hom E (presComplex P))

/-- **The obstruction class at the point**, for a square-zero extension whose *kernel* is a
`κ`-vector space on which `A` acts through the point.  This is `SquareZero.pointObstruction`
under the weaker — and correct — hypotheses discussed in the module docstring. -/
noncomputable def pointObstructionAt [Nonempty (Lift R M P.Ring)] :
    ObSpace κ E ⊗[κ] Coeff M :=
  extOneEquivObTensor κ (Coeff M) E (obstructionE M P φ)

/-- The obstruction at the point vanishes exactly when the lifting problem is solvable. -/
theorem pointObstructionAt_eq_zero_iff (h : IsObstructionTheory φ)
    [Nonempty (Lift R M P.Ring)] :
    pointObstructionAt M P κ φ = 0 ↔ Nonempty (Lift R M A) := by
  rw [← obstructionE_eq_zero_iff M P φ h]
  constructor
  · intro hz
    refine (extOneEquivObTensor κ (Coeff M) E).injective ?_
    rw [map_zero]
    exact hz
  · intro hz
    rw [pointObstructionAt, hz, map_zero]

/-- A trivialisation of the kernel identifies `Ob(x) ⊗[κ] M` with `Ob(x)`. -/
noncomputable def trivialiseTensorAt (E : LinearTwoTermComplex A) (β : Coeff M ≃ₗ[κ] κ) :
    ObSpace κ E ⊗[κ] Coeff M ≃ₗ[κ] ObSpace κ E :=
  (TensorProduct.congr (LinearEquiv.refl κ (ObSpace κ E)) β).trans (TensorProduct.rid κ _)

omit [Algebra A (B ⧸ M)] [IsSquareZero M] [IsScalarTower A κ (Coeff M)] in
@[simp]
theorem trivialiseTensorAt_tmul (E : LinearTwoTermComplex A) (β : Coeff M ≃ₗ[κ] κ)
    (v : ObSpace κ E) (m : Coeff M) :
    trivialiseTensorAt M κ E β (v ⊗ₜ[κ] m) = β m • v := by
  simp [trivialiseTensorAt]

omit [Algebra A (B ⧸ M)] [IsSquareZero M] [IsScalarTower A κ (Coeff M)] in
/-- Rescaling the trivialisation rescales the identification. -/
theorem trivialiseTensorAt_smulOfUnit (E : LinearTwoTermComplex A) (β : Coeff M ≃ₗ[κ] κ)
    (c : κˣ) (y : ObSpace κ E ⊗[κ] Coeff M) :
    trivialiseTensorAt M κ E (β.trans (LinearEquiv.smulOfUnit c)) y
      = (c : κ) • trivialiseTensorAt M κ E β y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => rw [map_add, map_add, hu, hw, smul_add]
  | tmul v m =>
    rw [trivialiseTensorAt_tmul, trivialiseTensorAt_tmul]
    change ((c : κ) • β m) • v = _
    rw [smul_eq_mul, mul_smul]

/-- **The obstruction of a square-zero extension over the point whose kernel is a line**, as a
single element of `Ob(x)`. -/
noncomputable def curvilinearObstructionAt [Nonempty (Lift R M P.Ring)]
    (β : Coeff M ≃ₗ[κ] κ) : ObSpace κ E :=
  trivialiseTensorAt M κ E β (pointObstructionAt M P κ φ)

/-- The single obstruction element vanishes exactly when the lifting problem is solvable. -/
theorem curvilinearObstructionAt_eq_zero_iff (h : IsObstructionTheory φ)
    [Nonempty (Lift R M P.Ring)] (β : Coeff M ≃ₗ[κ] κ) :
    curvilinearObstructionAt M P κ φ β = 0 ↔ Nonempty (Lift R M A) := by
  rw [← pointObstructionAt_eq_zero_iff M P κ φ h]
  constructor
  · intro hz
    refine (trivialiseTensorAt M κ E β).injective ?_
    rw [map_zero]
    exact hz
  · intro hz
    rw [curvilinearObstructionAt, hz, map_zero]

/-- Rescaling the trivialisation rescales the obstruction. -/
theorem curvilinearObstructionAt_smulOfUnit [Nonempty (Lift R M P.Ring)]
    (β : Coeff M ≃ₗ[κ] κ) (c : κˣ) :
    curvilinearObstructionAt M P κ φ (β.trans (LinearEquiv.smulOfUnit c))
      = (c : κ) • curvilinearObstructionAt M P κ φ β :=
  trivialiseTensorAt_smulOfUnit M κ E β c (pointObstructionAt M P κ φ)

end Weak

section Set

variable {E : LinearTwoTermComplex A} [Module.Finite A E.degreeZero]
  [Module.Finite A E.degreeOne] (φ : Hom E (presComplex P))

/-- **The set of obstructions at the point** coming from square-zero extensions whose kernel is
a trivialised `κ`-line on which `A` acts through the point.  This is the analogue of
`SquareZero.CurvilinearObstructions` with the correct hypotheses on the coefficients. -/
def CurvilinearObstructionsAt : Set (ObSpace κ E) :=
  {v | ∃ (B' : Type v) (_ : CommRing B') (_ : Algebra R B') (M' : Ideal B')
    (_ : IsSquareZero M') (_ : Algebra A (B' ⧸ M')) (_ : IsScalarTower R A (B' ⧸ M'))
    (_ : Module κ (Coeff M')) (_ : IsScalarTower A κ (Coeff M'))
    (_ : Nonempty (Lift R M' P.Ring)) (β : Coeff M' ≃ₗ[κ] κ),
    curvilinearObstructionAt M' P κ φ β = v}

/-- Every trivialised square-zero extension over the point contributes its obstruction. -/
theorem curvilinearObstructionAt_mem [Module κ (Coeff M)] [IsScalarTower A κ (Coeff M)]
    [Nonempty (Lift R M P.Ring)] (β : Coeff M ≃ₗ[κ] κ) :
    curvilinearObstructionAt M P κ φ β ∈ CurvilinearObstructionsAt P κ φ :=
  ⟨B, inferInstance, inferInstance, M, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, β, rfl⟩

/-- **The set of obstructions at the point is stable under scaling by `κˣ`.** -/
theorem smul_mem_curvilinearObstructionsAt (c : κˣ) {v : ObSpace κ E}
    (hv : v ∈ CurvilinearObstructionsAt P κ φ) :
    (c : κ) • v ∈ CurvilinearObstructionsAt P κ φ := by
  obtain ⟨B', hB, hRB, M', hsq, hAM, hRAM, hkM, hAkM, hne, β, rfl⟩ := hv
  exact ⟨B', hB, hRB, M', hsq, hAM, hRAM, hkM, hAkM, hne,
    β.trans (LinearEquiv.smulOfUnit c), curvilinearObstructionAt_smulOfUnit M' P κ φ β c⟩

/-- The obstructions of `PointObstruction.lean`, which are those of the extensions lying entirely
over the point, are obstructions at the point in the above sense. -/
theorem curvilinearObstructions_subset :
    CurvilinearObstructions P κ φ ⊆ CurvilinearObstructionsAt P κ φ := by
  rintro v ⟨B', hB, hRB, M', hsq, hAM, hRAM, hkM, hAkM, hne, β, rfl⟩
  exact ⟨B', hB, hRB, M', hsq, hAM, hRAM, inferInstance, inferInstance, hne, β, rfl⟩

end Set

end AtPoint

/-! ## Jets and the curvilinear obstructions in the strict sense -/

section Jet

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (κ : Type v) [Field κ] [Algebra R κ] [Algebra A κ] [IsScalarTower R A κ]

section Defs

variable (n : ℕ)

/-- The augmentation ideal `(t)` of `κ[t]/(tⁿ)`, the image of the ideal generated by `t`. -/
noncomputable def curvAug : Ideal (curvRing κ n ⧸ curvIdeal κ n) :=
  (Ideal.span {curvParam κ n}).map (Ideal.Quotient.mk (curvIdeal κ n))

variable [Algebra A (curvRing κ n ⧸ curvIdeal κ n)]

/-- **An `n`-jet at the point `x : A → κ`**: the `A`-algebra structure of `κ[t]/(tⁿ)` reduces to
`x` modulo `t`.  Together with the `A`-algebra structure and
`[IsScalarTower R A (curvRing κ n ⧸ curvIdeal κ n)]` this is the data of an `R`-algebra map
`A → κ[t]/(tⁿ)` lifting the point; the field below is its defining condition, not a supplied
conclusion. -/
class IsJet (A : Type v) [CommRing A] [Algebra A κ]
    [Algebra A (curvRing κ n ⧸ curvIdeal κ n)] : Prop where
  /-- A jet reduces to the point modulo `t`. -/
  reduces : ∀ a : A, algebraMap A (curvRing κ n ⧸ curvIdeal κ n) a
    - algebraMap κ (curvRing κ n ⧸ curvIdeal κ n) (algebraMap A κ a) ∈ curvAug κ n

/-- **The `A`-action on the kernel of a curvilinear extension factors through the point.**  This
is what the jet condition buys: the kernel `(tⁿ)/(tⁿ⁺¹)` is killed by `t`, so only the value of
the jet at `t = 0` — that is, the point — acts on it.  It is exactly the hypothesis needed to
view the obstruction inside `Ob(x) ⊗ M`. -/
instance isScalarTowerCoeff [NeZero n] [IsJet κ n A] :
    IsScalarTower A κ (Coeff (curvIdeal κ n)) := by
  refine ⟨fun a c m => ?_⟩
  obtain ⟨b, hb⟩ :=
    Ideal.Quotient.mk_surjective (algebraMap A (curvRing κ n ⧸ curvIdeal κ n) a)
  obtain ⟨u, hu, hmk⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (curvIdeal κ n))
      Ideal.Quotient.mk_surjective).1 (IsJet.reduces (A := A) (κ := κ) (n := n) a)
  have hw : algebraMap κ (curvRing κ n) c * m.val ∈ curvIdeal κ n :=
    Ideal.mul_mem_left _ _ m.val_mem
  have hd : b - algebraMap κ (curvRing κ n) (algebraMap A κ a) - u ∈ curvIdeal κ n := by
    rw [← Ideal.Quotient.eq, map_sub, hb, hmk]
    rfl
  have hzero : (b - algebraMap κ (curvRing κ n) (algebraMap A κ a))
      * (algebraMap κ (curvRing κ n) c * m.val) = 0 := by
    have hsplit : b - algebraMap κ (curvRing κ n) (algebraMap A κ a)
        = u + (b - algebraMap κ (curvRing κ n) (algebraMap A κ a) - u) := by ring
    rw [hsplit, add_mul, mul_eq_zero_of_mem_span_curvParam κ n hu hw,
      mul_eq_zero_of_mem (curvIdeal κ n) hd hw, add_zero]
  have hbw : b * (algebraMap κ (curvRing κ n) c * m.val)
      = algebraMap κ (curvRing κ n) (algebraMap A κ a)
        * (algebraMap κ (curvRing κ n) c * m.val) := by
    rw [← sub_eq_zero, ← sub_mul]
    exact hzero
  refine Coeff.ext _ ?_
  rw [curvCoeff_smul_val, Coeff.val_smul (curvIdeal κ n) a b hb, curvCoeff_smul_val,
    Algebra.smul_def, map_mul, mul_assoc]
  exact hbw.symm

end Defs

/-! ### The constant jet -/

section ConstJet

variable (n : ℕ)

/-- **The constant jet.**  The canonical `A`-algebra structure of `κ[t]/(tⁿ)`, the one that
factors through the point, is an `n`-jet at the point for every `n`: it is the jet of the constant
arc at `x`. -/
instance constIsJet : IsJet κ n A :=
  ⟨fun a => by
    have h : algebraMap A (curvRing κ n ⧸ curvIdeal κ n) a
        = algebraMap κ (curvRing κ n ⧸ curvIdeal κ n) (algebraMap A κ a) :=
      IsScalarTower.algebraMap_apply A κ (curvRing κ n ⧸ curvIdeal κ n) a
    rw [h, sub_self]
    exact Ideal.zero_mem _⟩

/-- **The constant jet always extends**: the point itself, viewed in `κ[t]/(tⁿ⁺¹)`, is a solution
of the lifting problem for the constant jet.  For `n = 1` this says that the curvilinear
obstruction of the constant `1`-jet vanishes. -/
noncomputable def constLift : Lift R (curvIdeal κ n) A :=
  ⟨(IsScalarTower.toAlgHom R κ (curvRing κ n)).comp (IsScalarTower.toAlgHom R A κ),
    AlgHom.ext fun a => by
      change Ideal.Quotient.mk (curvIdeal κ n) (algebraMap κ (curvRing κ n) (algebraMap A κ a))
        = algebraMap A (curvRing κ n ⧸ curvIdeal κ n) a
      rw [IsScalarTower.algebraMap_apply A κ (curvRing κ n ⧸ curvIdeal κ n) a]
      rfl⟩

end ConstJet

end Jet

end SquareZero

end CotangentComplex

end GromovWitten.AlgebraicGeometry
