/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.DeformationMeaning
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The obstruction space at a geometric point

For an obstruction theory `φ : E ⟶ L` in the affine two-term model of
`ObstructionTheory/DeformationMeaning.lean`, and a point `x : A → κ` with values in a field `κ`,
the *coarse obstruction space* at `x` is

`Ob(x) = h¹[Hom_κ(κ ⊗ E¹, κ) → Hom_κ(κ ⊗ E⁰, κ)]`,

the degree-one cohomology of the `κ`-dual of the fibre of `E` at `x`.  This file proves that
`Ob(x)` is a **universal obstruction space** for all square-zero extensions living over the point:
for such an extension with kernel `M`, the group `Ext¹(E, M)` in which the obstruction class of
`DeformationMeaning.lean` lives is `Ob(x) ⊗[κ] M`, so a single finite-dimensional `κ`-vector space
`Ob(x)` receives the obstruction of every square-zero deformation problem at `x`.

## Contents

* `SquareZero.obstructionE_baseChange`: the base-change naturality left out of
  `DeformationMeaning.lean`.  Along `R → R'` the square-zero extension `B → B ⧸ M` base changes to
  `R' ⊗[R] B → (R' ⊗[R] B) ⧸ baseIdeal R M R'` over the *same* `A`
  (`SquareZeroExt.basePush`), so the statement is the specialisation of
  `SquareZero.obstructionE_push` to `SquareZeroExt.basePush`; it is the exact analogue of
  `SquareZeroExt.obstruction_baseChange` for the obstruction class of `E`.
* `SquareZero.fibreComplex`, `SquareZero.ObSpace`, `SquareZero.TanSpace`: the fibre `κ ⊗[A] E` of
  the two-term complex at the point and the two cohomology spaces of its `κ`-dual.
* `SquareZero.dualPointComplex`, `SquareZero.pointDualEquiv`: the dual complex with coefficients
  in a module `N` which is a `κ`-vector space, and the degreewise identification
  `Hom_A(X, N) ≃ Hom_κ(κ ⊗[A] X, N) ≃ (κ ⊗[A] X)^∨ ⊗[κ] N` for a finite `A`-module `X`.
* `SquareZero.extOneEquivObTensor`: **universality**, `h¹` of the dual complex with coefficients
  in `N` is `Ob(x) ⊗[κ] N`, for every coefficient module `N` which is a `κ`-vector space, provided
  the two terms of `E` are finite `A`-modules.
* `SquareZero.pointObstruction`, `SquareZero.pointObstruction_eq_zero_iff`: the obstruction class
  of a square-zero extension at the point, as an element of `Ob(x) ⊗[κ] M`, and the fact that it
  vanishes exactly when the lifting problem is solvable.
* `SquareZero.obSpaceEquiv`: taking `N = κ` identifies `Ob(x)` with `h¹` of the dual complex of
  `E` with coefficients in `κ`, the description used in the roadmap.
* `SquareZero.h0DualEquivDerivation`: for an obstruction theory the degree-zero part of the dual
  complex is the module of `R`-derivations of `A`, for every coefficient module; with `N = κ`
  this is the tangent space at the point.
* `SquareZero.curvilinearObstruction`, `SquareZero.curvilinearObstruction_eq_zero_iff`,
  `SquareZero.curvilinearObstruction_smulOfUnit`, `SquareZero.CurvilinearObstructions`,
  `SquareZero.smul_mem_curvilinearObstructions`,
  `SquareZero.zero_mem_curvilinearObstructions`: for a square-zero extension over the point whose
  kernel is a line — the shape of the curvilinear extensions `κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)` — the
  obstruction is a single element of `Ob(x)`, it vanishes exactly when the jet extends, rescaling
  the trivialisation of the kernel rescales it, and the set of all such elements is therefore a
  `κˣ`-stable subset of `Ob(x)` containing the origin as soon as one of the extensions is
  unobstructed.

## What is not formalised here

* The curvilinear family itself: the truncated polynomial algebras `κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)` are
  not constructed, so `CurvilinearObstructions` ranges over *all* square-zero extensions over the
  point with a one-dimensional kernel, which a priori is a larger set.  Everything proved about it
  applies verbatim to the curvilinear subfamily once that family is constructed.
* The identification of the set of curvilinear obstructions with the fibre of the intrinsic normal
  cone inside `Ob(x)` (Behrend–Fantechi); only the cone property is proved.
* Base change of `E` itself: `obstructionE_baseChange` changes the square-zero extension over a
  fixed `A`, which is what `SquareZeroExt.basePush` provides.  Replacing `A` by `R' ⊗[R] A` and
  `E` by `R' ⊗[R] E`, with the corresponding presentation, is not treated.

## Conventions

"Living over the point" is expressed by the instances `[Algebra κ (B ⧸ M)]` and
`[IsScalarTower A κ (B ⧸ M)]`: the structure map `A → B ⧸ M` factors through `κ`.  The existing
instances of `SquareZero.Coeff` then make the kernel `Coeff M` a `κ`-vector space compatibly with
its `A`-module structure, which is the hypothesis "the ideal is annihilated by `ker x`" in the
usual formulation.

There are no `sorry`s and no new axioms; nothing is supplied as a structure field carrying a
conclusion.
-/

namespace GromovWitten.AlgebraicGeometry

namespace CotangentComplex

namespace SquareZero

open PicardCriteria LinearTwoTermComplex
open scoped TensorProduct

universe u v

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B] (M : Ideal B)
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{v} R A)

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-! ## Base change of the obstruction class of `E` -/

section BaseChange

variable {E : LinearTwoTermComplex A} (φ : Hom E (presComplex P))
variable (R' : Type v) [CommRing R'] [Algebra R R']

attribute [local instance 100] baseAlgebra
attribute [local instance] isScalarTower_baseAlgebra nonempty_lift_baseChange_ring

/-- **The obstruction class of `E` is natural under base change of the square-zero extension.**
Base change along `R → R'` replaces `B → B ⧸ M` by `R' ⊗[R] B → (R' ⊗[R] B) ⧸ (M)` over the same
`A`; the obstruction class of `E` for the base-changed problem is the image of the original one.
This is the analogue for `E` of `SquareZero.obstruction_baseChange`, and holds with no flatness
hypothesis. -/
theorem obstructionE_baseChange [Nonempty (Lift R M P.Ring)] :
    extOneEPush M (baseIdeal R M R') (basePush R M R') (obstructionE M P φ)
      = obstructionE (baseIdeal R M R') P φ :=
  obstructionE_push M P φ (baseIdeal R M R') (basePush R M R')

/-- Base change cannot create obstructions for `E`: if the base-changed obstruction class of `E`
is nonzero then so is the original one. -/
theorem obstructionE_ne_zero_of_baseChange [Nonempty (Lift R M P.Ring)]
    (h : obstructionE (baseIdeal R M R') P φ ≠ 0) : obstructionE M P φ ≠ 0 := by
  intro h0
  exact h (by rw [← obstructionE_baseChange M P φ R', h0, map_zero])

end BaseChange

/-! ## The fibre of a two-term complex at a point -/

section Fibre

variable (κ : Type v) [Field κ] [Algebra A κ] (E : LinearTwoTermComplex A)

/-- **The fibre of a two-term complex of `A`-modules at a `κ`-point `x : A → κ`**: the base
change `κ ⊗[A] E`, a two-term complex of `κ`-vector spaces. -/
noncomputable abbrev fibreComplex : LinearTwoTermComplex κ where
  degreeZero := κ ⊗[A] E.degreeZero
  degreeOne := κ ⊗[A] E.degreeOne
  differential := LinearMap.baseChange κ E.differential

/-- **The coarse obstruction space of `E` at the point `x`**: `h¹` of the `κ`-dual of the fibre,
that is, the cokernel of `(κ ⊗ E¹)^∨ → (κ ⊗ E⁰)^∨`. -/
noncomputable abbrev ObSpace : Type v := h1 (dualComplex (fibreComplex κ E) κ)

/-- **The tangent space of `E` at the point `x`**: `h⁰` of the `κ`-dual of the fibre, that is,
the kernel of `(κ ⊗ E¹)^∨ → (κ ⊗ E⁰)^∨`. -/
noncomputable abbrev TanSpace : Submodule κ ((κ ⊗[A] E.degreeOne) →ₗ[κ] κ) :=
  h0 (dualComplex (fibreComplex κ E) κ)

/-- **The coarse obstruction space is finite dimensional** as soon as the degree-zero term of
`E` is a finite `A`-module: it is a quotient of the `κ`-dual of the fibre. -/
instance finite_obSpace [Module.Finite A E.degreeZero] : Module.Finite κ (ObSpace κ E) :=
  inferInstance

/-- The differential of the fibre complex is the base change of the differential. -/
@[simp]
theorem fibreComplex_differential :
    (fibreComplex κ E).differential = LinearMap.baseChange κ E.differential :=
  rfl

end Fibre

/-! ## The dual complex with coefficients in a `κ`-vector space -/

section PointDual

variable (κ : Type v) [Field κ] [Algebra A κ]
variable (N : Type v) [AddCommGroup N] [Module A N] [Module κ N] [IsScalarTower A κ N]

/-- The dual complex of `E` with coefficients in `N`, viewed as a complex of `κ`-vector spaces.
It has the same underlying modules and the same differential as `PicardCriteria.dualComplex E N`;
only the base ring of the ambient category has changed, the `κ`-action coming from the
coefficients. -/
noncomputable abbrev dualPointComplex (E : LinearTwoTermComplex A) : LinearTwoTermComplex κ where
  degreeZero := E.degreeOne →ₗ[A] N
  degreeOne := E.degreeZero →ₗ[A] N
  differential :=
    { toFun := fun l => l.comp E.differential
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The `κ`-form and the `A`-form of the dual complex have literally the same differential. -/
theorem dualPointComplex_differential_apply (E : LinearTwoTermComplex A)
    (l : E.degreeOne →ₗ[A] N) :
    (dualPointComplex κ N E).differential l = (dualComplex E N).differential l :=
  rfl

/-- **The `κ`-points of a finite `A`-module at the point `x`.**  For a coefficient module `N`
which is a `κ`-vector space compatibly with its `A`-action, `A`-linear maps `X → N` are `κ`-linear
maps on the fibre `κ ⊗[A] X`, hence — when the fibre is finite dimensional — elements of
`(κ ⊗[A] X)^∨ ⊗[κ] N`. -/
noncomputable def pointDualEquiv (X : Type v) [AddCommGroup X] [Module A X] [Module.Finite A X] :
    (X →ₗ[A] N) ≃ₗ[κ] Module.Dual κ (κ ⊗[A] X) ⊗[κ] N :=
  (LinearMap.liftBaseChangeEquiv κ).trans (dualTensorHomEquiv κ (κ ⊗[A] X) N).symm

@[simp]
theorem pointDualEquiv_symm_tmul (X : Type v) [AddCommGroup X] [Module A X] [Module.Finite A X]
    (f : Module.Dual κ (κ ⊗[A] X)) (n : N) (x : X) :
    (pointDualEquiv κ N X).symm (f ⊗ₜ[κ] n) x = f (1 ⊗ₜ[A] x) • n := by
  simp [pointDualEquiv]

section Universality

variable (E : LinearTwoTermComplex A) [Module.Finite A E.degreeZero]
  [Module.Finite A E.degreeOne]

/-- The degreewise identification is compatible with the differentials. -/
theorem pointDualEquiv_symm_differential
    (y : Module.Dual κ (κ ⊗[A] E.degreeOne) ⊗[κ] N) :
    (dualPointComplex κ N E).differential ((pointDualEquiv κ N E.degreeOne).symm y)
      = (pointDualEquiv κ N E.degreeZero).symm
        (LinearMap.rTensor N (dualComplex (fibreComplex κ E) κ).differential y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul f n =>
    refine LinearMap.ext fun x => ?_
    change ((pointDualEquiv κ N E.degreeOne).symm (f ⊗ₜ[κ] n)) (E.differential x) = _
    rw [pointDualEquiv_symm_tmul, LinearMap.rTensor_tmul, pointDualEquiv_symm_tmul]
    simp

/-- The degreewise identification, read as a chain map. -/
theorem pointDualEquiv_comp_differential :
    (pointDualEquiv κ N E.degreeZero).toLinearMap.comp (dualPointComplex κ N E).differential
      = (LinearMap.rTensor N (dualComplex (fibreComplex κ E) κ).differential).comp
          (pointDualEquiv κ N E.degreeOne).toLinearMap := by
  refine LinearMap.ext fun l => ?_
  have h := pointDualEquiv_symm_differential κ N E (pointDualEquiv κ N E.degreeOne l)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, h,
    LinearEquiv.apply_symm_apply]

/-- The degreewise identification carries the coboundaries onto the coboundaries. -/
theorem map_range_pointDualEquiv :
    Submodule.map (pointDualEquiv κ N E.degreeZero).toLinearMap
        (LinearMap.range (dualPointComplex κ N E).differential)
      = LinearMap.range
        (LinearMap.rTensor N (dualComplex (fibreComplex κ E) κ).differential) := by
  rw [← LinearMap.range_comp, pointDualEquiv_comp_differential, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top]

omit [Module.Finite A E.degreeZero] [Module.Finite A E.degreeOne] in
/-- The presentation of the coarse obstruction space as a cokernel. -/
theorem exact_fibreDual :
    Function.Exact (dualComplex (fibreComplex κ E) κ).differential
      (Submodule.mkQ (LinearMap.range (dualComplex (fibreComplex κ E) κ).differential)) :=
  LinearMap.exact_iff.2 (Submodule.ker_mkQ _)

/-- **Universality of the coarse obstruction space, `κ`-linear form.**  The degree-one cohomology
of the dual complex with coefficients in a `κ`-vector space `N` is `Ob(x) ⊗[κ] N`. -/
noncomputable def h1DualPointEquiv :
    h1 (dualPointComplex κ N E) ≃ₗ[κ] ObSpace κ E ⊗[κ] N :=
  (Submodule.Quotient.equiv _ _ (pointDualEquiv κ N E.degreeZero)
      (map_range_pointDualEquiv κ N E)).trans
    (_root_.rTensor.equiv N (exact_fibreDual κ E) (Submodule.mkQ_surjective _))

omit [Module.Finite A E.degreeZero] [Module.Finite A E.degreeOne] in
/-- The coboundaries of the `A`-form and of the `κ`-form of the dual complex agree. -/
theorem range_dualComplex_eq_restrictScalars :
    LinearMap.range (dualComplex E N).differential
      = Submodule.restrictScalars A (LinearMap.range (dualPointComplex κ N E).differential) :=
  SetLike.ext fun _ => Iff.rfl

/-- The `A`-form of `h¹` of the dual complex is its `κ`-form. -/
noncomputable def h1DualEquivPoint :
    h1 (dualComplex E N) ≃ₗ[A] h1 (dualPointComplex κ N E) :=
  (Submodule.quotEquivOfEq _ _ (range_dualComplex_eq_restrictScalars κ N E)).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

/-- **Universality of the coarse obstruction space.**  For every coefficient module `N` which is a
`κ`-vector space compatibly with its `A`-action, the group `h¹` of the dual complex of `E` with
coefficients in `N` — the group in which the obstruction class of `E` lives — is
`Ob(x) ⊗[κ] N`.  A single `κ`-vector space `Ob(x)`, the cokernel of the dual of the fibre of `E`
at the point, therefore carries the obstruction of every square-zero deformation problem over the
point. -/
noncomputable def extOneEquivObTensor :
    h1 (dualComplex E N) ≃ₗ[A] ObSpace κ E ⊗[κ] N :=
  (h1DualEquivPoint κ N E).trans ((h1DualPointEquiv κ N E).restrictScalars A)

end Universality

end PointDual

/-! ## The obstruction class at the point -/

section PointObstruction

variable (κ : Type v) [Field κ] [Algebra A κ]

/-- The coarse obstruction space is the degree-one cohomology of the dual complex of `E` with
coefficients in `κ`: taking `N = κ` in `extOneEquivObTensor` identifies the two descriptions. -/
noncomputable def obSpaceEquiv (E : LinearTwoTermComplex A) [Module.Finite A E.degreeZero]
    [Module.Finite A E.degreeOne] : h1 (dualComplex E κ) ≃ₗ[A] ObSpace κ E :=
  (extOneEquivObTensor κ κ E).trans ((TensorProduct.rid κ (ObSpace κ E)).restrictScalars A)

variable [Algebra κ (B ⧸ M)] [IsScalarTower A κ (B ⧸ M)]
variable {E : LinearTwoTermComplex A} [Module.Finite A E.degreeZero]
  [Module.Finite A E.degreeOne] (φ : Hom E (presComplex P))

/-- **The obstruction class of a square-zero extension at the point.**  For a square-zero
extension whose structure map factors through the point — so that its kernel is a `κ`-vector
space — the obstruction class of `E` is an element of `Ob(x) ⊗[κ] M`. -/
noncomputable def pointObstruction [Nonempty (Lift R M P.Ring)] : ObSpace κ E ⊗[κ] Coeff M :=
  extOneEquivObTensor κ (Coeff M) E (obstructionE M P φ)

/-- **`Ob(x)` is a universal obstruction space.**  For an obstruction theory `φ` and a square-zero
extension over the point, the obstruction in `Ob(x) ⊗[κ] M` vanishes exactly when the lifting
problem is solvable. -/
theorem pointObstruction_eq_zero_iff (h : IsObstructionTheory φ) [Nonempty (Lift R M P.Ring)] :
    pointObstruction M P κ φ = 0 ↔ Nonempty (Lift R M A) := by
  rw [← obstructionE_eq_zero_iff M P φ h]
  constructor
  · intro hz
    refine (extOneEquivObTensor κ (Coeff M) E).injective ?_
    rw [map_zero]
    exact hz
  · intro hz
    rw [pointObstruction, hz, map_zero]

end PointObstruction

/-! ## The tangent space at the point -/

section Tangent

variable {E : LinearTwoTermComplex A} (φ : Hom E (presComplex P))
variable (N : Type v) [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]

/-- **For an obstruction theory, `h⁰` of the dual complex with coefficients in `N` is the module
of `R`-derivations of `A` with values in `N`.**  With `N = κ` this is the tangent space at the
point; with `N = Coeff M` it is `SquareZero.extZeroEEquivDerivation`. -/
noncomputable def h0DualEquivDerivation (h : IsObstructionTheory φ) :
    h0 (dualComplex E N) ≃ₗ[A] Derivation R A N :=
  (((LinearEquiv.ofBijective (dualComplexHom N φ).kernelMap
        (h.bijective_kernelMap_dualComplexHom N)).symm.trans
      (dualModuleH0Equiv N (presComplex P))).trans
    (LinearEquiv.arrowCongr (cotangentH0Equiv P) (LinearEquiv.refl A N))).trans
      (KaehlerDifferential.linearMapEquivDerivation R A)

end Tangent

/-! ## Curvilinear obstructions -/

section Curvilinear

variable (κ : Type v) [Field κ] [Algebra A κ]

/-- A trivialisation `β` of the kernel of a square-zero extension over the point — that is, an
identification of the kernel with the line `κ` — identifies `Ob(x) ⊗[κ] M` with `Ob(x)`. -/
noncomputable def trivialiseTensor (E : LinearTwoTermComplex A) [Algebra κ (B ⧸ M)]
    [IsScalarTower A κ (B ⧸ M)] (β : Coeff M ≃ₗ[κ] κ) :
    ObSpace κ E ⊗[κ] Coeff M ≃ₗ[κ] ObSpace κ E :=
  (TensorProduct.congr (LinearEquiv.refl κ (ObSpace κ E)) β).trans (TensorProduct.rid κ _)

@[simp]
theorem trivialiseTensor_tmul (E : LinearTwoTermComplex A) [Algebra κ (B ⧸ M)]
    [IsScalarTower A κ (B ⧸ M)] (β : Coeff M ≃ₗ[κ] κ) (v : ObSpace κ E) (m : Coeff M) :
    trivialiseTensor M κ E β (v ⊗ₜ[κ] m) = β m • v := by
  simp [trivialiseTensor]

/-- Rescaling the trivialisation of the kernel rescales the identification. -/
theorem trivialiseTensor_smulOfUnit (E : LinearTwoTermComplex A) [Algebra κ (B ⧸ M)]
    [IsScalarTower A κ (B ⧸ M)] (β : Coeff M ≃ₗ[κ] κ) (c : κˣ)
    (y : ObSpace κ E ⊗[κ] Coeff M) :
    trivialiseTensor M κ E (β.trans (LinearEquiv.smulOfUnit c)) y
      = (c : κ) • trivialiseTensor M κ E β y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => rw [map_add, map_add, hu, hw, smul_add]
  | tmul v m =>
    rw [trivialiseTensor_tmul, trivialiseTensor_tmul]
    change ((c : κ) • β m) • v = _
    rw [smul_eq_mul, mul_smul]

section WithPhi

variable {E : LinearTwoTermComplex A} [Module.Finite A E.degreeZero]
  [Module.Finite A E.degreeOne] (φ : Hom E (presComplex P))

/-- **The obstruction of a square-zero extension whose kernel is a line, as a single element of
the coarse obstruction space `Ob(x)`.**  For the curvilinear extension
`κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)` of an `n`-jet at `x`, whose kernel is the line spanned by `tⁿ`, this is
the obstruction to extending the jet one step further. -/
noncomputable def curvilinearObstruction [Algebra κ (B ⧸ M)] [IsScalarTower A κ (B ⧸ M)]
    [Nonempty (Lift R M P.Ring)] (β : Coeff M ≃ₗ[κ] κ) : ObSpace κ E :=
  trivialiseTensor M κ E β (pointObstruction M P κ φ)

/-- The single obstruction element vanishes exactly when the lifting problem is solvable. -/
theorem curvilinearObstruction_eq_zero_iff (h : IsObstructionTheory φ) [Algebra κ (B ⧸ M)]
    [IsScalarTower A κ (B ⧸ M)] [Nonempty (Lift R M P.Ring)] (β : Coeff M ≃ₗ[κ] κ) :
    curvilinearObstruction M P κ φ β = 0 ↔ Nonempty (Lift R M A) := by
  rw [← pointObstruction_eq_zero_iff M P κ φ h]
  constructor
  · intro hz
    refine (trivialiseTensor M κ E β).injective ?_
    rw [map_zero]
    exact hz
  · intro hz
    rw [curvilinearObstruction, hz, map_zero]

/-- **Rescaling the trivialisation rescales the obstruction.**  This is the `κˣ`-homogeneity that
makes the set of curvilinear obstructions a cone. -/
theorem curvilinearObstruction_smulOfUnit [Algebra κ (B ⧸ M)] [IsScalarTower A κ (B ⧸ M)]
    [Nonempty (Lift R M P.Ring)] (β : Coeff M ≃ₗ[κ] κ) (c : κˣ) :
    curvilinearObstruction M P κ φ (β.trans (LinearEquiv.smulOfUnit c))
      = (c : κ) • curvilinearObstruction M P κ φ β :=
  trivialiseTensor_smulOfUnit M κ E β c (pointObstruction M P κ φ)

/-- **The set of curvilinear obstructions at the point `x`**: the set of all elements of `Ob(x)`
arising as the obstruction of a square-zero extension over the point whose kernel is a `κ`-line,
together with a trivialisation of that kernel.  The curvilinear extensions
`κ[t]/(tⁿ⁺¹) → κ[t]/(tⁿ)` of `n`-jets at `x` are extensions of this kind; they are not
constructed here, so the set below is a priori larger. -/
def CurvilinearObstructions : Set (ObSpace κ E) :=
  {v | ∃ (B' : Type v) (_ : CommRing B') (_ : Algebra R B') (M' : Ideal B')
    (_ : IsSquareZero M') (_ : Algebra A (B' ⧸ M')) (_ : IsScalarTower R A (B' ⧸ M'))
    (_ : Algebra κ (B' ⧸ M')) (_ : IsScalarTower A κ (B' ⧸ M'))
    (_ : Nonempty (Lift R M' P.Ring)) (β : Coeff M' ≃ₗ[κ] κ),
    curvilinearObstruction M' P κ φ β = v}

/-- Every trivialised square-zero extension over the point contributes its obstruction to the
set of curvilinear obstructions. -/
theorem curvilinearObstruction_mem [Algebra κ (B ⧸ M)] [IsScalarTower A κ (B ⧸ M)]
    [Nonempty (Lift R M P.Ring)] (β : Coeff M ≃ₗ[κ] κ) :
    curvilinearObstruction M P κ φ β ∈ CurvilinearObstructions P κ φ :=
  ⟨B, inferInstance, inferInstance, M, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, β, rfl⟩

/-- **The set of curvilinear obstructions is stable under scaling by `κˣ`.** -/
theorem smul_mem_curvilinearObstructions (c : κˣ) {v : ObSpace κ E}
    (hv : v ∈ CurvilinearObstructions P κ φ) :
    (c : κ) • v ∈ CurvilinearObstructions P κ φ := by
  obtain ⟨B', hB, hRB, M', hsq, hAM, hRAM, hkM, hAkM, hne, β, rfl⟩ := hv
  exact ⟨B', hB, hRB, M', hsq, hAM, hRAM, hkM, hAkM, hne, β.trans (LinearEquiv.smulOfUnit c),
    curvilinearObstruction_smulOfUnit M' P κ φ β c⟩

/-- **The set of curvilinear obstructions contains the origin**, as soon as one trivialised
square-zero extension over the point is unobstructed. -/
theorem zero_mem_curvilinearObstructions (h : IsObstructionTheory φ) [Algebra κ (B ⧸ M)]
    [IsScalarTower A κ (B ⧸ M)] [Nonempty (Lift R M P.Ring)] (β : Coeff M ≃ₗ[κ] κ)
    (hlift : Nonempty (Lift R M A)) :
    (0 : ObSpace κ E) ∈ CurvilinearObstructions P κ φ := by
  have hzero : curvilinearObstruction M P κ φ β = 0 :=
    (curvilinearObstruction_eq_zero_iff M P κ φ h β).2 hlift
  exact hzero ▸ curvilinearObstruction_mem M P κ φ β

end WithPhi

end Curvilinear

end SquareZero

end CotangentComplex

end GromovWitten.AlgebraicGeometry
