/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZeroExt
import GromovWitten.AlgebraicGeometry.ObstructionTheory.AffineCriterion

/-!
# The deformation-theoretic meaning of an obstruction theory

Behrend–Fantechi §4: an obstruction theory `φ : E → L_X` is a morphism to the cotangent complex
such that, for every square-zero extension `T ↪ T̄` with ideal `J` and every morphism `T → X`,
the obstruction `ω ∈ Ext¹(L_X, J)` to extending the morphism pushes forward to
`φ^*ω ∈ Ext¹(E, J)`, the lift exists if and only if `φ^*ω = 0`, and the lifts then form a torsor
under `Ext⁰(E, J) = Ext⁰(L_X, J)`.

This file proves that statement in the affine model of `CotangentComplex/SquareZero.lean` and
`CotangentComplex/SquareZeroExt.lean`, where `X = Spec A`, the square-zero extension is
`B → B ⧸ M` with square-zero ideal `M` and `L_X` is the two-term presentation complex
`L = [I ⧸ I² → A ⊗ Ω]` of a presentation `P : Algebra.Extension R A`.  The complex `L` is
`SquareZero.presComplex P`, a reducible abbreviation which is definitionally
`CotangentComplex.AffinePresentation.twoTerm R A P` (`SquareZero.presComplex_eq_twoTerm`); the
abbreviation is used because the terms of a non-reducible definition do not unfold at instance
transparency, which blocks every rewrite mixing `L.degreeZero` with `P.Cotangent`.

## Module coefficients for the Picard criteria

`Cones/CriteriaBundle.lean` dualises a two-term complex into the complex of `B`-points
`[Hom_R(E¹, B) → Hom_R(E⁰, B)]` of an `R`-*algebra* `B`.  The coefficients occurring in
deformation theory are the `A`-module `Coeff M`, so the first part of this file redoes that
construction with module coefficients:

* `PicardCriteria.dualComplex E N = [Hom_A(E¹, N) → Hom_A(E⁰, N)]` and the contravariant
  `PicardCriteria.dualComplexHom φ N`, together with the covariant `dualComplexCoeffHom` in the
  coefficients and the commutation `dualComplexCoeffHom_comp`;
* `PicardCriteria.dualModuleH0Equiv : h0 (dualComplex E N) ≃ₗ Hom(h¹ E, N)`;
* `PicardCriteria.IsObstructionTheory.isCohomologicalMono_dualComplexHom`: if `φ` is an
  obstruction theory then `h⁰(dualComplexHom φ N)` is bijective and `h¹(dualComplexHom φ N)` is
  injective for **every** module `N`, with no finiteness or projectivity hypothesis.  This is the
  module-coefficient form of `AffineCriterion.IsObstructionTheory.isCohomologicalMono_dualHom`.

## The obstruction of `E`

* `SquareZero.extOneEquivDualHOne`, `SquareZero.extZeroEquivDualHZero`: the groups `ExtOne R M P`
  and `ExtZero R M P` of `SquareZeroExt.lean` *are* `h¹` and `h⁰` of the dual complex of the
  presentation complex with coefficients in `Coeff M`; `SquareZero.obstructionGroupEquivDualHOne`
  states the same for the obstruction group, and through `SquareZeroExt.homotopyExtOneEquiv` and
  `SquareZeroExt.obstructionGroupEquivDerivedExt` for the chain-level and derived `Ext¹`.
* `SquareZero.ExtOneE`, `SquareZero.ExtZeroE`, `SquareZero.extOneMap`, `SquareZero.obstructionE`:
  the two `Ext` groups of `E` and the image `φ^*ω` of the obstruction class.
* `SquareZero.obstructionE_eq_zero_iff`: **the obstruction of `E` vanishes exactly when the
  lifting problem is solvable**, for any obstruction theory `φ`.
* `SquareZero.extZeroEquivExtZeroE`, `SquareZero.extZeroEEquivDerivation`: `Ext⁰(E, M)` is
  `Ext⁰(L, M)`, hence is `Der_R(A, Coeff M)`.
* `SquareZero.extZeroEVAdd`, `SquareZero.exists_unique_extZeroEVAdd`,
  `SquareZero.liftEquivExtZeroE`: **the solutions of the lifting problem form a simply
  transitive set under `Ext⁰(E, M)`**, and `SquareZero.liftIsoClassEquivExtZeroE` identifies the
  isomorphism classes of the lifting groupoid with the quotient of `Ext⁰(E, M)` by the classes
  realised by automorphisms of the square-zero extension (`SquareZero.autExtZeroE`).

## Functoriality and trivialisations

* `SquareZero.obstructionE_push`: naturality of `φ^*ω` along a morphism `Push R M N A` of
  square-zero extensions.
* `SquareZero.derSection`, `SquareZero.derSection_comp`: the canonical splitting of
  `SquareZero.restrictDer`, which turns a derivation of the ambient ring into an actual map on
  the cotangent space; it is additive (`SquareZero.derSection_sub`) and computes degree-zero
  classes (`SquareZero.derSection_compAlgebraMap`).
* `SquareZero.obstructionObject`, `SquareZero.isoClass_obstructionObject`,
  `SquareZero.trivialisationOfLift`, `SquareZero.bijective_trivialisationOfLift`,
  `SquareZero.liftEquivTrivialisation`: the obstruction is an *object* of the Picard groupoid
  `(dualComplex E (Coeff M)).quotient`, whose isomorphism class is `obstructionE`, and **the
  lifts correspond bijectively to its trivialisations**, i.e. to the arrows from it to the
  vertex.  The bijection is equivariant for the two `Ext⁰`-torsor structures
  (`SquareZero.trivialisationOfLift_extZeroEVAdd`).

Nothing is supplied as a structure field carrying a conclusion; there are no `sorry`s and no new
axioms.
-/

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

universe u v

open LinearTwoTermComplex

variable {R : Type u} [CommRing R] {E L : LinearTwoTermComplex R}

/-! ## Duals with module coefficients -/

/-- Precomposition with an `R`-linear map, as an `R`-linear map between modules of functionals
with values in a fixed module `N`.  This is the module-coefficient version of
`PicardCriteria.precomp`. -/
def precompModule {M M' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (g : M →ₗ[R] M') (N : Type u) [AddCommGroup N] [Module R N] :
    (M' →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) where
  toFun l := l.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem precompModule_apply {M M' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (g : M →ₗ[R] M') (N : Type u) [AddCommGroup N] [Module R N]
    (l : M' →ₗ[R] N) (x : M) : precompModule g N l x = l (g x) :=
  rfl

/-- The dual of a two-term complex with coefficients in an `R`-module `N`:

`[Hom_R(E¹, N) → Hom_R(E⁰, N)]`,

again a two-term complex of `R`-modules.  Its `h⁰` is `Hom_R(h¹ E, N)` and its `h¹` is the
naive `Ext¹` of `E` with coefficients in `N`. -/
abbrev dualComplex (E : LinearTwoTermComplex R) (N : Type u) [AddCommGroup N] [Module R N] :
    LinearTwoTermComplex R where
  degreeZero := E.degreeOne →ₗ[R] N
  degreeOne := E.degreeZero →ₗ[R] N
  differential := precompModule E.differential N

@[simp]
theorem dualComplex_differential (E : LinearTwoTermComplex R) (N : Type u) [AddCommGroup N]
    [Module R N] : (dualComplex E N).differential = precompModule E.differential N :=
  rfl

variable (N N' : Type u) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/-- A chain map `φ : E ⟶ L` induces, contravariantly, a chain map of the duals with coefficients
in a module `N`. -/
def dualComplexHom (φ : Hom E L) : Hom (dualComplex L N) (dualComplex E N) where
  degreeZero := precompModule φ.degreeOne N
  degreeOne := precompModule φ.degreeZero N
  comm l := by
    refine LinearMap.ext fun z => ?_
    change l (L.differential (φ.degreeZero z)) = l (φ.degreeOne (E.differential z))
    exact congrArg l (φ.comm z).symm

@[simp]
theorem dualComplexHom_degreeZero (φ : Hom E L) :
    (dualComplexHom N φ).degreeZero = precompModule φ.degreeOne N :=
  rfl

@[simp]
theorem dualComplexHom_degreeOne (φ : Hom E L) :
    (dualComplexHom N φ).degreeOne = precompModule φ.degreeZero N :=
  rfl

/-- Dualising the identity chain map gives the identity. -/
theorem dualComplexHom_id : dualComplexHom N (Hom.id E) = Hom.id (dualComplex E N) :=
  rfl

/-- A linear map of coefficient modules induces, covariantly, a chain map of the duals. -/
def dualComplexCoeffHom (E : LinearTwoTermComplex R) (g : N →ₗ[R] N') :
    Hom (dualComplex E N) (dualComplex E N') where
  degreeZero := LinearMap.llcomp R E.degreeOne N N' g
  degreeOne := LinearMap.llcomp R E.degreeZero N N' g
  comm _ := rfl

@[simp]
theorem dualComplexCoeffHom_degreeOne_apply (E : LinearTwoTermComplex R) (g : N →ₗ[R] N')
    (l : (dualComplex E N).degreeOne) (x : E.degreeZero) :
    (dualComplexCoeffHom N N' E g).degreeOne l x = g (l x) :=
  rfl

/-- Changing the coefficients and dualising a chain map commute. -/
theorem dualComplexCoeffHom_comp (φ : Hom E L) (g : N →ₗ[R] N') :
    (dualComplexCoeffHom N N' E g).comp (dualComplexHom N φ) =
      (dualComplexHom N' φ).comp (dualComplexCoeffHom N N' L g) :=
  rfl

/-! ## `h⁰` of the module dual -/

/-- **`h⁰` of the dual with coefficients in `N` is `Hom_R(h¹ E, N)`.**  By
`PicardCriteria.autEquivKernel` this is the automorphism group of every object of the Picard
groupoid of the dual. -/
def dualModuleH0Equiv (E : LinearTwoTermComplex R) :
    h0 (dualComplex E N) ≃ₗ[R] (h1 E →ₗ[R] N) where
  toFun l :=
    Submodule.liftQ (LinearMap.range E.differential) l.1 (by
      rintro _ ⟨x, rfl⟩
      have hl : precompModule E.differential N l.1 = 0 := l.2
      exact congrArg (fun m : E.degreeZero →ₗ[R] N => m x) hl)
  invFun m := ⟨m.comp (Submodule.mkQ (LinearMap.range E.differential)), by
    change precompModule E.differential N
        (m.comp (Submodule.mkQ (LinearMap.range E.differential))) = 0
    refine LinearMap.ext fun x => ?_
    change m (h1mk E (E.differential x)) = 0
    rw [(h1mk_eq_zero_iff (E := E) (E.differential x)).2 ⟨x, rfl⟩, map_zero]⟩
  left_inv l := by
    apply Subtype.ext
    rfl
  right_inv m := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    rfl
  map_add' l l' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    rfl
  map_smul' r l := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    rfl

@[simp]
theorem dualModuleH0Equiv_apply (E : LinearTwoTermComplex R) (l : h0 (dualComplex E N))
    (x : E.degreeOne) : dualModuleH0Equiv N E l (h1mk E x) = l.1 x :=
  rfl

/-- Under the identification `h⁰(dualComplex E N) = Hom_R(h¹ E, N)`, the map induced by
`dualComplexHom φ N` on `h⁰` is precomposition with `H⁰(φ) = φ.cokernelMap`. -/
theorem dualModuleH0Equiv_kernelMap (φ : Hom E L) (l : h0 (dualComplex L N)) :
    dualModuleH0Equiv N E ((dualComplexHom N φ).kernelMap l)
      = (dualModuleH0Equiv N L l).comp φ.cokernelMap := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := h1mk_surjective q
  rfl

/-- The map induced by `dualComplexHom φ N` on `h⁰` is bijective exactly when precomposition
with `H⁰(φ)` is bijective on `N`-valued functionals. -/
theorem bijective_kernelMap_dualComplexHom_iff (φ : Hom E L) :
    Function.Bijective (dualComplexHom N φ).kernelMap ↔
      Function.Bijective (fun m : h1 L →ₗ[R] N => m.comp φ.cokernelMap) := by
  have key : ⇑(dualModuleH0Equiv N E) ∘ ⇑(dualComplexHom N φ).kernelMap
      = (fun m : h1 L →ₗ[R] N => m.comp φ.cokernelMap) ∘ ⇑(dualModuleH0Equiv N L) :=
    funext fun l => dualModuleH0Equiv_kernelMap N φ l
  rw [← Function.Bijective.of_comp_iff' (dualModuleH0Equiv N E).bijective, key,
    Function.Bijective.of_comp_iff _ (dualModuleH0Equiv N L).bijective]

/-! ## The forward direction of Behrend–Fantechi 4.5 with module coefficients -/

/-- **Descent of a pair of functionals along the mapping cone, module version.**

This is `PicardCriteria.exists_lift_of_isObstructionTheory` with the test algebra replaced by an
arbitrary coefficient module; the proof uses only the module structure of the target. -/
theorem exists_lift_module_of_isObstructionTheory {φ : Hom E L} (h : IsObstructionTheory φ)
    (lam : L.degreeZero →ₗ[R] N) (mu : E.degreeOne →ₗ[R] N)
    (hcomm : ∀ x : E.degreeZero, lam (φ.degreeZero x) = mu (E.differential x)) :
    ∃ nu : L.degreeOne →ₗ[R] N, ∀ a : L.degreeZero, nu (L.differential a) = lam a := by
  have hbeta : Function.Surjective (coneBeta φ) :=
    coneBeta_surjective φ h.bijective_cokernelMap.2
  have hexact : LinearMap.ker (coneBeta φ) = LinearMap.range (coneAlpha φ) :=
    ker_coneBeta φ h.surjective_kernelMap h.bijective_cokernelMap.1
  have hle : LinearMap.ker (coneBeta φ) ≤ LinearMap.ker (LinearMap.coprod lam mu) := by
    rw [hexact]
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, coneAlpha_apply, LinearMap.coprod_apply, map_neg, ← hcomm x,
      add_neg_cancel]
  refine ⟨(Submodule.liftQ _ (LinearMap.coprod lam mu) hle).comp
    ((LinearMap.quotKerEquivOfSurjective (coneBeta φ) hbeta).symm.toLinearMap), fun a => ?_⟩
  have hmk : (LinearMap.quotKerEquivOfSurjective (coneBeta φ) hbeta).symm (L.differential a)
      = Submodule.Quotient.mk ((a, 0) : L.degreeZero × E.degreeOne) := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk, coneBeta_apply,
      map_zero, add_zero]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hmk,
    Submodule.liftQ_apply, LinearMap.coprod_apply, map_zero, add_zero]

/-- **Injectivity on `h¹` of the module dual.**  A functional on `L⁻¹` with values in `N` whose
restriction along `φ⁻¹` is a coboundary is itself a coboundary. -/
theorem injective_cokernelMap_dualComplexHom {φ : Hom E L} (h : IsObstructionTheory φ) :
    Function.Injective (dualComplexHom N φ).cokernelMap := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  obtain ⟨lam, rfl⟩ := h1mk_surjective p
  rw [cokernelMap_h1mk, h1mk_eq_zero_iff] at hp
  obtain ⟨mu, hmu⟩ := hp
  obtain ⟨nu, hnu⟩ := exists_lift_module_of_isObstructionTheory N h lam mu
    (fun x => (congrArg (fun m : E.degreeZero →ₗ[R] N => m x) hmu).symm)
  rw [h1mk_eq_zero_iff]
  exact ⟨nu, LinearMap.ext hnu⟩

/-- **Behrend–Fantechi 4.5, forward direction, with module coefficients.**

If `φ : E ⟶ L` is an obstruction theory in the two-term model, then for every `R`-module `N` the
dualised chain map is a cohomological monomorphism: `h⁰` is bijective and `h¹` is injective. -/
theorem IsObstructionTheory.isCohomologicalMono_dualComplexHom {φ : Hom E L}
    (h : IsObstructionTheory φ) : IsCohomologicalMono (dualComplexHom N φ) :=
  ⟨(bijective_kernelMap_dualComplexHom_iff N φ).2
      (bijective_precomp_of_bijective h.bijective_cokernelMap N),
    injective_cokernelMap_dualComplexHom N h⟩

/-- The map induced on `h⁰` by an obstruction theory is bijective, for every coefficient
module. -/
theorem IsObstructionTheory.bijective_kernelMap_dualComplexHom {φ : Hom E L}
    (h : IsObstructionTheory φ) : Function.Bijective (dualComplexHom N φ).kernelMap :=
  (h.isCohomologicalMono_dualComplexHom N).1

/-- The map induced on `h¹` by an obstruction theory is injective, for every coefficient
module. -/
theorem IsObstructionTheory.injective_cokernelMap_dualComplexHom {φ : Hom E L}
    (h : IsObstructionTheory φ) : Function.Injective (dualComplexHom N φ).cokernelMap :=
  (h.isCohomologicalMono_dualComplexHom N).2

end PicardCriteria

namespace CotangentComplex

namespace SquareZero

open PicardCriteria LinearTwoTermComplex

universe u v

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B] (M : Ideal B)
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{v} R A) {E : LinearTwoTermComplex A}

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-! ## `Ext` of the presentation complex is `h¹/h⁰` of its module dual -/

/-- The two-term presentation complex `[I ⧸ I² → A ⊗ Ω]` of `P`, as a *reducible* abbreviation.
It is definitionally `CotangentComplex.presComplex P`
(`presComplex_eq_twoTerm`); the abbreviation exists so that its two terms reduce to
`P.Cotangent` and `P.CotangentSpace` at instance transparency, which the plain definition does
not. -/
noncomputable abbrev presComplex : LinearTwoTermComplex A where
  degreeZero := P.Cotangent
  degreeOne := P.CotangentSpace
  differential := P.cotangentComplex

omit [Algebra R B] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
/-- The reducible presentation complex is the one of
`CotangentComplex.AffinePresentation.twoTerm`. -/
theorem presComplex_eq_twoTerm : presComplex P = AffinePresentation.twoTerm R A P :=
  rfl

omit [Algebra R B] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
/-- The differential of the presentation complex is the cotangent differential. -/
@[simp]
theorem presComplex_differential : (presComplex P).differential = P.cotangentComplex :=
  rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- The map `Hom_A(K⁰, M) → Hom_A(K⁻¹, M)` of `SquareZero.restrictHom` is exactly the
differential of the module dual of the two-term presentation complex. -/
theorem restrictHom_eq_dualComplex_differential :
    restrictHom M P =
      (dualComplex (presComplex P) (Coeff M)).differential :=
  rfl

/-- **`Ext¹` of the presentation complex is `h¹` of its module dual.**  The two groups are the
same quotient; this records the identification. -/
noncomputable def extOneEquivDualHOne :
    ExtOne R M P ≃ₗ[A] h1 (dualComplex (presComplex P) (Coeff M)) :=
  Submodule.quotEquivOfEq _ _ rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem extOneEquivDualHOne_mk (θ : P.Cotangent →ₗ[A] Coeff M) :
    extOneEquivDualHOne M P (Submodule.Quotient.mk θ) =
      h1mk (dualComplex (presComplex P) (Coeff M)) θ :=
  rfl

/-- **`Ext⁰` of the presentation complex is `h⁰` of its module dual.** -/
noncomputable def extZeroEquivDualHZero :
    ExtZero R M P ≃ₗ[A] h0 (dualComplex (presComplex P) (Coeff M)) :=
  (dualModuleH0Equiv (Coeff M) (presComplex P)).symm

/-! ## The `Ext` groups of `E` and the obstruction class of `E` -/

/-- **`Ext¹(E, M)`**, the degree-one `Ext` group of `E` with coefficients in the kernel of the
square-zero extension: `h¹` of the dual `[Hom_A(E¹, M) → Hom_A(E⁰, M)]`. -/
abbrev ExtOneE (E : LinearTwoTermComplex A) : Type v :=
  h1 (dualComplex E (Coeff M))

/-- **`Ext⁰(E, M)`**, the degree-zero `Ext` group of `E` with coefficients in the kernel of the
square-zero extension: `h⁰` of the dual `[Hom_A(E¹, M) → Hom_A(E⁰, M)]`. -/
abbrev ExtZeroE (E : LinearTwoTermComplex A) : Submodule A (E.degreeOne →ₗ[A] Coeff M) :=
  h0 (dualComplex E (Coeff M))

variable (φ : Hom E (presComplex P))

/-- The map `Ext¹(L, M) → Ext¹(E, M)` induced by a morphism `φ : E ⟶ L` to the presentation
complex. -/
noncomputable def extOneMap : ExtOne R M P →ₗ[A] ExtOneE M E :=
  (dualComplexHom (Coeff M) φ).cokernelMap.comp (extOneEquivDualHOne M P).toLinearMap

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem extOneMap_mk (θ : P.Cotangent →ₗ[A] Coeff M) :
    extOneMap M P φ (Submodule.Quotient.mk θ) =
      h1mk (dualComplex E (Coeff M)) (θ.comp φ.degreeZero) :=
  rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- For an obstruction theory the comparison map on `Ext¹` is injective; this is the
module-coefficient form of the forward direction of Behrend–Fantechi 4.5. -/
theorem injective_extOneMap (h : IsObstructionTheory φ) :
    Function.Injective (extOneMap M P φ) := by
  intro x y hxy
  refine (extOneEquivDualHOne M P).injective ?_
  exact h.injective_cokernelMap_dualComplexHom (Coeff M) hxy

/-- **The obstruction class of `E`**: the image `φ^*ω` in `Ext¹(E, M)` of the obstruction class
of the square-zero lifting problem. -/
noncomputable def obstructionE [Nonempty (Lift R M P.Ring)] : ExtOneE M E :=
  extOneMap M P φ (extOneObstruction R M P)

/-- The obstruction class in `Ext¹` is represented by the obstruction cocycle of any lift on the
ambient ring of the presentation. -/
theorem extOneObstruction_eq [Nonempty (Lift R M P.Ring)] (F : Lift R M P.Ring) :
    extOneObstruction R M P = Submodule.Quotient.mk (obstructionMap R M P F) := by
  rw [extOneObstruction, obstruction_eq M F, obstructionGroupEquivExtOne_mk]

/-- The obstruction class of `E` is represented by the pullback along `φ` of the obstruction
cocycle of any lift on the ambient ring. -/
theorem obstructionE_eq_h1mk [Nonempty (Lift R M P.Ring)] (F : Lift R M P.Ring) :
    obstructionE M P φ =
      h1mk (dualComplex E (Coeff M)) ((obstructionMap R M P F).comp φ.degreeZero) := by
  rw [obstructionE, extOneObstruction_eq M P F, extOneMap_mk]

/-- **The deformation-theoretic meaning of an obstruction theory, part one.**  For an obstruction
theory `φ : E ⟶ L`, the obstruction class `φ^*ω ∈ Ext¹(E, M)` vanishes if and only if the
square-zero lifting problem for `A` has a solution. -/
theorem obstructionE_eq_zero_iff (h : IsObstructionTheory φ) [Nonempty (Lift R M P.Ring)] :
    obstructionE M P φ = 0 ↔ Nonempty (Lift R M A) := by
  rw [← extOneObstruction_eq_zero_iff R M P]
  constructor
  · intro hzero
    refine injective_extOneMap M P φ h ?_
    rw [map_zero]
    exact hzero
  · intro hzero
    rw [obstructionE, hzero, map_zero]

/-- The obstruction group of the presentation is `h¹` of the module dual of the presentation
complex.  Composing with `SquareZero.homotopyExtOneEquiv` and
`SquareZero.obstructionGroupEquivDerivedExt` identifies it further with the chain-level `Ext¹` in
the homotopy category and, when the two terms are projective, with the derived-category `Ext¹`. -/
noncomputable def obstructionGroupEquivDualHOne :
    ObstructionGroup R M P ≃ₗ[A] h1 (dualComplex (presComplex P) (Coeff M)) :=
  (obstructionGroupEquivExtOne R M P).trans (extOneEquivDualHOne M P)

/-- The obstruction class of `E` is the image of the obstruction class of the presentation under
the dual of `φ`. -/
theorem obstructionE_eq_map_obstruction [Nonempty (Lift R M P.Ring)] :
    obstructionE M P φ = (dualComplexHom (Coeff M) φ).cokernelMap
      (obstructionGroupEquivDualHOne M P (obstruction R M P)) :=
  rfl

/-- For the tautological obstruction theory the obstruction class of `E` is the obstruction class
of the presentation itself. -/
theorem obstructionE_id [Nonempty (Lift R M P.Ring)] :
    obstructionE M P (Hom.id (presComplex P))
      = extOneEquivDualHOne M P (extOneObstruction R M P) :=
  rfl

/-! ## The `Ext⁰`-torsor of lifts -/

/-- For an obstruction theory, `Ext⁰(L, M) ≃ Ext⁰(E, M)`: the degree-zero `Ext` groups of `E`
and of the presentation complex agree. -/
noncomputable def extZeroEquivExtZeroE (h : IsObstructionTheory φ) :
    ExtZero R M P ≃ₗ[A] ExtZeroE M E :=
  (extZeroEquivDualHZero M P).trans
    (LinearEquiv.ofBijective (dualComplexHom (Coeff M) φ).kernelMap
      (h.bijective_kernelMap_dualComplexHom (Coeff M)))

/-- **`Ext⁰(E, M)` is the module of `R`-derivations of `A` with values in `M`**, for every
obstruction theory `φ`. -/
noncomputable def extZeroEEquivDerivation (h : IsObstructionTheory φ) :
    ExtZeroE M E ≃ₗ[A] Derivation R A (Coeff M) :=
  (extZeroEquivExtZeroE M P φ h).symm.trans (extZeroEquivDerivation R M P)

/-- The action of `Ext⁰(E, M)` on the solutions of the lifting problem. -/
noncomputable def extZeroEVAdd (h : IsObstructionTheory φ) (θ : ExtZeroE M E)
    (f : Lift R M A) : Lift R M A :=
  extZeroEEquivDerivation M P φ h θ +ᵥ f

@[simp]
theorem extZeroEVAdd_hom (h : IsObstructionTheory φ) (θ : ExtZeroE M E) (f : Lift R M A)
    (a : A) : (extZeroEVAdd M P φ h θ f).hom a =
      (extZeroEEquivDerivation M P φ h θ a).val + f.hom a :=
  rfl

/-- The action of `Ext⁰(E, M)` is the action of `Ext⁰(L, M)` transported along the comparison
isomorphism. -/
theorem extZeroEVAdd_apply (h : IsObstructionTheory φ) (θ : ExtZero R M P) (f : Lift R M A) :
    extZeroEVAdd M P φ h (extZeroEquivExtZeroE M P φ h θ) f = extZeroVAdd R M P θ f := by
  rw [extZeroEVAdd, extZeroEEquivDerivation, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, extZeroVAdd]

/-- **The deformation-theoretic meaning of an obstruction theory, part two.**  The solutions of
the lifting problem form a simply transitive set under `Ext⁰(E, M)`. -/
theorem exists_unique_extZeroEVAdd (h : IsObstructionTheory φ) (f g : Lift R M A) :
    ∃! θ : ExtZeroE M E, extZeroEVAdd M P φ h θ f = g := by
  obtain ⟨θ₀, hθ₀, huniq⟩ := exists_unique_extZeroVAdd R M P f g
  refine ⟨extZeroEquivExtZeroE M P φ h θ₀, ?_, fun ψ hψ => ?_⟩
  · change extZeroEVAdd M P φ h (extZeroEquivExtZeroE M P φ h θ₀) f = g
    rw [extZeroEVAdd_apply]
    exact hθ₀
  · have hψ' : extZeroVAdd R M P ((extZeroEquivExtZeroE M P φ h).symm ψ) f = g := by
      rw [← extZeroEVAdd_apply, LinearEquiv.apply_symm_apply]
      exact hψ
    rw [← huniq _ hψ', LinearEquiv.apply_symm_apply]

/-- Choosing a base lift identifies the solutions of the lifting problem with `Ext⁰(E, M)`. -/
noncomputable def liftEquivExtZeroE (h : IsObstructionTheory φ) (f₀ : Lift R M A) :
    Lift R M A ≃ ExtZeroE M E :=
  (liftEquivExtZero R M P f₀).trans (extZeroEquivExtZeroE M P φ h).toEquiv

/-- The subgroup of `Ext⁰(E, M)` of classes realised by automorphisms of the square-zero
extension. -/
noncomputable def autExtZeroE (h : IsObstructionTheory φ) : AddSubgroup (ExtZeroE M E) :=
  AddSubgroup.map ((extZeroEEquivDerivation M P φ h).symm.toAddEquiv.toAddMonoidHom)
    (autDerivationMap R M A).range

/-- **The isomorphism classes of the lifting groupoid form a torsor under `Ext⁰(E, M)` modulo the
classes coming from automorphisms of the square-zero extension.** -/
noncomputable def liftIsoClassEquivExtZeroE (h : IsObstructionTheory φ) (f₀ : Lift R M A) :
    LiftIsoClass R M A ≃ (ExtZeroE M E ⧸ autExtZeroE M P φ h) :=
  (liftIsoClassEquiv R M A f₀).trans
    (QuotientAddGroup.congr _ _ (extZeroEEquivDerivation M P φ h).symm.toAddEquiv rfl).toEquiv

/-! ## Naturality in the square-zero extension -/

section Push

variable {C : Type v} [CommRing C] [Algebra R C] (N : Ideal C) [IsSquareZero N]
variable [Algebra A (C ⧸ N)] [IsScalarTower R A (C ⧸ N)] (π : Push R M N A)

/-- The map `Ext¹(E, M) → Ext¹(E, N)` induced by a morphism of square-zero extensions. -/
noncomputable def extOneEPush : ExtOneE M E →ₗ[A] ExtOneE N E :=
  (dualComplexCoeffHom (Coeff M) (Coeff N) E (pushCoeff M N π)).cokernelMap

omit [Algebra R A] [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A (C ⧸ N)] in
@[simp]
theorem extOneEPush_h1mk (θ : E.degreeZero →ₗ[A] Coeff M) :
    extOneEPush M N π (h1mk (dualComplex E (Coeff M)) θ) =
      h1mk (dualComplex E (Coeff N)) ((pushCoeff M N π).comp θ) :=
  rfl

/-- **Naturality of the obstruction class of `E` in the square-zero extension.** -/
theorem obstructionE_push [Nonempty (Lift R M P.Ring)] [Nonempty (Lift R N P.Ring)] :
    extOneEPush M N π (obstructionE M P φ) = obstructionE N P φ := by
  obtain ⟨F⟩ := (inferInstance : Nonempty (Lift R M P.Ring))
  rw [obstructionE_eq_h1mk M P φ F, extOneEPush_h1mk,
    obstructionE_eq_h1mk N P φ (pushLift M N (pushRing M P N π) F),
    obstructionMap_push M P N π F]
  rfl

end Push

/-! ## The obstruction object and its trivialisations -/

section Trivialisation

open scoped TensorProduct

/-- Two `A`-linear maps out of the cotangent space of a presentation agree as soon as they agree
on the elements `1 ⊗ dp`. -/
theorem cotangentSpace_hom_ext {ψ ψ' : P.CotangentSpace →ₗ[A] Coeff M}
    (hx : ∀ p : P.Ring, ψ (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p)
      = ψ' (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p)) : ψ = ψ' := by
  refine (LinearMap.liftBaseChangeEquiv (R := P.Ring) (M := Ω[P.Ring⁄R])
    (N := Coeff M) A).symm.injective ?_
  exact Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext hx)

/-- The `A`-linear map `A ⊗ Ω[P.Ring⁄R] → M` attached to an `R`-derivation of the ambient ring of
the presentation.  It is the canonical splitting of `SquareZero.restrictDer`. -/
noncomputable def derSection (d : Derivation R P.Ring (Coeff M)) :
    P.CotangentSpace →ₗ[A] Coeff M :=
  LinearMap.liftBaseChange A d.liftKaehlerDifferential

@[simp]
theorem derSection_tmul (d : Derivation R P.Ring (Coeff M)) (a : A) (p : P.Ring) :
    derSection M P d (a ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p) = a • d p := by
  rw [derSection, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]

/-- **`derSection` splits the restriction of derivations**: composing it with the cotangent
differential gives back `restrictDer`, so every coboundary is split by an explicit map. -/
theorem derSection_comp (d : Derivation R P.Ring (Coeff M)) :
    (derSection M P d).comp P.cotangentComplex = restrictDer R M P d := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  rw [LinearMap.comp_apply, Algebra.Extension.cotangentComplex_mk, derSection_tmul, one_smul,
    restrictDer_mk]

/-- The splitting is additive, hence compatible with differences of derivations. -/
theorem derSection_sub (d e : Derivation R P.Ring (Coeff M)) :
    derSection M P (d - e) = derSection M P d - derSection M P e := by
  refine cotangentSpace_hom_ext M P fun p => ?_
  simp

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- The value of a degree-zero class, read as a map on the cotangent space. -/
theorem extZeroEquivDualHZero_val_apply (ζ : ExtZero R M P) (x : P.CotangentSpace) :
    (extZeroEquivDualHZero M P ζ).val x = ζ (Submodule.Quotient.mk x) :=
  rfl

/-- The derivation attached to a degree-zero class, evaluated through the presentation. -/
theorem extZeroEquivDerivation_apply (ζ : ExtZero R M P) (a : A) :
    extZeroEquivDerivation R M P ζ a
      = ζ ((cotangentH0Equiv P).symm (KaehlerDifferential.D R A a)) :=
  rfl

/-- **The splitting computes degree-zero classes.**  Pulling back to the ambient ring the
derivation attached to a class in `Ext⁰(L, M)` and splitting it recovers the class itself. -/
theorem derSection_compAlgebraMap (ζ : ExtZero R M P) :
    derSection M P ((extZeroEquivDerivation R M P ζ).compAlgebraMap P.Ring)
      = (extZeroEquivDualHZero M P ζ).val := by
  refine cotangentSpace_hom_ext M P fun p => ?_
  have hker : cotangentH0Equiv P
        (Submodule.Quotient.mk (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p))
      = KaehlerDifferential.D R A (algebraMap P.Ring A p) := by
    rw [cotangentH0Equiv_mk]
    change KaehlerDifferential.mapBaseChange R P.Ring A _ = _
    rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  rw [derSection_tmul, one_smul, Derivation.compAlgebraMap_apply,
    extZeroEquivDualHZero_val_apply, extZeroEquivDerivation_apply, ← hker,
    LinearEquiv.symm_apply_apply]

/-- The `R`-derivation of the ambient ring measuring the difference between a chosen lift on the
ambient ring and the lift induced by a solution of the lifting problem. -/
noncomputable def derOfLift (F : Lift R M P.Ring) (f : Lift R M A) :
    Derivation R P.Ring (Coeff M) :=
  F -ᵥ liftToRing M P f

/-- The obstruction cocycle of a lift on the ambient ring is the restriction of `derOfLift`. -/
theorem restrictDer_derOfLift (F : Lift R M P.Ring) (f : Lift R M A) :
    restrictDer R M P (derOfLift M P F f) = obstructionMap R M P F := by
  rw [derOfLift, ← obstructionMap_sub, obstructionMap_liftToRing, sub_zero]

/-- Translating the solution translates the difference derivation. -/
theorem derOfLift_vadd (F : Lift R M P.Ring) (e : Derivation R A (Coeff M)) (f : Lift R M A) :
    derOfLift M P F (e +ᵥ f) = derOfLift M P F f - e.compAlgebraMap P.Ring := by
  refine Derivation.ext fun p => Coeff.ext M ?_
  rw [derOfLift, derOfLift, Derivation.sub_apply, Coeff.val_sub, Lift.vsub_val_apply,
    Lift.vsub_val_apply, liftToRing_hom, liftToRing_hom, Lift.vadd_hom_apply,
    Derivation.compAlgebraMap_apply]
  abel

/-- The obstruction cocycle of `E`: the pullback along `φ` of the obstruction cocycle of a lift
on the ambient ring of the presentation. -/
noncomputable def obstructionCocycleE (F : Lift R M P.Ring) : E.degreeZero →ₗ[A] Coeff M :=
  (obstructionMap R M P F).comp φ.degreeZero

/-- **The obstruction object**: the object of the Picard groupoid `h¹/h⁰(Eᵛ)` with coefficients
in `M` whose isomorphism class is the obstruction class of `E`. -/
noncomputable def obstructionObject (F : Lift R M P.Ring) : (dualComplex E (Coeff M)).quotient :=
  ⟨obstructionCocycleE M P φ F⟩

/-- The vertex of the Picard groupoid of the dual complex. -/
abbrev vertexE (E : LinearTwoTermComplex A) : (dualComplex E (Coeff M)).quotient :=
  ⟨0⟩

/-- The isomorphism class of the obstruction object is the obstruction class of `E`. -/
theorem isoClass_obstructionObject [Nonempty (Lift R M P.Ring)] (F : Lift R M P.Ring) :
    isoClass (obstructionObject M P φ F) = obstructionE M P φ :=
  (obstructionE_eq_h1mk M P φ F).symm

/-- **A solution of the lifting problem trivialises the obstruction object**: it produces an
arrow from the obstruction object to the vertex. -/
noncomputable def trivialisationOfLift (F : Lift R M P.Ring) (f : Lift R M A) :
    obstructionObject M P φ F ⟶ vertexE M E where
  val := -((derSection M P (derOfLift M P F f)).comp φ.degreeOne)
  translate := by
    refine LinearMap.ext fun x => ?_
    have hkey : derSection M P (derOfLift M P F f) (P.cotangentComplex (φ.degreeZero x))
        = obstructionMap R M P F (φ.degreeZero x) := by
      rw [← LinearMap.comp_apply, derSection_comp, restrictDer_derOfLift]
    change obstructionMap R M P F (φ.degreeZero x)
        + -(derSection M P (derOfLift M P F f) (φ.degreeOne (E.differential x))) = 0
    rw [φ.comm x, presComplex_differential, hkey, add_neg_cancel]

@[simp]
theorem trivialisationOfLift_val (F : Lift R M P.Ring) (f : Lift R M A) :
    (trivialisationOfLift M P φ F f).val
      = -((derSection M P (derOfLift M P F f)).comp φ.degreeOne) :=
  rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- The value of the comparison isomorphism on degree-zero classes. -/
theorem extZeroEquivExtZeroE_val (h : IsObstructionTheory φ) (ζ : ExtZero R M P) :
    (extZeroEquivExtZeroE M P φ h ζ).val
      = (extZeroEquivDualHZero M P ζ).val.comp φ.degreeOne :=
  rfl

/-- The splitting of the derivation attached to a class in `Ext⁰(E, M)` recovers the class. -/
theorem derSection_compAlgebraMap_extZeroE (h : IsObstructionTheory φ) (θ : ExtZeroE M E) :
    (derSection M P ((extZeroEEquivDerivation M P φ h θ).compAlgebraMap P.Ring)).comp
        φ.degreeOne = θ.val := by
  have hζ : extZeroEEquivDerivation M P φ h θ
      = extZeroEquivDerivation R M P ((extZeroEquivExtZeroE M P φ h).symm θ) := rfl
  rw [hζ, derSection_compAlgebraMap, ← extZeroEquivExtZeroE_val M P φ h,
    LinearEquiv.apply_symm_apply]

/-- **The bijection between lifts and trivialisations is equivariant** for the two
`Ext⁰(E, M)`-torsor structures: translating a solution by a degree-zero class translates its
trivialisation by the same class. -/
theorem trivialisationOfLift_extZeroEVAdd (h : IsObstructionTheory φ) (F : Lift R M P.Ring)
    (θ : ExtZeroE M E) (f : Lift R M A) :
    (trivialisationOfLift M P φ F (extZeroEVAdd M P φ h θ f)).val
      = (trivialisationOfLift M P φ F f).val + θ.val := by
  rw [trivialisationOfLift_val, trivialisationOfLift_val, extZeroEVAdd, derOfLift_vadd,
    derSection_sub, LinearMap.sub_comp, neg_sub,
    derSection_compAlgebraMap_extZeroE M P φ h θ]
  abel

/-- The zero class acts trivially on the solutions of the lifting problem. -/
theorem extZeroEVAdd_zero (h : IsObstructionTheory φ) (f : Lift R M A) :
    extZeroEVAdd M P φ h 0 f = f := by
  rw [extZeroEVAdd, map_zero]
  exact zero_vadd _ f

/-- **The solutions of the lifting problem are exactly the trivialisations of the obstruction
object.** -/
theorem bijective_trivialisationOfLift (h : IsObstructionTheory φ) (F : Lift R M P.Ring) :
    Function.Bijective (trivialisationOfLift M P φ F) := by
  constructor
  · intro f g hfg
    obtain ⟨θ, hθ, -⟩ := exists_unique_extZeroEVAdd M P φ h f g
    have hval := trivialisationOfLift_extZeroEVAdd M P φ h F θ f
    rw [hθ, hfg] at hval
    have hzero : θ = 0 := by
      refine Subtype.ext ?_
      rw [ZeroMemClass.coe_zero]
      exact (add_left_cancel (a := (trivialisationOfLift M P φ F g).val)
        (by rw [add_zero]; exact hval)).symm
    rw [← hθ, hzero, extZeroEVAdd_zero]
  · intro c
    have hneP : Nonempty (Lift R M P.Ring) := ⟨F⟩
    have hne : Nonempty (Lift R M A) := by
      refine (obstructionE_eq_zero_iff M P φ h).1 ?_
      have hiso : isoClass (obstructionObject M P φ F) = isoClass (vertexE M E) :=
        (isoClass_eq_iff _ _).2 ⟨(CategoryTheory.Groupoid.isoEquivHom _ _).symm c⟩
      rw [isoClass_obstructionObject] at hiso
      rw [hiso]
      exact h1mk_zero
    obtain ⟨f₀⟩ := hne
    refine ⟨extZeroEVAdd M P φ h (homEquivKernel (trivialisationOfLift M P φ F f₀) c) f₀, ?_⟩
    have hval : (trivialisationOfLift M P φ F
          (extZeroEVAdd M P φ h (homEquivKernel (trivialisationOfLift M P φ F f₀) c) f₀)).val
        = c.val := by
      rw [trivialisationOfLift_extZeroEVAdd]
      change (trivialisationOfLift M P φ F f₀).val
        + (c.val - (trivialisationOfLift M P φ F f₀).val) = c.val
      abel
    exact TwoTermQuotient.Hom.ext _ hval

/-- **The lifting groupoid is the torsor of trivialisations of the obstruction object.**  This is
the affine form of the Behrend–Fantechi statement that the solutions of a square-zero lifting
problem are the trivialisations of the obstruction inside the cone stack `h¹/h⁰(Eᵛ)`. -/
noncomputable def liftEquivTrivialisation (h : IsObstructionTheory φ) (F : Lift R M P.Ring) :
    Lift R M A ≃ (obstructionObject M P φ F ⟶ vertexE M E) :=
  Equiv.ofBijective _ (bijective_trivialisationOfLift M P φ h F)

@[simp]
theorem liftEquivTrivialisation_apply (h : IsObstructionTheory φ) (F : Lift R M P.Ring)
    (f : Lift R M A) :
    liftEquivTrivialisation M P φ h F f = trivialisationOfLift M P φ F f :=
  rfl

end Trivialisation

end SquareZero

end CotangentComplex

end GromovWitten.AlgebraicGeometry
