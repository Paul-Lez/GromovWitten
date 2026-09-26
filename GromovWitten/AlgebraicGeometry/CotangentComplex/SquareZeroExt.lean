/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.Derived
import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZero
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Groupoid
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Square-zero deformation theory: Ext groups, base change and the lifting groupoid

`CotangentComplex/SquareZero.lean` constructs, for a square-zero extension `B → B ⧸ M` and a
presentation `P : Algebra.Extension R A` of an `R`-algebra `A` mapping to `B ⧸ M`, the
obstruction class in the cokernel `ObstructionGroup R M P` of
`Hom_A(A ⊗ Ω[P.Ring⁄R], M) → Hom_A(I ⧸ I², M)`.  This file completes that picture.

## Main results

* `restrictHom`, `coboundary_eq_range`, `obstructionGroupEquivExtOne`: the obstruction group is
  literally the cokernel of `Hom_A(K⁰, M) → Hom_A(K⁻¹, M)` for the two-term complex
  `K = [I ⧸ I² → A ⊗ Ω]` of `AffinePresentation.twoTerm`, i.e. the naive `Ext¹` of that complex.
* `cotangentH0Equiv`, `extZeroEquivDerivation`: the degree-zero cohomology of `K` is `Ω[A⁄R]`,
  so `Ext⁰(K, M) = Hom_A(H⁰K, M) = Der_R(A, M)`, and `exists_unique_extZeroVAdd` proves that the
  lifts form a simply transitive set under this `Ext⁰`.
* `baseIdeal`, `isSquareZero_baseIdeal`, `basePush`, `obstruction_baseChange`: base change of a
  square-zero extension along `R → R'` and naturality of the obstruction class; over a flat
  `R → R'` the base-changed kernel is `R' ⊗[R] M` (`range_baseCoeffMap`, `baseIdealEquiv`).
* `Aut.instGroup`, `LiftHom`, `instGroupoidLift`, `nonempty_liftHom_iff`, `endEquivKer`,
  `liftIsoClassEquiv`: the automorphisms of the extension form a group isomorphic to
  `Der_R(B ⧸ M, M)`, the lifts form a groupoid, its isomorphism classes are a torsor under
  `Der_R(A, M)` modulo the automorphism derivations, and the automorphism group of every lift is
  the kernel of `Der_R(B ⧸ M, M) → Der_R(A, M)`.
* `unobstructed` point case: `obstruction_eq_zero_of_formallySmooth`,
  `obstruction_mvPolynomial_eq_zero`, `subsingleton_obstructionGroup_of_ker_eq_bot`.
* `chainHomEquiv`, `nonempty_homotopy_iff`, `homotopyExtOneEquiv`: `Ext¹` computed in the
  homotopy category of cochain complexes, `Hom_{K(ModuleCat A)}(K, M[1])`, is the obstruction
  group; this needs no hypothesis on the presentation.  Likewise `chainHomEquivZero`,
  `extZeroEquivSubtype` and `homotopyExtZeroEquiv` compute `Hom_{K(ModuleCat A)}(K, M[0])` as
  `Hom_A(H⁰K, M) = Der_R(A, M)`. Under projectivity of both terms,
  `derivedExtZeroEquiv` passes to the derived category.
* `derivedExtOneEquiv`, `obstructionGroupEquivDerivedExt`,
  `obstructionGroupEquivDerivedExt_obstruction_eq_zero_iff`: when both terms of `K` are
  projective the previous identification is the honest derived-category group
  `Ext¹_{D(ModuleCat A)}(K, M)`, and the obstruction class there vanishes exactly when the
  lifting problem is solvable.

Nothing here is supplied as a structure field carrying a conclusion, and there are no `sorry`s
and no new axioms.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace SquareZero

open CategoryTheory

universe u v w t

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
variable (M : Ideal B)

/-! ## The obstruction group as the cokernel of `Hom(K⁰, M) → Hom(K⁻¹, M)` -/

section Cokernel

variable {A : Type w} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{t} R A)

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- Precomposition with the cotangent differential `I ⧸ I² → A ⊗ Ω[P.Ring⁄R]`, i.e. the map
`Hom_A(K⁰, M) → Hom_A(K⁻¹, M)` induced by the differential of `AffinePresentation.twoTerm`. -/
noncomputable def restrictHom :
    (P.CotangentSpace →ₗ[A] Coeff M) →ₗ[A] (P.Cotangent →ₗ[A] Coeff M) where
  toFun ψ := ψ.comp P.cotangentComplex
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem restrictHom_apply (ψ : P.CotangentSpace →ₗ[A] Coeff M) (x : P.Cotangent) :
    restrictHom M P ψ x = ψ (P.cotangentComplex x) :=
  rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- The differential of `AffinePresentation.twoTerm` is the map inducing `restrictHom`. -/
theorem restrictHom_eq_comp_twoTerm (Q : Algebra.Extension.{w} R A)
    (ψ : Q.CotangentSpace →ₗ[A] Coeff M) :
    restrictHom M Q ψ = ψ.comp (AffinePresentation.twoTerm R A Q).differential :=
  rfl

/-- The coboundaries are exactly the image of `Hom_A(K⁰, M) → Hom_A(K⁻¹, M)`. -/
theorem coboundary_eq_range : coboundary R M P = LinearMap.range (restrictHom M P) := by
  refine SetLike.ext fun θ => ?_
  rw [mem_coboundary_iff_comp_cotangentComplex, LinearMap.mem_range]
  exact Iff.rfl

variable (R)

/-- The degree-one `Ext` group of the two-term presentation complex with coefficients in `M`,
computed as the cokernel of `Hom_A(K⁰, M) → Hom_A(K⁻¹, M)`. -/
abbrev ExtOne : Type _ :=
  (P.Cotangent →ₗ[A] Coeff M) ⧸ LinearMap.range (restrictHom M P)

/-- **The obstruction group is `Ext¹` of the two-term presentation complex.** -/
noncomputable def obstructionGroupEquivExtOne : ObstructionGroup R M P ≃ₗ[A] ExtOne R M P :=
  Submodule.quotEquivOfEq _ _ (coboundary_eq_range M P)

@[simp]
theorem obstructionGroupEquivExtOne_mk (θ : P.Cotangent →ₗ[A] Coeff M) :
    obstructionGroupEquivExtOne R M P (Submodule.Quotient.mk θ) = Submodule.Quotient.mk θ :=
  rfl

/-- The obstruction class, viewed in `Ext¹`. -/
noncomputable def extOneObstruction [Nonempty (Lift R M P.Ring)] : ExtOne R M P :=
  obstructionGroupEquivExtOne R M P (obstruction R M P)

/-- **Square-zero deformation theory in `Ext¹`.**  The `Ext¹` obstruction class vanishes exactly
when the lifting problem for `A` is solvable. -/
theorem extOneObstruction_eq_zero_iff [Nonempty (Lift R M P.Ring)] :
    extOneObstruction R M P = 0 ↔ Nonempty (Lift R M A) := by
  rw [extOneObstruction, ← obstruction_eq_zero_iff R M P]
  exact ⟨fun h => (obstructionGroupEquivExtOne R M P).injective (by simpa using h),
    fun h => by rw [h, map_zero]⟩

end Cokernel

/-! ## `Ext⁰` and the torsor of lifts -/

section ExtZero

variable {A : Type w} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{t} R A)

/-- The degree-zero cohomology of the two-term presentation complex. -/
abbrev CotangentH0 : Type _ := P.CotangentSpace ⧸ LinearMap.range P.cotangentComplex

/-- The image of the cotangent differential is the kernel of the map to Kähler
differentials. -/
theorem range_cotangentComplex_eq_ker :
    LinearMap.range P.cotangentComplex = LinearMap.ker P.toKaehler :=
  (LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler).symm

/-- `H⁰` of the two-term presentation complex is the module of Kähler differentials. -/
noncomputable def cotangentH0Equiv : CotangentH0 P ≃ₗ[A] Ω[A⁄R] :=
  (Submodule.quotEquivOfEq _ _ (range_cotangentComplex_eq_ker P)).trans
    (P.toKaehler.quotKerEquivOfSurjective P.toKaehler_surjective)

@[simp]
theorem cotangentH0Equiv_mk (x : P.CotangentSpace) :
    cotangentH0Equiv P (Submodule.Quotient.mk x) = P.toKaehler x :=
  rfl

variable (R)

/-- The degree-zero `Ext` group of the two-term presentation complex with coefficients in `M`,
computed as `Hom_A(H⁰ K, M)`. -/
abbrev ExtZero : Type _ := CotangentH0 P →ₗ[A] Coeff M

/-- **`Ext⁰` of the two-term presentation complex is the module of `R`-derivations of `A` with
values in the kernel `M`.** -/
noncomputable def extZeroEquivDerivation : ExtZero R M P ≃ₗ[A] Derivation R A (Coeff M) :=
  (LinearEquiv.arrowCongr (cotangentH0Equiv P) (LinearEquiv.refl A (Coeff M))).trans
    (KaehlerDifferential.linearMapEquivDerivation R A)

/-- The action of a degree-zero class on a lift. -/
noncomputable def extZeroVAdd (θ : ExtZero R M P) (f : Lift R M A) : Lift R M A :=
  extZeroEquivDerivation R M P θ +ᵥ f

theorem extZeroVAdd_eq (θ : ExtZero R M P) (f : Lift R M A) :
    extZeroVAdd R M P θ f = extZeroEquivDerivation R M P θ +ᵥ f :=
  rfl

@[simp]
theorem extZeroVAdd_hom (θ : ExtZero R M P) (f : Lift R M A) (a : A) :
    (extZeroVAdd R M P θ f).hom a = (extZeroEquivDerivation R M P θ a).val + f.hom a :=
  rfl

/-- **The lifts form a simply transitive set under `Ext⁰`.**  For any two lifts there is a
unique degree-zero class carrying the first to the second. -/
theorem exists_unique_extZeroVAdd (f g : Lift R M A) :
    ∃! θ : ExtZero R M P, extZeroVAdd R M P θ f = g := by
  have hne : Nonempty (Lift R M A) := ⟨f⟩
  refine ⟨(extZeroEquivDerivation R M P).symm (g -ᵥ f), ?_, ?_⟩
  · simp only [extZeroVAdd_eq, LinearEquiv.apply_symm_apply]
    exact vsub_vadd g f
  · intro θ hθ
    refine (extZeroEquivDerivation R M P).injective ?_
    rw [LinearEquiv.apply_symm_apply, ← hθ, extZeroVAdd_eq, vadd_vsub]

/-- Choosing a base lift identifies the lifts with `Ext⁰`. -/
noncomputable def liftEquivExtZero (f₀ : Lift R M A) : Lift R M A ≃ ExtZero R M P :=
  (Lift.equivDerivation f₀).trans (extZeroEquivDerivation R M P).toEquiv.symm

end ExtZero

/-! ## Base change of a square-zero extension -/

section BaseChange

open scoped TensorProduct

variable (R)
variable (R' : Type*) [CommRing R'] [Algebra R R']

/-- The kernel of the base-changed square-zero extension: the ideal of `R' ⊗[R] B` generated by
the image of `M`. -/
noncomputable def baseIdeal : Ideal (R' ⊗[R] B) :=
  Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B) M

theorem baseIdeal_eq_span :
    baseIdeal R M R' =
      Ideal.span ((Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B) '' (M : Set B)) :=
  rfl

theorem includeRight_mem_baseIdeal {m : B} (hm : m ∈ M) :
    (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B) m ∈ baseIdeal R M R' :=
  Ideal.mem_map_of_mem _ hm

/-- **The base change of a square-zero extension is a square-zero extension.**  No flatness
hypothesis is needed for this. -/
instance isSquareZero_baseIdeal [IsSquareZero M] : IsSquareZero (baseIdeal R M R') := by
  refine ⟨?_⟩
  rw [pow_two, baseIdeal_eq_span, Ideal.span_mul_span, Ideal.span_eq_bot]
  rintro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
  obtain ⟨m, hm, rfl⟩ := ha
  obtain ⟨n, hn, rfl⟩ := hb
  rw [← map_mul, mul_eq_zero_of_mem M hm hn, map_zero]

/-- The reduction map from the quotient of the original extension to the quotient of the
base-changed extension. -/
noncomputable def baseQuotientMap :
    (B ⧸ M) →ₐ[R] ((R' ⊗[R] B) ⧸ baseIdeal R M R') :=
  Ideal.quotientMapₐ _ (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B)
    fun _ hm => includeRight_mem_baseIdeal R M R' hm

@[simp]
theorem baseQuotientMap_mk (b : B) :
    baseQuotientMap R M R' (Ideal.Quotient.mk M b) =
      Ideal.Quotient.mk (baseIdeal R M R')
        ((Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B) b) :=
  rfl


/-! ### The base-changed kernel -/

/-- The natural map from the base change of the kernel into the base-changed ambient ring. -/
noncomputable def baseCoeffMap : R' ⊗[R] (↥M) →ₗ[R'] R' ⊗[R] B :=
  LinearMap.baseChange R' (M.subtype.restrictScalars R)

@[simp]
theorem baseCoeffMap_tmul (r : R') (m : ↥M) :
    baseCoeffMap R M R' (r ⊗ₜ[R] m) = r ⊗ₜ[R] (m : B) :=
  rfl

/-- The image of the base-changed kernel is an ideal: it is stable under multiplication. -/
theorem mul_mem_range_baseCoeffMap (a : R' ⊗[R] B) {x : R' ⊗[R] B}
    (hx : x ∈ LinearMap.range (baseCoeffMap R M R')) :
    a * x ∈ LinearMap.range (baseCoeffMap R M R') := by
  obtain ⟨y, rfl⟩ := hx
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa [add_mul] using add_mem ha hb
  | tmul r b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simpa [mul_add] using add_mem hy hz
    | tmul s m =>
      refine ⟨(r * s) ⊗ₜ[R] ⟨b * (m : B), M.mul_mem_left b m.2⟩, ?_⟩
      rw [baseCoeffMap_tmul, baseCoeffMap_tmul, Algebra.TensorProduct.tmul_mul_tmul]

/-- **The kernel of the base-changed square-zero extension is the image of `R' ⊗[R] M`.** -/
theorem range_baseCoeffMap :
    LinearMap.range (baseCoeffMap R M R') =
      Submodule.restrictScalars R' (baseIdeal R M R') := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simpa using add_mem hy hz
    | tmul r m =>
      have h : (r ⊗ₜ[R] (m : B) : R' ⊗[R] B) =
          (r ⊗ₜ[R] (1 : B)) *
            (Algebra.TensorProduct.includeRight (R := R) (A := R') (m : B)) := by
        rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
      rw [baseCoeffMap_tmul, h]
      exact Ideal.mul_mem_left _ _ (includeRight_mem_baseIdeal R M R' m.2)
  · intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨m, hm, rfl⟩
      exact ⟨(1 : R') ⊗ₜ[R] ⟨m, hm⟩, rfl⟩
    · exact zero_mem _
    · intro a b _ _ ha hb
      exact add_mem ha hb
    · intro a x _ hx
      exact mul_mem_range_baseCoeffMap R M R' a hx

/-- Along a flat base change the map `R' ⊗[R] M → R' ⊗[R] B` is injective. -/
theorem injective_baseCoeffMap [Module.Flat R R'] :
    Function.Injective (baseCoeffMap R M R') :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := R')
    (M.subtype.restrictScalars R) Subtype.val_injective

/-- **Base change of the kernel along a flat ring map.**  For `R → R'` flat, the kernel of the
base-changed square-zero extension is `R' ⊗[R] M`. -/
noncomputable def baseIdealEquiv [Module.Flat R R'] :
    (R' ⊗[R] (↥M)) ≃ₗ[R'] ↥(Submodule.restrictScalars R' (baseIdeal R M R')) :=
  (LinearEquiv.ofInjective (baseCoeffMap R M R') (injective_baseCoeffMap R M R')).trans
    (LinearEquiv.ofEq _ _ (range_baseCoeffMap R M R'))

@[simp]
theorem baseIdealEquiv_tmul [Module.Flat R R'] (r : R') (m : ↥M) :
    (baseIdealEquiv R M R' (r ⊗ₜ[R] m) : R' ⊗[R] B) = r ⊗ₜ[R] (m : B) :=
  rfl

section Algebra

variable {A : Type w} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]

/-- `A` acts on the quotient of the base-changed extension through `B ⧸ M`. -/
@[instance_reducible]
noncomputable def baseAlgebra : Algebra A ((R' ⊗[R] B) ⧸ baseIdeal R M R') :=
  ((baseQuotientMap R M R').toRingHom.comp (algebraMap A (B ⧸ M))).toAlgebra

attribute [local instance 100] baseAlgebra

omit [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
theorem algebraMap_baseAlgebra (a : A) :
    algebraMap A ((R' ⊗[R] B) ⧸ baseIdeal R M R') a =
      baseQuotientMap R M R' (algebraMap A (B ⧸ M) a) :=
  rfl

/-- Scalars pass from `R` through `A` to the quotient of the base-changed extension. -/
theorem isScalarTower_baseAlgebra :
    IsScalarTower R A ((R' ⊗[R] B) ⧸ baseIdeal R M R') := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  have h : algebraMap A ((R' ⊗[R] B) ⧸ baseIdeal R M R') (algebraMap R A r) =
      baseQuotientMap R M R' (algebraMap A (B ⧸ M) (algebraMap R A r)) := rfl
  rw [h, ← IsScalarTower.algebraMap_apply R A (B ⧸ M), (baseQuotientMap R M R').commutes]

attribute [local instance] isScalarTower_baseAlgebra

variable [IsSquareZero M]

/-- **Base change of a square-zero extension along `R → R'`**, as a morphism of square-zero
extensions over the structure maps of `A`. -/
noncomputable def basePush : Push R M (baseIdeal R M R') A where
  hom := Algebra.TensorProduct.includeRight
  map_mem := fun _ hm => includeRight_mem_baseIdeal R M R' hm
  compat := fun b a hb => by
    rw [algebraMap_baseAlgebra, ← hb, baseQuotientMap_mk]

omit [Algebra R A] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
@[simp]
theorem basePush_hom (b : B) :
    (basePush R M R' : Push R M (baseIdeal R M R') A).hom b =
      (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B) b :=
  rfl

/-- The base change of a solution of the lifting problem. -/
noncomputable def baseLift (f : Lift R M A) : Lift R (baseIdeal R M R') A :=
  pushLift M (baseIdeal R M R') (basePush R M R') f

omit [IsSquareZero M] in
@[simp]
theorem baseLift_hom (f : Lift R M A) (a : A) :
    (baseLift R M R' f).hom a =
      (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B) (f.hom a) :=
  rfl

omit [IsSquareZero M] in
/-- If the original lifting problem is solvable, so is the base-changed one. -/
theorem nonempty_lift_baseChange [Nonempty (Lift R M A)] :
    Nonempty (Lift R (baseIdeal R M R') A) :=
  ⟨baseLift R M R' (Classical.arbitrary _)⟩

attribute [local instance] nonempty_lift_baseChange

variable (P : Algebra.Extension.{t} R A)

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

omit [IsSquareZero M] in
/-- The base-changed lifting problem on the ambient ring of a presentation is again
solvable. -/
theorem nonempty_lift_baseChange_ring [Nonempty (Lift R M P.Ring)] :
    Nonempty (Lift R (baseIdeal R M R') P.Ring) :=
  nonempty_lift_push M P (baseIdeal R M R') (basePush R M R')

attribute [local instance] nonempty_lift_baseChange_ring

/-- **The obstruction class is natural under base change of the square-zero extension.**  The
obstruction class of the base-changed lifting problem is the image of the original one under the
map of obstruction groups induced by `B → R' ⊗[R] B`. -/
theorem obstruction_baseChange [Nonempty (Lift R M P.Ring)] :
    obstructionGroupMap M P (baseIdeal R M R') (basePush R M R') (obstruction R M P) =
      obstruction R (baseIdeal R M R') P := by
  exact obstructionGroupMap_obstruction M P (baseIdeal R M R') (basePush R M R')

/-- Base change cannot create obstructions: if the base-changed obstruction class is nonzero,
so is the original one. -/
theorem obstruction_ne_zero_of_baseChange [Nonempty (Lift R M P.Ring)]
    (h : obstruction R (baseIdeal R M R') P ≠ 0) : obstruction R M P ≠ 0 := by
  intro h0
  exact h (by rw [← obstruction_baseChange R M R' P, h0, map_zero])

end Algebra

end BaseChange

/-! ## The group of automorphisms of a square-zero extension -/

section AutGroup

variable [IsSquareZero M]

namespace Aut

/-- The derivation attached to `Aut.ofDerivation` is the given one. -/
@[simp]
theorem derivation_ofDerivation (d : Derivation R (B ⧸ M) (Coeff M)) :
    (ofDerivation M d).derivation = d :=
  (equivDerivation M).right_inv d

/-- The identity automorphism of the square-zero extension. -/
def idAut : Aut R M where
  hom := AlgHom.id R B
  mk_hom _ := rfl
  hom_mem _ _ := rfl

omit [IsSquareZero M] in
@[simp]
theorem idAut_hom (b : B) : (idAut M : Aut R M).hom b = b := rfl

/-- The inverse of an automorphism of the square-zero extension. -/
noncomputable def invAut (ψ : Aut R M) : Aut R M := ofDerivation M (-ψ.derivation)

@[simp]
theorem invAut_hom (ψ : Aut R M) (b : B) :
    (invAut M ψ).hom b = b + ((-ψ.derivation) (Ideal.Quotient.mk M b)).val :=
  rfl

/-- The inverse automorphism is a two-sided inverse for composition. -/
theorem invAut_comp (ψ : Aut R M) : (invAut M ψ).comp ψ = idAut M := by
  refine Aut.ext (AlgHom.ext fun b => ?_)
  have h : ((invAut M ψ).comp ψ).hom b =
      ψ.hom b + ((-ψ.derivation) (Ideal.Quotient.mk M (ψ.hom b))).val := rfl
  have hneg : ((-ψ.derivation) (Ideal.Quotient.mk M b) : Coeff M) =
      -(ψ.derivation (Ideal.Quotient.mk M b)) := rfl
  rw [h, ψ.mk_hom, hneg, Coeff.val_neg, derivation_mk, idAut_hom]
  ring

/-- **The automorphisms of a square-zero extension form a group** under composition,
isomorphic (through `Aut.equivDerivation`) to the additive group of derivations
`Der_R(B ⧸ M, M)`. -/
noncomputable instance instGroup : Group (Aut R M) where
  mul ψ φ := ψ.comp φ
  one := idAut M
  inv := invAut M
  mul_assoc _ _ _ := Aut.ext (AlgHom.ext fun _ => rfl)
  one_mul _ := Aut.ext (AlgHom.ext fun _ => rfl)
  mul_one _ := Aut.ext (AlgHom.ext fun _ => rfl)
  inv_mul_cancel ψ := invAut_comp M ψ

@[simp]
theorem mul_hom (ψ φ : Aut R M) (b : B) : (ψ * φ).hom b = ψ.hom (φ.hom b) := rfl

@[simp]
theorem one_hom (b : B) : (1 : Aut R M).hom b = b := rfl

@[simp]
theorem inv_hom (ψ : Aut R M) (b : B) :
    (ψ⁻¹).hom b = b + ((-ψ.derivation) (Ideal.Quotient.mk M b)).val := rfl

@[simp]
theorem one_eq_idAut : (1 : Aut R M) = idAut M := rfl

/-- Composition of automorphisms corresponds to addition of derivations. -/
@[simp]
theorem mul_derivation (ψ φ : Aut R M) : (ψ * φ).derivation = ψ.derivation + φ.derivation :=
  derivation_comp ψ φ

/-- **The automorphism group of a square-zero extension is `Der_R(B ⧸ M, M)`.** -/
noncomputable def mulEquivDerivation :
    Aut R M ≃* Multiplicative (Derivation R (B ⧸ M) (Coeff M)) where
  toEquiv := equivDerivation M
  map_mul' ψ φ := derivation_comp ψ φ

end Aut

end AutGroup

/-! ## The lifting groupoid -/

section LiftGroupoid

variable {A : Type w} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M]

/-- A morphism between two solutions of the square-zero lifting problem: an automorphism of the
extension `B → B ⧸ M` carrying the first lift to the second.  Both fields are data plus a
condition on that data; no conclusion is supplied. -/
@[ext]
structure LiftHom (f g : Lift R M A) where
  /-- The underlying automorphism of the square-zero extension. -/
  aut : Aut R M
  /-- The automorphism intertwines the two lifts. -/
  aut_hom : ∀ a : A, aut.hom (f.hom a) = g.hom a

/-- **The solutions of a square-zero lifting problem form a groupoid**, with the automorphisms
of the extension as morphisms. The objects are algebra lifts and the morphisms are exactly
the automorphisms of `B` over `B ⧸ M` and `M` that intertwine them. This action groupoid
is not an identification with the deformation groupoid of an arbitrary algebraic stack. -/
noncomputable instance instGroupoidLift : Groupoid (Lift R M A) where
  Hom f g := LiftHom M f g
  id f := ⟨1, fun _ => rfl⟩
  comp {f _ h} α β := ⟨β.aut * α.aut, fun a => by
    rw [Aut.mul_hom, α.aut_hom a, β.aut_hom a]⟩
  id_comp _ := LiftHom.ext (mul_one _)
  comp_id _ := LiftHom.ext (one_mul _)
  assoc _ _ _ := LiftHom.ext (mul_assoc _ _ _).symm
  inv {f _} α := ⟨α.aut⁻¹, fun a => by
    rw [← α.aut_hom a, ← Aut.mul_hom, inv_mul_cancel, Aut.one_hom]⟩
  inv_comp _ := LiftHom.ext (mul_inv_cancel _)
  comp_inv _ := LiftHom.ext (inv_mul_cancel _)

@[simp]
theorem liftHom_id_aut (f : Lift R M A) : (𝟙 f : f ⟶ f).aut = 1 := rfl

@[simp]
theorem liftHom_comp_aut {f g h : Lift R M A} (α : f ⟶ g) (β : g ⟶ h) :
    (α ≫ β).aut = β.aut * α.aut := rfl

section AutDerivation

variable (R A)

/-- The restriction of derivations of `B ⧸ M` along the structure map `A → B ⧸ M`.  Its image
is the subgroup of derivations of `A` realised by automorphisms of the extension, and its kernel
is the automorphism group of every lift. -/
noncomputable def autDerivationMap :
    Derivation R (B ⧸ M) (Coeff M) →+ Derivation R A (Coeff M) where
  toFun d :=
    { toLinearMap := d.toLinearMap.comp (IsScalarTower.toAlgHom R A (B ⧸ M)).toLinearMap
      map_one_eq_zero' := by
        change d (algebraMap A (B ⧸ M) 1) = 0
        rw [map_one, d.map_one_eq_zero]
      leibniz' := fun a b => by
        have hsm : ∀ (c : A) (m : Coeff M), (algebraMap A (B ⧸ M) c) • m = c • m :=
          fun _ _ => rfl
        change d (algebraMap A (B ⧸ M) (a * b)) =
          a • d (algebraMap A (B ⧸ M) b) + b • d (algebraMap A (B ⧸ M) a)
        rw [map_mul, d.leibniz, hsm, hsm] }
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem autDerivationMap_apply (d : Derivation R (B ⧸ M) (Coeff M)) (a : A) :
    autDerivationMap R M A d a = d (algebraMap A (B ⧸ M) a) :=
  rfl

end AutDerivation

/-- The difference of a lift with itself is the zero derivation. -/
theorem Lift.vsub_self (f : Lift R M A) : (f -ᵥ f : Derivation R A (Coeff M)) = 0 :=
  Derivation.ext fun a => Coeff.ext M (by simp)

/-- A morphism of lifts moves the first lift by the restriction of its automorphism
derivation. -/
theorem autDerivationMap_aut_derivation {f g : Lift R M A} (α : f ⟶ g) :
    autDerivationMap R M A α.aut.derivation = (g -ᵥ f : Derivation R A (Coeff M)) := by
  refine Derivation.ext fun a => Coeff.ext M ?_
  rw [autDerivationMap_apply, ← Lift.mk_hom f a, Aut.derivation_mk, Lift.vsub_val_apply,
    α.aut_hom a]

/-- **Two lifts are isomorphic in the lifting groupoid exactly when their difference derivation
comes from an automorphism of the square-zero extension.** -/
theorem nonempty_liftHom_iff (f g : Lift R M A) :
    Nonempty (f ⟶ g) ↔
      (g -ᵥ f : Derivation R A (Coeff M)) ∈ (autDerivationMap R M A).range := by
  constructor
  · rintro ⟨α⟩
    exact ⟨α.aut.derivation, autDerivationMap_aut_derivation M α⟩
  · rintro ⟨d, hd⟩
    refine ⟨⟨Aut.ofDerivation M d, fun a => ?_⟩⟩
    have hval : (d (algebraMap A (B ⧸ M) a)).val = g.hom a - f.hom a := by
      rw [← autDerivationMap_apply R M A d a, hd, Lift.vsub_val_apply]
    rw [Aut.ofDerivation_hom, Lift.mk_hom f a, hval]
    ring

/-- The automorphisms of a lift are exactly the derivations of `B ⧸ M` restricting to zero
on `A`: the kernel of `Der_R(B ⧸ M, M) → Der_R(A, M)`.  In particular this group does not
depend on the chosen lift. -/
noncomputable def endEquivKer (f : Lift R M A) :
    (f ⟶ f) ≃ (autDerivationMap R M A).ker where
  toFun α := ⟨α.aut.derivation, by
    rw [AddMonoidHom.mem_ker, autDerivationMap_aut_derivation M α, Lift.vsub_self]⟩
  invFun d := ⟨Aut.ofDerivation M d.1, fun a => by
    have hval : (d.1 (algebraMap A (B ⧸ M) a)).val = 0 := by
      have h : autDerivationMap R M A d.1 = 0 := d.2
      rw [← autDerivationMap_apply R M A d.1 a, h]
      rfl
    rw [Aut.ofDerivation_hom, Lift.mk_hom f a, hval, add_zero]⟩
  left_inv α := LiftHom.ext ((Aut.equivDerivation M).left_inv α.aut)
  right_inv d := Subtype.ext ((Aut.equivDerivation M).right_inv d.1)

@[simp]
theorem endEquivKer_apply_coe (f : Lift R M A) (α : f ⟶ f) :
    ((endEquivKer M f α : (autDerivationMap R M A).ker) : Derivation R (B ⧸ M) (Coeff M))
      = α.aut.derivation :=
  rfl

/-- The identification of the automorphism group of a lift with the kernel of the restriction
map on derivations turns composition into addition. -/
theorem endEquivKer_comp (f : Lift R M A) (α β : f ⟶ f) :
    (endEquivKer M f (α ≫ β) : Derivation R (B ⧸ M) (Coeff M)) =
      (endEquivKer M f α : Derivation R (B ⧸ M) (Coeff M)) +
        (endEquivKer M f β : Derivation R (B ⧸ M) (Coeff M)) := by
  rw [endEquivKer_apply_coe, endEquivKer_apply_coe, endEquivKer_apply_coe, liftHom_comp_aut,
    Aut.mul_derivation, add_comm]


section IsoClasses

variable (R A)

/-- Isomorphism in the lifting groupoid, as an equivalence relation.  Reflexivity, symmetry and
transitivity are witnessed by the identity, the inverse and the composition of the groupoid. -/
def isoSetoid : Setoid (Lift R M A) where
  r f g := Nonempty (f ⟶ g)
  iseqv := ⟨fun f => ⟨𝟙 f⟩, fun ⟨α⟩ => ⟨CategoryTheory.Groupoid.inv α⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α ≫ β⟩⟩

/-- The set of isomorphism classes of solutions of the square-zero lifting problem. -/
def LiftIsoClass : Type _ := Quotient (isoSetoid R M A)

/-- The isomorphism class of a lift. -/
def liftClass (f : Lift R M A) : LiftIsoClass R M A := Quotient.mk (isoSetoid R M A) f

theorem liftClass_surjective : Function.Surjective (liftClass R M A) :=
  Quotient.mk_surjective

variable {R A}

/-- Two lifts have the same isomorphism class exactly when their difference derivation is
realised by an automorphism of the square-zero extension. -/
theorem liftClass_eq_iff (f g : Lift R M A) :
    liftClass R M A f = liftClass R M A g ↔
      (g -ᵥ f : Derivation R A (Coeff M)) ∈ (autDerivationMap R M A).range :=
  (Quotient.eq (r := isoSetoid R M A)).trans (nonempty_liftHom_iff M f g)

variable (R A)

/-- **The isomorphism classes of lifts form a torsor under `Der_R(A, M)` modulo the derivations
that come from automorphisms of the square-zero extension.**  Choosing a lift identifies the two
sets. -/
noncomputable def liftIsoClassEquiv (f₀ : Lift R M A) :
    LiftIsoClass R M A ≃ (Derivation R A (Coeff M) ⧸ (autDerivationMap R M A).range) where
  toFun :=
    Quotient.lift
      (fun f => (QuotientAddGroup.mk (f -ᵥ f₀) :
        Derivation R A (Coeff M) ⧸ (autDerivationMap R M A).range))
      (by
        intro f g hfg
        have hne : Nonempty (Lift R M A) := ⟨f₀⟩
        rw [QuotientAddGroup.eq, neg_add_eq_sub, vsub_sub_vsub_cancel_right]
        exact (nonempty_liftHom_iff M f g).1 hfg)
  invFun :=
    Quotient.lift (fun d => liftClass R M A (d +ᵥ f₀))
      (by
        intro d e hde
        have hne : Nonempty (Lift R M A) := ⟨f₀⟩
        have hde' : -d + e ∈ (autDerivationMap R M A).range :=
          QuotientAddGroup.leftRel_apply.mp hde
        rw [neg_add_eq_sub] at hde'
        rw [liftClass_eq_iff, vadd_vsub_vadd_cancel_right]
        exact hde')
  left_inv := by
    refine Quotient.ind fun f => ?_
    have hne : Nonempty (Lift R M A) := ⟨f₀⟩
    exact congrArg (liftClass R M A) (vsub_vadd f f₀)
  right_inv := by
    refine Quotient.ind fun d => ?_
    have hne : Nonempty (Lift R M A) := ⟨f₀⟩
    exact congrArg QuotientAddGroup.mk (vadd_vsub d f₀)

end IsoClasses

end LiftGroupoid

/-! ## The point case: polynomial and formally smooth algebras -/

section PointCase

variable {A : Type w} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{t} R A)

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- A presentation with trivial kernel has trivial conormal module. -/
theorem subsingleton_cotangent_of_ker_eq_bot (h : P.ker = ⊥) : Subsingleton P.Cotangent := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective y
  have hx : x = 0 := Subtype.ext (by simpa [h] using x.2)
  have hy : y = 0 := Subtype.ext (by simpa [h] using y.2)
  rw [hx, hy]

omit [IsScalarTower R A (B ⧸ M)] in
/-- A presentation with trivial kernel — the tautological presentation of `A` by itself — has
trivial obstruction group, so its lifting problems are unobstructed. -/
theorem subsingleton_obstructionGroup_of_ker_eq_bot (h : P.ker = ⊥) :
    Subsingleton (ObstructionGroup R M P) := by
  have hc : Subsingleton P.Cotangent := subsingleton_cotangent_of_ker_eq_bot P h
  have hhom : Subsingleton (P.Cotangent →ₗ[A] Coeff M) :=
    ⟨fun θ η => LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg Submodule.Quotient.mk (Subsingleton.elim x y)

variable [Algebra.FormallySmooth R A]

/-- **Point case.**  For a formally smooth algebra — for instance a polynomial algebra, the
"point case" of the affine presentation — every square-zero lifting problem is solvable. -/
theorem nonempty_lift_of_formallySmooth : Nonempty (Lift R M A) :=
  inferInstance

/-- **Point case.**  For a formally smooth algebra the obstruction class of every presentation
vanishes: the lifting problem is unobstructed. -/
theorem obstruction_eq_zero_of_formallySmooth [Nonempty (Lift R M P.Ring)] :
    obstruction R M P = 0 :=
  (obstruction_eq_zero_iff R M P).2 inferInstance

/-- **Point case, in `Ext¹`.**  For a formally smooth algebra the `Ext¹` obstruction class of
every presentation vanishes. -/
theorem extOneObstruction_eq_zero_of_formallySmooth [Nonempty (Lift R M P.Ring)] :
    extOneObstruction R M P = 0 := by
  rw [extOneObstruction, obstruction_eq_zero_of_formallySmooth M P, map_zero]

/-- **Point case.**  The lifting groupoid of a formally smooth algebra is nonempty. -/
theorem nonempty_liftIsoClass : Nonempty (LiftIsoClass R M A) :=
  ⟨liftClass R M A (Classical.arbitrary _)⟩

end PointCase

section Polynomial

variable {ι : Type*}
variable [Algebra (MvPolynomial ι R) (B ⧸ M)] [IsScalarTower R (MvPolynomial ι R) (B ⧸ M)]
variable [IsSquareZero M]

/-- **Point case for polynomial algebras.**  Every square-zero lifting problem for a polynomial
algebra over `R` is solvable. -/
theorem nonempty_lift_mvPolynomial : Nonempty (Lift R M (MvPolynomial ι R)) :=
  inferInstance

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- **Point case for polynomial algebras.**  The obstruction class of every presentation of a
polynomial algebra vanishes. -/
theorem obstruction_mvPolynomial_eq_zero (P : Algebra.Extension.{t} R (MvPolynomial ι R))
    [Nonempty (Lift R M P.Ring)] : obstruction R M P = 0 :=
  obstruction_eq_zero_of_formallySmooth M P

end Polynomial

/-! ## `Ext¹` in the homotopy category and in the derived category -/

section Derived

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable (R)
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{v} R A)

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- The kernel `M` of the square-zero extension, viewed as the cochain complex `M[1]`: the
module `M` placed in cohomological degree `-1`. -/
noncomputable abbrev coeffComplex (A : Type v) [CommRing A] [Algebra A (B ⧸ M)] :
    CochainComplex (ModuleCat.{v} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{v} A) (ComplexShape.up ℤ) (-1)).obj
    (ModuleCat.of A (Coeff M))

omit [Algebra R B] [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
/-- Every degree of `M[1]` other than `-1` is a zero object. -/
theorem isZero_coeffComplex_X (i : ℤ) (hi : i ≠ -1) : IsZero ((coeffComplex M A).X i) :=
  isZero_single_obj_X _ _ _ i hi

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
/-- Every degree of the presentation complex other than `-1` and `0` is a zero object. -/
theorem isZero_presentationComplex_X (i : ℤ) (h1 : i ≠ -1) (h0 : i ≠ 0) :
    IsZero ((AffinePresentation.cochainComplex R A P).X i) :=
  (AffinePresentation.twoTerm R A P).toCochainComplex_X_isZero i h1 h0

omit [Algebra R B] [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
/-- In degree `-1` the complex `M[1]` is the coefficient module on the nose. -/
theorem singleObjXIsoOfEq_coeffComplex (h : (-1 : ℤ) = -1) :
    singleObjXIsoOfEq (ComplexShape.up ℤ) (-1) (ModuleCat.of A (Coeff M)) (-1) h = Iso.refl _ :=
  rfl

omit [Algebra R B] [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
/-- The canonical isomorphism in degree `-1` of `M[1]` is the identity. -/
theorem singleObjXSelf_coeffComplex :
    singleObjXSelf (ComplexShape.up ℤ) (-1) (ModuleCat.of A (Coeff M)) = Iso.refl _ :=
  rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- Two morphisms of complexes into `M[1]` agree as soon as they agree in degree `-1`. -/
theorem hom_ext_to_coeffComplex {K : CochainComplex (ModuleCat.{v} A) ℤ}
    {f g : K ⟶ coeffComplex M A} (h : f.f (-1) = g.f (-1)) : f = g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : i = -1
  · subst hi
    exact h
  · exact (isZero_coeffComplex_X M i hi).eq_of_tgt _ _

/-- **Morphisms of complexes `K ⟶ M[1]` are exactly the `A`-linear maps `I ⧸ I² → M`.** -/
noncomputable def chainHomEquiv :
    (AffinePresentation.cochainComplex R A P ⟶ coeffComplex M A) ≃
      (P.Cotangent →ₗ[A] Coeff M) where
  toFun f :=
    (f.f (-1) ≫
      (singleObjXSelf (ComplexShape.up ℤ) (-1) (ModuleCat.of A (Coeff M))).hom).hom
  invFun θ :=
    mkHomToSingle (ModuleCat.ofHom θ) (fun i hi => by
      have hi' : i = -2 := by
        simp only [ComplexShape.up_Rel] at hi
        omega
      subst hi'
      exact (isZero_presentationComplex_X R P (-2) (by omega) (by omega)).eq_of_src _ _)
  left_inv f := by
    refine hom_ext_to_coeffComplex M ?_
    dsimp only
    simp [mkHomToSingle, singleObjXIsoOfEq_coeffComplex, singleObjXSelf_coeffComplex]
    rfl
  right_inv θ := by
    dsimp only
    simp [mkHomToSingle, singleObjXIsoOfEq_coeffComplex, singleObjXSelf_coeffComplex]
    rfl

/-- The difference of two chain maps into `M[1]` that factors through the differential gives a
homotopy between them. -/
noncomputable def homotopyOfFactor {K : CochainComplex (ModuleCat.{v} A) ℤ}
    (f g : K ⟶ coeffComplex M A) (ψ : K.X 0 ⟶ (coeffComplex M A).X (-1))
    (hfg : f.f (-1) = K.d (-1) 0 ≫ ψ + g.f (-1)) : Homotopy f g where
  hom i j :=
    if h : i = 0 ∧ j = -1 then
      (K.XIsoOfEq h.1).hom ≫ ψ ≫ ((coeffComplex M A).XIsoOfEq h.2.symm).hom
    else 0
  zero i j hij := by
    refine dif_neg fun h => hij ?_
    rw [h.1, h.2]
    simp
  comm i := by
    have hprev : prevD i
        (fun i j => if h : i = 0 ∧ j = -1 then
          (K.XIsoOfEq h.1).hom ≫ ψ ≫ ((coeffComplex M A).XIsoOfEq h.2.symm).hom else 0) = 0 := by
      rw [prevD]
      simp
    by_cases hi : i = -1
    · subst hi
      rw [hprev, add_zero, dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      rw [dif_pos ⟨rfl, rfl⟩]
      simpa using hfg
    · rw [(isZero_coeffComplex_X M i hi).eq_of_tgt (f.f i) 0,
        (isZero_coeffComplex_X M i hi).eq_of_tgt (g.f i) 0, hprev,
        dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp)]
      rw [dif_neg (fun h => hi h.2)]
      simp

/-- Conversely, a homotopy between two chain maps into `M[1]` exhibits their difference in
degree `-1` as a factorisation through the differential. -/
theorem eq_of_homotopy_to_coeffComplex {K : CochainComplex (ModuleCat.{v} A) ℤ}
    {f g : K ⟶ coeffComplex M A} (h : Homotopy f g) :
    f.f (-1) = K.d (-1) 0 ≫ h.hom 0 (-1) + g.f (-1) := by
  have hcomm := h.comm (-1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp), prevD] at hcomm
  simpa using hcomm


omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
/-- The differential of the presentation complex from degree `-1` to degree `0` is the cotangent
differential `I ⧸ I² → A ⊗ Ω`. -/
theorem presentationComplex_d :
    (AffinePresentation.cochainComplex R A P).d (-1) 0 = ModuleCat.ofHom P.cotangentComplex :=
  (AffinePresentation.twoTerm R A P).toCochainComplex_d_negOne_zero

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- A chain map `K ⟶ M[1]` is its degree `-1` component. -/
theorem chainHomEquiv_apply (f : AffinePresentation.cochainComplex R A P ⟶ coeffComplex M A) :
    chainHomEquiv R M P f = ModuleCat.Hom.hom (f.f (-1)) :=
  rfl

/-- The degree `(0, -1)` component of a homotopy between chain maps into `M[1]`, as an
`A`-linear map `A ⊗ Ω → M`.  This is the map exhibiting the difference as a coboundary. -/
noncomputable def homotopyComponent
    {f g : AffinePresentation.cochainComplex R A P ⟶ coeffComplex M A} (h : Homotopy f g) :
    P.CotangentSpace →ₗ[A] Coeff M :=
  ModuleCat.Hom.hom (eqToHom (AffinePresentation.cochainComplex_X_zero R A P).symm ≫
    h.hom 0 (-1) ≫
      (singleObjXSelf (ComplexShape.up ℤ) (-1) (ModuleCat.of A (Coeff M))).hom)

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem homotopyComponent_apply
    {f g : AffinePresentation.cochainComplex R A P ⟶ coeffComplex M A} (h : Homotopy f g)
    (y : P.CotangentSpace) :
    homotopyComponent R M P h y = ModuleCat.Hom.hom (h.hom 0 (-1)) y :=
  rfl

/-- **Two chain maps `K ⟶ M[1]` are homotopic exactly when the corresponding `A`-linear maps
`I ⧸ I² → M` differ by a coboundary.** -/
theorem nonempty_homotopy_iff
    (f g : AffinePresentation.cochainComplex R A P ⟶ coeffComplex M A) :
    Nonempty (Homotopy f g) ↔
      chainHomEquiv R M P f - chainHomEquiv R M P g ∈ coboundary R M P := by
  rw [coboundary_eq_range]
  constructor
  · rintro ⟨h⟩
    refine ⟨homotopyComponent R M P h, LinearMap.ext fun x => ?_⟩
    have key := eq_of_homotopy_to_coeffComplex M h
    rw [presentationComplex_d] at key
    have key2 : chainHomEquiv R M P f x =
        homotopyComponent R M P h (P.cotangentComplex x) + chainHomEquiv R M P g x := by
      rw [chainHomEquiv_apply, chainHomEquiv_apply, homotopyComponent_apply, key,
        ModuleCat.hom_add]
      rfl
    rw [restrictHom_apply, LinearMap.sub_apply, key2]
    abel
  · rintro ⟨ψ, hψ⟩
    have hψ' : ψ.comp P.cotangentComplex =
        chainHomEquiv R M P f - chainHomEquiv R M P g := hψ
    refine ⟨homotopyOfFactor M f g (ModuleCat.ofHom ψ) ?_⟩
    have goal2 : ModuleCat.ofHom (chainHomEquiv R M P f) =
        ModuleCat.ofHom (ψ.comp P.cotangentComplex + chainHomEquiv R M P g) := by
      rw [hψ', sub_add_cancel]
    exact goal2

/-- `Ext¹` of the two-term presentation complex, computed in the homotopy category of cochain
complexes of `A`-modules: the homotopy classes of chain maps `K ⟶ M[1]`. -/
noncomputable abbrev HomotopyExtOne : Type _ :=
  (HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).obj
      (AffinePresentation.cochainComplex R A P) ⟶
    (HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).obj (coeffComplex M A)

/-- **The obstruction group is `Ext¹` of the two-term complex of the presentation**, computed as
the group of homotopy classes of chain maps into `M[1]`. -/
noncomputable def homotopyExtOneEquiv : ObstructionGroup R M P ≃ HomotopyExtOne R M P where
  toFun :=
    Quotient.lift
      (fun θ => (HomotopyCategory.quotient _ _).map ((chainHomEquiv R M P).symm θ))
      (by
        intro θ θ' hθ
        have hmem : θ - θ' ∈ coboundary R M P :=
          (Submodule.Quotient.eq _).1 (Quotient.sound hθ)
        refine HomotopyCategory.eq_of_homotopy _ _ ?_
        refine ((nonempty_homotopy_iff R M P _ _).2 ?_).some
        rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  invFun x := Submodule.Quotient.mk (chainHomEquiv R M P (Quot.out x))
  left_inv := by
    refine Quotient.ind fun θ => ?_
    refine (Submodule.Quotient.eq _).2 ?_
    have key : chainHomEquiv R M P
          (Quot.out ((HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).map
            ((chainHomEquiv R M P).symm θ))) -
          chainHomEquiv R M P ((chainHomEquiv R M P).symm θ) ∈ coboundary R M P :=
      (nonempty_homotopy_iff R M P _ _).1 ⟨HomotopyCategory.homotopyOutMap _⟩
    rw [Equiv.apply_symm_apply] at key
    exact key
  right_inv x := by
    have h : (chainHomEquiv R M P).symm (chainHomEquiv R M P (Quot.out x)) = Quot.out x :=
      (chainHomEquiv R M P).symm_apply_apply _
    change (HomotopyCategory.quotient _ _).map
      ((chainHomEquiv R M P).symm (chainHomEquiv R M P (Quot.out x))) = x
    rw [h]
    exact HomotopyCategory.quotient_map_out x

/-! ### Passing to the derived category -/

attribute [local instance] HasDerivedCategory.standard

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
/-- If both terms of the two-term presentation complex are projective, the complex is
K-projective, so its morphisms in the derived category are computed by homotopy classes. -/
theorem isKProjective_presentationComplex
    [hneg : Projective (ModuleCat.of A P.Cotangent)]
    [hzero : Projective (ModuleCat.of A P.CotangentSpace)] :
    (AffinePresentation.cochainComplex R A P).IsKProjective := by
  have hle : (AffinePresentation.cochainComplex R A P).IsStrictlyLE 0 :=
    (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
      isZero_presentationComplex_X R P i (by omega) (by omega)
  have hproj : ∀ n, Projective ((AffinePresentation.cochainComplex R A P).X n) := by
    intro n
    by_cases h1 : n = -1
    · subst h1
      exact hneg
    · by_cases h0 : n = 0
      · subst h0
        exact hzero
      · exact (isZero_presentationComplex_X R P n h1 h0).projective
  exact CochainComplex.isKProjective_of_projective _ 0

/-- **The obstruction group is `Ext¹` in the derived category of `A`-modules** whenever the
two terms of the presentation complex are projective (for instance for a presentation by a
regular sequence, or whenever the conormal module is projective). -/
noncomputable def derivedExtOneEquiv
    [Projective (ModuleCat.of A P.Cotangent)] [Projective (ModuleCat.of A P.CotangentSpace)] :
    ObstructionGroup R M P ≃
      (DerivedCategory.Q.obj (AffinePresentation.cochainComplex R A P) ⟶
        DerivedCategory.Q.obj (coeffComplex M A)) :=
  have := isKProjective_presentationComplex R P
  (homotopyExtOneEquiv R M P).trans
    (Equiv.ofBijective _
      (CochainComplex.IsKProjective.Qh_map_bijective (AffinePresentation.cochainComplex R A P)
        ((HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).obj
          (coeffComplex M A))))

omit [Algebra R B] [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
/-- The complex `M[1]` represents the shift by one of the coefficient module in the derived
category. -/
noncomputable def coeffComplexIso :
    DerivedCategory.Q.obj (coeffComplex M A) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
        (ModuleCat.of A (Coeff M)))⟦(1 : ℤ)⟧ :=
  (((DerivedCategory.singleFunctors (ModuleCat.{v} A)).shiftIso 1 (-1) 0
    (by ring)).app (ModuleCat.of A (Coeff M))).symm

/-- **`Ext¹` of the affine cotangent complex with coefficients in the kernel is the obstruction
group.**  This identifies the cokernel `ObstructionGroup R M P` with the derived `Ext¹` of the
derived object `AffinePresentation.derivedObject R A P` of the presentation. -/
noncomputable def obstructionGroupEquivDerivedExt
    [Projective (ModuleCat.of A P.Cotangent)] [Projective (ModuleCat.of A P.CotangentSpace)] :
    ObstructionGroup R M P ≃
      DerivedExt (AffinePresentation.derivedObject R A P)
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A (Coeff M))) 1 :=
  (derivedExtOneEquiv R M P).trans (Iso.homCongr (Iso.refl _) (coeffComplexIso M (A := A)))

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- The zero linear map corresponds to the zero chain map. -/
theorem chainHomEquiv_zero : chainHomEquiv R M P 0 = 0 := rfl

/-- The identification with homotopy classes sends the zero class to zero. -/
theorem homotopyExtOneEquiv_zero : homotopyExtOneEquiv R M P 0 = 0 := by
  have h0 : (chainHomEquiv R M P).symm 0 = 0 :=
    (chainHomEquiv R M P).injective (by rw [Equiv.apply_symm_apply, chainHomEquiv_zero])
  have hz : (0 : ObstructionGroup R M P) = Submodule.Quotient.mk 0 := rfl
  rw [hz]
  change (HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).map
    ((chainHomEquiv R M P).symm 0) = 0
  rw [h0, Functor.map_zero]

/-- The identification with derived `Ext¹` sends the zero class to zero. -/
theorem obstructionGroupEquivDerivedExt_zero
    [Projective (ModuleCat.of A P.Cotangent)] [Projective (ModuleCat.of A P.CotangentSpace)] :
    obstructionGroupEquivDerivedExt R M P 0 = 0 := by
  have h1 : derivedExtOneEquiv R M P 0 = 0 := by
    change DerivedCategory.Qh.map (homotopyExtOneEquiv R M P 0) = 0
    rw [homotopyExtOneEquiv_zero, Functor.map_zero]
  change Iso.homCongr (Iso.refl _) (coeffComplexIso M (A := A)) (derivedExtOneEquiv R M P 0) = 0
  rw [h1]
  simp only [Iso.homCongr, Iso.refl_inv, Equiv.coe_fn_mk]
  rw [zero_comp, comp_zero]

/-- **Square-zero deformation theory in derived `Ext¹`.**  The image of the obstruction class in
`Ext¹` of the derived object of the presentation vanishes exactly when the square-zero lifting
problem for `A` is solvable. -/
theorem obstructionGroupEquivDerivedExt_obstruction_eq_zero_iff [Nonempty (Lift R M P.Ring)]
    [Projective (ModuleCat.of A P.Cotangent)] [Projective (ModuleCat.of A P.CotangentSpace)] :
    obstructionGroupEquivDerivedExt R M P (obstruction R M P) = 0 ↔ Nonempty (Lift R M A) := by
  rw [← obstruction_eq_zero_iff R M P]
  constructor
  · intro h
    refine (obstructionGroupEquivDerivedExt R M P).injective ?_
    rw [h, obstructionGroupEquivDerivedExt_zero]
  · intro h
    rw [h, obstructionGroupEquivDerivedExt_zero]

/-! ### `Ext⁰` in the homotopy category and in the derived category -/

/-- The coefficient module `M` viewed as the cochain complex `M[0]`: the module `M` placed in
cohomological degree `0`. -/
noncomputable abbrev coeffComplexZero (A : Type v) [CommRing A] [Algebra A (B ⧸ M)] :
    CochainComplex (ModuleCat.{v} A) ℤ :=
  (HomologicalComplex.single (ModuleCat.{v} A) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of A (Coeff M))

omit [Algebra R B] [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
/-- In degree `0` the complex `M[0]` is the coefficient module on the nose. -/
theorem singleObjXIsoOfEq_coeffComplexZero (h : (0 : ℤ) = 0) :
    singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (ModuleCat.of A (Coeff M)) 0 h = Iso.refl _ :=
  rfl

omit [Algebra R B] [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
/-- The canonical isomorphism in degree `0` of `M[0]` is the identity. -/
theorem singleObjXSelf_coeffComplexZero :
    singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A (Coeff M)) = Iso.refl _ :=
  rfl

omit [Algebra R B] [Algebra R A] [IsScalarTower R A (B ⧸ M)] in
/-- Every degree of `M[0]` other than `0` is a zero object. -/
theorem isZero_coeffComplexZero_X (i : ℤ) (hi : i ≠ 0) : IsZero ((coeffComplexZero M A).X i) :=
  isZero_single_obj_X _ _ _ i hi

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- Two morphisms of complexes into `M[0]` agree as soon as they agree in degree `0`. -/
theorem hom_ext_to_coeffComplexZero {K : CochainComplex (ModuleCat.{v} A) ℤ}
    {f g : K ⟶ coeffComplexZero M A} (h : f.f 0 = g.f 0) : f = g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : i = 0
  · subst hi
    exact h
  · exact (isZero_coeffComplexZero_X M i hi).eq_of_tgt _ _

/-- **Morphisms of complexes `K ⟶ M[0]` are exactly the `A`-linear maps `A ⊗ Ω → M` that kill
the cotangent differential**, i.e. the `A`-linear maps out of `H⁰ K`. -/
noncomputable def chainHomEquivZero :
    (AffinePresentation.cochainComplex R A P ⟶ coeffComplexZero M A) ≃
      {φ : P.CotangentSpace →ₗ[A] Coeff M // φ.comp P.cotangentComplex = 0} where
  toFun f :=
    ⟨(f.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A (Coeff M))).hom).hom, by
      have hcomm : (AffinePresentation.cochainComplex R A P).d (-1) 0 ≫ f.f 0 = 0 := by
        rw [← f.comm (-1) 0, HomologicalComplex.single_obj_d, comp_zero]
      have key : (AffinePresentation.cochainComplex R A P).d (-1) 0 ≫
          (f.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (Coeff M))).hom) = 0 := by
        rw [← Category.assoc, hcomm, zero_comp]
      exact congrArg ModuleCat.Hom.hom key⟩
  invFun φ :=
    mkHomToSingle (ModuleCat.ofHom φ.1) (fun i hi => by
      have hi' : i = -1 := by
        simp only [ComplexShape.up_Rel] at hi
        omega
      subst hi'
      exact ModuleCat.hom_ext φ.2)
  left_inv f := by
    refine hom_ext_to_coeffComplexZero M ?_
    dsimp only
    simp [mkHomToSingle, singleObjXIsoOfEq_coeffComplexZero, singleObjXSelf_coeffComplexZero]
    rfl
  right_inv φ := by
    refine Subtype.ext ?_
    dsimp only
    simp [mkHomToSingle, singleObjXIsoOfEq_coeffComplexZero, singleObjXSelf_coeffComplexZero]
    rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- Chain maps into `M[0]` admit no nontrivial homotopies: a homotopy between two such maps
forces them to be equal. -/
theorem eq_of_homotopy_to_coeffComplexZero
    {f g : AffinePresentation.cochainComplex R A P ⟶ coeffComplexZero M A} (h : Homotopy f g) :
    f = g := by
  refine hom_ext_to_coeffComplexZero M ?_
  have hcomm := h.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp), prevD] at hcomm
  rw [hcomm]
  have hz : (AffinePresentation.cochainComplex R A P).d 0 1 = 0 :=
    (isZero_presentationComplex_X R P 1 (by omega) (by omega)).eq_of_tgt _ _
  simp [hz]

/-- The `A`-linear maps out of `H⁰` of the two-term complex are exactly the maps out of
`A ⊗ Ω` that kill the cotangent differential. -/
noncomputable def extZeroEquivSubtype :
    ExtZero R M P ≃ {φ : P.CotangentSpace →ₗ[A] Coeff M // φ.comp P.cotangentComplex = 0} where
  toFun ξ := ⟨ξ.comp (LinearMap.range P.cotangentComplex).mkQ, by
    refine LinearMap.ext fun x => ?_
    have hx : (LinearMap.range P.cotangentComplex).mkQ (P.cotangentComplex x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
    simp only [LinearMap.comp_apply, hx, map_zero, LinearMap.zero_apply]⟩
  invFun φ := (LinearMap.range P.cotangentComplex).liftQ φ.1 (by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun φ.2 x)
  left_inv ξ := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  right_inv φ := by
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    rfl

/-- `Ext⁰` of the two-term presentation complex, computed in the homotopy category of cochain
complexes of `A`-modules: the homotopy classes of chain maps `K ⟶ M[0]`. -/
noncomputable abbrev HomotopyExtZero : Type _ :=
  (HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).obj
      (AffinePresentation.cochainComplex R A P) ⟶
    (HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).obj (coeffComplexZero M A)

/-- **`Ext⁰` of the two-term presentation complex is `Hom_A(H⁰ K, M)`**, hence, through
`extZeroEquivDerivation`, the module `Der_R(A, M)` acting simply transitively on the lifts. -/
noncomputable def homotopyExtZeroEquiv : ExtZero R M P ≃ HomotopyExtZero R M P where
  toFun ξ :=
    (HomotopyCategory.quotient _ _).map
      ((chainHomEquivZero R M P).symm (extZeroEquivSubtype R M P ξ))
  invFun x := (extZeroEquivSubtype R M P).symm (chainHomEquivZero R M P (Quot.out x))
  left_inv ξ := by
    dsimp only
    have hout : Quot.out ((HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).map
        ((chainHomEquivZero R M P).symm (extZeroEquivSubtype R M P ξ))) =
        (chainHomEquivZero R M P).symm (extZeroEquivSubtype R M P ξ) :=
      eq_of_homotopy_to_coeffComplexZero R M P (HomotopyCategory.homotopyOutMap _)
    refine Eq.trans (congrArg (fun c => (extZeroEquivSubtype R M P).symm
      (chainHomEquivZero R M P c)) hout) ?_
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  right_inv x := by
    have h : (chainHomEquivZero R M P).symm (extZeroEquivSubtype R M P
        ((extZeroEquivSubtype R M P).symm (chainHomEquivZero R M P (Quot.out x)))) =
        Quot.out x := by
      rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      rfl
    change (HomotopyCategory.quotient _ _).map ((chainHomEquivZero R M P).symm
      (extZeroEquivSubtype R M P ((extZeroEquivSubtype R M P).symm
        (chainHomEquivZero R M P (Quot.out x))))) = x
    rw [h]
    exact HomotopyCategory.quotient_map_out x

/-- **`Ext⁰` in the derived category is `Der_R(A, M)`** when the two terms of the presentation
complex are projective. -/
noncomputable def derivedExtZeroEquiv
    [Projective (ModuleCat.of A P.Cotangent)] [Projective (ModuleCat.of A P.CotangentSpace)] :
    Derivation R A (Coeff M) ≃
      (DerivedCategory.Q.obj (AffinePresentation.cochainComplex R A P) ⟶
        DerivedCategory.Q.obj (coeffComplexZero M A)) :=
  have := isKProjective_presentationComplex R P
  ((extZeroEquivDerivation R M P).toEquiv.symm.trans (homotopyExtZeroEquiv R M P)).trans
    (Equiv.ofBijective _
      (CochainComplex.IsKProjective.Qh_map_bijective (AffinePresentation.cochainComplex R A P)
        ((HomotopyCategory.quotient (ModuleCat.{v} A) (ComplexShape.up ℤ)).obj
          (coeffComplexZero M A))))

end Derived

end SquareZero





end GromovWitten.AlgebraicGeometry.CotangentComplex
