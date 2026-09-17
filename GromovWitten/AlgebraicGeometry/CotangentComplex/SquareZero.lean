/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.AffinePresentation
import Mathlib.Algebra.Torsor.Basic
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!
# Square-zero deformation theory

Let `R` be a commutative ring, let `B` be an `R`-algebra and let `M : Ideal B` be a square-zero
ideal, so that `B → B ⧸ M` is a square-zero extension with kernel `M`.  For an `R`-algebra `A`
equipped with a structure map `A → B ⧸ M`, this file studies the *lifting problem* of finding an
`R`-algebra map `A → B` reducing to the given map.

Everything here is constructed; no conclusion is provided as a structure field, and there are no
`sorry`s or new axioms.

## Main definitions

* `IsSquareZero M` : the condition `M ^ 2 = ⊥` on an ideal, used as a class so that the module
  structures on `M` below can be instances.
* `Coeff M` : the kernel `M`, regarded as a module over every algebra over `B ⧸ M`.  It is a type
  synonym for `↥M` so that the module structures, which all factor through `B ⧸ M`, are instances
  without creating diamonds.
* `Lift R M A` : the type of solutions of the lifting problem for `A`.
* `Lift.sub`, `Lift.vadd` : the difference of two lifts as an `R`-derivation `A → M`, and the
  translation of a lift by a derivation.
* `Aut R M` : `R`-algebra endomorphisms of `B` inducing the identity on `B ⧸ M` and on `M`.
* `Push R M N A` : a morphism of square-zero extensions over the structure maps of `A`.
* `obstructionMap`, `restrictDer`, `coboundary`, `ObstructionGroup`, `obstruction` : for a
  presentation `P : Algebra.Extension R A` with kernel `I`, the obstruction cocycle attached to a
  lift on the ambient ring, the image of `Hom(Ω[P.Ring⁄R], M) = Der_R(P.Ring, M)` inside
  `Hom_A(I ⧸ I², M)`, the resulting cokernel, and the obstruction class in it.

## Main results

* `Lift.instAddTorsor` : the lifts form a torsor under `Derivation R A (Coeff M)` as soon as one
  lift exists; `Lift.equivDerivation` is the resulting bijection after choosing a base point.
* `nonempty_lift`, `subsingleton_lift`, `unique_lift` : a formally smooth algebra admits a lift,
  a formally unramified one admits at most one, hence a formally étale one exactly one.
* `Aut.equivDerivation` : the automorphisms of the square-zero extension are exactly the
  `R`-derivations of `B ⧸ M` with values in `M`, compatibly with composition
  (`Aut.derivation_comp`); every such automorphism is bijective (`Aut.bijective`).
* `obstruction_eq` : the obstruction class does not depend on the chosen lift on the ambient ring
  of the presentation.
* `obstruction_eq_zero_iff` : **the obstruction class vanishes if and only if the lifting problem
  for `A` has a solution.**
* `nonempty_lift_iff_obstruction_eq_zero`, `nonempty_lift_iff_obstruction_generators` : the same
  criterion for a presentation with formally smooth ambient ring, in particular for a
  presentation by a family of generators, where no extra hypothesis is needed.
* `mem_coboundary_iff_comp_cotangentComplex`, `mem_coboundary_iff_comp_twoTerm` : the
  coboundaries are exactly the maps factoring through Mathlib's cotangent complex
  `I ⧸ I² → A ⊗[P.Ring] Ω[P.Ring⁄R]`, equivalently through the differential of the two-term
  complex of `CotangentComplex.AffinePresentation`.
* `obstructionGroupMap_obstruction` : naturality of the obstruction class under a pushforward of
  the coefficient module along a morphism of square-zero extensions.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace SquareZero

universe u v w t

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- An ideal `M` is *square zero* when `M ^ 2 = ⊥`. -/
class IsSquareZero (M : Ideal B) : Prop where
  /-- The defining condition: the square of the ideal is the zero ideal. -/
  sq_eq_bot : M ^ 2 = ⊥

variable (M : Ideal B)

/-- The square of a square-zero ideal is the zero ideal. -/
theorem sq_eq_bot [IsSquareZero M] : M ^ 2 = ⊥ := IsSquareZero.sq_eq_bot

/-- A square-zero ideal is nilpotent. -/
theorem isNilpotent [IsSquareZero M] : IsNilpotent M := ⟨2, sq_eq_bot M⟩

/-- The product of two elements of a square-zero ideal vanishes. -/
theorem mul_eq_zero_of_mem [IsSquareZero M] {x y : B} (hx : x ∈ M) (hy : y ∈ M) :
    x * y = 0 := by
  have hxy : x * y ∈ M ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  simpa [sq_eq_bot M] using hxy

/-- A square-zero ideal is annihilated by itself. -/
theorem isTorsionBySet [IsSquareZero M] : Module.IsTorsionBySet B ↥M M := by
  intro x a
  exact Subtype.ext (by simpa using mul_eq_zero_of_mem M a.2 x.2)

/-- The reduction of `algebraMap R B` is the structure map of the quotient. -/
theorem mk_algebraMap (r : R) :
    Ideal.Quotient.mk M (algebraMap R B r) = algebraMap R (B ⧸ M) r := by
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- The kernel `M` of a square-zero extension `B → B ⧸ M`, regarded as a module over any
algebra over `B ⧸ M`.  This is a type synonym for `↥M`; the synonym exists exactly so that the
module structures below, which all factor through `B ⧸ M`, can be genuine instances. -/
def Coeff (M : Ideal B) : Type v := ↥M

namespace Coeff

instance : AddCommGroup (Coeff M) := inferInstanceAs (AddCommGroup ↥M)

/-- The identity map from the type synonym back to the ideal. -/
def toIdeal (m : Coeff M) : ↥M := m

/-- The identity map from the ideal into the type synonym. -/
def of (m : ↥M) : Coeff M := m

/-- The underlying element of `B` of a coefficient. -/
def val (m : Coeff M) : B := (toIdeal M m : B)

/-- A coefficient built from an element of the ideal. -/
def mk (b : B) (hb : b ∈ M) : Coeff M := of M ⟨b, hb⟩

/-- The underlying element of a coefficient lies in the ideal. -/
theorem val_mem (m : Coeff M) : m.val ∈ M := (toIdeal M m).2

@[ext]
theorem ext {m n : Coeff M} (h : m.val = n.val) : m = n := Subtype.ext h

/-- Coefficients are equal exactly when their underlying elements are. -/
theorem val_injective : Function.Injective (val M) := fun _ _ h => ext M h

@[simp] theorem val_mk (b : B) (hb : b ∈ M) : (mk M b hb).val = b := rfl

@[simp] theorem val_zero : (0 : Coeff M).val = 0 := rfl

@[simp] theorem val_add (m n : Coeff M) : (m + n).val = m.val + n.val := rfl

@[simp] theorem val_neg (m : Coeff M) : (-m).val = -m.val := rfl

@[simp] theorem val_sub (m n : Coeff M) : (m - n).val = m.val - n.val := rfl

@[simp] theorem val_eq_zero_iff {m : Coeff M} : m.val = 0 ↔ m = 0 :=
  ⟨fun h => ext M (by simpa using h), fun h => by rw [h]; simp⟩

/-- `M` is a module over the quotient ring `B ⧸ M`. -/
instance (priority := 1100) instModuleQuotient [IsSquareZero M] : Module (B ⧸ M) (Coeff M) :=
  (isTorsionBySet M).module

/-- `M` is a module over every algebra over `B ⧸ M`. -/
instance (priority := 100) instModule {A : Type w} [CommRing A] [Algebra A (B ⧸ M)]
    [IsSquareZero M] : Module A (Coeff M) :=
  Module.compHom (Coeff M) (algebraMap A (B ⧸ M))

@[simp]
theorem val_smul_mk [IsSquareZero M] (b : B) (m : Coeff M) :
    (Ideal.Quotient.mk M b • m).val = b * m.val := by
  have h : toIdeal M (Ideal.Quotient.mk M b • m) = b • toIdeal M m :=
    Module.IsTorsionBySet.mk_smul (isTorsionBySet M) b (toIdeal M m)
  change ((toIdeal M (Ideal.Quotient.mk M b • m) : ↥M) : B) = _
  rw [h]
  simp [val]

/-- The action of an algebra over `B ⧸ M`, computed through any representative. -/
theorem val_smul {A : Type w} [CommRing A] [Algebra A (B ⧸ M)] [IsSquareZero M]
    (a : A) (b : B) (hb : Ideal.Quotient.mk M b = algebraMap A (B ⧸ M) a) (m : Coeff M) :
    (a • m).val = b * m.val := by
  have h : (a • m : Coeff M) = algebraMap A (B ⧸ M) a • m := rfl
  rw [h, ← hb, val_smul_mk]

/-- The action of an element of the ideal is zero. -/
theorem smul_eq_zero_of_mem [IsSquareZero M] {b : B} (hb : b ∈ M) (m : Coeff M) :
    Ideal.Quotient.mk M b • m = 0 := by
  refine ext M ?_
  rw [val_smul_mk, val_zero]
  exact mul_eq_zero_of_mem M hb m.val_mem

/-- Actions through `B ⧸ M` commute with one another. -/
instance instSMulCommClass {A₁ : Type*} {A₂ : Type*} [CommRing A₁] [CommRing A₂]
    [Algebra A₁ (B ⧸ M)] [Algebra A₂ (B ⧸ M)] [IsSquareZero M] :
    SMulCommClass A₁ A₂ (Coeff M) := by
  refine ⟨fun a₁ a₂ m => ?_⟩
  change algebraMap A₁ (B ⧸ M) a₁ • algebraMap A₂ (B ⧸ M) a₂ • m =
    algebraMap A₂ (B ⧸ M) a₂ • algebraMap A₁ (B ⧸ M) a₁ • m
  rw [← mul_smul, ← mul_smul, mul_comm]

/-- Scalars compose through `B ⧸ M`. -/
instance instIsScalarTower {A₁ : Type*} {A₂ : Type*} [CommRing A₁] [CommRing A₂] [Algebra A₁ A₂]
    [Algebra A₁ (B ⧸ M)] [Algebra A₂ (B ⧸ M)] [IsScalarTower A₁ A₂ (B ⧸ M)] [IsSquareZero M] :
    IsScalarTower A₁ A₂ (Coeff M) := by
  refine ⟨fun a₁ a₂ m => ?_⟩
  change algebraMap A₂ (B ⧸ M) (a₁ • a₂) • m = _
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]
  rfl

end Coeff

/-! ## The lifting problem and its torsor structure -/

section Lift

variable (R)
variable (A : Type w) [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]

/-- The square-zero lifting problem for the structure map `A → B ⧸ M`: the type of `R`-algebra
maps `A → B` whose reduction modulo `M` is the given map. -/
def Lift : Type _ :=
  { f : A →ₐ[R] B // (Ideal.Quotient.mkₐ R M).comp f = IsScalarTower.toAlgHom R A (B ⧸ M) }

namespace Lift

variable {R M A}

/-- The underlying algebra map of a lift. -/
def hom (f : Lift R M A) : A →ₐ[R] B := f.1

/-- A lift reduces to the structure map. -/
@[simp]
theorem mk_hom (f : Lift R M A) (a : A) :
    Ideal.Quotient.mk M (f.hom a) = algebraMap A (B ⧸ M) a :=
  AlgHom.congr_fun f.2 a

@[ext]
theorem ext {f g : Lift R M A} (h : ∀ a, f.hom a = g.hom a) : f = g :=
  Subtype.ext (AlgHom.ext h)

/-- The difference of the values of two lifts lies in `M`. -/
theorem sub_mem (f g : Lift R M A) (a : A) : f.hom a - g.hom a ∈ M := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, mk_hom, mk_hom, sub_self]

variable [IsSquareZero M]

/-- The difference of two lifts, as an `R`-derivation of `A` with values in `M`. -/
def sub (f g : Lift R M A) : Derivation R A (Coeff M) where
  toFun a := Coeff.mk M (f.hom a - g.hom a) (sub_mem f g a)
  map_add' a b := by
    refine Coeff.ext M ?_
    rw [Coeff.val_add, Coeff.val_mk, Coeff.val_mk, Coeff.val_mk, map_add, map_add]
    ring
  map_smul' r a := by
    refine Coeff.ext M ?_
    simp only [RingHom.id_apply]
    rw [Coeff.val_smul M r (algebraMap R B r) (mk_algebraMap M r), Coeff.val_mk, Coeff.val_mk,
      Algebra.smul_def, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
    ring
  map_one_eq_zero' := by
    refine Coeff.ext M ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Coeff.val_mk, Coeff.val_zero, map_one, map_one, sub_self]
  leibniz' a b := by
    refine Coeff.ext M ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have h : (f.hom a - g.hom a) * (f.hom b - g.hom b) = 0 :=
      mul_eq_zero_of_mem M (sub_mem f g a) (sub_mem f g b)
    rw [Coeff.val_add, Coeff.val_smul M a (f.hom a) (mk_hom f a),
      Coeff.val_smul M b (f.hom b) (mk_hom f b), Coeff.val_mk, Coeff.val_mk, Coeff.val_mk,
      map_mul, map_mul]
    linear_combination -h

@[simp]
theorem sub_val (f g : Lift R M A) (a : A) : (sub f g a).val = f.hom a - g.hom a := rfl

/-- Adding a derivation to a lift produces another lift. -/
def vadd (d : Derivation R A (Coeff M)) (f : Lift R M A) : Lift R M A :=
  ⟨{ toFun := fun a => (d a).val + f.hom a
     map_one' := by simp
     map_zero' := by simp
     map_add' := fun a b => by
       simp only [map_add, Coeff.val_add, map_add]
       ring
     map_mul' := fun a b => by
       have h : (d a).val * (d b).val = 0 :=
         mul_eq_zero_of_mem M (d a).val_mem (d b).val_mem
       rw [d.leibniz, Coeff.val_add, Coeff.val_smul M a (f.hom a) (mk_hom f a),
         Coeff.val_smul M b (f.hom b) (mk_hom f b), map_mul]
       linear_combination -h
     commutes' := fun r => by
       simp only [Derivation.map_algebraMap, Coeff.val_zero, zero_add]
       exact f.hom.commutes r }, by
    refine AlgHom.ext fun a => ?_
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (d a).val_mem⟩

@[simp]
theorem vadd_hom (d : Derivation R A (Coeff M)) (f : Lift R M A) (a : A) :
    (vadd d f).hom a = (d a).val + f.hom a := rfl

instance : VAdd (Derivation R A (Coeff M)) (Lift R M A) := ⟨vadd⟩

instance : VSub (Derivation R A (Coeff M)) (Lift R M A) := ⟨sub⟩

@[simp]
theorem vadd_hom_apply (d : Derivation R A (Coeff M)) (f : Lift R M A) (a : A) :
    (d +ᵥ f).hom a = (d a).val + f.hom a := rfl

@[simp]
theorem vsub_val_apply (f g : Lift R M A) (a : A) : ((f -ᵥ g : Derivation R A (Coeff M)) a).val =
    f.hom a - g.hom a := rfl

instance : AddAction (Derivation R A (Coeff M)) (Lift R M A) where
  zero_vadd f := by ext a; simp
  add_vadd d e f := by ext a; simp; ring

/-- The lifts of a square-zero lifting problem form a torsor under the `R`-derivations of `A`
with values in `M`, as soon as one lift exists. -/
instance instAddTorsor [Nonempty (Lift R M A)] :
    AddTorsor (Derivation R A (Coeff M)) (Lift R M A) where
  vsub_vadd' f g := by ext a; simp
  vadd_vsub' d f := by ext a; simp

/-- Two lifts differ by a unique derivation. -/
theorem eq_vadd_iff (f g : Lift R M A) (d : Derivation R A (Coeff M)) :
    f = d +ᵥ g ↔ d = f -ᵥ g := by
  constructor
  · rintro rfl
    ext a
    simp
  · rintro rfl
    ext a
    simp

/-- Choosing a base lift identifies the lifts with the derivations. -/
def equivDerivation (f₀ : Lift R M A) : Lift R M A ≃ Derivation R A (Coeff M) where
  toFun f := f -ᵥ f₀
  invFun d := d +ᵥ f₀
  left_inv f := by ext a; simp
  right_inv d := by ext a; simp

end Lift

end Lift

/-! ## Existence and uniqueness criteria -/

section Criteria

variable (R)
variable (A : Type w) [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M]

/-- Derivations into `M` are the `A`-linear maps out of the Kähler differentials.  This is the
degree-zero deformation module of the square-zero lifting problem. -/
noncomputable def derivationEquivHom :
    (Ω[A⁄R] →ₗ[A] Coeff M) ≃ₗ[A] Derivation R A (Coeff M) :=
  KaehlerDifferential.linearMapEquivDerivation R A

/-- A formally smooth algebra lifts along every square-zero extension. -/
instance nonempty_lift [Algebra.FormallySmooth R A] : Nonempty (Lift R M A) := by
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift (R := R) (A := A) M (isNilpotent M)
    (IsScalarTower.toAlgHom R A (B ⧸ M))
  exact ⟨⟨f, hf⟩⟩

/-- A formally unramified algebra has at most one lift along a square-zero extension. -/
instance subsingleton_lift [Algebra.FormallyUnramified R A] : Subsingleton (Lift R M A) :=
  ⟨fun f g => Subtype.ext (Algebra.FormallyUnramified.comp_injective M (sq_eq_bot M)
    (f.2.trans g.2.symm))⟩

/-- A formally unramified algebra has no nonzero derivations into `M`. -/
instance subsingleton_derivation [Algebra.FormallyUnramified R A] :
    Subsingleton (Derivation R A (Coeff M)) := by
  have key : ∀ (D : Derivation R A (Coeff M)) (a : A), D a = 0 := by
    intro D a
    rw [← D.liftKaehlerDifferential_comp_D a,
      Subsingleton.elim (KaehlerDifferential.D R A a) 0, map_zero]
  exact ⟨fun d e => Derivation.ext fun a => by rw [key d a, key e a]⟩

/-- A formally étale algebra has exactly one lift along every square-zero extension. -/
noncomputable instance unique_lift [Algebra.FormallySmooth R A]
    [Algebra.FormallyUnramified R A] : Unique (Lift R M A) where
  default := Classical.arbitrary _
  uniq _ := Subsingleton.elim _ _

end Criteria

/-! ## Automorphisms of a square-zero extension -/

section Aut

variable (R)
variable [IsSquareZero M]

/-- An automorphism of the square-zero extension `B → B ⧸ M`: an `R`-algebra endomorphism of
`B` inducing the identity on `B ⧸ M` and restricting to the identity on `M`.  The two
properties are conditions on `hom`; nothing is supplied as data beyond that map. -/
@[ext]
structure Aut where
  /-- The underlying endomorphism of the ambient ring. -/
  hom : B →ₐ[R] B
  /-- The endomorphism induces the identity on the quotient. -/
  mk_hom : ∀ b : B, Ideal.Quotient.mk M (hom b) = Ideal.Quotient.mk M b
  /-- The endomorphism restricts to the identity on the kernel. -/
  hom_mem : ∀ m ∈ M, hom m = m

variable {R}

/-- An arbitrary representative in `B` of an element of `B ⧸ M`. -/
noncomputable def rep (x : B ⧸ M) : B := Function.surjInv Ideal.Quotient.mk_surjective x

omit [IsSquareZero M] in
@[simp]
theorem mk_rep (x : B ⧸ M) : Ideal.Quotient.mk M (rep M x) = x :=
  Function.surjInv_eq _ x

namespace Aut

variable {M}

omit [IsSquareZero M] in
/-- The displacement of an automorphism of the extension lies in the kernel. -/
theorem sub_mem (ψ : Aut R M) (b : B) : ψ.hom b - b ∈ M := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ψ.mk_hom, sub_self]

/-- The displacement of an automorphism, as a function on the ambient ring. -/
noncomputable def derivationFun (ψ : Aut R M) (x : B ⧸ M) : Coeff M :=
  Coeff.mk M (ψ.hom (rep M x) - rep M x) (ψ.sub_mem _)

omit [IsSquareZero M] in
@[simp]
theorem derivationFun_mk (ψ : Aut R M) (b : B) :
    (ψ.derivationFun (Ideal.Quotient.mk M b)).val = ψ.hom b - b := by
  have hb : b - rep M (Ideal.Quotient.mk M b) ∈ M := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, mk_rep, sub_self]
  have h := ψ.hom_mem _ hb
  rw [map_sub] at h
  rw [derivationFun, Coeff.val_mk]
  linear_combination -h

/-- The `R`-derivation of `B ⧸ M` with values in `M` attached to an automorphism of the
square-zero extension. -/
noncomputable def derivation (ψ : Aut R M) : Derivation R (B ⧸ M) (Coeff M) where
  toFun := ψ.derivationFun
  map_add' x y := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Coeff.ext M ?_
    rw [Coeff.val_add, ← map_add, derivationFun_mk, derivationFun_mk, derivationFun_mk, map_add]
    ring
  map_smul' r x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Coeff.ext M ?_
    have hsmul : r • Ideal.Quotient.mk M b = Ideal.Quotient.mk M (algebraMap R B r * b) := by
      rw [map_mul, mk_algebraMap, Algebra.smul_def]
    rw [RingHom.id_apply, hsmul, derivationFun_mk,
      Coeff.val_smul M r (algebraMap R B r) (mk_algebraMap M r), derivationFun_mk, map_mul,
      AlgHom.commutes]
    ring
  map_one_eq_zero' := by
    refine Coeff.ext M ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Coeff.val_zero, show (1 : B ⧸ M) = Ideal.Quotient.mk M 1 from (map_one _).symm,
      derivationFun_mk, map_one, sub_self]
  leibniz' x y := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Coeff.ext M ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have hzero : (ψ.hom b - b) * (ψ.hom c - c) = 0 :=
      mul_eq_zero_of_mem M (ψ.sub_mem b) (ψ.sub_mem c)
    rw [← map_mul, Coeff.val_add, Coeff.val_smul_mk, Coeff.val_smul_mk, derivationFun_mk,
      derivationFun_mk, derivationFun_mk, map_mul]
    linear_combination hzero

@[simp]
theorem derivation_mk (ψ : Aut R M) (b : B) :
    (ψ.derivation (Ideal.Quotient.mk M b)).val = ψ.hom b - b :=
  ψ.derivationFun_mk b

variable (M)

/-- The automorphism of the square-zero extension attached to an `R`-derivation of `B ⧸ M`
with values in `M`. -/
noncomputable def ofDerivation (d : Derivation R (B ⧸ M) (Coeff M)) : Aut R M where
  hom :=
    { toFun := fun b => b + (d (Ideal.Quotient.mk M b)).val
      map_one' := by
        rw [map_one, d.map_one_eq_zero, Coeff.val_zero, add_zero]
      map_zero' := by
        rw [map_zero, map_zero, Coeff.val_zero, add_zero]
      map_add' := fun b c => by
        rw [map_add, map_add, Coeff.val_add]
        ring
      map_mul' := fun b c => by
        have hzero : (d (Ideal.Quotient.mk M b)).val * (d (Ideal.Quotient.mk M c)).val = 0 :=
          mul_eq_zero_of_mem M (d _).val_mem (d _).val_mem
        rw [map_mul, d.leibniz, Coeff.val_add, Coeff.val_smul_mk, Coeff.val_smul_mk]
        linear_combination -hzero
      commutes' := fun r => by
        rw [mk_algebraMap, Derivation.map_algebraMap, Coeff.val_zero, add_zero] }
  mk_hom b := by
    change Ideal.Quotient.mk M (b + (d (Ideal.Quotient.mk M b)).val) = _
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (d _).val_mem, add_zero]
  hom_mem m hm := by
    change m + (d (Ideal.Quotient.mk M m)).val = m
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero, Coeff.val_zero, add_zero]

@[simp]
theorem ofDerivation_hom (d : Derivation R (B ⧸ M) (Coeff M)) (b : B) :
    (ofDerivation M d).hom b = b + (d (Ideal.Quotient.mk M b)).val := rfl

/-- **Automorphisms of a square-zero extension are the derivations of the quotient with values
in the kernel.** -/
noncomputable def equivDerivation : Aut R M ≃ Derivation R (B ⧸ M) (Coeff M) where
  toFun ψ := ψ.derivation
  invFun d := ofDerivation M d
  left_inv ψ := by
    refine Aut.ext (AlgHom.ext fun b => ?_)
    rw [ofDerivation_hom, derivation_mk]
    ring
  right_inv d := by
    refine Derivation.ext fun x => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Coeff.ext M ?_
    rw [derivation_mk, ofDerivation_hom]
    ring

variable {M}

/-- The composition of two automorphisms of a square-zero extension. -/
def comp (ψ φ : Aut R M) : Aut R M where
  hom := ψ.hom.comp φ.hom
  mk_hom b := by
    change Ideal.Quotient.mk M (ψ.hom (φ.hom b)) = _
    rw [ψ.mk_hom, φ.mk_hom]
  hom_mem m hm := by
    change ψ.hom (φ.hom m) = m
    rw [φ.hom_mem m hm, ψ.hom_mem m hm]

omit [IsSquareZero M] in
@[simp]
theorem comp_hom (ψ φ : Aut R M) (b : B) : (ψ.comp φ).hom b = ψ.hom (φ.hom b) := rfl

/-- Composition of automorphisms corresponds to addition of derivations. -/
theorem derivation_comp (ψ φ : Aut R M) :
    (ψ.comp φ).derivation = ψ.derivation + φ.derivation := by
  refine Derivation.ext fun x => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Coeff.ext M ?_
  have hfix := ψ.hom_mem _ (φ.sub_mem b)
  rw [map_sub] at hfix
  simp only [Derivation.add_apply, Coeff.val_add, derivation_mk, comp_hom]
  linear_combination hfix

/-- Every automorphism of a square-zero extension is bijective. -/
theorem bijective (ψ : Aut R M) : Function.Bijective ψ.hom := by
  constructor
  · intro b c h
    have hmem : b - c ∈ M := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ψ.mk_hom b, ← ψ.mk_hom c, h, sub_self]
    have hfix := ψ.hom_mem _ hmem
    rw [map_sub, h, sub_self] at hfix
    linear_combination -hfix
  · intro c
    have hv : Ideal.Quotient.mk M (c - (ψ.derivation (Ideal.Quotient.mk M c)).val) =
        Ideal.Quotient.mk M c := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (ψ.derivation _).val_mem, sub_zero]
    have hd := derivation_mk ψ (c - (ψ.derivation (Ideal.Quotient.mk M c)).val)
    rw [hv] at hd
    exact ⟨_, by linear_combination -hd⟩

/-- An automorphism of a square-zero extension, as an algebra equivalence. -/
noncomputable def toAlgEquiv (ψ : Aut R M) : B ≃ₐ[R] B :=
  AlgEquiv.ofBijective ψ.hom ψ.bijective

@[simp]
theorem toAlgEquiv_apply (ψ : Aut R M) (b : B) : ψ.toAlgEquiv b = ψ.hom b := rfl

end Aut

end Aut

/-! ## Pushforward along a morphism of square-zero extensions -/

section Pushforward

variable (R)
variable {C : Type*} [CommRing C] [Algebra R C] (N : Ideal C)
variable (A : Type w) [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [Algebra A (C ⧸ N)]
variable [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A (C ⧸ N)]

/-- A morphism from the square-zero extension `B → B ⧸ M` to the square-zero extension
`C → C ⧸ N`, over the structure maps of `A`.  Both properties are conditions on the ambient
algebra map; no conclusion is supplied as data. -/
structure Push where
  /-- The map of ambient rings. -/
  hom : B →ₐ[R] C
  /-- The map carries `M` into `N`. -/
  map_mem : ∀ m ∈ M, hom m ∈ N
  /-- The induced map on the quotients commutes with the structure maps from `A`. -/
  compat : ∀ (b : B) (a : A), Ideal.Quotient.mk M b = algebraMap A (B ⧸ M) a →
    Ideal.Quotient.mk N (hom b) = algebraMap A (C ⧸ N) a

variable {R A}
variable [IsSquareZero M] [IsSquareZero N] (π : Push R M N A)

/-- Pushforward of coefficients along a morphism of square-zero extensions. -/
def pushCoeff : Coeff M →ₗ[A] Coeff N where
  toFun m := Coeff.mk N (π.hom m.val) (π.map_mem _ m.val_mem)
  map_add' m n := Coeff.ext N (by simp)
  map_smul' a m := Coeff.ext N (by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A (B ⧸ M) a)
    simp only [RingHom.id_apply]
    rw [Coeff.val_mk, Coeff.val_smul M a b hb, map_mul,
      Coeff.val_smul N a (π.hom b) (π.compat b a hb), Coeff.val_mk])

omit [Algebra R A] [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A (C ⧸ N)] in
@[simp]
theorem pushCoeff_val (m : Coeff M) : (pushCoeff M N π m).val = π.hom m.val := rfl

/-- Pushforward of lifts along a morphism of square-zero extensions. -/
def pushLift (f : Lift R M A) : Lift R N A :=
  ⟨π.hom.comp f.hom, AlgHom.ext fun a => π.compat _ a (Lift.mk_hom f a)⟩

omit [IsSquareZero M] [IsSquareZero N] in
@[simp]
theorem pushLift_hom (f : Lift R M A) (a : A) :
    (pushLift M N π f).hom a = π.hom (f.hom a) := rfl

/-- Pushforward of derivations along a morphism of square-zero extensions. -/
def pushDer (d : Derivation R A (Coeff M)) : Derivation R A (Coeff N) :=
  (pushCoeff M N π).compDer d

@[simp]
theorem pushDer_apply (d : Derivation R A (Coeff M)) (a : A) :
    pushDer M N π d a = pushCoeff M N π (d a) := rfl

/-- Pushforward is compatible with the torsor structure on the lifts. -/
theorem pushLift_vsub (f g : Lift R M A) :
    (pushLift M N π f -ᵥ pushLift M N π g : Derivation R A (Coeff N)) =
      pushDer M N π (f -ᵥ g) := by
  refine Derivation.ext fun a => Coeff.ext N ?_
  simp

end Pushforward

/-! ## The obstruction class of an affine presentation -/

section Obstruction

variable (R)
variable {A : Type w} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)] [IsScalarTower R A (B ⧸ M)]
variable [IsSquareZero M] (P : Algebra.Extension.{t} R A)

/-- The ambient ring of a presentation of `A` acts on `B ⧸ M` through `A`. -/
@[instance_reducible]
noncomputable def ringAlgebra : Algebra P.Ring (B ⧸ M) :=
  ((algebraMap A (B ⧸ M)).comp (algebraMap P.Ring A)).toAlgebra

attribute [local instance] ringAlgebra

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
/-- The structure map of the ambient ring factors through `A`. -/
theorem algebraMap_ring :
    (algebraMap P.Ring (B ⧸ M) : P.Ring →+* B ⧸ M) =
      (algebraMap A (B ⧸ M)).comp (algebraMap P.Ring A) :=
  rfl

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] [IsSquareZero M] in
/-- Scalars pass from the ambient ring of a presentation through `A`. -/
theorem isScalarTower_ring : IsScalarTower P.Ring A (B ⧸ M) :=
  IsScalarTower.of_algebraMap_eq' (algebraMap_ring R M P)

attribute [local instance] isScalarTower_ring

omit [IsSquareZero M] in
/-- Scalars pass from `R` through the ambient ring of a presentation. -/
theorem isScalarTower_base : IsScalarTower R P.Ring (B ⧸ M) := by
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  change _ = algebraMap A (B ⧸ M) (algebraMap P.Ring A (algebraMap R P.Ring r))
  rw [← IsScalarTower.algebraMap_apply R P.Ring A r,
    ← IsScalarTower.algebraMap_apply R A (B ⧸ M) r]

attribute [local instance] isScalarTower_base

variable {R P}

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- The chosen section of a presentation acts on coefficients as the corresponding element
of `A`. -/
theorem smul_σ (a : A) (m : Coeff M) : P.σ a • m = a • m := by
  have h : algebraMap P.Ring (B ⧸ M) (P.σ a) = algebraMap A (B ⧸ M) a := by
    change algebraMap A (B ⧸ M) (algebraMap P.Ring A (P.σ a)) = _
    rw [P.algebraMap_σ]
  change algebraMap P.Ring (B ⧸ M) (P.σ a) • m = algebraMap A (B ⧸ M) a • m
  rw [h]

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
/-- Elements of the kernel of a presentation act trivially on the coefficients. -/
theorem ker_smul_eq_zero {p : P.Ring} (hp : p ∈ P.ker) (m : Coeff M) : p • m = 0 := by
  have h : algebraMap P.Ring (B ⧸ M) p = 0 := by
    change algebraMap A (B ⧸ M) (algebraMap P.Ring A p) = 0
    rw [RingHom.mem_ker.mp hp, map_zero]
  change algebraMap P.Ring (B ⧸ M) p • m = 0
  rw [h, zero_smul]

/-- The descent of a `P.Ring`-linear map on the kernel through `I ⧸ I²`. -/
noncomputable def descendQ (g : ↥P.ker →ₗ[P.Ring] Coeff M) :
    P.ker.Cotangent →ₗ[P.Ring] Coeff M :=
  Submodule.liftQ _ g (Submodule.smul_le.2 fun p hp y _ =>
    LinearMap.mem_ker.2 (by rw [map_smul]; exact ker_smul_eq_zero M hp _))

/-- A `P.Ring`-linear map on the kernel of a presentation descends to an `A`-linear map on the
conormal module `I ⧸ I²`. -/
noncomputable def descend (g : ↥P.ker →ₗ[P.Ring] Coeff M) : P.Cotangent →ₗ[A] Coeff M where
  toFun x := descendQ M g x.val
  map_add' x y := by rw [Algebra.Extension.Cotangent.val_add, map_add]
  map_smul' a x := by
    rw [RingHom.id_apply, Algebra.Extension.Cotangent.val_smul, map_smul, smul_σ M]

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem descend_mk (g : ↥P.ker →ₗ[P.Ring] Coeff M) (x : ↥P.ker) :
    descend M g (Algebra.Extension.Cotangent.mk x) = g x := rfl

/-- The restriction to the kernel of an `R`-derivation of the ambient ring. -/
noncomputable def derKerMap (d : Derivation R P.Ring (Coeff M)) : ↥P.ker →ₗ[P.Ring] Coeff M where
  toFun x := d (x : P.Ring)
  map_add' x y := by simp
  map_smul' p x := by
    simp only [RingHom.id_apply, Submodule.coe_smul, smul_eq_mul, d.leibniz]
    rw [ker_smul_eq_zero M x.2 (d p), add_zero]

omit [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem derKerMap_apply (d : Derivation R P.Ring (Coeff M)) (x : ↥P.ker) :
    derKerMap M d x = d (x : P.Ring) := rfl

/-- The restriction to the kernel of a lift of the structure map on the ambient ring. -/
noncomputable def kerMap (F : Lift R M P.Ring) : ↥P.ker →ₗ[P.Ring] Coeff M where
  toFun x := Coeff.mk M (F.hom (x : P.Ring)) (by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Lift.mk_hom]
    change algebraMap A (B ⧸ M) (algebraMap P.Ring A (x : P.Ring)) = 0
    rw [RingHom.mem_ker.mp x.2, map_zero])
  map_add' x y := Coeff.ext M (by simp)
  map_smul' p x := Coeff.ext M (by
    simp only [RingHom.id_apply]
    rw [Coeff.val_smul M p (F.hom p) (Lift.mk_hom F p), Coeff.val_mk, Coeff.val_mk]
    simp only [Submodule.coe_smul, smul_eq_mul, map_mul])

@[simp]
theorem kerMap_val (F : Lift R M P.Ring) (x : ↥P.ker) :
    (kerMap M F x).val = F.hom (x : P.Ring) := rfl

variable (R P)

/-- The obstruction cocycle attached to a lift of the structure map on the ambient ring of a
presentation: the induced `A`-linear map `I ⧸ I² → M`. -/
noncomputable def obstructionMap (F : Lift R M P.Ring) : P.Cotangent →ₗ[A] Coeff M :=
  descend M (kerMap M F)

/-- The `A`-linear map `I ⧸ I² → M` obtained by restricting an `R`-derivation of the ambient
ring; this is the image of `Hom(Ω[P.Ring⁄R], M)` in `Hom(I ⧸ I², M)`. -/
noncomputable def restrictDer (d : Derivation R P.Ring (Coeff M)) : P.Cotangent →ₗ[A] Coeff M :=
  descend M (derKerMap M d)

variable {R P}

@[simp]
theorem obstructionMap_mk_val (F : Lift R M P.Ring) (x : ↥P.ker) :
    (obstructionMap R M P F (Algebra.Extension.Cotangent.mk x)).val = F.hom (x : P.Ring) := rfl

omit [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem restrictDer_mk (d : Derivation R P.Ring (Coeff M)) (x : ↥P.ker) :
    restrictDer R M P d (Algebra.Extension.Cotangent.mk x) = d (x : P.Ring) := rfl

omit [IsScalarTower R A (B ⧸ M)] in
/-- Restriction of derivations is additive. -/
theorem restrictDer_add (d e : Derivation R P.Ring (Coeff M)) :
    restrictDer R M P (d + e) = restrictDer R M P d + restrictDer R M P e := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp

omit [IsScalarTower R A (B ⧸ M)] in
/-- Restriction of the zero derivation is the zero map. -/
theorem restrictDer_zero : restrictDer R M P (0 : Derivation R P.Ring (Coeff M)) = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp

omit [IsScalarTower R A (B ⧸ M)] in
/-- Restriction of derivations commutes with the `A`-action. -/
theorem restrictDer_smul_σ (a : A) (d : Derivation R P.Ring (Coeff M)) :
    restrictDer R M P (P.σ a • d) = a • restrictDer R M P d := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp only [restrictDer_mk, Derivation.smul_apply, LinearMap.smul_apply, smul_σ M]

variable (R P)

/-- The `A`-submodule of maps `I ⧸ I² → M` which extend to a derivation of the ambient ring;
that is, the image of `Hom(Ω[P.Ring⁄R], M) → Hom(I ⧸ I², M)`. -/
noncomputable def coboundary : Submodule A (P.Cotangent →ₗ[A] Coeff M) where
  carrier := Set.range (fun d : Derivation R P.Ring (Coeff M) => restrictDer R M P d)
  add_mem' := by
    rintro _ _ ⟨d, rfl⟩ ⟨e, rfl⟩
    exact ⟨d + e, restrictDer_add M d e⟩
  zero_mem' := ⟨0, restrictDer_zero M⟩
  smul_mem' a _ := by
    rintro ⟨d, rfl⟩
    exact ⟨P.σ a • d, restrictDer_smul_σ M a d⟩

/-- The obstruction group of a presentation with coefficients in `M`: the cokernel of
`Hom(Ω[P.Ring⁄R], M) → Hom(I ⧸ I², M)`. -/
abbrev ObstructionGroup : Type _ := (P.Cotangent →ₗ[A] Coeff M) ⧸ coboundary R M P

variable {R P}

omit [IsScalarTower R A (B ⧸ M)] in
/-- Membership in the coboundary submodule is exactly extendability to the ambient ring. -/
theorem mem_coboundary_iff (θ : P.Cotangent →ₗ[A] Coeff M) :
    θ ∈ coboundary R M P ↔ ∃ d : Derivation R P.Ring (Coeff M), restrictDer R M P d = θ :=
  Iff.rfl

/-- The coboundaries are exactly the maps `I ⧸ I² → M` that factor through the cotangent complex
`I ⧸ I² → A ⊗[P.Ring] Ω[P.Ring⁄R]` of the presentation.  In other words, the obstruction group is
the cokernel of `Hom_A(A ⊗ Ω[P.Ring⁄R], M) → Hom_A(I ⧸ I², M)`. -/
theorem mem_coboundary_iff_comp_cotangentComplex (θ : P.Cotangent →ₗ[A] Coeff M) :
    θ ∈ coboundary R M P ↔
      ∃ ψ : P.CotangentSpace →ₗ[A] Coeff M, ψ.comp P.cotangentComplex = θ := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨LinearMap.liftBaseChange A d.liftKaehlerDifferential, LinearMap.ext fun x => ?_⟩
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    simp [Algebra.Extension.cotangentComplex_mk]
  · rintro ⟨ψ, rfl⟩
    refine ⟨(((ψ.restrictScalars P.Ring).comp
      (TensorProduct.mk P.Ring A (Ω[P.Ring⁄R]) 1)).compDer (KaehlerDifferential.D R P.Ring)),
      LinearMap.ext fun x => ?_⟩
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    simp [Algebra.Extension.cotangentComplex_mk]

/-- The differential of the two-term affine presentation complex of
`CotangentComplex.AffinePresentation` is exactly the cotangent complex used above, so the
obstruction group is the cokernel of `Hom_A(-, M)` applied to that differential. -/
theorem mem_coboundary_iff_comp_twoTerm (Q : Algebra.Extension.{w} R A)
    (θ : Q.Cotangent →ₗ[A] Coeff M) :
    θ ∈ coboundary R M Q ↔ ∃ ψ : Q.CotangentSpace →ₗ[A] Coeff M,
      ψ.comp (AffinePresentation.twoTerm R A Q).differential = θ :=
  mem_coboundary_iff_comp_cotangentComplex (P := Q) M θ

omit [IsScalarTower R A (B ⧸ M)] in
/-- Restriction of the negative of a derivation. -/
theorem restrictDer_neg (d : Derivation R P.Ring (Coeff M)) :
    restrictDer R M P (-d) = -restrictDer R M P d := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp

/-- Changing the lift on the ambient ring changes the obstruction cocycle by a coboundary. -/
theorem obstructionMap_sub (F G : Lift R M P.Ring) :
    obstructionMap R M P F - obstructionMap R M P G = restrictDer R M P (F -ᵥ G) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  refine Coeff.ext M ?_
  simp

/-- Translating a lift by a derivation translates the obstruction cocycle by its restriction. -/
theorem obstructionMap_vadd (d : Derivation R P.Ring (Coeff M)) (F : Lift R M P.Ring) :
    obstructionMap R M P (d +ᵥ F) = obstructionMap R M P F + restrictDer R M P d := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  refine Coeff.ext M ?_
  simp [add_comm]

variable (R P)

/-- The obstruction class of the square-zero lifting problem, computed from a presentation.
It is defined using some lift on the ambient ring; `obstruction_eq` shows that the resulting
class in the obstruction group does not depend on that choice. -/
noncomputable def obstruction [Nonempty (Lift R M P.Ring)] : ObstructionGroup R M P :=
  Submodule.Quotient.mk (obstructionMap R M P (Classical.arbitrary _))

variable {R P}

/-- The obstruction class is computed by every lift on the ambient ring. -/
theorem obstruction_eq [Nonempty (Lift R M P.Ring)] (F : Lift R M P.Ring) :
    obstruction R M P = Submodule.Quotient.mk (obstructionMap R M P F) := by
  rw [obstruction, Submodule.Quotient.eq]
  exact ⟨_, (obstructionMap_sub M _ F).symm⟩

/-- A lift on the ambient ring whose obstruction cocycle vanishes kills the kernel. -/
theorem hom_eq_zero_of_obstructionMap_eq_zero {F : Lift R M P.Ring}
    (hF : obstructionMap R M P F = 0) {x : P.Ring} (hx : x ∈ P.ker) : F.hom x = 0 := by
  have h : obstructionMap R M P F (Algebra.Extension.Cotangent.mk ⟨x, hx⟩) = 0 := by
    rw [hF, LinearMap.zero_apply]
  simpa using congrArg (Coeff.val M) h

omit [IsSquareZero M] in
/-- A lift on the ambient ring which kills the kernel is constant on fibres of the
presentation. -/
theorem hom_congr {F : Lift R M P.Ring} (hF : ∀ x ∈ P.ker, F.hom x = 0) {p q : P.Ring}
    (h : algebraMap P.Ring A p = algebraMap P.Ring A q) : F.hom p = F.hom q := by
  have hmem : p - q ∈ P.ker := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  have hzero := hF _ hmem
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

variable (P)

/-- A lift on the ambient ring which kills the kernel descends to a lift on `A`. -/
noncomputable def descendLift (F : Lift R M P.Ring) (hF : ∀ x ∈ P.ker, F.hom x = 0) :
    Lift R M A :=
  ⟨{ toFun := fun a => F.hom (P.σ a)
     map_one' := (hom_congr M hF (by simp)).trans (map_one F.hom)
     map_zero' := (hom_congr M hF (by simp)).trans (map_zero F.hom)
     map_add' := fun a b =>
       (hom_congr M hF (q := P.σ a + P.σ b) (by simp)).trans (map_add F.hom _ _)
     map_mul' := fun a b =>
       (hom_congr M hF (q := P.σ a * P.σ b) (by simp)).trans (map_mul F.hom _ _)
     commutes' := fun r =>
       (hom_congr M hF (q := algebraMap R P.Ring r)
         (by simp [← IsScalarTower.algebraMap_apply])).trans (F.hom.commutes r) }, by
    refine AlgHom.ext fun a => ?_
    change Ideal.Quotient.mk M (F.hom (P.σ a)) = algebraMap A (B ⧸ M) a
    rw [Lift.mk_hom F (P.σ a)]
    change algebraMap A (B ⧸ M) (algebraMap P.Ring A (P.σ a)) = _
    rw [P.algebraMap_σ]⟩

omit [IsSquareZero M] in
@[simp]
theorem descendLift_hom (F : Lift R M P.Ring) (hF : ∀ x ∈ P.ker, F.hom x = 0) (a : A) :
    (descendLift M P F hF).hom a = F.hom (P.σ a) := rfl

/-- A lift of the structure map on `A` induces one on the ambient ring of a presentation. -/
noncomputable def liftToRing (f : Lift R M A) : Lift R M P.Ring :=
  ⟨f.hom.comp (IsScalarTower.toAlgHom R P.Ring A), by
    refine AlgHom.ext fun p => ?_
    change Ideal.Quotient.mk M (f.hom (algebraMap P.Ring A p)) = algebraMap P.Ring (B ⧸ M) p
    rw [Lift.mk_hom f]
    rfl⟩

omit [IsSquareZero M] in
@[simp]
theorem liftToRing_hom (f : Lift R M A) (p : P.Ring) :
    (liftToRing M P f).hom p = f.hom (algebraMap P.Ring A p) := rfl

/-- The obstruction cocycle of a lift induced from `A` vanishes. -/
theorem obstructionMap_liftToRing (f : Lift R M A) :
    obstructionMap R M P (liftToRing M P f) = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  refine Coeff.ext M ?_
  rw [obstructionMap_mk_val, liftToRing_hom, LinearMap.zero_apply, Coeff.val_zero,
    RingHom.mem_ker.mp x.2, map_zero]

variable (R)

/-- **Square-zero deformation theory, affine case.**  The obstruction class of a presentation
vanishes exactly when the square-zero lifting problem for `A` has a solution. -/
theorem obstruction_eq_zero_iff [Nonempty (Lift R M P.Ring)] :
    obstruction R M P = 0 ↔ Nonempty (Lift R M A) := by
  constructor
  · intro h
    obtain ⟨F⟩ := (inferInstance : Nonempty (Lift R M P.Ring))
    rw [obstruction_eq M F, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨d, hd⟩ := h
    replace hd : restrictDer R M P d = obstructionMap R M P F := hd
    refine ⟨descendLift M P ((-d) +ᵥ F) fun x hx => ?_⟩
    refine hom_eq_zero_of_obstructionMap_eq_zero M ?_ hx
    rw [obstructionMap_vadd, restrictDer_neg, hd, add_neg_cancel]
  · rintro ⟨f⟩
    rw [obstruction_eq M (liftToRing M P f), obstructionMap_liftToRing M P f,
      Submodule.Quotient.mk_zero]

/-- If the ambient ring of the presentation is formally smooth over `R` — for instance a
polynomial ring, as for a presentation coming from `Algebra.Generators` — then the obstruction
class is defined and detects the solvability of the lifting problem. -/
theorem nonempty_lift_iff_obstruction_eq_zero [Algebra.FormallySmooth R P.Ring] :
    Nonempty (Lift R M A) ↔ obstruction R M P = 0 :=
  (obstruction_eq_zero_iff R M P).symm

/-- The ambient ring of a presentation by a family of generators is a polynomial ring, hence
formally smooth over `R`. -/
instance formallySmooth_generators {ι : Type*} (G : Algebra.Generators R A ι) :
    Algebra.FormallySmooth R G.toExtension.Ring :=
  inferInstanceAs (Algebra.FormallySmooth R G.Ring)

/-- The obstruction criterion for a presentation of `A` by a family of generators, whose ambient
ring is a polynomial ring over `R`. -/
theorem nonempty_lift_iff_obstruction_generators {ι : Type*} (G : Algebra.Generators R A ι) :
    Nonempty (Lift R M A) ↔ obstruction R M G.toExtension = 0 :=
  nonempty_lift_iff_obstruction_eq_zero R M G.toExtension

variable {R}


/-! ### Naturality of the obstruction class in the coefficient module -/

section Naturality

variable {C : Type*} [CommRing C] [Algebra R C] (N : Ideal C) [IsSquareZero N]
variable [Algebra A (C ⧸ N)] [IsScalarTower R A (C ⧸ N)] (π : Push R M N A)

/-- A morphism of square-zero extensions over `A` is also one over the ambient ring of a
presentation of `A`. -/
def pushRing : Push R M N P.Ring where
  hom := π.hom
  map_mem := π.map_mem
  compat b p hb := π.compat b (algebraMap P.Ring A p) hb

omit [IsSquareZero M] [IsSquareZero N] [IsScalarTower R A (B ⧸ M)]
  [IsScalarTower R A (C ⧸ N)] in
@[simp]
theorem pushRing_hom : (pushRing M P N π).hom = π.hom := rfl

/-- Postcomposition of the maps `I ⧸ I² → M` with a pushforward of coefficients. -/
noncomputable def pushConormalHom :
    (P.Cotangent →ₗ[A] Coeff M) →ₗ[A] (P.Cotangent →ₗ[A] Coeff N) where
  toFun θ := (pushCoeff M N π).comp θ
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := LinearMap.comp_smul _ _ _

omit [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A (C ⧸ N)] in
@[simp]
theorem pushConormalHom_apply (θ : P.Cotangent →ₗ[A] Coeff M) (x : P.Cotangent) :
    pushConormalHom M P N π θ x = pushCoeff M N π (θ x) := rfl

/-- Naturality of the obstruction cocycle under a pushforward of the coefficient module. -/
theorem obstructionMap_push (F : Lift R M P.Ring) :
    obstructionMap R N P (pushLift M N (pushRing M P N π) F) =
      pushConormalHom M P N π (obstructionMap R M P F) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  refine Coeff.ext N ?_
  simp

/-- Naturality of the restriction of derivations under a pushforward of the coefficient
module. -/
theorem restrictDer_push (d : Derivation R P.Ring (Coeff M)) :
    restrictDer R N P (pushDer M N (pushRing M P N π) d) =
      pushConormalHom M P N π (restrictDer R M P d) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  refine Coeff.ext N ?_
  simp

/-- The map induced on obstruction groups by a pushforward of the coefficient module. -/
noncomputable def obstructionGroupMap :
    ObstructionGroup R M P →ₗ[A] ObstructionGroup R N P :=
  Submodule.mapQ _ _ (pushConormalHom M P N π) (by
    rintro _ ⟨d, rfl⟩
    exact ⟨pushDer M N (pushRing M P N π) d, restrictDer_push M P N π d⟩)

@[simp]
theorem obstructionGroupMap_mk (θ : P.Cotangent →ₗ[A] Coeff M) :
    obstructionGroupMap M P N π (Submodule.Quotient.mk θ) =
      Submodule.Quotient.mk (pushConormalHom M P N π θ) := rfl

/-- The obstruction class is natural in the coefficient module. -/
theorem obstructionGroupMap_obstruction [Nonempty (Lift R M P.Ring)]
    [Nonempty (Lift R N P.Ring)] :
    obstructionGroupMap M P N π (obstruction R M P) = obstruction R N P := by
  obtain ⟨F⟩ := (inferInstance : Nonempty (Lift R M P.Ring))
  rw [obstruction_eq M F, obstructionGroupMap_mk, ← obstructionMap_push M P N π F,
    obstruction_eq N (pushLift M N (pushRing M P N π) F)]

omit [IsSquareZero M] [IsSquareZero N] in
include π in
/-- A lift on the ambient ring pushes forward, so the target lifting problem is again
solvable on the ambient ring. -/
theorem nonempty_lift_push [Nonempty (Lift R M P.Ring)] : Nonempty (Lift R N P.Ring) :=
  ⟨pushLift M N (pushRing M P N π) (Classical.arbitrary _)⟩

end Naturality


end Obstruction

end SquareZero

end GromovWitten.AlgebraicGeometry.CotangentComplex
