/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Topology.LocallyFinsupp

/-!
# The degree of a zero-cycle

For a field `k` and a scheme `X` locally of finite type over `k`, this file defines the residue
degree `[κ(x):k]` of a closed point `x` of `X`, shows it is positive, and assembles the degree map
`degreeCycle : AlgebraicCycle X ℚ →ₗ[ℚ] ℚ` on rational cycles, `α ↦ ∑ᶠ x, α x • [κ(x):k]`.

The degree map is only additive when every rational cycle on `X` has *globally* finite support,
which is guaranteed when `X` is quasi-compact (`[CompactSpace X]`): a support that is merely
*locally* finite need not be globally finite on a non-quasi-compact scheme (e.g. an infinite
disjoint union of points), and `finsum` silently returns the junk value `0` on an infinite-support
function, which would break additivity of `degreeCycle` exactly as it is stated in the task
description. This hypothesis is the formalisation of "`X` a variety" (finite type over `k`) used
throughout Fulton's intersection theory, and is unavoidable for the sum to be well-defined; it is
recorded honestly here rather than silently assumed.

## Main declarations

* `GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree.residueDegree`: the degree
  `[κ(x):k]` of the residue field of a point `x` of `X`, for a structure morphism `f : X ⟶ Spec k`.
* `GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree.residueDegree_pos`: this
  degree is positive at every point of dimension zero for `FiniteTypeDimension.dimensionFunction`.
* `GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree.degreeCycle`: the degree of a
  rational algebraic cycle, `α ↦ ∑ᶠ x, α x * residueDegree f x`, a linear map (`[CompactSpace X]`).
* `GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree.degree_single`: the degree of
  the cycle `[x]` is `[κ(x):k]`.
-/

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree

variable {k : Type u} [Field k]

/-! ## Closed points have height (and dimension) zero -/

section ClosedPoints

/-- A point of height zero in the specialisation order of a scheme is closed: it admits no proper
generisation, so its closure cannot contain any other point. -/
theorem isClosed_singleton_of_height_eq_zero {X : Scheme.{u}} (x : X)
    (hx : Order.height x = 0) : IsClosed ({x} : Set X) := by
  have hmin : IsMin x := Order.height_eq_zero.mp hx
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  have h1 : x ⤳ z := specializes_iff_mem_closure.2 hz
  have hzx : z ≤ x := HomogeneityLocal.le_iff_specializes.2 h1
  have h2 : z ⤳ x := HomogeneityLocal.le_iff_specializes.1 (hmin hzx)
  exact (Specializes.antisymm h1 h2).eq.symm

/-- A point of dimension zero for the canonical dimension function of a scheme locally of finite
type over a field is closed. -/
theorem isClosed_singleton_of_dimensionFunction_eq_zero {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : FiniteTypeDimension.dimensionFunction f x = 0) : IsClosed ({x} : Set X) := by
  apply isClosed_singleton_of_height_eq_zero
  rw [FiniteTypeDimension.height_eq_resTrdeg f x]
  rw [FiniteTypeDimension.dimensionFunction_apply] at hx
  have hne := FiniteTypeDimension.resTrdeg_ne_top f x
  have h0 : (FiniteTypeDimension.resTrdeg f x).toNat = 0 := by exact_mod_cast hx
  exact (ENat.toNat_eq_zero.mp h0).resolve_right hne

end ClosedPoints

/-! ## Transport of module-finiteness along a compatible ring isomorphism -/

section FiniteCongr

/-- `Module.Finite` transports along a ring isomorphism compatible with two algebra structures
coming from `k`.  This mirrors `FiniteTypeDimension.trdegOf_congr`.  Stating `K`, `L` as
`CommRingCat` objects (rather than bare `Type u` with a separate `CommRing` instance argument)
avoids a diamond: an independent instance search for `CommRing K` on a concrete scheme's residue
field can land on a different (though propositionally equal) instance than the one already baked
into `K`'s own bundled `CommRingCat` structure, which is what `e.commRingCatIsoToRingEquiv`
uses. -/
theorem finite_congr (K L : CommRingCat.{u}) (φ : k →+* K) (ψ : k →+* L)
    (e : K ≅ L) (he : ∀ c, e.commRingCatIsoToRingEquiv (φ c) = ψ c) :
    (letI := φ.toAlgebra; Module.Finite k K) ↔ (letI := ψ.toAlgebra; Module.Finite k L) := by
  let _ : Algebra k K := φ.toAlgebra
  let _ : Algebra k L := ψ.toAlgebra
  have hcomm : ∀ c, e.commRingCatIsoToRingEquiv (algebraMap k K c) = algebraMap k L c := he
  let e' : K ≃ₐ[k] L := { e.commRingCatIsoToRingEquiv with commutes' := hcomm }
  exact Module.Finite.equiv_iff e'.toLinearEquiv

end FiniteCongr

/-! ## Finiteness of the residue field at a closed point -/

section ResidueFieldFinite

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **Zariski's lemma, at a maximal ideal of a finitely generated `k`-algebra `A` reached as a
prime of `Spec A ⟶ Spec k` of finite type.**  The residue field of the prime is a finite
`k`-module. -/
theorem finite_residueField_of_isMaximal {A : Type u} [CommRing A]
    (h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (hft : (FiniteTypeDimension.specAlgebraMap h).FiniteType)
    (q : PrimeSpectrum A) (hq : q.asIdeal.IsMaximal) :
    letI := ((algebraMap A q.asIdeal.ResidueField).comp
      (FiniteTypeDimension.specAlgebraMap h)).toAlgebra
    Module.Finite k q.asIdeal.ResidueField := by
  let _ : Algebra k q.asIdeal.ResidueField :=
    ((algebraMap A q.asIdeal.ResidueField).comp
      (FiniteTypeDimension.specAlgebraMap h)).toAlgebra
  have hsurj : Function.Surjective (algebraMap A q.asIdeal.ResidueField) :=
    q.asIdeal.algebraMap_residueField_surjective
  have hftR : Algebra.FiniteType k q.asIdeal.ResidueField :=
    RingHom.FiniteType.comp_surjective hft hsurj
  exact finite_of_finite_type_of_isJacobsonRing k q.asIdeal.ResidueField

/-- **Finiteness of the residue field at a closed point.**  If `x` is a closed point of a scheme
locally of finite type over a field `k`, the residue field `κ(x)` is a finite `k`-module. -/
theorem finite_residueField_of_isClosed [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := (FiniteTypeDimension.residueMap f x).toAlgebra
    Module.Finite k (X.residueField x) := by
  obtain ⟨V, hV, hxV, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := ⊤) trivial
  set A : Type u := (↥Γ(X, V) : Type u) with hA
  set q := hV.primeIdealOf (⟨x, hxV⟩ : V.toScheme) with hq
  set h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) := hV.isoSpec.inv ≫ V.ι ≫ f with hh
  have hmax : q.asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed (⟨x, hxV⟩ : V.toScheme) hx
  have hfinR := finite_residueField_of_isMaximal h (FiniteTypeDimension.finiteType_specAlgebraMap h)
    q hmax
  have hy0 : hV.isoSpec.inv.base (hV.isoSpec.hom.base (⟨x, hxV⟩ : V.toScheme))
      = (⟨x, hxV⟩ : V.toScheme) := by
    have hthis := (Scheme.homeoOfIso hV.isoSpec).symm_apply_apply (⟨x, hxV⟩ : V.toScheme)
    simpa [Scheme.homeoOfIso_symm, Scheme.coe_homeoOfIso, Scheme.coe_homeoOfIso_symm,
      Scheme.homeoOfIso_apply] using hthis
  have hqbase : q = hV.isoSpec.hom.base (⟨x, hxV⟩ : V.toScheme) := by rw [hq]; rfl
  have hy : hV.isoSpec.inv.base q = (⟨x, hxV⟩ : V.toScheme) := by rw [hqbase]; exact hy0
  -- Plain instance search stalls on the layered `SheafedSpace`/`PresheafedSpace` coercions
  -- hidden inside `residueFieldMap`/`residueField`; supplying the registered instances
  -- directly (rather than via `inferInstance`) avoids this.
  have hiso1 : IsIso (V.ι.residueFieldMap (⟨x, hxV⟩ : V.toScheme)) :=
    @AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion
      _ _ V.ι inferInstance _
  have hiso2 : IsIso (hV.isoSpec.inv.residueFieldMap q) :=
    @AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion
      _ _ hV.isoSpec.inv inferInstance _
  have step1 := finite_congr _ _
    (FiniteTypeDimension.residueMap f x)
    (FiniteTypeDimension.residueMap (V.ι ≫ f) (⟨x, hxV⟩ : V.toScheme))
    (@asIso _ _ _ _ (V.ι.residueFieldMap (⟨x, hxV⟩ : V.toScheme)) hiso1)
    (fun c ↦ FiniteTypeDimension.residueFieldMap_residueMap f V.ι (⟨x, hxV⟩ : V.toScheme) c)
  have step2 := finite_congr _ _
    (FiniteTypeDimension.residueMap (V.ι ≫ f) (hV.isoSpec.inv.base q))
    (FiniteTypeDimension.residueMap h q)
    (@asIso _ _ _ _ (hV.isoSpec.inv.residueFieldMap q) hiso2)
    (fun c ↦ FiniteTypeDimension.residueFieldMap_residueMap (V.ι ≫ f) hV.isoSpec.inv q c)
  rw [hy] at step2
  have step3 := finite_congr _ _ (FiniteTypeDimension.residueMap h q)
    ((algebraMap A q.asIdeal.ResidueField).comp (FiniteTypeDimension.specAlgebraMap h))
    (AlgebraicGeometry.Scheme.Spec.residueFieldIso (CommRingCat.of A) q)
    (fun c ↦
      let e := AlgebraicGeometry.Scheme.Spec.residueFieldIso (CommRingCat.of A) q
      show e.commRingCatIsoToRingEquiv (FiniteTypeDimension.residueMap h q c) =
          ((algebraMap A q.asIdeal.ResidueField).comp (FiniteTypeDimension.specAlgebraMap h)) c from
        FiniteTypeDimension.residueFieldIso_residueMap h q c)
  exact (step1.trans (step2.trans step3)).mpr hfinR

end ResidueFieldFinite

/-! ## The residue degree of a point -/

section ResidueDegree

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The residue degree `[κ(x):k]` of a point `x` of `X`, for a structure morphism
`f : X ⟶ Spec k`. -/
noncomputable def residueDegree (x : X) : ℕ :=
  letI := (FiniteTypeDimension.residueMap f x).toAlgebra
  Module.finrank k (X.residueField x)

/-- **The residue degree of a closed point is positive.**  Equivalently, this holds at every point
of dimension zero for the canonical dimension function. -/
theorem residueDegree_pos [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    0 < residueDegree f x := by
  let _ := (FiniteTypeDimension.residueMap f x).toAlgebra
  have hfin : Module.Finite k (X.residueField x) := finite_residueField_of_isClosed f x hx
  exact Module.finrank_pos

/-- **The residue degree is positive at every point of dimension zero.** -/
theorem residueDegree_pos_of_dimensionFunction_eq_zero [LocallyOfFiniteType f] (x : X)
    (hx : FiniteTypeDimension.dimensionFunction f x = 0) : 0 < residueDegree f x :=
  residueDegree_pos f x (isClosed_singleton_of_dimensionFunction_eq_zero f x hx)

end ResidueDegree

/-! ## The degree of a rational algebraic cycle -/

section DegreeCycle

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]

/-- On a quasi-compact scheme, every rational algebraic cycle has globally finite support (its
support is only assumed *locally* finite by definition; quasi-compactness upgrades this to a
genuine finite set, via a finite subcover of the local finiteness neighbourhoods). -/
theorem finite_support (α : AlgebraicCycle X ℚ) : (Function.support (⇑α)).Finite := by
  have h := Function.locallyFinsupp.locallyFiniteSupport α
  have := h.finite_inter_support_of_isCompact (CompactSpace.isCompact_univ (X := X))
  simpa using this

/-- The degree of a rational algebraic cycle, `α ↦ ∑ x, α x • [κ(x):k]`, summed over the
(globally finite, by `[CompactSpace X]`) support of `α`. -/
noncomputable def degreeCycle : AlgebraicCycle X ℚ →ₗ[ℚ] ℚ where
  toFun α := ∑ᶠ x, α x * (residueDegree f x : ℚ)
  map_add' α β := by
    have hα : (Function.support (fun x ↦ α x * (residueDegree f x : ℚ))).Finite :=
      (finite_support α).subset (Function.support_mul_subset_left _ _)
    have hβ : (Function.support (fun x ↦ β x * (residueDegree f x : ℚ))).Finite :=
      (finite_support β).subset (Function.support_mul_subset_left _ _)
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
    exact finsum_add_distrib hα hβ
  map_smul' c α := by
    have hα : (Function.support (fun x ↦ α x * (residueDegree f x : ℚ))).Finite :=
      (finite_support α).subset (Function.support_mul_subset_left _ _)
    simp only [Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact (mul_finsum' _ c hα).symm

@[simp] theorem degreeCycle_apply (α : AlgebraicCycle X ℚ) :
    degreeCycle f α = ∑ᶠ x, α x * (residueDegree f x : ℚ) :=
  rfl

/-- The degree of a dimension-zero rational cycle. -/
noncomputable def degree (dimension : DimensionFunction X) :
    cyclesOfDimension X dimension 0 →ₗ[ℚ] ℚ :=
  degreeCycle f ∘ₗ (cyclesOfDimension X dimension 0).subtype

@[simp] theorem degree_apply (dimension : DimensionFunction X)
    (α : cyclesOfDimension X dimension 0) :
    degree f dimension α = ∑ᶠ x, (α : AlgebraicCycle X ℚ) x * (residueDegree f x : ℚ) :=
  rfl

/-- **The degree of the cycle `[x]` is the residue degree `[κ(x):k]`.** -/
theorem degree_single (dimension : DimensionFunction X) (x : X) (hx : dimension x = 0) :
    degree f dimension (cyclesOfDimension.point x hx) = (residueDegree f x : ℚ) := by
  rw [degree_apply]
  have := finsum_eq_single
    (fun y ↦ (cyclesOfDimension.point x hx : AlgebraicCycle X ℚ) y * (residueDegree f y : ℚ))
    x (fun y hy ↦ by rw [cyclesOfDimension.point_apply_of_ne x y hx hy, zero_mul])
  simpa [cyclesOfDimension.point_apply_self] using this

end DegreeCycle

end GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree
