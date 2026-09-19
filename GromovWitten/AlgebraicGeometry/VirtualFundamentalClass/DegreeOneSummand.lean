/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Unconditional

/-!
# Adjoining a summand in degree one does not change the resolved cone

Let `φ : E ⟶ L = conormalComplex k R I` be an obstruction theory in the affine two-term model of
`VirtualFundamentalClass/ResolvedCone.lean`, let `W` be a module over `R ⧸ I` and let
`j : W →ₗ (R ⧸ I) ⊗[R] Ω[R⁄k]` be a linear map.  The complex `E.addDegreeOne W` has the *same*
degree-zero term `E⁻¹`, degree-one term `E⁰ × W` and differential `x ↦ (d x, 0)`, and
`φ.addDegreeOne j` is the chain map with the same degree-zero component and with
`φ⁰.coprod j` in degree one.  Geometrically the bundle `E₁ = Spec Sym(E⁻¹)` is untouched while
the bundle `E₀ = Spec Sym(E⁰)` is replaced by `E₀ × 𝔸(W)`; the extra factor acts trivially on
`E₁`, so the resolved cone `C(E) ⊆ E₁` does not move.

This is the algebraic heart of Behrend–Fantechi's comparison between an obstruction theory
relative to a smooth base and the associated absolute one: the relative datum is recovered from
the absolute one by deleting a degree-one summand, and the two resolved cones coincide inside
the same bundle, so the two virtual classes differ only by the degree shift `rk W`.

## Main definitions

* `LinearTwoTermComplex.addDegreeOne E W`, `LinearTwoTermComplex.Hom.addDegreeOne φ j`: the
  complex and chain map described above.
* `DegreeOneSummand.productInclusion φ j`, `DegreeOneSummand.productProjection φ j`: the algebra
  map `gr_I(R) ⊗ Sym(E⁰) → gr_I(R) ⊗ Sym(E⁰ × W)` induced by `LinearMap.inl` and its retraction
  induced by `LinearMap.fst`.
* `DegreeOneSummand.relativeVirtualClassAt φ e dimX dimE d RX RE hhom hinj`: the virtual class of
  `φ` placed in the degree `virtualDimension φ + d`, the degree in which the virtual class of an
  obstruction theory relative to a smooth base of dimension `d` lives.

## Main results

* `DegreeOneSummand.productMap_addDegreeOne`: `productMap (φ.addDegreeOne j)` is
  `productInclusion φ j` composed with `productMap φ`.
* `DegreeOneSummand.ideal_addDegreeOne`: **the two resolved cones have the same ideal** inside
  `Sym(E⁻¹)`, hence are the same closed subscheme of the same bundle `E₁`.
* `DegreeOneSummand.resolvedConeCycleAt_addDegreeOne`,
  `DegreeOneSummand.resolvedConeClassAt_addDegreeOne`,
  `DegreeOneSummand.virtualClassAt_addDegreeOne`: the resolved-cone cycle, the resolved-cone
  class and the degree-generic virtual class are unchanged.
* `DegreeOneSummand.virtualDimension_addDegreeOne`,
  `DegreeOneSummand.coneDegree_addDegreeOne`: the virtual dimension and the cone degree go up by
  `rk W`, while `DegreeOneSummand.bundleRank_addDegreeOne` and
  `DegreeOneSummand.trivialization_addDegreeOne` say that the bundle and its trivialisation are
  literally the same.
* `DegreeOneSummand.virtualClassAt_addDegreeOne_eq_relativeVirtualClassAt` and
  `DegreeOneSummand.virtualClass_addDegreeOne_eq_relativeVirtualClassAt`: the comparison in the
  form "absolute class = relative class", for the degree-generic and for the unconditional
  virtual class of `VirtualFundamentalClass/Unconditional.lean`.
* Obstruction-theory bookkeeping: `DegreeOneSummand.cokernelMap_comp_inclusionQ`,
  `DegreeOneSummand.surjective_cokernelMap_addDegreeOne` (no hypothesis),
  `DegreeOneSummand.injective_cokernelMap_of_addDegreeOne`,
  `DegreeOneSummand.surjective_cokernelMap_of_addDegreeOne` (needs `range j ≤ range φ⁰`),
  `DegreeOneSummand.surjective_kernelMap_addDegreeOne_iff`,
  `DegreeOneSummand.isObstructionTheory_of_addDegreeOne` and, for `W` a subsingleton,
  `DegreeOneSummand.isObstructionTheory_addDegreeOne`.  Note that for a nonzero `W` the chain map
  `φ.addDegreeOne j` is **never** an obstruction theory: it adds `W` to `H⁰`.  This is exactly
  why a relative obstruction theory is not an absolute one.
-/

universe u

-- As in `VirtualFundamentalClass/ResolvedCone.lean`, the coordinate ring `gr_I(R) ⊗ Sym(E⁰)` of
-- the product `C ×_X E₀` needs one more level of pending instance problems than the default.
set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

/-! ## Adjoining a summand in degree one -/

namespace LinearTwoTermComplex

variable {S : Type u} [CommRing S]

/-- Adjoin a module `W` to the degree-one term of a two-term complex, with zero differential
into it.  The degree-zero term, together with its module structure, is untouched, so the vector
bundle `E₁ = Spec Sym(E⁻¹)` of `VirtualFundamentalClass/ResolvedCone.lean` is literally the
same for `E` and for `E.addDegreeOne W`. -/
abbrev addDegreeOne (E : LinearTwoTermComplex S) (W : Type u) [AddCommGroup W] [Module S W] :
    LinearTwoTermComplex S where
  degreeZero := E.degreeZero
  degreeOne := E.degreeOne × W
  differential := (LinearMap.inl S E.degreeOne W).comp E.differential

@[simp]
theorem addDegreeOne_differential (E : LinearTwoTermComplex S) (W : Type u) [AddCommGroup W]
    [Module S W] (x : E.degreeZero) :
    (E.addDegreeOne W).differential x = (E.differential x, 0) :=
  rfl

namespace Hom

variable {E F : LinearTwoTermComplex S}

/-- Extend a chain map `φ : E ⟶ F` over the adjoined degree-one summand `W` by a linear map
`j : W →ₗ F⁰`.  The degree-zero component is unchanged and the degree-one component is
`φ⁰.coprod j`. -/
def addDegreeOne (φ : Hom E F) {W : Type u} [AddCommGroup W] [Module S W]
    (j : W →ₗ[S] F.degreeOne) : Hom (E.addDegreeOne W) F where
  degreeZero := φ.degreeZero
  degreeOne := φ.degreeOne.coprod j
  comm x := by
    change φ.degreeOne (E.differential x) + j 0 = _
    rw [map_zero, add_zero, φ.comm]

@[simp]
theorem addDegreeOne_degreeZero (φ : Hom E F) {W : Type u} [AddCommGroup W] [Module S W]
    (j : W →ₗ[S] F.degreeOne) : (φ.addDegreeOne j).degreeZero = φ.degreeZero :=
  rfl

@[simp]
theorem addDegreeOne_degreeOne (φ : Hom E F) {W : Type u} [AddCommGroup W] [Module S W]
    (j : W →ₗ[S] F.degreeOne) : (φ.addDegreeOne j).degreeOne = φ.degreeOne.coprod j :=
  rfl

end Hom

end LinearTwoTermComplex

namespace VirtualFundamentalClass.DegreeOneSummand

open NormalSheafPicard.AffineIntrinsicNormalSheaf
open scoped TensorProduct

/-! ## The comparison of the two coordinate rings of `C ×_X E₀` -/

section Ideal

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable {W : Type u} [AddCommGroup W] [Module (R ⧸ I) W]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (j : W →ₗ[R ⧸ I] (conormalComplex k R I).degreeOne)

/-- The algebra map `gr_I(R) ⊗ Sym(E⁰) → gr_I(R) ⊗ Sym(E⁰ × W)` induced by the inclusion of the
first factor.  On spectra it is the projection `C ×_X E₀ ×_X 𝔸(W) → C ×_X E₀`. -/
noncomputable def productInclusion :
    ResolvedCone.productRing φ →ₐ[R ⧸ I] ResolvedCone.productRing (φ.addDegreeOne j) :=
  Algebra.TensorProduct.map
    (AlgHom.id (R ⧸ I) (AffineNormalCone.associatedGradedRing R I))
    (ConeQuotient.symMap (LinearMap.inl (R ⧸ I) E.degreeOne W))

/-- The retraction of `productInclusion`, induced by the first projection `E⁰ × W → E⁰`. -/
noncomputable def productProjection :
    ResolvedCone.productRing (φ.addDegreeOne j) →ₐ[R ⧸ I] ResolvedCone.productRing φ :=
  Algebra.TensorProduct.map
    (AlgHom.id (R ⧸ I) (AffineNormalCone.associatedGradedRing R I))
    (ConeQuotient.symMap (LinearMap.fst (R ⧸ I) E.degreeOne W))

/-- `productProjection` is a left inverse of `productInclusion`. -/
theorem productProjection_comp_productInclusion :
    (productProjection φ j).comp (productInclusion φ j) =
      AlgHom.id (R ⧸ I) (ResolvedCone.productRing φ) := by
  have h : (ConeQuotient.symMap (LinearMap.fst (R ⧸ I) E.degreeOne W)).comp
      (ConeQuotient.symMap (LinearMap.inl (R ⧸ I) E.degreeOne W)) =
      AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne) :=
    SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => by simp)
  rw [productInclusion, productProjection, ← Algebra.TensorProduct.map_comp, h,
    AlgHom.id_comp, Algebra.TensorProduct.map_id]

/-- `productInclusion` is injective: it is split by `productProjection`. -/
theorem productInclusion_injective : Function.Injective (productInclusion φ j) := by
  have h : ∀ a, productProjection φ j (productInclusion φ j a) = a := fun a =>
    congrArg (fun f : ResolvedCone.productRing φ →ₐ[R ⧸ I] ResolvedCone.productRing φ => f a)
      (productProjection_comp_productInclusion φ j)
  exact Function.LeftInverse.injective h

/-- **The coordinate-ring map of the adjoined datum factors through the one of `φ`.**  Both send
a generator `x` of `E⁻¹` to `γ(φ⁻¹ x) ⊗ 1 + 1 ⊗ ι(d x)`, the second summand being read in
`Sym(E⁰ × W)` through `LinearMap.inl` on the right-hand side. -/
theorem productMap_addDegreeOne :
    ResolvedCone.productMap (φ.addDegreeOne j) =
      (productInclusion φ j).comp (ResolvedCone.productMap φ) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  change ResolvedCone.productMap (φ.addDegreeOne j)
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
    productInclusion φ j (ResolvedCone.productMap φ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x))
  rw [ResolvedCone.productMap_ι, ResolvedCone.productMap_ι]
  simp [productInclusion]

/-- **A degree-one summand does not change the resolved cone.**  The two ideals are ideals of the
same ring `Sym(E⁻¹)`, so the resolved cones `C(E.addDegreeOne W)` and `C(E)` are the same closed
subscheme of the same vector bundle `E₁ = Spec Sym(E⁻¹)`. -/
theorem ideal_addDegreeOne :
    ResolvedCone.ideal (φ.addDegreeOne j) = ResolvedCone.ideal φ := by
  ext a
  rw [ResolvedCone.mem_ideal_iff, ResolvedCone.mem_ideal_iff, productMap_addDegreeOne,
    AlgHom.comp_apply]
  refine ⟨fun h => productInclusion_injective φ j ?_, fun h => ?_⟩
  · rw [h, map_zero]
  · rw [h, map_zero]

/-- The two resolved cones have the same coordinate ring. -/
theorem ring_addDegreeOne : ResolvedCone.ring (φ.addDegreeOne j) = ResolvedCone.ring φ := by
  rw [ResolvedCone.ring, ResolvedCone.ring, ideal_addDegreeOne]

end Ideal

/-! ## Obstruction-theory bookkeeping -/

section Obstruction

open PicardCriteria

variable {S : Type u} [CommRing S] {E F : LinearTwoTermComplex S}
variable {W : Type u} [AddCommGroup W] [Module S W]
variable (φ : LinearTwoTermComplex.Hom E F) (j : W →ₗ[S] F.degreeOne)

/-- The map `E⁰ ⧸ im d → (E⁰ × W) ⧸ im d'` induced by `LinearMap.inl`. -/
def inclusionQ :
    (E.degreeOne ⧸ (LinearMap.range E.differential : Submodule S E.degreeOne)) →ₗ[S]
      ((E.addDegreeOne W).degreeOne ⧸
        (LinearMap.range (E.addDegreeOne W).differential :
          Submodule S (E.addDegreeOne W).degreeOne)) :=
  Submodule.mapQ _ _ (LinearMap.inl S E.degreeOne W) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩)

/-- `inclusionQ` is injective: `(u, 0)` lies in the image of `x ↦ (d x, 0)` exactly when `u`
lies in the image of `d`. -/
theorem inclusionQ_injective : Function.Injective (inclusionQ (W := W) (E := E) (S := S)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [inclusionQ, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨x, hx⟩ := hy
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨x, congrArg Prod.fst hx⟩

/-- **The cokernel map of the adjoined datum restricts to the cokernel map of `φ`.**  All the
statements below about `H⁰` are consequences of this factorisation. -/
theorem cokernelMap_comp_inclusionQ :
    ((φ.addDegreeOne j).cokernelMap).comp (inclusionQ (W := W) (E := E) (S := S)) =
      φ.cokernelMap := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.comp_apply, inclusionQ, Submodule.mapQ_apply,
    LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply,
    LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply,
    LinearTwoTermComplex.Hom.addDegreeOne_degreeOne]
  change Submodule.Quotient.mk (φ.degreeOne u + j 0) = _
  rw [map_zero, add_zero]

/-- Surjectivity of `H⁰(φ)` is inherited by the adjoined datum: the image only grows. -/
theorem surjective_cokernelMap_addDegreeOne (h : Function.Surjective φ.cokernelMap) :
    Function.Surjective (φ.addDegreeOne j).cokernelMap := by
  rw [← cokernelMap_comp_inclusionQ φ j] at h
  exact Function.Surjective.of_comp (g := inclusionQ) h

/-- Injectivity of `H⁰` descends from the adjoined datum to `φ`. -/
theorem injective_cokernelMap_of_addDegreeOne
    (h : Function.Injective (φ.addDegreeOne j).cokernelMap) :
    Function.Injective φ.cokernelMap := by
  rw [← cokernelMap_comp_inclusionQ φ j]
  exact h.comp inclusionQ_injective

/-- Surjectivity of `H⁰` descends from the adjoined datum to `φ`, provided the adjoined map `j`
does not enlarge the image: this is the case that matters for a relative obstruction theory,
where `j` is a coordinate map of the conormal complex already hit by `φ⁰`. -/
theorem surjective_cokernelMap_of_addDegreeOne
    (hj : LinearMap.range j ≤ LinearMap.range φ.degreeOne)
    (h : Function.Surjective (φ.addDegreeOne j).cokernelMap) :
    Function.Surjective φ.cokernelMap := by
  intro z
  obtain ⟨y, hy⟩ := h z
  obtain ⟨uw, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨u', hu'⟩ := hj (LinearMap.mem_range_self j uw.2)
  refine ⟨Submodule.Quotient.mk (uw.1 + u'), ?_⟩
  rw [LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply, map_add, hu']
  rw [LinearTwoTermComplex.Hom.cokernelMap, Submodule.mapQ_apply,
    LinearTwoTermComplex.Hom.addDegreeOne_degreeOne, LinearMap.coprod_apply] at hy
  exact hy

/-- If `W` is trivial the inclusion of cokernels is also surjective. -/
theorem inclusionQ_surjective [Subsingleton W] :
    Function.Surjective (inclusionQ (W := W) (E := E) (S := S)) := by
  intro y
  obtain ⟨uw, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨Submodule.Quotient.mk uw.1, ?_⟩
  rw [inclusionQ, Submodule.mapQ_apply]
  congr 1
  exact Prod.ext rfl (Subsingleton.elim _ _)

/-- For a trivial `W` the adjoined datum has an injective `H⁰` as soon as `φ` has. -/
theorem injective_cokernelMap_addDegreeOne [Subsingleton W]
    (h : Function.Injective φ.cokernelMap) :
    Function.Injective (φ.addDegreeOne j).cokernelMap := by
  rw [← cokernelMap_comp_inclusionQ φ j, LinearMap.coe_comp] at h
  exact h.of_comp_right inclusionQ_surjective

/-- `H⁻¹` is unchanged: the differential of `E.addDegreeOne W` has the same kernel as that of
`E`, and the adjoined chain map has the same degree-zero component. -/
theorem surjective_kernelMap_addDegreeOne_iff :
    Function.Surjective (φ.addDegreeOne j).kernelMap ↔ Function.Surjective φ.kernelMap := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    have hx0 : E.differential (x : E.degreeZero) = 0 :=
      congrArg Prod.fst (LinearMap.mem_ker.mp x.2)
    exact ⟨⟨(x : E.degreeZero), hx0⟩, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    have hx0 : (E.addDegreeOne W).differential (x : E.degreeZero) = 0 := by
      rw [LinearTwoTermComplex.addDegreeOne_differential, LinearMap.mem_ker.mp x.2]
      rfl
    exact ⟨⟨(x : E.degreeZero), hx0⟩, hx⟩

/-- **If the adjoined datum is an obstruction theory, so is `φ`**, provided `j` does not enlarge
the image of `φ⁰`. -/
theorem isObstructionTheory_of_addDegreeOne
    (hj : LinearMap.range j ≤ LinearMap.range φ.degreeOne)
    (h : IsObstructionTheory (φ.addDegreeOne j)) : IsObstructionTheory φ where
  bijective_cokernelMap :=
    ⟨injective_cokernelMap_of_addDegreeOne φ j h.bijective_cokernelMap.1,
      surjective_cokernelMap_of_addDegreeOne φ j hj h.bijective_cokernelMap.2⟩
  surjective_kernelMap :=
    (surjective_kernelMap_addDegreeOne_iff φ j).1 h.surjective_kernelMap

/-- **Adjoining a trivial degree-one summand preserves obstruction theories.**  For a nonzero
`W` this fails: `H⁰(φ.addDegreeOne j)` is never injective, since `(0, w)` is a nonzero class in
the kernel for every `w ≠ 0`. -/
theorem isObstructionTheory_addDegreeOne [Subsingleton W] (h : IsObstructionTheory φ) :
    IsObstructionTheory (φ.addDegreeOne j) where
  bijective_cokernelMap :=
    ⟨injective_cokernelMap_addDegreeOne φ j h.bijective_cokernelMap.1,
      surjective_cokernelMap_addDegreeOne φ j h.bijective_cokernelMap.2⟩
  surjective_kernelMap :=
    (surjective_kernelMap_addDegreeOne_iff φ j).2 h.surjective_kernelMap

end Obstruction

/-! ## Ranks and the trivialisation of the bundle -/

section Ranks

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable {W : Type u} [AddCommGroup W] [Module (R ⧸ I) W]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (j : W →ₗ[R ⧸ I] (conormalComplex k R I).degreeOne)

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The bundle `E₁` has the same rank for the two data: only the degree-one term changed. -/
theorem bundleRank_addDegreeOne :
    VirtualClass.bundleRank (φ.addDegreeOne j) = VirtualClass.bundleRank φ :=
  rfl

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The two data have literally the same trivialisation of `E₁ = Spec Sym(E⁻¹)`. -/
theorem trivialization_addDegreeOne :
    VirtualClass.trivialization (φ.addDegreeOne j) = VirtualClass.trivialization φ :=
  rfl

variable [Nontrivial (R ⧸ I)]
variable [Module.Free (R ⧸ I) E.degreeOne] [Module.Finite (R ⧸ I) E.degreeOne]
variable [Module.Free (R ⧸ I) W] [Module.Finite (R ⧸ I) W]

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- **The virtual dimension goes up by the rank of the adjoined summand.** -/
theorem virtualDimension_addDegreeOne :
    VirtualClass.virtualDimension (φ.addDegreeOne j) =
      VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ) := by
  rw [VirtualClass.virtualDimension, VirtualClass.virtualDimension]
  change ((Module.finrank (R ⧸ I) (E.degreeOne × W) : ℤ) - _) = _
  rw [Module.finrank_prod]
  push_cast
  ring

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- **The degree of the resolved-cone cycle goes up by the rank of the adjoined summand.** -/
theorem coneDegree_addDegreeOne :
    VirtualClass.coneDegree (φ.addDegreeOne j) =
      VirtualClass.coneDegree φ + (Module.finrank (R ⧸ I) W : ℤ) := by
  rw [VirtualClass.coneDegree, VirtualClass.coneDegree, virtualDimension_addDegreeOne,
    bundleRank_addDegreeOne]
  ring

end Ranks

/-! ## The resolved-cone cycle, class and virtual class -/

section Cycle

open IntersectionTheory hiding Scheme AlgebraicCycle

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable {W : Type u} [AddCommGroup W] [Module (R ⧸ I) W]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (j : W →ₗ[R ⧸ I] (conormalComplex k R I).degreeOne)

/-- **The degree-generic resolved-cone cycle is unchanged by a degree-one summand.** -/
theorem resolvedConeCycleAt_addDegreeOne
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (d : ℤ) :
    VirtualClass.resolvedConeCycleAt (φ.addDegreeOne j) dimE d =
      VirtualClass.resolvedConeCycleAt φ dimE d := by
  rw [HomotopyInvariance.resolvedConeCycleAt_eq_quotientCycle,
    HomotopyInvariance.resolvedConeCycleAt_eq_quotientCycle,
    HomotopyInvariance.quotientCycle_congr (ideal_addDegreeOne φ j)]

/-- **The degree-generic resolved-cone class is unchanged by a degree-one summand.** -/
theorem resolvedConeClassAt_addDegreeOne {ι : Type u}
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (i : ℤ)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ))) :
    VirtualClass.resolvedConeClassAt (ι := ι) (φ.addDegreeOne j) dimE i RE =
      VirtualClass.resolvedConeClassAt (ι := ι) φ dimE i RE :=
  congrArg RE.quotientMap (resolvedConeCycleAt_addDegreeOne φ j dimE (i + (Nat.card ι : ℤ)))

variable {ι : Type u} [Finite ι]
variable (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))

/-- **The degree-generic virtual class is unchanged by a degree-one summand.**  Both sides are
computed in the same trivialisation `e` of the same bundle `E₁` and in the same degree `i`; only
the *canonical* degree of the two data differs, by `virtualDimension_addDegreeOne`. -/
theorem virtualClassAt_addDegreeOne (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    VirtualClass.virtualClassAt (φ.addDegreeOne j) e dimX dimE i RX RE hhom hinj =
      VirtualClass.virtualClassAt φ e dimX dimE i RX RE hhom hinj :=
  congrArg (VectorBundle.zeroSectionGysin' e dimX dimE i RX RE hhom hinj)
    (resolvedConeClassAt_addDegreeOne φ j dimE i RE)

/-! ## The relative virtual class -/

/-- **The relative virtual class of `φ` in relative dimension `d`.**

If `φ` is an obstruction theory for `X` relative to a smooth base `Y` of dimension `d`, then the
degree-one term `E⁰` of `E` computes the *relative* cotangent complex, so the resolved cone
`C(E) ⊆ E₁` has dimension `rk E⁰ + d` rather than `rk E⁰` (Behrend–Fantechi §7: the relative
intrinsic normal cone has the dimension of the base added to it).  Its class therefore lives in
the degree `virtualDimension φ + d` after the Gysin pullback, and this definition is exactly the
degree-generic virtual class `virtualClassAt` in that degree. -/
noncomputable def relativeVirtualClassAt (d : ℕ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension φ + (d : ℤ)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.virtualDimension φ + (d : ℤ) + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE
      (VirtualClass.virtualDimension φ + (d : ℤ)) RX RE)) : RX.ChowGroup :=
  VirtualClass.virtualClassAt φ e dimX dimE (VirtualClass.virtualDimension φ + (d : ℤ)) RX RE
    hhom hinj

/-- **The absolute virtual class of `φ.addDegreeOne j` is the relative virtual class of `φ` in
relative dimension `rk W`.**  The common degree is `virtualDimension φ + rk W`, which is
`virtualDimension (φ.addDegreeOne j)` by `virtualDimension_addDegreeOne`. -/
theorem virtualClassAt_addDegreeOne_eq_relativeVirtualClassAt
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ) + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE
      (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ)) RX RE)) :
    VirtualClass.virtualClassAt (φ.addDegreeOne j) e dimX dimE
        (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ)) RX RE hhom hinj =
      relativeVirtualClassAt φ e dimX dimE (Module.finrank (R ⧸ I) W) RX RE hhom hinj :=
  virtualClassAt_addDegreeOne φ j e dimX dimE _ RX RE hhom hinj

end Cycle

/-! ## The unconditional form -/

section Unconditional

open IntersectionTheory hiding Scheme AlgebraicCycle

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable {W : Type u} [AddCommGroup W] [Module (R ⧸ I) W]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (j : W →ₗ[R ⧸ I] (conormalComplex k R I).degreeOne)
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))

/-- **The unconditional virtual class of the adjoined datum is the relative virtual class of
`φ`.**  Here the degree is the canonical one of `φ.addDegreeOne j`; by
`virtualDimension_addDegreeOne` it equals `virtualDimension φ + rk W` whenever `R ⧸ I` is
nontrivial and `E⁰` and `W` are finite free, and then the right-hand side is
`relativeVirtualClassAt φ … (rk W) …`. -/
theorem virtualClass_addDegreeOne_eq_virtualClassAt
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension (φ.addDegreeOne j)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.coneDegree (φ.addDegreeOne j)))
    (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) :
    Unconditional.virtualClass (φ.addDegreeOne j) dimX dimE RX RE hdim hunit =
      VirtualClass.virtualClassAt φ (VirtualClass.trivialization φ) dimX dimE
        (VirtualClass.virtualDimension (φ.addDegreeOne j)) RX RE
        (Unconditional.hhomOf φ dimE hdim)
        (Unconditional.hinjAt φ dimX dimE (VirtualClass.virtualDimension (φ.addDegreeOne j))
          RX RE hdim hunit) :=
  virtualClassAt_addDegreeOne φ j (VirtualClass.trivialization φ) dimX dimE _ RX RE _ _

/-- **The unconditional comparison**: the absolute virtual class of `φ.addDegreeOne j` equals
the relative virtual class of `φ` in relative dimension `rk W`, both read in the degree
`virtualDimension φ + rk W` (which is the canonical degree of `φ.addDegreeOne j` whenever
`R ⧸ I` is nontrivial and `E⁰`, `W` are finite free, by `virtualDimension_addDegreeOne`). -/
theorem virtualClass_addDegreeOne_eq_relativeVirtualClassAt
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ)))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ) +
        (VirtualClass.bundleRank φ : ℤ)))
    (hdim : VectorBundle.HasUniversalDimensionFormula (R ⧸ I))
    (hunit : VectorBundle.UnitDifferences (R ⧸ I)) :
    VirtualClass.virtualClassAt (φ.addDegreeOne j)
        (VirtualClass.trivialization (φ.addDegreeOne j)) dimX dimE
        (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ)) RX RE
        (Unconditional.hhomOf φ dimE hdim)
        (Unconditional.hinjAt φ dimX dimE
          (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ)) RX RE hdim hunit) =
      relativeVirtualClassAt φ (VirtualClass.trivialization φ) dimX dimE
        (Module.finrank (R ⧸ I) W) RX RE (Unconditional.hhomOf φ dimE hdim)
        (Unconditional.hinjAt φ dimX dimE
          (VirtualClass.virtualDimension φ + (Module.finrank (R ⧸ I) W : ℤ)) RX RE hdim hunit) :=
  virtualClassAt_addDegreeOne φ j (VirtualClass.trivialization φ) dimX dimE _ RX RE _ _

end Unconditional

end VirtualFundamentalClass.DegreeOneSummand

end GromovWitten.AlgebraicGeometry
