/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Independence

/-!
# Chain-homotopy invariance of the resolved cone and of the virtual class

Let `X = Spec (R ⧸ I) ⊆ Spec R`, let `L = conormalComplex k R I` be the conormal two-term complex
and let `φ, φ' : E ⟶ L` be two chain maps out of the *same* two-term complex `E` which differ by
a chain homotopy.  In degree `-1` this says

`φ'.degreeZero = φ.degreeZero + h ∘ E.differential`

for a linear map `h : E⁰ →ₗ I/I²`.  The resolved cone `C(E) ⊆ E₁` of
`VirtualFundamentalClass/ResolvedCone.lean` is then literally the same closed subscheme for `φ`
and for `φ'`, and consequently the whole virtual-class construction of
`VirtualFundamentalClass/Construction.lean` is unchanged.

The reason is the translation automorphism of the coordinate ring
`gr_I(R) ⊗_{R/I} Sym(E⁰)` of `C ×_X E₀`, which is the identity on the left tensor factor and
sends a degree-one generator `ι y` of `Sym(E⁰)` to `γ(h y) ⊗ 1 + 1 ⊗ ι y`, where
`γ = AffineNormalCone.conormalToAssociatedGraded`.  It is an algebra automorphism (its inverse is
the translation by `-h`) and it intertwines the two coordinate-ring maps
`productMap φ` and `productMap φ'`, hence the two kernels agree.

## Main definitions

* `translationLinear φ h`, `translationAlgHom φ h`, `translationAut φ h`: the translation
  endomorphism of `ResolvedCone.productRing φ` attached to `h : E⁰ →ₗ I/I²`, and its promotion to
  an `R ⧸ I`-algebra automorphism.
* `quotientImmersion J`, `quotientCycle J dim d`: the closed immersion `Spec (A ⧸ J) ↪ Spec A` and
  the dimension-`d` part of the pushforward of the fundamental cycle of `Spec (A ⧸ J)`.  These are
  the ideal-parametrised versions of `ResolvedCone.toBundle` and of
  `VirtualClass.resolvedConeCycleAt`, used to rewrite the ideal inside a dependent quotient.

## Main results

* `translationAlgHom_comp`, `translationAlgHom_zero`: the translations compose additively, so
  `translationAut φ h` is an automorphism.
* `translationAlgHom_comp_productMap`: `translationAut φ h ∘ productMap φ = productMap φ'`.
* `ideal_congr`, `ideal_congr_chainHomotopy`: the ideal of the resolved cone is unchanged.
* `resolvedConeCycle_congr`, `resolvedConeCycleAt_congr`, `resolvedConeClass_congr`,
  `resolvedConeClassAt_congr`: the resolved-cone cycle and class are unchanged.
* `virtualClass_congr`, `virtualClassAt_congr`, `virtualDimension_congr`: the virtual class and
  the virtual dimension are unchanged, for the canonical and for an arbitrary trivialisation.
* `isObstructionTheory_of_chainHomotopy`: being an obstruction theory is a chain-homotopy
  invariant condition.
-/

universe u

-- As in `VirtualFundamentalClass/ResolvedCone.lean`: synthesising `CommRing` for the tensor
-- product `gr_I(R) ⊗_{R/I} Sym(E⁰)` of a quotient of a Rees algebra with a symmetric algebra
-- needs one more level of pending instance problems than the default.
set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.HomotopyInvariance

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open scoped TensorProduct

/-! ## The translation automorphism of `gr_I(R) ⊗ Sym(E⁰)` -/

section Translation

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The linear map `E⁰ → gr_I(R) ⊗ Sym(E⁰)`, `y ↦ γ(h y) ⊗ 1 + 1 ⊗ ι y`, classifying the
translation of the bundle `E₀` by the section `h` of the normal cone. -/
noncomputable def translationLinear
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero) :
    E.degreeOne →ₗ[R ⧸ I] ResolvedCone.productRing φ :=
  ((TensorProduct.mk (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
        (SymmetricAlgebra (R ⧸ I) E.degreeOne)).flip 1).comp
      ((AffineNormalCone.conormalToAssociatedGraded R I).comp h) +
    (TensorProduct.mk (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
        (SymmetricAlgebra (R ⧸ I) E.degreeOne) 1).comp
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeOne)

@[simp]
theorem translationLinear_apply
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero) (y : E.degreeOne) :
    translationLinear φ h y =
      AffineNormalCone.conormalToAssociatedGraded R I (h y) ⊗ₜ[R ⧸ I] 1 +
        1 ⊗ₜ[R ⧸ I] SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y :=
  rfl

/-- **The translation endomorphism** of the coordinate ring `gr_I(R) ⊗ Sym(E⁰)` of `C ×_X E₀`
attached to a linear map `h : E⁰ →ₗ I/I²`: the identity on the normal-cone factor, and
`ι y ↦ γ(h y) ⊗ 1 + 1 ⊗ ι y` on the generators of the symmetric algebra. -/
noncomputable def translationAlgHom
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero) :
    ResolvedCone.productRing φ →ₐ[R ⧸ I] ResolvedCone.productRing φ :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (SymmetricAlgebra.lift (translationLinear φ h)) fun _ _ => Commute.all _ _

theorem translationAlgHom_tmul
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)
    (c : AffineNormalCone.associatedGradedRing R I)
    (b : SymmetricAlgebra (R ⧸ I) E.degreeOne) :
    translationAlgHom φ h (c ⊗ₜ[R ⧸ I] b) =
      c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne) *
        SymmetricAlgebra.lift (translationLinear φ h) b :=
  rfl

@[simp]
theorem translationAlgHom_tmul_one
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)
    (c : AffineNormalCone.associatedGradedRing R I) :
    translationAlgHom φ h (c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) =
      c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne) := by
  rw [translationAlgHom_tmul, map_one, mul_one]

@[simp]
theorem translationAlgHom_one_tmul_ι
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero) (y : E.degreeOne) :
    translationAlgHom φ h
        ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
          SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y) =
      AffineNormalCone.conormalToAssociatedGraded R I (h y) ⊗ₜ[R ⧸ I] 1 +
        1 ⊗ₜ[R ⧸ I] SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y := by
  rw [translationAlgHom_tmul, SymmetricAlgebra.lift_ι_apply, translationLinear_apply,
    ← Algebra.TensorProduct.one_def, one_mul]

/-- Two algebra maps out of `gr_I(R) ⊗ Sym(E⁰)` agree as soon as they agree on the normal-cone
factor and on the degree-one generators of the symmetric algebra. -/
theorem productRing_algHom_ext {C : Type u} [CommRing C] [Algebra (R ⧸ I) C]
    {f g : ResolvedCone.productRing φ →ₐ[R ⧸ I] C}
    (hleft : ∀ c : AffineNormalCone.associatedGradedRing R I,
      f (c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) =
        g (c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)))
    (hright : ∀ y : E.degreeOne,
      f ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
          SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y) =
        g ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
          SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y)) :
    f = g := by
  refine Algebra.TensorProduct.ext (AlgHom.ext hleft) ?_
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun y => ?_)
  exact hright y

/-- The translations compose additively. -/
theorem translationAlgHom_comp
    (h h' : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero) :
    (translationAlgHom φ h').comp (translationAlgHom φ h) = translationAlgHom φ (h + h') := by
  refine productRing_algHom_ext φ (fun c => ?_) (fun y => ?_)
  · change translationAlgHom φ h' (translationAlgHom φ h _) = _
    rw [translationAlgHom_tmul_one, translationAlgHom_tmul_one, translationAlgHom_tmul_one]
  · change translationAlgHom φ h' (translationAlgHom φ h _) = _
    rw [translationAlgHom_one_tmul_ι, map_add, translationAlgHom_tmul_one,
      translationAlgHom_one_tmul_ι, translationAlgHom_one_tmul_ι, LinearMap.add_apply,
      map_add, TensorProduct.add_tmul, ← add_assoc]

/-- The translation by the zero map is the identity. -/
theorem translationAlgHom_zero :
    translationAlgHom φ (0 : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero) =
      AlgHom.id (R ⧸ I) (ResolvedCone.productRing φ) := by
  refine productRing_algHom_ext φ (fun c => ?_) (fun y => ?_)
  · rw [translationAlgHom_tmul_one, AlgHom.id_apply]
  · rw [translationAlgHom_one_tmul_ι, AlgHom.id_apply, LinearMap.zero_apply, map_zero,
      TensorProduct.zero_tmul, zero_add]

/-- **The translation automorphism** of the coordinate ring of `C ×_X E₀`.  Its inverse is the
translation by `-h`. -/
noncomputable def translationAut
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero) :
    ResolvedCone.productRing φ ≃ₐ[R ⧸ I] ResolvedCone.productRing φ :=
  AlgEquiv.ofAlgHom (translationAlgHom φ h) (translationAlgHom φ (-h))
    (by rw [translationAlgHom_comp, neg_add_cancel, translationAlgHom_zero])
    (by rw [translationAlgHom_comp, add_neg_cancel, translationAlgHom_zero])

@[simp]
theorem translationAut_apply
    (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)
    (z : ResolvedCone.productRing φ) :
    translationAut φ h z = translationAlgHom φ h z :=
  rfl

end Translation

/-! ## The ideal of the resolved cone is a chain-homotopy invariant -/

section Ideal

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable (φ φ' : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)

/-- **The translation automorphism intertwines the two coordinate-ring maps of `C ×_X E₀ → E₁`**
attached to two chain maps differing by the homotopy `h` in degree `-1`. -/
theorem translationAlgHom_comp_productMap
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential) :
    (translationAlgHom φ h).comp (ResolvedCone.productMap φ) = ResolvedCone.productMap φ' := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  have h0 : φ'.degreeZero x = φ.degreeZero x + h (E.differential x) := by
    rw [hφ]; rfl
  change translationAlgHom φ h
      (ResolvedCone.productMap φ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)) =
    ResolvedCone.productMap φ' (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)
  rw [ResolvedCone.productMap_ι, ResolvedCone.productMap_ι, map_add, translationAlgHom_tmul_one,
    translationAlgHom_one_tmul_ι, h0, map_add, TensorProduct.add_tmul, add_assoc]

/-- The pointwise form of `translationAlgHom_comp_productMap`. -/
theorem translationAlgHom_productMap
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential) (a : ResolvedCone.bundleRing φ) :
    translationAlgHom φ h (ResolvedCone.productMap φ a) = ResolvedCone.productMap φ' a :=
  congrArg (fun f : ResolvedCone.bundleRing φ →ₐ[R ⧸ I] ResolvedCone.productRing φ => f a)
    (translationAlgHom_comp_productMap φ φ' h hφ)

/-- **The translation automorphism carries the coordinate-ring map of `φ` to the one of `φ'`.**
This is `translationAlgHom_productMap` phrased for the automorphism. -/
theorem translationAut_productMap
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential) (a : ResolvedCone.bundleRing φ) :
    translationAut φ h (ResolvedCone.productMap φ a) = ResolvedCone.productMap φ' a :=
  translationAlgHom_productMap φ φ' h hφ a

/-- **The ideal of the resolved cone is unchanged by a degree `-1` chain homotopy.** -/
theorem ideal_congr (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential) :
    ResolvedCone.ideal φ' = ResolvedCone.ideal φ := by
  ext a
  rw [ResolvedCone.mem_ideal_iff, ResolvedCone.mem_ideal_iff,
    ← translationAlgHom_productMap φ φ' h hφ a]
  constructor
  · intro ha
    refine (translationAut φ h).injective ?_
    rw [translationAut_apply, translationAut_apply, ha, map_zero]
  · intro ha
    rw [ha, map_zero]

end Ideal

section ChainHomotopy

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable {φ φ' : LinearTwoTermComplex.Hom E (conormalComplex k R I)}

/-- The degree `-1` component of a chain homotopy, in the shape used by `ideal_congr`. -/
theorem degreeZero_eq_of_chainHomotopy (H : LinearTwoTermComplex.ChainHomotopy φ φ') :
    φ'.degreeZero = φ.degreeZero + H.homotopy.comp E.differential :=
  LinearMap.ext H.degreeZero

/-- **Chain-homotopic obstruction theories have the same resolved cone.** -/
theorem ideal_congr_chainHomotopy (H : LinearTwoTermComplex.ChainHomotopy φ φ') :
    ResolvedCone.ideal φ' = ResolvedCone.ideal φ :=
  ideal_congr φ φ' H.homotopy (degreeZero_eq_of_chainHomotopy H)

/-- **Being an obstruction theory is a chain-homotopy invariant.**  Both the map induced on the
kernel and the map induced on the cokernel of the differential are unchanged by a chain
homotopy. -/
theorem isObstructionTheory_of_chainHomotopy (H : LinearTwoTermComplex.ChainHomotopy φ φ')
    (hφ : PicardCriteria.IsObstructionTheory φ) : PicardCriteria.IsObstructionTheory φ' where
  bijective_cokernelMap := by
    rw [← H.cokernelMap_eq]; exact hφ.bijective_cokernelMap
  surjective_kernelMap := by
    rw [← H.kernelMap_eq]; exact hφ.surjective_kernelMap

end ChainHomotopy

/-! ## The cycle of a closed subscheme, as a function of its ideal -/

section QuotientCycle

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The closed immersion `Spec (A ⧸ J) ↪ Spec A`. -/
noncomputable def quotientImmersion (J : Ideal A) :
    Spec (CommRingCat.of (A ⧸ J)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

/-- The quotient morphism is a closed immersion. -/
noncomputable instance quotientImmersion_isClosedImmersion (J : Ideal A) :
    IsClosedImmersion (quotientImmersion J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The dimension-`d` part of the pushforward of the fundamental cycle of the closed subscheme
`Spec (A ⧸ J) ⊆ Spec A`.  In contrast with `VirtualClass.resolvedConeCycleAt`, the *type* of this
cycle does not mention the ideal `J`, so equalities of ideals may be rewritten inside it. -/
noncomputable def quotientCycle (J : Ideal A)
    (dim : DimensionFunction (Spec (CommRingCat.of A))) (d : ℤ) :
    cyclesOfDimension (Spec (CommRingCat.of A)) dim d :=
  cyclesOfDimension.project
    (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotientImmersion J)
      (DimensionFunction.comapClosedImmersion (quotientImmersion J) dim) dim
      (Spec (CommRingCat.of (A ⧸ J))).fundamentalCycle)

/-- Equal ideals give equal cycles. -/
theorem quotientCycle_congr {J J' : Ideal A} (hJ : J' = J)
    (dim : DimensionFunction (Spec (CommRingCat.of A))) (d : ℤ) :
    quotientCycle J' dim d = quotientCycle J dim d := by
  rw [hJ]

end QuotientCycle

/-! ## Invariance of the resolved-cone cycle, class and virtual class -/

section Cycle

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ φ' : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (h : E.degreeOne →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero)

/-- The degree-generic resolved-cone cycle is the cycle of the ideal of the resolved cone. -/
theorem resolvedConeCycleAt_eq_quotientCycle
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (d : ℤ) :
    VirtualClass.resolvedConeCycleAt φ dimE d = quotientCycle (ResolvedCone.ideal φ) dimE d :=
  rfl

/-- **The degree-generic resolved-cone cycle is unchanged by a degree `-1` chain homotopy.** -/
theorem resolvedConeCycleAt_congr
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (d : ℤ) :
    VirtualClass.resolvedConeCycleAt φ' dimE d = VirtualClass.resolvedConeCycleAt φ dimE d := by
  rw [resolvedConeCycleAt_eq_quotientCycle, resolvedConeCycleAt_eq_quotientCycle,
    quotientCycle_congr (ideal_congr φ φ' h hφ)]

/-- **The resolved-cone cycle is unchanged by a degree `-1` chain homotopy.** -/
theorem resolvedConeCycle_congr
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) :
    VirtualClass.resolvedConeCycle φ' dimE = VirtualClass.resolvedConeCycle φ dimE :=
  resolvedConeCycleAt_congr φ φ' h hφ dimE (VirtualClass.coneDegree φ)

/-- **The resolved-cone class is unchanged by a degree `-1` chain homotopy.** -/
theorem resolvedConeClass_congr
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.coneDegree φ)) :
    VirtualClass.resolvedConeClass φ' dimE RE = VirtualClass.resolvedConeClass φ dimE RE :=
  congrArg RE.quotientMap (resolvedConeCycle_congr φ φ' h hφ dimE)

/-- **The degree-generic resolved-cone class is unchanged by a degree `-1` chain homotopy.** -/
theorem resolvedConeClassAt_congr
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential)
    {ι : Type u} (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (i : ℤ)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (i + (Nat.card ι : ℤ))) :
    VirtualClass.resolvedConeClassAt (ι := ι) φ' dimE i RE =
      VirtualClass.resolvedConeClassAt (ι := ι) φ dimE i RE :=
  congrArg RE.quotientMap (resolvedConeCycleAt_congr φ φ' h hφ dimE (i + (Nat.card ι : ℤ)))

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The virtual dimension only depends on the complex `E`, so it is unchanged. -/
theorem virtualDimension_congr :
    VirtualClass.virtualDimension φ' = VirtualClass.virtualDimension φ :=
  rfl

/-- **The virtual class computed in an arbitrary trivialisation `e` and degree `i` is unchanged
by a degree `-1` chain homotopy.** -/
theorem virtualClassAt_congr
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential)
    {ι : Type u} [Finite ι] (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    VirtualClass.virtualClassAt φ' e dimX dimE i RX RE hhom hinj =
      VirtualClass.virtualClassAt φ e dimX dimE i RX RE hhom hinj :=
  congrArg (VectorBundle.zeroSectionGysin' e dimX dimE i RX RE hhom hinj)
    (resolvedConeClassAt_congr φ φ' h hφ dimE i RE)

/-- **The virtual fundamental class is unchanged by a degree `-1` chain homotopy.**  The
hypotheses `hhom` and `hinj` only mention the complex `E`, so the same pair serves for `φ` and
for `φ'`. -/
theorem virtualClass_congr
    (hφ : φ'.degreeZero = φ.degreeZero + h.comp E.differential)
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension φ))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.coneDegree φ))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VirtualClass.bundlePullback φ dimX dimE RX RE)) :
    VirtualClass.virtualClass φ' dimX dimE RX RE hhom hinj =
      VirtualClass.virtualClass φ dimX dimE RX RE hhom hinj :=
  congrArg
    (VectorBundle.zeroSectionGysin' (VirtualClass.trivialization φ) dimX dimE
      (VirtualClass.virtualDimension φ) RX RE hhom hinj)
    (resolvedConeClass_congr φ φ' h hφ dimE RE)

end Cycle

/-! ## The chain-homotopy corollaries -/

section ChainHomotopyClass

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable {φ φ' : LinearTwoTermComplex.Hom E (conormalComplex k R I)}

/-- **Chain-homotopic obstruction theories have the same resolved-cone cycle.** -/
theorem resolvedConeCycle_congr_chainHomotopy (H : LinearTwoTermComplex.ChainHomotopy φ φ')
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) :
    VirtualClass.resolvedConeCycle φ' dimE = VirtualClass.resolvedConeCycle φ dimE :=
  resolvedConeCycle_congr φ φ' H.homotopy (degreeZero_eq_of_chainHomotopy H) dimE

/-- **Chain-homotopic obstruction theories have the same virtual fundamental class.** -/
theorem virtualClass_congr_chainHomotopy (H : LinearTwoTermComplex.ChainHomotopy φ φ')
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
      (VirtualClass.virtualDimension φ))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
      (VirtualClass.coneDegree φ))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VirtualClass.bundlePullback φ dimX dimE RX RE)) :
    VirtualClass.virtualClass φ' dimX dimE RX RE hhom hinj =
      VirtualClass.virtualClass φ dimX dimE RX RE hhom hinj :=
  virtualClass_congr φ φ' H.homotopy (degreeZero_eq_of_chainHomotopy H) dimX dimE RX RE hhom hinj

/-- **Chain-homotopic obstruction theories have the same virtual class in every
trivialisation.** -/
theorem virtualClassAt_congr_chainHomotopy (H : LinearTwoTermComplex.ChainHomotopy φ φ')
    {ι : Type u} [Finite ι] (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    VirtualClass.virtualClassAt φ' e dimX dimE i RX RE hhom hinj =
      VirtualClass.virtualClassAt φ e dimX dimE i RX RE hhom hinj :=
  virtualClassAt_congr φ φ' H.homotopy (degreeZero_eq_of_chainHomotopy H) e dimX dimE i RX RE
    hhom hinj

end ChainHomotopyClass

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.HomotopyInvariance
