/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.ObstructionTheory.AffineObstructionCone
import GromovWitten.AlgebraicGeometry.Cones.Affine

/-!
# The resolved cone `C(E) ⊆ E₁` of an obstruction theory, in the affine model

Let `X = Spec (R ⧸ I)` be the affine closed subscheme of `Spec R` cut out by `I`, let
`L = conormalComplex k R I` be the two-term conormal complex `[I/I² → (R/I) ⊗ Ω[R⁄k]]` and let
`φ : E ⟶ L` be a chain map of two-term complexes (an obstruction theory in the sense of
`PicardCriteria.IsObstructionTheory`, although none of the constructions below need that
hypothesis).  Dually, `E₁ = Spec Sym(E⁻¹)` and `E₀ = Spec Sym(E⁰)` are vector bundles over `X`
and `C = Spec gr_I(R)` is the normal cone.

Behrend–Fantechi's resolved cone is the fibre product `C(E) = 𝔠_X ×_{h¹/h⁰(E^∨)} E₁`.  In the
affine model with a global two-term resolution it is the scheme-theoretic image of the morphism

`C ×_X E₀ ⟶ E₁`, `(c, e₀) ↦ φ^∨(c) + d^∨(e₀)`,

whose map on coordinate rings is `productMap φ : Sym(E⁻¹) → gr_I(R) ⊗ Sym(E⁰)`, sending a
degree-one generator `x` to `γ(φ⁻¹(x)) ⊗ 1 + 1 ⊗ ι(d x)`, where `γ = conormalToAssociatedGraded`
is the canonical map `I/I² → gr_I(R)`.

## Main definitions

* `ResolvedCone.bundleRing φ`, `ResolvedCone.bundleSpace φ`: the coordinate ring `Sym(E⁻¹)` and
  the vector bundle `E₁ = Spec Sym(E⁻¹)`.
* `ResolvedCone.productRing φ`, `ResolvedCone.productMap φ`: the coordinate ring
  `gr_I(R) ⊗_{R/I} Sym(E⁰)` of `C ×_X E₀` and the coordinate-ring map of `C ×_X E₀ → E₁`.
* `ResolvedCone.ideal φ`, `ResolvedCone.ring φ`, `ResolvedCone.scheme φ`: the kernel of
  `productMap φ`, the quotient `Sym(E⁻¹) ⧸ ker`, and the resolved cone `C(E) = Spec` of it.
* `ResolvedCone.toBundle φ`, `ResolvedCone.fromProduct φ`: the closed immersion `C(E) ↪ E₁` and
  the factorisation `C ×_X E₀ → C(E)`.
* `ResolvedCone.bundlePoints φ B`, `ResolvedCone.conePoints A J B`, `ResolvedCone.mem φ B`: the
  `B`-points of `E₁` and of `C`, and the condition on a `B`-point of `E₁` that it lies in `C(E)`
  (that is, that its coordinate-ring map kills the ideal of `C(E)`).
* `ResolvedCone.coaction φ`: the translation coaction of the bundle `E₀` on `E₁`, and
  `ResolvedCone.ringCoaction φ`, its descent to `C(E)` when `E⁰` is free.

## Main results

* `ResolvedCone.toBundle_isClosedImmersion`, `ResolvedCone.toProduct_injective`,
  `ResolvedCone.fromProduct_toBundle`: `C(E)` is a closed subscheme of `E₁`, and it is the
  scheme-theoretic image of `C ×_X E₀` (the map on coordinate rings is injective and the
  morphism `C ×_X E₀ → E₁` factors through it).
* `ResolvedCone.le_ideal_of_productMap_eq_zero`: the universal property of the ideal of `C(E)`.
* `ResolvedCone.mem_of_cone_add`: every point of the form `φ^∨(c) + d^∨(e₀)` lies in `C(E)`.
* `ResolvedCone.mem_add`: `C(E)` is stable under translation by `E₀`; proved from flatness of
  `Sym(E⁰)` over `R ⧸ I`, hence under the hypothesis `[Module.Free (R ⧸ I) E.degreeOne]`.
* `ResolvedCone.mem_obstructionCone_obj`: the comparison with the obstruction cone functor of
  `ObstructionTheory/AffineObstructionCone.lean`: the underlying `B`-point of the image of an
  object of `[C/T](B)` lies in `C(E)`, and so does every point isomorphic to it in
  `h¹/h⁰(E^∨)(B)`.

The dimension theory of `C(E)` (purity, the trivialisation of the `T_M`-torsor `C ×_X E₀`) is
in `VirtualFundamentalClass/ResolvedConeDimension.lean`.
-/

universe u

-- The coordinate ring of `C ×_X E₀` is a tensor product whose left factor is itself a quotient
-- of a Rees algebra; synthesising `CommSemiring`/`CommRing` for it, and for its tensor product
-- with `Sym(E⁰)`, needs one more level of pending instance problems than the default.
set_option maxSynthPendingDepth 5

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone

open CategoryTheory
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open scoped TensorProduct

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}

/-! ## The bundle `E₁` and the product `C ×_X E₀` -/

/-- The coordinate ring `Sym_{R/I}(E⁻¹)` of the vector bundle `E₁` dual to the degree-zero term
of the obstruction complex. -/
abbrev bundleRing (_φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) : Type u :=
  SymmetricAlgebra (R ⧸ I) E.degreeZero

/-- The vector bundle `E₁ = Spec Sym_{R/I}(E⁻¹)` over `X = Spec (R ⧸ I)`. -/
noncomputable abbrev bundleSpace (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    _root_.AlgebraicGeometry.Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec (.of (bundleRing φ))

/-- The coordinate ring `gr_I(R) ⊗_{R/I} Sym_{R/I}(E⁰)` of the product `C ×_X E₀` of the normal
cone with the vector bundle `E₀`. -/
abbrev productRing (_φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) : Type u :=
  AffineNormalCone.associatedGradedRing R I ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne

/-- The linear map `E⁻¹ → gr_I(R) ⊗ Sym(E⁰)` classifying the morphism
`C ×_X E₀ → E₁`, `(c, e₀) ↦ φ^∨(c) + d^∨(e₀)`: a generator `x` of `E⁻¹` goes to
`γ(φ⁻¹(x)) ⊗ 1 + 1 ⊗ ι(d x)`. -/
noncomputable def productLinear (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    E.degreeZero →ₗ[R ⧸ I] productRing φ :=
  ((TensorProduct.mk (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
        (SymmetricAlgebra (R ⧸ I) E.degreeOne)).flip 1).comp
      ((AffineNormalCone.conormalToAssociatedGraded R I).comp φ.degreeZero) +
    (TensorProduct.mk (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
        (SymmetricAlgebra (R ⧸ I) E.degreeOne) 1).comp
      ((SymmetricAlgebra.ι (R ⧸ I) E.degreeOne).comp E.differential)

/-- **The coordinate-ring map of `C ×_X E₀ → E₁`.** -/
noncomputable def productMap (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    bundleRing φ →ₐ[R ⧸ I] productRing φ :=
  SymmetricAlgebra.lift (productLinear φ)

@[simp]
theorem productMap_ι (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (x : E.degreeZero) :
    productMap φ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
      AffineNormalCone.conormalToAssociatedGraded R I (φ.degreeZero x) ⊗ₜ[R ⧸ I] 1 +
        1 ⊗ₜ[R ⧸ I] SymmetricAlgebra.ι (R ⧸ I) E.degreeOne (E.differential x) := by
  rw [productMap, SymmetricAlgebra.lift_ι_apply]
  rfl

/-! ## The resolved cone -/

/-- The ideal of the resolved cone inside the coordinate ring of `E₁`: the kernel of the
coordinate-ring map of `C ×_X E₀ → E₁`.  Its vanishing locus is the scheme-theoretic image. -/
noncomputable def ideal (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    Ideal (bundleRing φ) :=
  RingHom.ker (productMap φ)

theorem mem_ideal_iff {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
    {a : bundleRing φ} : a ∈ ideal φ ↔ productMap φ a = 0 :=
  Iff.rfl

/-- The coordinate ring of the resolved cone `C(E)`. -/
abbrev ring (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) : Type u :=
  bundleRing φ ⧸ ideal φ

/-- **The resolved cone** `C(E) ⊆ E₁`. -/
noncomputable abbrev scheme (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    _root_.AlgebraicGeometry.Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec (.of (ring φ))

/-- The closed immersion `C(E) ↪ E₁`. -/
noncomputable def toBundle (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    scheme φ ⟶ bundleSpace φ :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (Ideal.Quotient.mk (ideal φ)))

/-- The resolved cone is a closed subscheme of the bundle `E₁`. -/
noncomputable instance toBundle_isClosedImmersion
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    _root_.AlgebraicGeometry.IsClosedImmersion (toBundle φ) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    Ideal.Quotient.mk_surjective

/-- The defining hypothesis of the factorisation, stated separately so that the quotient lift
below is not built from an anonymous proof term. -/
theorem productMap_eq_zero_of_mem_ideal
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) (a : bundleRing φ)
    (ha : a ∈ ideal φ) : productMap φ a = 0 :=
  ha

/-- **The coordinate-ring map of the factorisation `C ×_X E₀ → C(E)`.**  It is injective: this
is the statement that `C(E)` is the scheme-theoretic image of `C ×_X E₀`. -/
noncomputable def toProduct (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    ring φ →ₐ[R ⧸ I] productRing φ :=
  Ideal.Quotient.liftₐ (ideal φ) (productMap φ) (productMap_eq_zero_of_mem_ideal φ)

@[simp]
theorem toProduct_mk (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (a : bundleRing φ) :
    toProduct φ (Ideal.Quotient.mk (ideal φ) a) = productMap φ a :=
  rfl

/-- The resolved cone is the scheme-theoretic image of `C ×_X E₀`: its coordinate ring embeds
into the coordinate ring of `C ×_X E₀`. -/
theorem toProduct_injective (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    Function.Injective (toProduct φ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ha

/-- The factorisation `C ×_X E₀ → C(E)` of the morphism `C ×_X E₀ → E₁`. -/
noncomputable def fromProduct (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    _root_.AlgebraicGeometry.Spec (.of (productRing φ)) ⟶ scheme φ :=
  _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (toProduct φ).toRingHom)

/-- **The factorisation.**  The morphism `C ×_X E₀ → E₁` is the composite of the factorisation
through the resolved cone and the closed immersion `C(E) ↪ E₁`. -/
theorem fromProduct_toBundle (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    fromProduct φ ≫ toBundle φ =
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (productMap φ).toRingHom) := by
  rw [fromProduct, toBundle, ← _root_.AlgebraicGeometry.Spec.map_comp]
  congr 1

/-- **The universal property of the ideal of the resolved cone.**  Every ideal of the coordinate
ring of `E₁` which is killed by the coordinate-ring map of `C ×_X E₀ → E₁` is contained in the
ideal of `C(E)`; equivalently, `C(E)` is the smallest closed subscheme of `E₁` through which
`C ×_X E₀ → E₁` factors. -/
theorem le_ideal_of_productMap_eq_zero
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) (J : Ideal (bundleRing φ))
    (hJ : ∀ a ∈ J, productMap φ a = 0) : J ≤ ideal φ :=
  fun _ ha => hJ _ ha

/-! ## Points of the resolved cone -/

section Points

/-- The `B`-points of the vector bundle `E₁`: linear forms on `E⁻¹`.  Through
`SymmetricAlgebra.lift` these are the `R/I`-algebra maps `Sym(E⁻¹) → B`. -/
abbrev bundlePoints (_φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) (B : Type u)
    [CommRing B] [Algebra (R ⧸ I) B] : Type u :=
  E.degreeZero →ₗ[R ⧸ I] B

/-- The `B`-points of the normal cone `C = Spec gr_J(A)` of an ideal `J ⊆ A`. -/
abbrev conePoints (A : Type u) [CommRing A] (J : Ideal A) (B : Type u) [CommRing B]
    [Algebra (A ⧸ J) B] : Type u :=
  AffineNormalCone.associatedGradedRing A J →ₐ[A ⧸ J] B

/-- The `B`-point `φ^∨(c) + d^∨(e₀)` of `E₁` determined by a `B`-point `c` of the normal cone
and a `B`-point `e₀` of the bundle `E₀`; that is, the image of `(c, e₀)` under the morphism
`C ×_X E₀ → E₁`. -/
noncomputable def conePoint (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (c : conePoints R I B)
    (e₀ : E.degreeOne →ₗ[R ⧸ I] B) : bundlePoints φ B :=
  c.toLinearMap.comp ((AffineNormalCone.conormalToAssociatedGraded R I).comp φ.degreeZero) +
    e₀.comp E.differential

@[simp]
theorem conePoint_apply (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (c : conePoints R I B)
    (e₀ : E.degreeOne →ₗ[R ⧸ I] B) (x : E.degreeZero) :
    conePoint φ B c e₀ x =
      c (AffineNormalCone.conormalToAssociatedGraded R I (φ.degreeZero x)) +
        e₀ (E.differential x) :=
  rfl

/-- **Membership in the resolved cone on `B`-points.**  A `B`-point of `E₁` lies in `C(E)`
exactly when the `R/I`-algebra map `Sym(E⁻¹) → B` it classifies kills the ideal of `C(E)`;
equivalently, when it factors through the coordinate ring of `C(E)`. -/
def mem (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) (B : Type u) [CommRing B]
    [Algebra (R ⧸ I) B] (e : bundlePoints φ B) : Prop :=
  ideal φ ≤ RingHom.ker (SymmetricAlgebra.lift e : bundleRing φ →ₐ[R ⧸ I] B)

theorem mem_iff {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)} {B : Type u}
    [CommRing B] [Algebra (R ⧸ I) B] {e : bundlePoints φ B} :
    mem φ B e ↔ ∀ a ∈ ideal φ, SymmetricAlgebra.lift e a = 0 :=
  Iff.rfl

/-- The algebra map classified by `φ^∨(c) + d^∨(e₀)` factors through the coordinate ring of
`C ×_X E₀`: it is the composite of `productMap φ` with the map classified by `(c, e₀)`. -/
theorem lift_conePoint (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (c : conePoints R I B)
    (e₀ : E.degreeOne →ₗ[R ⧸ I] B) :
    (SymmetricAlgebra.lift (conePoint φ B c e₀) : bundleRing φ →ₐ[R ⧸ I] B) =
      (Algebra.TensorProduct.lift c (SymmetricAlgebra.lift e₀)
        (fun _ _ => Commute.all _ _)).comp (productMap φ) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simp [conePoint]

/-- **The image of `C ×_X E₀` lies in the resolved cone.**  For every `B`-point `c` of the
normal cone and every `B`-point `e₀` of `E₀`, the point `φ^∨(c) + d^∨(e₀)` of `E₁` lies in
`C(E)`. -/
theorem mem_of_cone_add (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (c : conePoints R I B)
    (e₀ : E.degreeOne →ₗ[R ⧸ I] B) : mem φ B (conePoint φ B c e₀) := by
  intro a ha
  refine RingHom.mem_ker.mpr ?_
  rw [lift_conePoint, AlgHom.comp_apply, mem_ideal_iff.mp ha, map_zero]

/-- Postcomposing a point of `E₁` with a map of test algebras corresponds to composing the
classified algebra maps. -/
theorem lift_comp_algHom (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    {B B' : Type u} [CommRing B] [Algebra (R ⧸ I) B] [CommRing B'] [Algebra (R ⧸ I) B']
    (g : B →ₐ[R ⧸ I] B') (e : bundlePoints φ B) :
    (SymmetricAlgebra.lift (g.toLinearMap.comp e) : bundleRing φ →ₐ[R ⧸ I] B') =
      g.comp (SymmetricAlgebra.lift e) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simp

/-- **Membership is natural in the test algebra.** -/
theorem mem_comp (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    {B B' : Type u} [CommRing B] [Algebra (R ⧸ I) B] [CommRing B'] [Algebra (R ⧸ I) B']
    (g : B →ₐ[R ⧸ I] B') {e : bundlePoints φ B} (h : mem φ B e) :
    mem φ B' (g.toLinearMap.comp e) := by
  intro a ha
  refine RingHom.mem_ker.mpr ?_
  rw [lift_comp_algHom, AlgHom.comp_apply, RingHom.mem_ker.mp (h ha), map_zero]

end Points

/-! ## Translation by the bundle `E₀` -/

section Translation

/-- The linear map underlying the translation coaction of `E₀` on `E₁`: a generator `x` of
`E⁻¹` goes to `x ⊗ 1 + 1 ⊗ ι(d x)`. -/
noncomputable def coactionLinear (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    E.degreeZero →ₗ[R ⧸ I] bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne :=
  ((TensorProduct.mk (R ⧸ I) (bundleRing φ)
        (SymmetricAlgebra (R ⧸ I) E.degreeOne)).flip 1).comp
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero) +
    (TensorProduct.mk (R ⧸ I) (bundleRing φ) (SymmetricAlgebra (R ⧸ I) E.degreeOne) 1).comp
      ((SymmetricAlgebra.ι (R ⧸ I) E.degreeOne).comp E.differential)

/-- **The translation coaction of the bundle `E₀` on the bundle `E₁`**, on coordinate rings:
it classifies the action map `E₁ ×_X E₀ → E₁`, `(e, e₀) ↦ e + d^∨(e₀)`. -/
noncomputable def coaction (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    bundleRing φ →ₐ[R ⧸ I] bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne :=
  SymmetricAlgebra.lift (coactionLinear φ)

@[simp]
theorem coaction_ι (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (x : E.degreeZero) :
    coaction φ (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
      SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x ⊗ₜ[R ⧸ I] 1 +
        1 ⊗ₜ[R ⧸ I] SymmetricAlgebra.ι (R ⧸ I) E.degreeOne (E.differential x) := by
  rw [coaction, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The linear map underlying the translation coaction of `E₀` on `C ×_X E₀`, restricted to the
degree-one generators of the second factor. -/
noncomputable def translationLinear (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    E.degreeOne →ₗ[R ⧸ I] productRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne :=
  ((TensorProduct.mk (R ⧸ I) (productRing φ)
        (SymmetricAlgebra (R ⧸ I) E.degreeOne)).flip 1).comp
      ((Algebra.TensorProduct.includeRight :
          SymmetricAlgebra (R ⧸ I) E.degreeOne →ₐ[R ⧸ I] productRing φ).toLinearMap.comp
        (SymmetricAlgebra.ι (R ⧸ I) E.degreeOne)) +
    (TensorProduct.mk (R ⧸ I) (productRing φ) (SymmetricAlgebra (R ⧸ I) E.degreeOne) 1).comp
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeOne)

/-- The restriction of the translation coaction on `C ×_X E₀` to the normal-cone factor: it
is the inclusion of `gr_I(R)` as the first tensor factor. -/
noncomputable def thetaLeft (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    AffineNormalCone.associatedGradedRing R I →ₐ[R ⧸ I]
      productRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne :=
  (Algebra.TensorProduct.includeLeft :
      productRing φ →ₐ[R ⧸ I] productRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne).comp
    (Algebra.TensorProduct.includeLeft :
      AffineNormalCone.associatedGradedRing R I →ₐ[R ⧸ I] productRing φ)

/-- The restriction of the translation coaction on `C ×_X E₀` to the bundle factor. -/
noncomputable def thetaRight (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    SymmetricAlgebra (R ⧸ I) E.degreeOne →ₐ[R ⧸ I]
      productRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne :=
  SymmetricAlgebra.lift (translationLinear φ)

@[simp]
theorem thetaLeft_apply (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (a : AffineNormalCone.associatedGradedRing R I) :
    thetaLeft φ a =
      (a ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) ⊗ₜ[R ⧸ I]
        (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne) :=
  rfl

@[simp]
theorem thetaRight_ι (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (y : E.degreeOne) :
    thetaRight φ (SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y) =
      ((1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
          SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y) ⊗ₜ[R ⧸ I]
        (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne) +
      (1 : productRing φ) ⊗ₜ[R ⧸ I] SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y := by
  rw [thetaRight, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The two halves of the translation coaction on `C ×_X E₀` commute, the target being a
commutative ring. -/
theorem commute_thetaLeft_thetaRight
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (a : AffineNormalCone.associatedGradedRing R I)
    (b : SymmetricAlgebra (R ⧸ I) E.degreeOne) :
    Commute (thetaLeft φ a) (thetaRight φ b) := by
  exact Commute.all _ _

/-- **The translation coaction of `E₀` on `C ×_X E₀`**, on coordinate rings: it classifies
`(C ×_X E₀) ×_X E₀ → C ×_X E₀`, `((c, e₀), e₀') ↦ (c, e₀ + e₀')`. -/
noncomputable def theta (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    productRing φ →ₐ[R ⧸ I] productRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne :=
  Algebra.TensorProduct.lift (thetaLeft φ) (thetaRight φ)
    (commute_thetaLeft_thetaRight φ)

/-- **The morphism `C ×_X E₀ → E₁` is equivariant for the translation actions of `E₀`.**  This
is the coordinate-ring form of the statement that translating a point of `C ×_X E₀` in its
`E₀`-coordinate translates its image in `E₁`. -/
theorem map_productMap_comp_coaction
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    (Algebra.TensorProduct.map (productMap φ)
        (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne))).comp (coaction φ) =
      (theta φ).comp (productMap φ) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simp [theta, TensorProduct.add_tmul, add_assoc, ← Algebra.TensorProduct.one_def]

end Translation

/-! ## Invariance of the resolved cone under translation by `E₀` -/

section Invariance

/-- The linear map underlying `productMap φ ⊗ id` is right tensoring with `Sym(E⁰)`. -/
theorem map_productMap_toLinearMap
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) :
    (Algebra.TensorProduct.map (productMap φ)
        (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne))).toLinearMap =
      LinearMap.rTensor (SymmetricAlgebra (R ⧸ I) E.degreeOne) (productMap φ).toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

/-- An element of the ideal of `C(E)` is carried by the translation coaction into the kernel of
`productMap φ ⊗ id`. -/
theorem rTensor_productMap_coaction
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) (a : bundleRing φ)
    (ha : a ∈ ideal φ) :
    LinearMap.rTensor (SymmetricAlgebra (R ⧸ I) E.degreeOne) (productMap φ).toLinearMap
        (coaction φ a) = 0 := by
  have h : (Algebra.TensorProduct.map (productMap φ)
      (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne))) (coaction φ a) = 0 := by
    rw [← AlgHom.comp_apply, map_productMap_comp_coaction, AlgHom.comp_apply,
      mem_ideal_iff.mp ha, map_zero]
  rw [← h]
  exact (congrArg (fun L => L (coaction φ a)) (map_productMap_toLinearMap φ)).symm

/-- Every element of the image of `ker(productMap φ) ⊗ Sym(E⁰)` lies in the ideal generated by
the ideal of `C(E)` inside `Sym(E⁻¹) ⊗ Sym(E⁰)`. -/
theorem rTensor_subtype_mem_map
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (y : (LinearMap.ker (productMap φ).toLinearMap) ⊗[R ⧸ I]
      SymmetricAlgebra (R ⧸ I) E.degreeOne) :
    LinearMap.rTensor (SymmetricAlgebra (R ⧸ I) E.degreeOne)
        (LinearMap.ker (productMap φ).toLinearMap).subtype y ∈
      Ideal.map (Algebra.TensorProduct.includeLeft : bundleRing φ →ₐ[R ⧸ I]
        bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne) (ideal φ) := by
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · rw [map_zero]
    exact Ideal.zero_mem _
  · rintro ⟨c, hc⟩ t
    have hmem : c ∈ ideal φ := hc
    have hfac : LinearMap.rTensor (SymmetricAlgebra (R ⧸ I) E.degreeOne)
        (LinearMap.ker (productMap φ).toLinearMap).subtype
          ((⟨c, hc⟩ : LinearMap.ker (productMap φ).toLinearMap) ⊗ₜ[R ⧸ I] t) =
        ((1 : bundleRing φ) ⊗ₜ[R ⧸ I] t) *
          (Algebra.TensorProduct.includeLeft : bundleRing φ →ₐ[R ⧸ I]
            bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne) c := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one]
      rfl
    rw [hfac]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)
  · intro y₁ y₂ h₁ h₂
    rw [map_add]
    exact Ideal.add_mem _ h₁ h₂

/-- **The translation coaction preserves the ideal of the resolved cone.**  For `Sym(E⁰)` flat
over `R ⧸ I` — for instance when `E⁰` is free — the coaction carries the ideal of `C(E)` into
the ideal it generates in `Sym(E⁻¹) ⊗ Sym(E⁰)`.  Geometrically: `C(E) ×_X E₀` maps into `C(E)`
under the translation action of `E₀` on `E₁`. -/
theorem coaction_mem_ideal_map
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    [Module.Free (R ⧸ I) E.degreeOne] (a : bundleRing φ) (ha : a ∈ ideal φ) :
    coaction φ a ∈ Ideal.map (Algebra.TensorProduct.includeLeft : bundleRing φ →ₐ[R ⧸ I]
      bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne) (ideal φ) := by
  have hex := Module.Flat.rTensor_exact (R := R ⧸ I)
    (M := SymmetricAlgebra (R ⧸ I) E.degreeOne)
    (LinearMap.exact_subtype_ker_map (productMap φ).toLinearMap)
  obtain ⟨y, hy⟩ := (hex (coaction φ a)).mp (rTensor_productMap_coaction φ a ha)
  rw [← hy]
  exact rTensor_subtype_mem_map φ y

/-- The algebra map classified by a pair `(e, e₀)` of a `B`-point of `E₁` and a `B`-point of
`E₀`, on the coordinate ring of `E₁ ×_X E₀`. -/
noncomputable def translatePoint (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (e : bundlePoints φ B)
    (e₀ : E.degreeOne →ₗ[R ⧸ I] B) :
    bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne →ₐ[R ⧸ I] B :=
  Algebra.TensorProduct.lift (SymmetricAlgebra.lift e) (SymmetricAlgebra.lift e₀)
    (fun _ _ => Commute.all _ _)

/-- The translated point `e + d^∨(e₀)` classifies the composite of the translation coaction with
the map classified by `(e, e₀)`. -/
theorem lift_add_comp_differential
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)) (B : Type u) [CommRing B]
    [Algebra (R ⧸ I) B] (e : bundlePoints φ B) (e₀ : E.degreeOne →ₗ[R ⧸ I] B) :
    (SymmetricAlgebra.lift (e + e₀.comp E.differential) : bundleRing φ →ₐ[R ⧸ I] B) =
      (translatePoint φ B e e₀).comp (coaction φ) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simp [translatePoint]

/-- **`E₀`-invariance of the resolved cone on points.**  If a `B`-point `e` of `E₁` lies in
`C(E)` then so does its translate `e + d^∨(e₀)` by any `B`-point `e₀` of `E₀`.  The hypothesis
that `E⁰` is free makes `Sym(E⁰)` flat over `R ⧸ I`, which is what identifies the kernel of
`productMap φ ⊗ id` with the ideal generated by the ideal of `C(E)`. -/
theorem mem_add (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    [Module.Free (R ⧸ I) E.degreeOne] (B : Type u) [CommRing B] [Algebra (R ⧸ I) B]
    (e : bundlePoints φ B) (e₀ : E.degreeOne →ₗ[R ⧸ I] B) (h : mem φ B e) :
    mem φ B (e + e₀.comp E.differential) := by
  have hle : Ideal.map (Algebra.TensorProduct.includeLeft : bundleRing φ →ₐ[R ⧸ I]
      bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne) (ideal φ) ≤
      RingHom.ker (translatePoint φ B e e₀) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    refine Ideal.mem_comap.mpr (RingHom.mem_ker.mpr ?_)
    rw [Algebra.TensorProduct.includeLeft_apply, translatePoint,
      Algebra.TensorProduct.lift_tmul, RingHom.mem_ker.mp (h hb), map_one, zero_mul]
  intro a ha
  refine RingHom.mem_ker.mpr ?_
  rw [lift_add_comp_differential, AlgHom.comp_apply]
  exact RingHom.mem_ker.mp (hle (coaction_mem_ideal_map φ a ha))

/-- The hypothesis of the descent of the translation coaction to the resolved cone, stated
separately so that the quotient lift below is not built from an anonymous proof term. -/
theorem quotientMap_coaction_eq_zero
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    [Module.Free (R ⧸ I) E.degreeOne] (a : bundleRing φ) (ha : a ∈ ideal φ) :
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ (R ⧸ I) (ideal φ))
        (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne))).comp (coaction φ)) a = 0 := by
  have hle : Ideal.map (Algebra.TensorProduct.includeLeft : bundleRing φ →ₐ[R ⧸ I]
      bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne) (ideal φ) ≤
      RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ (R ⧸ I) (ideal φ))
        (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne))) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    refine Ideal.mem_comap.mpr (RingHom.mem_ker.mpr ?_)
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hb,
      TensorProduct.zero_tmul]
  rw [AlgHom.comp_apply]
  exact RingHom.mem_ker.mp (hle (coaction_mem_ideal_map φ a ha))

/-- **The translation coaction descends to the resolved cone.**  It exhibits `C(E)` as stable
under the translation action of the vector bundle `E₀` on `E₁`. -/
noncomputable def ringCoaction (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    [Module.Free (R ⧸ I) E.degreeOne] :
    ring φ →ₐ[R ⧸ I] ring φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) E.degreeOne :=
  Ideal.Quotient.liftₐ (ideal φ)
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ (R ⧸ I) (ideal φ))
      (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne))).comp (coaction φ))
    (quotientMap_coaction_eq_zero φ)

end Invariance

/-! ## Comparison with the obstruction cone functor -/

section Comparison

open ConeQuotient PicardCriteria

/-- The coordinate-ring map `Sym(J/J²) → gr_J(A)` of the closed immersion of the normal cone
into the normal sheaf, as an `A/J`-algebra map.  It is the symmetric-algebra lift of the
canonical degree-one map `AffineNormalCone.conormalToAssociatedGraded`. -/
noncomputable def coneCoordinateAlgHom (A : Type u) [CommRing A] (J : Ideal A) :
    SymmetricAlgebra (A ⧸ J) J.Cotangent →ₐ[A ⧸ J] AffineNormalCone.associatedGradedRing A J :=
  SymmetricAlgebra.lift (AffineNormalCone.conormalToAssociatedGraded A J)

@[simp]
theorem coneCoordinateAlgHom_ι (A : Type u) [CommRing A] (J : Ideal A) (x : J.Cotangent) :
    coneCoordinateAlgHom A J (SymmetricAlgebra.ι (A ⧸ J) J.Cotangent x) =
      AffineNormalCone.conormalToAssociatedGraded A J x :=
  SymmetricAlgebra.lift_ι_apply _ x

/-- Reading a `B`-point of the normal cone as a `B`-point of the normal sheaf, that is, as a
linear form on `I/I²`. -/
theorem lift_symm_comp_coneCoordinateAlgHom (B : Type u) [CommRing B] [Algebra (R ⧸ I) B]
    (c : AffineNormalCone.associatedGradedRing R I →ₐ[R ⧸ I] B) :
    SymmetricAlgebra.lift.symm (c.comp (coneCoordinateAlgHom R I)) =
      c.toLinearMap.comp (AffineNormalCone.conormalToAssociatedGraded R I) := by
  rw [Equiv.symm_apply_eq]
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun y => ?_)
  simp

/-- **The obstruction cone functor lands in the resolved cone, on objects.**  The `B`-point of
`E₁` underlying the image of an object of `[C/T](B)` under
`PicardCriteria.obstructionCone` is the point `φ^∨(c)` of `C ×_X E₀` with zero `E₀`-component. -/
theorem obstructionCone_obj_back
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    {Ac : ConeAction (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
      (conormalComplex k R I).degreeOne}
    (h : IsEquivariant (bundleTranslationAction (AffineNormalCone.conormalMap k R I)) Ac
      (coneCoordinateAlgHom R I) LinearMap.id)
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (c : QuotientGroupoid Ac B) :
    dualBack E B ((obstructionCone φ h B).obj c) = conePoint φ B c.point 0 := by
  have key : dualBack E B ((obstructionCone φ h B).obj c) =
      (SymmetricAlgebra.lift.symm (c.point.comp (coneCoordinateAlgHom R I))).comp
        φ.degreeZero :=
    rfl
  rw [key, lift_symm_comp_coneCoordinateAlgHom, conePoint, LinearMap.zero_comp, add_zero,
    LinearMap.comp_assoc]

/-- **Comparison with the obstruction cone.**  The `B`-point of `E₁` underlying the image of an
object of the quotient groupoid `[C/T](B)` under the obstruction cone functor lies in the
resolved cone `C(E)`.  The cone action `Ac` on `gr_I(R)` and the equivariance `h` of the closed
immersion `C ↪ N` are hypotheses: they are the data with which
`PicardCriteria.obstructionCone` is formed. -/
theorem mem_obstructionCone_obj
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    {Ac : ConeAction (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
      (conormalComplex k R I).degreeOne}
    (h : IsEquivariant (bundleTranslationAction (AffineNormalCone.conormalMap k R I)) Ac
      (coneCoordinateAlgHom R I) LinearMap.id)
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (c : QuotientGroupoid Ac B) :
    mem φ B (dualBack E B ((obstructionCone φ h B).obj c)) := by
  rw [obstructionCone_obj_back]
  exact mem_of_cone_add φ B c.point 0

/-- **Comparison with the obstruction cone, up to isomorphism.**  If a `B`-point of `E₁` is
isomorphic, in the fibre `h¹/h⁰(E^∨)(B)`, to the image of an object of `[C/T](B)` under the
obstruction cone functor, then it lies in the resolved cone `C(E)`.  Since an arrow of
`h¹/h⁰(E^∨)(B)` is a `B`-point `e₀` of `E₀` translating the source to the target, this is
literally `ResolvedCone.mem_of_cone_add` with that `e₀`; in particular no flatness hypothesis is
needed here. -/
theorem mem_of_hom_obstructionCone_obj
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    {Ac : ConeAction (R ⧸ I) (AffineNormalCone.associatedGradedRing R I)
      (conormalComplex k R I).degreeOne}
    (h : IsEquivariant (bundleTranslationAction (AffineNormalCone.conormalMap k R I)) Ac
      (coneCoordinateAlgHom R I) LinearMap.id)
    (B : Type u) [CommRing B] [Algebra (R ⧸ I) B] (c : QuotientGroupoid Ac B)
    (z : (dualPoints E B).quotient) (a : (obstructionCone φ h B).obj c ⟶ z) :
    mem φ B (dualBack E B z) := by
  have ht : dualBack E B ((obstructionCone φ h B).obj c) +
      (dualVal E B a).comp E.differential = dualBack E B z := a.translate
  have hz : dualBack E B z = conePoint φ B c.point (dualVal E B a) := by
    rw [← ht, obstructionCone_obj_back, conePoint, conePoint, LinearMap.zero_comp, add_zero]
  rw [hz]
  exact mem_of_cone_add φ B c.point (dualVal E B a)

end Comparison

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ResolvedCone
