/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.NormalConeAction
import GromovWitten.AlgebraicGeometry.Cones.RefinementQuotient
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat

/-!
# The tangent action on the affine normal cone beyond the polynomial model

`Cones/ConeTranslation.lean` constructs the translation coaction

`ConeTranslation.coaction : gr_I(P) →ₐ[P] gr_I(P)[ε_σ]`,  `P = A[x_i]_{i ∈ σ}`,

of the tangent bundle `T_M|_U = U × 𝔸^σ` of the *polynomial* ambient scheme `M = 𝔸^σ_A` on the
affine normal cone `C_{U/M} = Spec gr_I(P)`.  For the global gluing of the intrinsic normal cone
one needs the same structure over ambient schemes which are only *étale-locally* affine space:
open subschemes `D(f) ⊆ 𝔸^σ`, and more generally any `M' = Spec R` with `R` a flat `P`-algebra
whose relative tangent bundle is still trivialised by `x_1, …, x_σ`.

This file carries the whole coaction package across flat base change `P → R`.

## Main construction

Fix a commutative ring `A`, an index type `σ`, `P = Amb A σ = A[x_i]`, an ideal `I ⊆ P` and a flat
`P`-algebra `R`.  Write `J = I·R` (`locIdeal`) and `gr_J(R)` (`GrLoc`).  Flat base change of the
Rees algebra (`AffineNormalCone.grTensorEquiv`) gives

* `ConeLocalisation.grLocEquiv : R ⊗_P gr_I(P) ≃ₐ[R] gr_J(R)`,

and the base-change adjunction `AlgHom.liftEquiv` transports `coaction` to

* `ConeLocalisation.locCoaction : gr_J(R) →ₐ[R] gr_J(R)[ε_σ]`,
  characterised by `locCoaction_grLocMap` and `locCoaction_algebraMap`.

All the laws of the polynomial model are proved for it:

* `locCoaction_counit` (the counit law), `locCoaction_coassoc` (coassociativity),
* `locTranslatePoint_zero` and `locTranslatePoint_add` (the action on `B`-points is an action of
  the additive group `σ → B`),
* `locNsCoaction` together with `locCoaction_comp_nsToGr`: the normal-sheaf coaction and the
  equivariance of the closed immersion `C_{U/M'} ↪ N_{U/M'}` (Vistoli's lemma after base change).

## Localisation invariance of `[C/T](B)`

For a ring `B` which is both an `R`-algebra and a `P`-algebra compatibly, the `R`-algebra points
of `gr_J(R)` are exactly the `P`-algebra points of `gr_I(P)` (`pointEquiv`), compatibly with
translation (`locTranslatePoint_iff`).  Packaged as groupoids this is

* `ConeLocalisation.locConeEquivalence :
    LocConeGroupoid R I B ≌ AlgConeGroupoid I B`,

an equivalence between the action groupoid of the translation action on the `B`-points of
`C_{U/M'}` and the `P`-algebra points of the polynomial model, and

* `ConeLocalisation.toConeGroupoid : AlgConeGroupoid I B ⥤ ConeRefinement.ConeGroupoid I B`,
  the forgetful functor to the polynomial-model groupoid of `Cones/RefinementQuotient.lean`,
  which is full (`instFullToConeGroupoid`) and faithful (`instFaithfulToConeGroupoid`) with
  essential image described by `exists_obj_eq_iff`.

This is the statement that the chart transitions of the global gluing need: passing from `𝔸^σ` to
an open (or flat) subchart does not change the quotient groupoid `[C_{U/M}/T_M|_U]`.

## Localisations and étale charts

* `flat_of_isLocalization` / `flat_of_isLocalizationAway`: a localisation `S⁻¹P`, in particular
  an open chart `D(f)`, is flat over `P`, so everything above applies to it;
* `locIdeal_comap`: *every* ideal of a localisation is extended from `P`, so the above describes
  the normal cone of an arbitrary closed subscheme of the open chart;
* `flat_of_etale` / `flat_of_smooth`: an étale (or smooth) algebra over `𝔸^σ` is flat over it,
  which is the finitely presented case of "formally étale over affine space";
* `locCoaction_unique`: the extended coaction is the unique `R`-algebra map extending
  `ConeTranslation.coaction`, the algebraic form of the uniqueness of the Taylor lifts along the
  nilpotent thickenings `R[ε]/(ε)^N → R`.
-/

namespace GromovWitten.AlgebraicGeometry

namespace ConeLocalisation

universe u

open ConeTranslation AffineNormalCone TensorProduct

noncomputable section

variable {A : Type u} [CommRing A] {σ : Type u} (R : Type u) [CommRing R]
  [Algebra (Amb A σ) R] (I : Ideal (Amb A σ))

/-! ### The extended ideal and its associated graded ring -/

/-- The ideal `I·R` extended from the polynomial ring to the flat ambient extension `R`. -/
abbrev locIdeal : Ideal R := I.map (algebraMap (Amb A σ) R)

/-- The associated graded ring `gr_{I·R}(R)`, the coordinate ring of the affine normal cone of
`Spec (R/I·R) ⊆ Spec R`. -/
abbrev GrLoc : Type u := associatedGradedRing R (locIdeal R I)

/-- Shortcut instance: `gr_{I·R}(R)` is a commutative ring (instance search does not find this
through the Rees subalgebra quotient). -/
instance instCommRingGrLoc : CommRing (GrLoc R I) := Ideal.Quotient.commRing _

/-- Shortcut instance for the polynomial ring `gr_{I·R}(R)[ε_σ]`. -/
instance instCommRingPolyGrLoc : CommRing (MvPolynomial σ (GrLoc R I)) :=
  AddMonoidAlgebra.commRing

/-- Shortcut instance for the twice-iterated polynomial ring, used in coassociativity. -/
instance instCommRingPolyPolyGrLoc :
    CommRing (MvPolynomial σ (MvPolynomial σ (GrLoc R I))) :=
  AddMonoidAlgebra.commRing

/-- The canonical map `gr_I(P) → gr_{I·R}(R)` of associated graded rings. -/
def grLocMap : Gr I →+* GrLoc R I :=
  grMapOfEq I (algebraMap (Amb A σ) R) (locIdeal R I) rfl

@[simp]
theorem grLocMap_algebraMap (r : Amb A σ) :
    grLocMap R I (algebraMap (Amb A σ) (Gr I) r) =
      algebraMap R (GrLoc R I) (algebraMap (Amb A σ) R r) :=
  grMapOfEq_algebraMap I _ _ rfl r

/-! ### The coaction -/

/-- The composite `gr_I(P) → gr_I(P)[ε_σ] → gr_{I·R}(R)[ε_σ]`, a `P`-algebra map. -/
def locCoactionAux : Gr I →ₐ[Amb A σ] MvPolynomial σ (GrLoc R I) where
  toRingHom := (MvPolynomial.map (grLocMap R I)).comp (coaction I).toRingHom
  commutes' r := by
    change MvPolynomial.map (grLocMap R I) (coaction I (algebraMap _ _ r)) = _
    rw [coaction_algebraMap, MvPolynomial.map_C, grLocMap_algebraMap,
      MvPolynomial.algebraMap_apply, IsScalarTower.algebraMap_apply (Amb A σ) R (GrLoc R I)]

theorem locCoactionAux_apply (z : Gr I) :
    locCoactionAux R I z = MvPolynomial.map (grLocMap R I) (coaction I z) := rfl

/-! ### The `P`-algebra points of the polynomial-model quotient groupoid -/

section AlgGroupoid

open CategoryTheory

/-- The `B`-points of `[C_{U/M}/T_M|_U]` which are `P`-algebra points: the action groupoid of
`Cones/RefinementQuotient.lean` with the structure map of `B` over the ambient polynomial ring
remembered. -/
@[ext]
structure AlgConeGroupoid (I : Ideal (Amb A σ)) (B : Type u) [CommRing B]
    [Algebra (Amb A σ) B] where
  /-- The underlying `P`-algebra point of the affine normal cone. -/
  point : Gr I →ₐ[Amb A σ] B

namespace AlgConeGroupoid

variable {I} {B : Type u} [CommRing B] [Algebra (Amb A σ) B]

/-- An arrow of the action groupoid: a `B`-point of the tangent bundle `T_M|_U = U × 𝔸^σ`
carrying the source to the target. -/
@[ext]
structure Hom (x y : AlgConeGroupoid I B) where
  /-- The translating tangent vector. -/
  val : σ → B
  /-- It carries the source point to the target point. -/
  translate_eq : translatePoint I x.point.toRingHom val = y.point.toRingHom

/-- The action groupoid structure on the `P`-algebra `B`-points. -/
instance instCategory : Category (AlgConeGroupoid I B) where
  Hom := Hom
  id x := ⟨0, translatePoint_zero I _⟩
  comp f g := ⟨f.val + g.val, by
    rw [← translatePoint_add, f.translate_eq, g.translate_eq]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

/-- The identity arrow translates by the zero tangent vector. -/
@[simp] theorem id_val (x : AlgConeGroupoid I B) : (𝟙 x : x ⟶ x).val = 0 := rfl

/-- Composition of arrows adds the tangent vectors. -/
@[simp] theorem comp_val {x y z : AlgConeGroupoid I B} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val := rfl

/-- Every arrow of the action groupoid is invertible. -/
instance instGroupoid : Groupoid (AlgConeGroupoid I B) where
  inv f := ⟨-f.val, by
    rw [← f.translate_eq, translatePoint_add, add_neg_cancel, translatePoint_zero]⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

/-- The arrow induced by an equality of objects translates by zero. -/
theorem eqToHom_val {x y : AlgConeGroupoid I B} (e : x = y) : (eqToHom e).val = 0 := by
  subst e; rfl

end AlgConeGroupoid

/-- Forgetting that the `B`-points are `P`-algebra maps: the comparison with the quotient
groupoid `ConeRefinement.ConeGroupoid` of `Cones/RefinementQuotient.lean`. -/
def toConeGroupoid (I : Ideal (Amb A σ)) (B : Type u) [CommRing B] [Algebra (Amb A σ) B] :
    AlgConeGroupoid I B ⥤ ConeRefinement.ConeGroupoid I B where
  obj x := ⟨x.point.toRingHom⟩
  map f := ⟨f.val, f.translate_eq⟩
  map_id _ := ConeRefinement.ConeGroupoid.Hom.ext rfl
  map_comp _ _ := ConeRefinement.ConeGroupoid.Hom.ext rfl

/-- The comparison functor is faithful: an arrow is its tangent vector. -/
instance instFaithfulToConeGroupoid (I : Ideal (Amb A σ)) (B : Type u) [CommRing B]
    [Algebra (Amb A σ) B] : (toConeGroupoid I B).Faithful where
  map_injective h := AlgConeGroupoid.Hom.ext (congrArg ConeRefinement.ConeGroupoid.Hom.val h)

/-- The comparison functor is full: the translation condition does not see the algebra
structure. -/
instance instFullToConeGroupoid (I : Ideal (Amb A σ)) (B : Type u) [CommRing B]
    [Algebra (Amb A σ) B] : (toConeGroupoid I B).Full where
  map_surjective g := ⟨⟨g.val, g.translate_eq⟩, rfl⟩

/-- The essential image of the comparison functor: a `B`-point of the affine normal cone comes
from a `P`-algebra point exactly when it is compatible with the structure map of `B`. -/
theorem exists_obj_eq_iff {I : Ideal (Amb A σ)} {B : Type u} [CommRing B]
    [Algebra (Amb A σ) B] (x : ConeRefinement.ConeGroupoid I B) :
    (∃ y : AlgConeGroupoid I B, (toConeGroupoid I B).obj y = x) ↔
      ∀ r : Amb A σ, x.point (algebraMap (Amb A σ) (Gr I) r) = algebraMap (Amb A σ) B r := by
  constructor
  · rintro ⟨y, rfl⟩ r
    exact y.point.commutes r
  · intro h
    exact ⟨⟨⟨x.point, h⟩⟩, rfl⟩

end AlgGroupoid

section Flat

variable [Module.Flat (Amb A σ) R]

/-! ### Flat base change of the associated graded ring -/

/-- **Flat base change of the normal cone**: `gr_{I·R}(R) ≅ R ⊗_P gr_I(P)`. -/
def grLocEquiv : R ⊗[Amb A σ] Gr I ≃ₐ[R] GrLoc R I :=
  grTensorEquiv I (locIdeal R I) rfl

@[simp]
theorem grLocEquiv_one_tmul (z : Gr I) :
    grLocEquiv R I ((1 : R) ⊗ₜ[Amb A σ] z) = grLocMap R I z :=
  grTensorEquiv_one_tmul I (locIdeal R I) rfl z

theorem grLocEquiv_tmul (r : R) (z : Gr I) :
    grLocEquiv R I (r ⊗ₜ[Amb A σ] z) = algebraMap R (GrLoc R I) r * grLocMap R I z := by
  have h : (r ⊗ₜ[Amb A σ] z : R ⊗[Amb A σ] Gr I) = r • ((1 : R) ⊗ₜ[Amb A σ] z) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, grLocEquiv_one_tmul, Algebra.smul_def]

/-- Extensionality for ring maps out of `gr_{I·R}(R)`: it is generated by the image of `R` and
the image of `gr_I(P)`. -/
theorem grLoc_ringHom_ext {T : Type u} [CommSemiring T] {f g : GrLoc R I →+* T}
    (h0 : ∀ r : R, f (algebraMap R (GrLoc R I) r) = g (algebraMap R (GrLoc R I) r))
    (h1 : ∀ z : Gr I, f (grLocMap R I z) = g (grLocMap R I z)) : f = g := by
  refine RingHom.ext fun w ↦ ?_
  obtain ⟨u, rfl⟩ := (grLocEquiv R I).surjective w
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul r z => rw [grLocEquiv_tmul, map_mul, map_mul, h0, h1]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The translation coaction on the normal cone of a flat ambient extension.**  It is the
unique `R`-algebra map extending `ConeTranslation.coaction`. -/
def locCoaction : GrLoc R I →ₐ[R] MvPolynomial σ (GrLoc R I) :=
  (AlgHom.liftEquiv (Amb A σ) R (Gr I) (MvPolynomial σ (GrLoc R I))
    (locCoactionAux R I)).comp (grLocEquiv R I).symm.toAlgHom

theorem locCoaction_grLocMap (z : Gr I) :
    locCoaction R I (grLocMap R I z) = MvPolynomial.map (grLocMap R I) (coaction I z) := by
  have h : (grLocEquiv R I).symm (grLocMap R I z) = (1 : R) ⊗ₜ[Amb A σ] z := by
    rw [AlgEquiv.symm_apply_eq, grLocEquiv_one_tmul]
  change AlgHom.liftEquiv (Amb A σ) R (Gr I) (MvPolynomial σ (GrLoc R I))
    (locCoactionAux R I) ((grLocEquiv R I).symm (grLocMap R I z)) = _
  rw [h, AlgHom.liftEquiv_tmul, one_smul, locCoactionAux_apply]

theorem locCoaction_algebraMap (r : R) :
    locCoaction R I (algebraMap R (GrLoc R I) r) =
      MvPolynomial.C (algebraMap R (GrLoc R I) r) := by
  rw [AlgHom.commutes, MvPolynomial.algebraMap_apply]

/-! ### The action on points -/

variable {R I}

/-- Translating a `B`-point of the normal cone by a tangent vector `v : σ → B`. -/
def locTranslatePoint {B : Type u} [CommRing B] (φ : GrLoc R I →+* B) (v : σ → B) :
    GrLoc R I →+* B :=
  (MvPolynomial.eval₂Hom φ v).comp (locCoaction R I).toRingHom

theorem locTranslatePoint_algebraMap {B : Type u} [CommRing B] (φ : GrLoc R I →+* B)
    (v : σ → B) (r : R) :
    locTranslatePoint φ v (algebraMap R (GrLoc R I) r) = φ (algebraMap R (GrLoc R I) r) := by
  change MvPolynomial.eval₂Hom φ v (locCoaction R I (algebraMap R (GrLoc R I) r)) = _
  rw [locCoaction_algebraMap, MvPolynomial.eval₂Hom_C]

/-- **Compatibility of the two translation actions**: the map `gr_I(P) → gr_{I·R}(R)` is
equivariant for the translation action of `σ → B`. -/
theorem locTranslatePoint_grLocMap {B : Type u} [CommRing B] (φ : GrLoc R I →+* B) (v : σ → B)
    (z : Gr I) :
    locTranslatePoint φ v (grLocMap R I z) = translatePoint I (φ.comp (grLocMap R I)) v z := by
  change MvPolynomial.eval₂Hom φ v (locCoaction R I (grLocMap R I z)) = _
  rw [locCoaction_grLocMap, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  rfl

theorem locTranslatePoint_comp_grLocMap {B : Type u} [CommRing B] (φ : GrLoc R I →+* B)
    (v : σ → B) :
    (locTranslatePoint φ v).comp (grLocMap R I) = translatePoint I (φ.comp (grLocMap R I)) v :=
  RingHom.ext fun z ↦ locTranslatePoint_grLocMap φ v z

/-- Translating by the zero tangent vector does nothing. -/
theorem locTranslatePoint_zero {B : Type u} [CommRing B] (φ : GrLoc R I →+* B) :
    locTranslatePoint φ 0 = φ := by
  refine grLoc_ringHom_ext R I (fun r ↦ locTranslatePoint_algebraMap φ 0 r) fun z ↦ ?_
  rw [locTranslatePoint_grLocMap, translatePoint_zero]
  rfl

/-- Translating twice is translating by the sum: the `B`-points of `T_M|_U` act on the `B`-points
of the normal cone. -/
theorem locTranslatePoint_add {B : Type u} [CommRing B] (φ : GrLoc R I →+* B) (v w : σ → B) :
    locTranslatePoint (locTranslatePoint φ v) w = locTranslatePoint φ (v + w) := by
  refine grLoc_ringHom_ext R I (fun r ↦ ?_) fun z ↦ ?_
  · rw [locTranslatePoint_algebraMap, locTranslatePoint_algebraMap, locTranslatePoint_algebraMap]
  · rw [locTranslatePoint_grLocMap, locTranslatePoint_grLocMap, locTranslatePoint_comp_grLocMap,
      translatePoint_add]

variable (R I)

/-- The counit law: evaluating the tangent coordinates at `0` recovers the identity. -/
theorem locCoaction_counit :
    (MvPolynomial.eval₂Hom (RingHom.id (GrLoc R I)) fun _ : σ ↦ (0 : GrLoc R I)).comp
      (locCoaction R I).toRingHom = RingHom.id (GrLoc R I) :=
  locTranslatePoint_zero (RingHom.id (GrLoc R I))

/-- Coassociativity: translating by `ε` and then by `ε'` is translating by `ε + ε'`. -/
theorem locCoaction_coassoc :
    (MvPolynomial.map (locCoaction R I).toRingHom).comp (locCoaction R I).toRingHom =
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun i : σ ↦
        MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (GrLoc R I)) + MvPolynomial.X i).comp
          (locCoaction R I).toRingHom := by
  have hC : MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
      (fun i : σ ↦ MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (GrLoc R I))) =
      (MvPolynomial.C : MvPolynomial σ (GrLoc R I) →+*
        MvPolynomial σ (MvPolynomial σ (GrLoc R I))) :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by simp)
  have h := locTranslatePoint_add (R := R) (I := I)
    (B := MvPolynomial σ (MvPolynomial σ (GrLoc R I)))
    ((MvPolynomial.C : MvPolynomial σ (GrLoc R I) →+*
        MvPolynomial σ (MvPolynomial σ (GrLoc R I))).comp
      (MvPolynomial.C : GrLoc R I →+* MvPolynomial σ (GrLoc R I)))
    (fun i : σ ↦ MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (GrLoc R I)))
    (fun i : σ ↦ MvPolynomial.X i)
  unfold locTranslatePoint at h
  rw [hC, show ((fun i : σ ↦ MvPolynomial.C (MvPolynomial.X i : MvPolynomial σ (GrLoc R I))) +
    fun i ↦ MvPolynomial.X i) = fun i ↦ MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i from
    rfl] at h
  have hmap : MvPolynomial.map (σ := σ) (locCoaction R I).toRingHom =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (locCoaction R I).toRingHom)
        fun i ↦ MvPolynomial.X i :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by simp)
  rw [hmap]
  exact h

/-! ### The normal sheaf and Vistoli's lemma after base change -/

section NormalSheaf

/-- The coordinate ring `Sym_R(I·R)/(I·R)·Sym_R(I·R)` of the normal sheaf of
`Spec (R/I·R) ⊆ Spec R`. -/
abbrev NsLoc : Type u := normalSheafRing R (locIdeal R I)

/-- Shortcut instance: the normal-sheaf coordinate ring is a commutative ring. -/
instance instCommRingNsLoc : CommRing (NsLoc R I) := Ideal.Quotient.commRing _

/-- Shortcut instance for the tangent polynomial ring over the normal sheaf. -/
instance instCommRingPolyNsLoc : CommRing (MvPolynomial σ (NsLoc R I)) :=
  AddMonoidAlgebra.commRing

/-- The canonical map of normal-sheaf coordinate rings induced by `P → R`. -/
def nsLocMap : Ns I →+* NsLoc R I :=
  nsMapOfEq I (algebraMap (Amb A σ) R) (locIdeal R I) rfl

omit [Module.Flat (Amb A σ) R] in
/-- The map of normal-sheaf coordinate rings is compatible with the structure maps. -/
@[simp]
theorem nsLocMap_algebraMap (r : Amb A σ) :
    nsLocMap R I (algebraMap (Amb A σ) (Ns I) r) =
      algebraMap R (NsLoc R I) (algebraMap (Amb A σ) R r) :=
  nsMapOfEq_algebraMap I _ _ rfl r

/-- Flat base change of the normal sheaf: `Ns_{I·R}(R) ≅ R ⊗_P Ns_I(P)`. -/
def nsLocEquiv : R ⊗[Amb A σ] Ns I ≃ₐ[R] NsLoc R I :=
  nsTensorEquiv I (locIdeal R I) rfl

/-- The base-change isomorphism restricted along `Ns_I(P) → Ns_{I·R}(R)`. -/
@[simp]
theorem nsLocEquiv_one_tmul (z : Ns I) :
    nsLocEquiv R I ((1 : R) ⊗ₜ[Amb A σ] z) = nsLocMap R I z :=
  nsTensorEquiv_one_tmul I (locIdeal R I) rfl z

/-- The base-change isomorphism on a general elementary tensor. -/
theorem nsLocEquiv_tmul (r : R) (z : Ns I) :
    nsLocEquiv R I (r ⊗ₜ[Amb A σ] z) = algebraMap R (NsLoc R I) r * nsLocMap R I z := by
  have h : (r ⊗ₜ[Amb A σ] z : R ⊗[Amb A σ] Ns I) = r • ((1 : R) ⊗ₜ[Amb A σ] z) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, nsLocEquiv_one_tmul, Algebra.smul_def]

/-- Extensionality for ring maps out of the base-changed normal sheaf. -/
theorem nsLoc_ringHom_ext {T : Type u} [CommSemiring T] {f g : NsLoc R I →+* T}
    (h0 : ∀ r : R, f (algebraMap R (NsLoc R I) r) = g (algebraMap R (NsLoc R I) r))
    (h1 : ∀ z : Ns I, f (nsLocMap R I z) = g (nsLocMap R I z)) : f = g := by
  refine RingHom.ext fun w ↦ ?_
  obtain ⟨u, rfl⟩ := (nsLocEquiv R I).surjective w
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul r z => rw [nsLocEquiv_tmul, map_mul, map_mul, h0, h1]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The composite `Ns_I(P) → Ns_I(P)[ε_σ] → Ns_{I·R}(R)[ε_σ]`, a `P`-algebra map. -/
def locNsCoactionAux : Ns I →ₐ[Amb A σ] MvPolynomial σ (NsLoc R I) where
  toRingHom := (MvPolynomial.map (nsLocMap R I)).comp (nsCoaction I).toRingHom
  commutes' r := by
    change MvPolynomial.map (nsLocMap R I) (nsCoaction I (algebraMap _ _ r)) = _
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, MvPolynomial.map_C,
      nsLocMap_algebraMap, MvPolynomial.algebraMap_apply,
      IsScalarTower.algebraMap_apply (Amb A σ) R (NsLoc R I)]

omit [Module.Flat (Amb A σ) R] in
/-- Unfolding of the auxiliary normal-sheaf map. -/
theorem locNsCoactionAux_apply (z : Ns I) :
    locNsCoactionAux R I z = MvPolynomial.map (nsLocMap R I) (nsCoaction I z) := rfl

/-- **The translation coaction on the normal sheaf of a flat ambient extension**, the derivative
of the translation action of `T_M|_U` on `N_{U/M'}`. -/
def locNsCoaction : NsLoc R I →ₐ[R] MvPolynomial σ (NsLoc R I) :=
  (AlgHom.liftEquiv (Amb A σ) R (Ns I) (MvPolynomial σ (NsLoc R I))
    (locNsCoactionAux R I)).comp (nsLocEquiv R I).symm.toAlgHom

/-- The normal-sheaf coaction extends the polynomial-model one. -/
theorem locNsCoaction_nsLocMap (z : Ns I) :
    locNsCoaction R I (nsLocMap R I z) = MvPolynomial.map (nsLocMap R I) (nsCoaction I z) := by
  have h : (nsLocEquiv R I).symm (nsLocMap R I z) = (1 : R) ⊗ₜ[Amb A σ] z := by
    rw [AlgEquiv.symm_apply_eq, nsLocEquiv_one_tmul]
  change AlgHom.liftEquiv (Amb A σ) R (Ns I) (MvPolynomial σ (NsLoc R I))
    (locNsCoactionAux R I) ((nsLocEquiv R I).symm (nsLocMap R I z)) = _
  rw [h, AlgHom.liftEquiv_tmul, one_smul, locNsCoactionAux_apply]

/-- The normal-sheaf coaction is the identity in degree zero. -/
theorem locNsCoaction_algebraMap (r : R) :
    locNsCoaction R I (algebraMap R (NsLoc R I) r) =
      MvPolynomial.C (algebraMap R (NsLoc R I) r) := by
  rw [AlgHom.commutes, MvPolynomial.algebraMap_apply]

omit [Module.Flat (Amb A σ) R] in
/-- The comparison `nsToGr` intertwines the two base-change maps. -/
theorem nsToGr_nsLocMap (z : Ns I) :
    nsToGr R (locIdeal R I) (nsLocMap R I z) = grLocMap R I (nsToGr (Amb A σ) I z) :=
  RingHom.congr_fun (nsToGr_naturality I (algebraMap (Amb A σ) R) (locIdeal R I) rfl) z

/-- **Vistoli's lemma over a flat ambient extension.**  The closed immersion
`C_{U/M'} ↪ N_{U/M'}` is equivariant for the tangent translation: the coaction on the normal cone
is compatible with the translation coaction on the normal sheaf through the surjection
`Sym((I·R)/(I·R)²) ↠ gr_{I·R}(R)`. -/
theorem locCoaction_comp_nsToGr :
    (locCoaction R I).comp (nsToGr R (locIdeal R I)) =
      (MvPolynomial.mapAlgHom (nsToGr R (locIdeal R I))).comp (locNsCoaction R I) := by
  have key : ((locCoaction R I).comp (nsToGr R (locIdeal R I))).toRingHom =
      ((MvPolynomial.mapAlgHom (nsToGr R (locIdeal R I))).comp
        (locNsCoaction R I)).toRingHom := by
    refine nsLoc_ringHom_ext R I (fun r ↦ ?_) fun z ↦ ?_
    · change locCoaction R I (nsToGr R (locIdeal R I) (algebraMap R (NsLoc R I) r)) =
        MvPolynomial.mapAlgHom (nsToGr R (locIdeal R I))
          (locNsCoaction R I (algebraMap R (NsLoc R I) r))
      rw [AlgHom.commutes, locCoaction_algebraMap, locNsCoaction_algebraMap,
        MvPolynomial.mapAlgHom_apply, MvPolynomial.map_C, AlgHom.coe_toRingHom, AlgHom.commutes]
    · change locCoaction R I (nsToGr R (locIdeal R I) (nsLocMap R I z)) =
        MvPolynomial.mapAlgHom (nsToGr R (locIdeal R I)) (locNsCoaction R I (nsLocMap R I z))
      rw [nsToGr_nsLocMap, locCoaction_grLocMap, locNsCoaction_nsLocMap,
        MvPolynomial.mapAlgHom_apply, MvPolynomial.map_map]
      have h := RingHom.congr_fun
        (congrArg AlgHom.toRingHom (coaction_comp_nsToGr I)) z
      change coaction I (nsToGr (Amb A σ) I z) =
        MvPolynomial.mapAlgHom (nsToGr (Amb A σ) I) (nsCoaction I z) at h
      rw [h, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_map]
      refine congrArg (fun ψ ↦ MvPolynomial.map ψ (nsCoaction I z)) ?_
      exact (nsToGr_naturality I (algebraMap (Amb A σ) R) (locIdeal R I) rfl).symm
  exact AlgHom.ext fun z ↦ RingHom.congr_fun key z

/-- Translating a `B`-point of the normal sheaf of the flat ambient extension. -/
def locNsTranslatePoint {B : Type u} [CommRing B] (φ : NsLoc R I →+* B) (v : σ → B) :
    NsLoc R I →+* B :=
  (MvPolynomial.eval₂Hom φ v).comp (locNsCoaction R I).toRingHom

/-- On `B`-points: translating a point of the cone, viewed in the normal sheaf, is translating it
in the normal sheaf. -/
theorem locNsTranslatePoint_comp_nsToGr {B : Type u} [CommRing B] (φ : GrLoc R I →+* B)
    (v : σ → B) :
    locNsTranslatePoint R I (φ.comp (nsToGr R (locIdeal R I)).toRingHom) v =
      (locTranslatePoint φ v).comp (nsToGr R (locIdeal R I)).toRingHom := by
  have h : (locCoaction R I).toRingHom.comp (nsToGr R (locIdeal R I)).toRingHom =
      (MvPolynomial.mapAlgHom (nsToGr R (locIdeal R I))).toRingHom.comp
        (locNsCoaction R I).toRingHom :=
    congrArg AlgHom.toRingHom (locCoaction_comp_nsToGr R I)
  rw [locNsTranslatePoint, locTranslatePoint, RingHom.comp_assoc, h, ← RingHom.comp_assoc]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp
  · simp

end NormalSheaf

/-! ### Localisation invariance of the quotient groupoid `[C/T](B)` -/

section Points

open CategoryTheory

/-- The `B`-points of `[C_{U/M'} / T_{M'}|_U]` for the flat ambient extension `M' = Spec R`:
the action groupoid of the translation action on the `R`-algebra points of `gr_{I·R}(R)`. -/
@[ext]
structure LocConeGroupoid (B : Type u) [CommRing B] [Algebra R B] where
  /-- The underlying `R`-algebra point of the affine normal cone. -/
  point : GrLoc R I →ₐ[R] B

namespace LocConeGroupoid

variable {R I} {B : Type u} [CommRing B] [Algebra R B]

/-- An arrow of the action groupoid: a `B`-point of the tangent bundle carrying the source to the
target. -/
@[ext]
structure Hom (x y : LocConeGroupoid R I B) where
  /-- The translating tangent vector. -/
  val : σ → B
  /-- It carries the source point to the target point. -/
  translate_eq : locTranslatePoint x.point.toRingHom val = y.point.toRingHom

/-- The action groupoid structure on the `B`-points of `[C_{U/M'}/T_{M'}|_U]`. -/
instance instCategory : Category (LocConeGroupoid R I B) where
  Hom := Hom
  id x := ⟨0, locTranslatePoint_zero _⟩
  comp f g := ⟨f.val + g.val, by
    rw [← locTranslatePoint_add, f.translate_eq, g.translate_eq]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

/-- The identity arrow translates by the zero tangent vector. -/
@[simp] theorem id_val (x : LocConeGroupoid R I B) : (𝟙 x : x ⟶ x).val = 0 := rfl

/-- Composition of arrows adds the tangent vectors. -/
@[simp] theorem comp_val {x y z : LocConeGroupoid R I B} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val := rfl

/-- Every arrow of the action groupoid is invertible. -/
instance instGroupoid : Groupoid (LocConeGroupoid R I B) where
  inv f := ⟨-f.val, by
    rw [← f.translate_eq, locTranslatePoint_add, add_neg_cancel, locTranslatePoint_zero]⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

/-- The arrow induced by an equality of objects translates by zero. -/
theorem eqToHom_val {x y : LocConeGroupoid R I B} (e : x = y) : (eqToHom e).val = 0 := by
  subst e; rfl

end LocConeGroupoid

variable (B : Type u) [CommRing B] [Algebra (Amb A σ) B] [Algebra R B]
  [IsScalarTower (Amb A σ) R B]

/-- **The `B`-points of the two normal cones agree.**  For an `R`-algebra `B`, restriction along
`gr_I(P) → gr_{I·R}(R)` is a bijection from the `R`-algebra points of `gr_{I·R}(R)` onto the
`P`-algebra points of `gr_I(P)`.  This is the base-change adjunction for `gr_{I·R}(R) =
R ⊗_P gr_I(P)`. -/
def pointEquiv : (GrLoc R I →ₐ[R] B) ≃ (Gr I →ₐ[Amb A σ] B) :=
  ((grLocEquiv R I).arrowCongr (AlgEquiv.refl (A₁ := B))).symm.trans
    (AlgHom.liftEquiv (Amb A σ) R (Gr I) B).symm

variable {B}

/-- The bijection of points is restriction along `gr_I(P) → gr_{I·R}(R)`. -/
@[simp]
theorem pointEquiv_apply (φ : GrLoc R I →ₐ[R] B) (z : Gr I) :
    pointEquiv R I B φ z = φ (grLocMap R I z) := by
  have h : pointEquiv R I B φ z = φ (grLocEquiv R I ((1 : R) ⊗ₜ[Amb A σ] z)) := rfl
  rw [h, grLocEquiv_one_tmul]

/-- Ring-map form of `pointEquiv_apply`. -/
theorem pointEquiv_toRingHom (φ : GrLoc R I →ₐ[R] B) :
    (pointEquiv R I B φ).toRingHom = φ.toRingHom.comp (grLocMap R I) :=
  RingHom.ext fun z ↦ pointEquiv_apply R I φ z

/-- **The bijection of points intertwines the two translation actions.**  Together with
`pointEquiv` this is the localisation invariance of the action groupoid `[C/T](B)`. -/
theorem locTranslatePoint_iff (φ φ' : GrLoc R I →ₐ[R] B) (v : σ → B) :
    locTranslatePoint φ.toRingHom v = φ'.toRingHom ↔
      translatePoint I (pointEquiv R I B φ).toRingHom v = (pointEquiv R I B φ').toRingHom := by
  constructor
  · intro h
    rw [pointEquiv_toRingHom, pointEquiv_toRingHom, ← locTranslatePoint_comp_grLocMap, h]
  · intro h
    refine grLoc_ringHom_ext R I (fun r ↦ ?_) fun z ↦ ?_
    · rw [locTranslatePoint_algebraMap]
      change φ (algebraMap R (GrLoc R I) r) = φ' (algebraMap R (GrLoc R I) r)
      rw [AlgHom.commutes, AlgHom.commutes]
    · rw [locTranslatePoint_grLocMap, ← pointEquiv_toRingHom, RingHom.congr_fun h z,
        pointEquiv_toRingHom]
      rfl

variable (B)

/-- The comparison functor from the quotient groupoid of the flat ambient extension to the
`P`-algebra points of the polynomial-model quotient groupoid. -/
def locConeFunctor : LocConeGroupoid R I B ⥤ AlgConeGroupoid I B where
  obj x := ⟨pointEquiv R I B x.point⟩
  map f := ⟨f.val, (locTranslatePoint_iff R I _ _ _).mp f.translate_eq⟩
  map_id _ := AlgConeGroupoid.Hom.ext rfl
  map_comp _ _ := AlgConeGroupoid.Hom.ext rfl

/-- The comparison functor is faithful. -/
instance instFaithfulLocConeFunctor : (locConeFunctor R I B).Faithful where
  map_injective h := LocConeGroupoid.Hom.ext (congrArg AlgConeGroupoid.Hom.val h)

/-- The comparison functor is full. -/
instance instFullLocConeFunctor : (locConeFunctor R I B).Full where
  map_surjective g := ⟨⟨g.val, (locTranslatePoint_iff R I _ _ _).mpr g.translate_eq⟩, rfl⟩

/-- The comparison functor is essentially surjective, by `pointEquiv`. -/
instance instEssSurjLocConeFunctor : (locConeFunctor R I B).EssSurj where
  mem_essImage y := ⟨⟨(pointEquiv R I B).symm y.point⟩, ⟨eqToIso (AlgConeGroupoid.ext
    ((pointEquiv R I B).apply_symm_apply y.point))⟩⟩

/-- The comparison functor is an equivalence. -/
instance instIsEquivalenceLocConeFunctor : (locConeFunctor R I B).IsEquivalence where

/-- **Localisation invariance of `[C/T](B)`.**  For every `R`-algebra `B` the action groupoid of
the translation action on the `B`-points of the affine normal cone of `Spec(R/I·R) ⊆ Spec R` is
equivalent to the `P`-algebra points of the polynomial-model action groupoid `[C_{U/M}/T_M|_U]`
of `Cones/RefinementQuotient.lean`.  Combined with `toConeGroupoid` (fully faithful, with
essential image `exists_obj_eq_iff`) this says that passing to a flat — in particular an open —
subchart of `𝔸^σ` does not change the quotient groupoid. -/
def locConeEquivalence : LocConeGroupoid R I B ≌ AlgConeGroupoid I B :=
  (locConeFunctor R I B).asEquivalence

/-- The composite comparison to the polynomial-model groupoid is restriction along
`gr_I(P) → gr_{I·R}(R)`. -/
theorem locConeFunctor_comp_toConeGroupoid_obj (x : LocConeGroupoid R I B) :
    ((locConeFunctor R I B ⋙ toConeGroupoid I B).obj x).point =
      x.point.toRingHom.comp (grLocMap R I) :=
  pointEquiv_toRingHom R I x.point

end Points

end Flat

/-! ### Uniqueness of the extended coaction -/

section Uniqueness

variable [Module.Flat (Amb A σ) R]

/-- The coaction of a flat ambient extension is the *unique* `R`-algebra map extending the
polynomial-model coaction.  (This is the algebraic counterpart of the uniqueness of the Taylor
lifts `τ_N` along the nilpotent thickenings `R[ε]/(ε)^N → R`.) -/
theorem locCoaction_unique (f : GrLoc R I →ₐ[R] MvPolynomial σ (GrLoc R I))
    (hf : ∀ z : Gr I, f (grLocMap R I z) = MvPolynomial.map (grLocMap R I) (coaction I z)) :
    f = locCoaction R I := by
  refine AlgHom.ext fun w ↦ RingHom.congr_fun (grLoc_ringHom_ext R I (fun r ↦ ?_)
    (fun z ↦ ?_)) w
  · change f (algebraMap R (GrLoc R I) r) = locCoaction R I (algebraMap R (GrLoc R I) r)
    rw [AlgHom.commutes, AlgHom.commutes]
  · change f (grLocMap R I z) = locCoaction R I (grLocMap R I z)
    rw [hf, locCoaction_grLocMap]

end Uniqueness

/-! ### Localisations of affine space, and étale charts -/

section Charts

/-- A localisation of the polynomial ring is flat over it, so every result of this file applies
to the open charts `D(f) = Spec (A[x]_f) ⊆ 𝔸^σ` and, more generally, to `Spec (S⁻¹A[x])`. -/
theorem flat_of_isLocalization (Sm : Submonoid (Amb A σ)) [IsLocalization Sm R] :
    Module.Flat (Amb A σ) R :=
  IsLocalization.flat R Sm

/-- The standard open chart `D(f)` of affine space is flat over affine space. -/
theorem flat_of_isLocalizationAway (f : Amb A σ) [IsLocalization.Away f R] :
    Module.Flat (Amb A σ) R :=
  IsLocalization.flat R (Submonoid.powers f)

/-- **Every ideal of a localisation of the polynomial ring is extended.**  Consequently the
constructions above describe the affine normal cone of an *arbitrary* closed subscheme of the
open chart `Spec R`, not only of the extended ones. -/
theorem locIdeal_comap (Sm : Submonoid (Amb A σ)) [IsLocalization Sm R] (J : Ideal R) :
    locIdeal R (J.comap (algebraMap (Amb A σ) R)) = J :=
  IsLocalization.map_under (S := R) Sm J

/-- An algebra which is étale over affine space — in particular a standard étale chart of a
scheme smooth over `A` — is flat over it, so the whole coaction package of this file applies to
étale ambient charts.  This is the (finitely presented) case of "formally étale over `𝔸^σ`". -/
theorem flat_of_etale [Algebra.Etale (Amb A σ) R] : Module.Flat (Amb A σ) R :=
  inferInstance

/-- An algebra smooth over affine space is flat over it. -/
theorem flat_of_smooth [Algebra.Smooth (Amb A σ) R] : Module.Flat (Amb A σ) R :=
  inferInstance

end Charts


end

end ConeLocalisation

end GromovWitten.AlgebraicGeometry
