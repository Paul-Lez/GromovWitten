/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.Quotient
import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackClassifying
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The affine cone quotient `[C/E]` as a torsor prestack

Let `C = Spec S` be an affine cone over `Spec R` equipped with an action of the vector bundle
`E = Spec Sym(F)` in the sense of `GromovWitten.AlgebraicGeometry.ConeQuotient.ConeAction`, and
assume that `F` is a *free* `R`-module with a chosen basis indexed by `σ`.  This file compares
the algebra-points quotient groupoid `QuotientGroupoid A B = [C/E](B)` of
`GromovWitten.AlgebraicGeometry.Cones.Quotient` with the torsor groupoid
`ActionTorsor G U (Spec B)` of `GromovWitten.AlgebraicGeometry.Stacks.QuotientStack`.

## The group algebraic space

The repository's `AlgebraicSpaceGroup` is an *absolute* group object in fppf sheaves on all
schemes, so it cannot be the relative group scheme `E = 𝔸^σ_R` over `Spec R`: the addition
`E ×_{Spec R} E → E` is not defined on the absolute product `E × E`, and for a general `R` there
is no unit section `Spec ℤ → E`.  We therefore use the `ℤ`-model `𝔾ₐ^σ = Spec ℤ[xᵢ]`
(`bundleScheme σ`), whose `B`-points are `σ → B = Hom_R(F, B)` for every `R`-algebra `B`, and
which acts on `C` through the same coaction; over `Spec R` it base changes to `E`.

## Main definitions and results

* `vectorBundleGroup σ : AlgebraicSpaceGroup`: the bundle as a group algebraic space.  Its group
  structure is obtained from the representable presheaf of groups `X ↦ (σ → Γ(X, ⊤))`
  (`coordGrp`, `coordGrpRepresentableBy`), so the group axioms are proved, not assumed.
* `actOn`, `actOn_zero`, `actOn_add`: the action of a vector on a ring-valued point of the cone,
  with its unit and associativity laws deduced from the `ConeAction` axioms; over an `R`-algebra
  it is the repository's `translate` (`actOn_eq_translate`).
* `coneActionSpace A b : AlgebraicSpaceAction (vectorBundleGroup σ)`: the cone as an algebraic
  space acted on by the bundle, via the scheme-level action `actScheme` and the transport
  `modObjObj` of module objects along a monoidal functor.
* `trivialWithPoint t`: the trivial torsor with the equivariant map `(e, s) ↦ e · t(s)`;
  `trivialHomEquiv`: morphisms of such trivial torsors are exactly the translations by
  `T`-points of `G` carrying one point of `U` to the other (`eq_translationMap`).
* `trivialTorsorFunctor A b : QuotientGroupoid A B ⥤ ActionTorsor ...`, together with instances
  `Full` and `Faithful` and `trivialTorsorFunctorFullyFaithful`.
* `trivialTorsorFunctorNaturality`: object-level naturality in the test algebra, comparing
  `QuotientGroupoid.mapQuotient` with `ActionTorsor.pullbackFunctor`.
* `isoTrivialOfSection`: a torsor with a global section is isomorphic to a trivial one (proved
  from `principal_isIso`), and `essSurj_trivialTorsorFunctor`: essential surjectivity under the
  explicit hypotheses `AllTorsorsTrivial` (every torsor over `Spec B` has a section, i.e. the
  vanishing of `H¹(Spec B, E)`, which is *not* proved here) and that the point of the cone
  obtained from a section is an `R`-algebra point.

## What is not done here

The full pseudofunctor coherence of the naturality isomorphism is not established, and neither
is the triviality of all `E`-torsors over an affine base.
-/

universe u

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

namespace ConeQuotient

/-! ### Points of affine schemes -/

section Points

variable {B : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- The ring map attached to a morphism from a scheme into an affine scheme. -/
noncomputable def pt (f : X ⟶ Spec B) : B ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ f.appTop

/-- Taking the ring map of a point is contravariantly functorial. -/
theorem pt_comp (g : Y ⟶ X) (f : X ⟶ Spec B) : pt (g ≫ f) = pt f ≫ g.appTop := by
  rw [pt, pt, _root_.AlgebraicGeometry.Scheme.Hom.comp_appTop, Category.assoc]

/-- Morphisms into an affine scheme are exactly ring maps out of its coordinate ring. -/
noncomputable def ptEquiv : (X ⟶ Spec B) ≃ (B ⟶ Γ(X, ⊤)) where
  toFun := pt
  invFun φ := (ΓSpec.adjunction.homEquiv X (Opposite.op B)) φ.op
  left_inv f := by
    obtain ⟨ψ, rfl⟩ := (ΓSpec.adjunction.homEquiv X (Opposite.op B)).surjective f
    have h : pt ((ΓSpec.adjunction.homEquiv X (Opposite.op B)) ψ) = ψ.unop :=
      _root_.AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := X) ψ.unop
    change (ΓSpec.adjunction.homEquiv X (Opposite.op B)) (pt _).op = _
    rw [h]
    rfl
  right_inv φ := _root_.AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

/-- The equivalence with ring maps is given by `pt`. -/
@[simp]
theorem ptEquiv_apply (f : X ⟶ Spec B) : ptEquiv f = pt f := rfl

/-- The ring map of the point attached to a ring map is that ring map. -/
@[simp]
theorem pt_ptEquiv_symm (φ : B ⟶ Γ(X, ⊤)) : pt (ptEquiv.symm φ) = φ :=
  ptEquiv.apply_symm_apply φ

/-- A morphism into an affine scheme is determined by its ring map. -/
theorem pt_injective : Function.Injective (pt : (X ⟶ Spec B) → (B ⟶ Γ(X, ⊤))) :=
  ptEquiv.injective

end Points


/-! ### The vector bundle as a group scheme -/

section Bundle

variable (σ : Type u)

/-- The coordinate ring `ℤ[xᵢ]` of the affine space `𝔸^σ` over the integers. -/
noncomputable abbrev intPoly : CommRingCat.{u} := CommRingCat.of (MvPolynomial σ (ULift.{u} ℤ))

/-- The `ℤ`-model `𝔸^σ = Spec ℤ[xᵢ]` of the vector bundle `E = Spec Sym(F)`, for `F` free on
`σ`.  Over any `R`-algebra `B` its points are `σ → B = Hom_R(F, B)`. -/
noncomputable abbrev bundleScheme : Scheme.{u} := Spec (intPoly σ)

variable {σ}

/-- The coordinates of a point of the bundle scheme. -/
noncomputable def coords {X : Scheme.{u}} (f : X ⟶ bundleScheme σ) : σ → Γ(X, ⊤) :=
  AffineSpace.toSpecMvPolyIntEquiv σ f

/-- The point of the bundle scheme with prescribed coordinates. -/
noncomputable def ofCoords {X : Scheme.{u}} (v : σ → Γ(X, ⊤)) : X ⟶ bundleScheme σ :=
  (AffineSpace.toSpecMvPolyIntEquiv σ).symm v

/-- The coordinates of the point with prescribed coordinates. -/
@[simp]
theorem coords_ofCoords {X : Scheme.{u}} (v : σ → Γ(X, ⊤)) : coords (ofCoords v) = v :=
  (AffineSpace.toSpecMvPolyIntEquiv σ).apply_symm_apply v

/-- A point of the bundle scheme is determined by its coordinates. -/
theorem coords_injective {X : Scheme.{u}} :
    Function.Injective (coords : (X ⟶ bundleScheme σ) → (σ → Γ(X, ⊤))) :=
  (AffineSpace.toSpecMvPolyIntEquiv σ).injective

/-- Coordinates are natural in the test scheme. -/
theorem coords_comp {X Y : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ bundleScheme σ) (i : σ) :
    coords (g ≫ f) i = g.appTop (coords f i) :=
  rfl

variable (σ) in
/-- The functor of points of the bundle scheme, as a presheaf of groups: over a scheme `X` it
is the additive group `σ → Γ(X, ⊤)`, written multiplicatively. -/
noncomputable def coordGrp : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u} where
  obj X := GrpCat.of (Multiplicative (σ → Γ(X.unop, ⊤)))
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative
    { toFun := fun v i => f.unop.appTop (v i)
      map_zero' := by ext i; simp
      map_add' := fun v w => by ext i; simp })
  map_id _ := rfl
  map_comp _ _ := rfl

variable (σ) in
/-- The bundle scheme represents its functor of points. -/
noncomputable def coordGrpRepresentableBy :
    ((coordGrp σ) ⋙ forget GrpCat).RepresentableBy (bundleScheme σ) where
  homEquiv := AffineSpace.toSpecMvPolyIntEquiv σ
  homEquiv_comp _ _ := rfl

/-- The bundle scheme is a group scheme: the addition of vectors. -/
noncomputable instance : GrpObj (bundleScheme σ) :=
  GrpObj.ofRepresentableBy _ (coordGrp σ) (coordGrpRepresentableBy σ)

end Bundle


section GroupStructure

open scoped CategoryTheory.MonObj

variable {σ : Type u} {X : Scheme.{u}}

/-- A point of the bundle scheme is recovered from its coordinates. -/
@[simp]
theorem ofCoords_coords (f : X ⟶ bundleScheme σ) : ofCoords (coords f) = f :=
  (AffineSpace.toSpecMvPolyIntEquiv σ).symm_apply_apply f

/-- The multiplication of the bundle group scheme adds the two coordinate vectors. -/
theorem mul_eq_ofCoords :
    (MonObj.mul : bundleScheme σ ⊗ bundleScheme σ ⟶ bundleScheme σ) =
      ofCoords (fun i => coords (fst _ _) i + coords (snd _ _) i) :=
  rfl

/-- The unit of the bundle group scheme is the zero vector. -/
theorem one_eq_ofCoords :
    (MonObj.one : 𝟙_ Scheme.{u} ⟶ bundleScheme σ) = ofCoords 0 :=
  rfl

/-- The inverse of the bundle group scheme negates the coordinate vector. -/
theorem inv_eq_ofCoords :
    (GrpObj.inv : bundleScheme σ ⟶ bundleScheme σ) =
      ofCoords (fun i => -coords (𝟙 (bundleScheme σ)) i) :=
  rfl

/-- On points, the group law of the bundle scheme is the addition of coordinate vectors. -/
@[simp]
theorem coords_mul (f g : X ⟶ bundleScheme σ) (i : σ) :
    coords (f * g) i = coords f i + coords g i := by
  change coords (lift f g ≫ MonObj.mul) i = _
  rw [coords_comp, mul_eq_ofCoords, coords_ofCoords, map_add, ← coords_comp, ← coords_comp,
    lift_fst, lift_snd]

/-- On points, the unit of the bundle scheme is the zero vector. -/
@[simp]
theorem coords_one (i : σ) : coords (1 : X ⟶ bundleScheme σ) i = 0 := by
  change coords (toUnit X ≫ MonObj.one) i = 0
  rw [coords_comp, one_eq_ofCoords, coords_ofCoords]
  exact map_zero _

/-- On points, the inverse of the bundle scheme is the negation of the coordinate vector. -/
@[simp]
theorem coords_inv (f : X ⟶ bundleScheme σ) (i : σ) :
    coords (f⁻¹) i = -coords f i := by
  change coords (f ≫ GrpObj.inv) i = _
  rw [coords_comp, inv_eq_ofCoords, coords_ofCoords, map_neg, ← coords_comp, Category.comp_id]

end GroupStructure


/-! ### The action of the bundle on the cone, on ring-valued points -/

section RingAction

open scoped TensorProduct

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u}
variable (A : ConeAction R S F) (b : Module.Basis σ R F)

/-- The universal translation: the `MvPolynomial σ S`-point of the cone obtained by translating
the tautological point by the vector of variables.  It is the coaction of the coordinate ring of
the cone for the free `R`-module `F` with basis `b`. -/
noncomputable def universalTranslate : S →ₐ[R] MvPolynomial σ S :=
  translate A.act (IsScalarTower.toAlgHom R S (MvPolynomial σ S))
    (b.constr R fun i => MvPolynomial.X i)

variable {B C : Type u} [CommRing B] [CommRing C]

/-- The translate of a ring-valued point `φ` of the cone by the vector `v` of the bundle.  No
`R`-algebra structure on `B` is needed: the structure map is `φ` itself. -/
noncomputable def actOn (φ : S →+* B) (v : σ → B) : S →+* B :=
  (MvPolynomial.eval₂Hom φ v).comp (universalTranslate A b).toRingHom

/-- The translation action on points is natural in the test ring. -/
theorem comp_actOn (g : B →+* C) (φ : S →+* B) (v : σ → B) :
    g.comp (actOn A b φ v) = actOn A b (g.comp φ) fun i => g (v i) := by
  rw [actOn, actOn, ← RingHom.comp_assoc, MvPolynomial.comp_eval₂Hom]

variable [Algebra R B]

/-- Evaluation of a polynomial with coefficients in `S`, as an `R`-algebra map. -/
noncomputable def evalAlgHom (φ : S →ₐ[R] B) (v : σ → B) : MvPolynomial σ S →ₐ[R] B where
  toRingHom := MvPolynomial.eval₂Hom (φ : S →+* B) v
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R S (MvPolynomial σ S)]
    change MvPolynomial.eval₂Hom (φ : S →+* B) v (MvPolynomial.C _) = _
    rw [MvPolynomial.eval₂Hom_C]
    exact φ.commutes r

/-- Evaluation sends a variable to the corresponding entry of the vector. -/
@[simp]
theorem evalAlgHom_X (φ : S →ₐ[R] B) (v : σ → B) (i : σ) :
    evalAlgHom φ v (MvPolynomial.X i) = v i :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- Over a test `R`-algebra, the translation action on points is the action `translate` of the
cone action on the `B`-points of the quotient groupoid. -/
theorem actOn_eq_translate (φ : S →ₐ[R] B) (v : σ → B) :
    actOn A b (φ : S →+* B) v = ((translate A.act φ (b.constr R v) : S →ₐ[R] B) : S →+* B) := by
  have h1 : (evalAlgHom φ v).comp (IsScalarTower.toAlgHom R S (MvPolynomial σ S)) = φ := by
    refine AlgHom.ext fun s => ?_
    exact MvPolynomial.eval₂Hom_C _ _ s
  have h2 : (evalAlgHom φ v).toLinearMap.comp (b.constr R fun i => MvPolynomial.X i) =
      b.constr R v := by
    refine b.ext fun i => ?_
    simp [Module.Basis.constr_basis]
  have key : (evalAlgHom φ v).comp (universalTranslate A b) =
      translate A.act φ (b.constr R v) := by
    rw [universalTranslate, comp_translate, h1, h2]
  exact congrArg (fun f : S →ₐ[R] B => (f : S →+* B)) key

omit [Algebra R B] in
/-- Translating a ring-valued point by the zero vector does nothing. -/
theorem actOn_zero (φ : S →+* B) : actOn A b φ 0 = φ := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have h := actOn_eq_translate A b φ' 0
  rw [show ((φ' : S →+* B)) = φ from rfl] at h
  rw [h, map_zero, A.act_zero]
  rfl

omit [Algebra R B] in
/-- Translating a ring-valued point twice is translating by the sum of the two vectors. -/
theorem actOn_add (φ : S →+* B) (v w : σ → B) :
    actOn A b (actOn A b φ v) w = actOn A b φ (v + w) := by
  let _ : Algebra R B := (φ.comp (algebraMap R S)).toAlgebra
  let φ' : S →ₐ[R] B := { φ with commutes' := fun _ => rfl }
  have hcoe : ((φ' : S →+* B)) = φ := rfl
  have h1 := actOn_eq_translate A b φ' v
  have h2 := actOn_eq_translate A b (translate A.act φ' (b.constr R v)) w
  have h3 := actOn_eq_translate A b φ' (v + w)
  rw [hcoe] at h1 h3
  rw [h1, h2, h3, A.act_add, map_add]

end RingAction

/-! ### The cone as a scheme with an action of the bundle group scheme -/

section SchemeAction

open scoped CategoryTheory.MonObj

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u}

variable (S) in
/-- The affine cone `C = Spec S` as a scheme. -/
noncomputable abbrev coneScheme : Scheme.{u} := Spec (CommRingCat.of S)

/-- The ring map attached to a morphism into the cone. -/
noncomputable def conePt {X : Scheme.{u}} (f : X ⟶ coneScheme S) : S →+* Γ(X, ⊤) :=
  (pt f).hom

/-- The morphism into the cone attached to a ring map. -/
noncomputable def ofConePt {X : Scheme.{u}} (φ : S →+* Γ(X, ⊤)) : X ⟶ coneScheme S :=
  ptEquiv.symm (CommRingCat.ofHom φ)

/-- The ring map of the point attached to a ring map is that ring map. -/
@[simp]
theorem conePt_ofConePt {X : Scheme.{u}} (φ : S →+* Γ(X, ⊤)) : conePt (ofConePt φ) = φ := by
  rw [conePt, ofConePt, pt_ptEquiv_symm]
  rfl

/-- A morphism into the cone is determined by its ring map. -/
theorem conePt_injective {X : Scheme.{u}} :
    Function.Injective (conePt : (X ⟶ coneScheme S) → (S →+* Γ(X, ⊤))) := by
  intro f g h
  refine pt_injective ?_
  exact CommRingCat.hom_ext h

/-- The ring map of a point of the cone is natural in the test scheme. -/
theorem conePt_comp {X Y : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ coneScheme S) :
    conePt (g ≫ f) = (g.appTop).hom.comp (conePt f) := by
  rw [conePt, conePt, pt_comp]
  rfl

variable (A : ConeAction R S F) (b : Module.Basis σ R F)

/-- The action of the bundle group scheme on the cone, as a morphism of schemes. -/
noncomputable def actScheme : bundleScheme σ ⊗ coneScheme S ⟶ coneScheme S :=
  ofConePt (actOn A b (conePt (snd (bundleScheme σ) (coneScheme S)))
    (coords (fst (bundleScheme σ) (coneScheme S))))

/-- The action of the bundle group scheme on the cone, computed on points. -/
theorem conePt_comp_actScheme {X : Scheme.{u}} (h : X ⟶ bundleScheme σ ⊗ coneScheme S) :
    conePt (h ≫ actScheme A b) =
      actOn A b (conePt (h ≫ snd _ _)) (coords (h ≫ fst _ _)) := by
  rw [conePt_comp, actScheme, conePt_ofConePt, comp_actOn, ← conePt_comp]
  rfl

/-- The coordinates of a point of the bundle group scheme composed with the multiplication. -/
theorem coords_comp_mul {X : Scheme.{u}} (h : X ⟶ bundleScheme σ ⊗ bundleScheme σ) (i : σ) :
    coords (h ≫ MonObj.mul) i = coords (h ≫ fst _ _) i + coords (h ≫ snd _ _) i := by
  have hx : h ≫ MonObj.mul = (h ≫ fst _ _) * (h ≫ snd _ _) := by
    change _ = lift (h ≫ fst _ _) (h ≫ snd _ _) ≫ MonObj.mul
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  rw [hx, coords_mul]

/-- The cone is an object with an action of the bundle group scheme. -/
@[instance_reducible]
noncomputable def coneModObj : ModObj (bundleScheme σ) (coneScheme S) where
  smul := actScheme A b
  one_smul := by
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionUnitIso,
      MonoidalCategory.selfLeftAction_actionObj]
    refine conePt_injective ?_
    have hz : coords ((MonObj.one ▷ coneScheme S) ≫ fst (bundleScheme σ) (coneScheme S)) =
        (0 : σ → Γ(𝟙_ Scheme.{u} ⊗ coneScheme S, ⊤)) := by
      funext i
      rw [whiskerRight_fst, coords_comp, one_eq_ofCoords, coords_ofCoords]
      exact map_zero _
    rw [conePt_comp_actScheme, hz, actOn_zero, whiskerRight_snd, leftUnitor_hom]
  mul_smul := by
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionHomRight,
      MonoidalCategory.selfLeftAction_actionAssocIso,
      MonoidalCategory.selfLeftAction_actionObj]
    refine conePt_injective ?_
    rw [← Category.assoc, conePt_comp_actScheme, conePt_comp_actScheme]
    simp only [Category.assoc, whiskerRight_snd, whiskerRight_fst, whiskerLeft_snd,
      whiskerLeft_fst, associator_hom_fst]
    rw [← Category.assoc ((α_ (bundleScheme σ) (bundleScheme σ) (coneScheme S)).hom)
      (snd _ _) (actScheme A b), conePt_comp_actScheme]
    simp only [Category.assoc, associator_hom_snd_snd, associator_hom_snd_fst]
    rw [actOn_add]
    congr 1
    funext i
    rw [coords_comp_mul]
    exact add_comm _ _

end SchemeAction

/-! ### Transport to fppf sheaves: the group algebraic space and its action -/

section Transport

open scoped CategoryTheory.MonObj CategoryTheory.Obj

/-- The fppf Yoneda embedding is a monoidal functor for the cartesian structures. -/
noncomputable instance fppfYonedaMonoidal : fppfYoneda.{u}.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

variable {C D : Type*} [Category C] [CartesianMonoidalCategory C]
  [Category D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

/-- The image of an object with a monoid action under a monoidal functor between cartesian
monoidal categories again carries an action of the image monoid. -/
@[instance_reducible]
noncomputable def modObjObj {M X : C} [MonObj M] [ModObj M X] : ModObj (F.obj M) (F.obj X) where
  smul := Functor.LaxMonoidal.μ F M X ≫ F.map (ModObj.smul (M := M) (X := X))
  one_smul := by
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionUnitIso, MonoidalCategory.selfLeftAction_actionObj]
    have hone : ((MonObj.one : 𝟙_ C ⟶ M) ▷ X ≫ (ModObj.smul (M := M) (X := X))) = (λ_ X).hom := by
      simp
    rw [Functor.obj.η_def, MonoidalCategory.comp_whiskerRight, Category.assoc,
      Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, hone,
      ← Functor.LaxMonoidal.left_unitality]
  mul_smul := by
    simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
      MonoidalCategory.selfLeftAction_actionHomRight,
      MonoidalCategory.selfLeftAction_actionAssocIso,
      MonoidalCategory.selfLeftAction_actionObj]
    have hmul : ((MonObj.mul : M ⊗ M ⟶ M) ▷ X ≫ (ModObj.smul (M := M) (X := X))) =
        (α_ M M X).hom ≫ (M ◁ (ModObj.smul (M := M) (X := X))) ≫ ModObj.smul (M := M) (X := X) := by
      simp
    rw [Functor.obj.μ_def]
    simp_rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      Functor.LaxMonoidal.μ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, hmul]
    simp

end Transport

/-! ### The vector bundle as a group algebraic space -/

section Spaces

open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u}

variable (σ) in
/-- The vector bundle `E = Spec Sym(F)` for `F` free on `σ`, as a group algebraic space: the
`ℤ`-model `𝔸^σ` with its addition.  On the points of any `R`-algebra `B` the group is
`Hom_R(F, B)`. -/
noncomputable def vectorBundleGroup : AlgebraicSpaceGroup.{u} where
  space := AlgebraicSpace.ofScheme.obj (bundleScheme σ)
  group := Functor.grpObjObj (F := fppfYoneda) (G := bundleScheme σ)

/-- The underlying algebraic space of the bundle group is `𝔸^σ`. -/
@[simp]
theorem vectorBundleGroup_space (σ : Type u) :
    (vectorBundleGroup σ).space = AlgebraicSpace.ofScheme.obj (bundleScheme σ) :=
  rfl

/-- The affine cone `C = Spec S` as an algebraic space with an action of the vector bundle. -/
noncomputable def coneActionSpace (A : ConeAction R S F) (b : Module.Basis σ R F) :
    AlgebraicSpaceAction (vectorBundleGroup σ) where
  space := AlgebraicSpace.ofScheme.obj (coneScheme S)
  action :=
    let _ := coneModObj A b
    modObjObj fppfYoneda (M := bundleScheme σ) (X := coneScheme S)

/-- The underlying algebraic space of the cone action is `Spec S`. -/
@[simp]
theorem coneActionSpace_space (A : ConeAction R S F) (b : Module.Basis σ R F) :
    (coneActionSpace A b).space = AlgebraicSpace.ofScheme.obj (coneScheme S) :=
  rfl

end Spaces

/-! ### Cartesian calculus for monoid actions -/

section CartesianCalculus

open scoped CategoryTheory.MonObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- Composing a lift with a left whiskering. -/
@[reassoc]
theorem lift_whiskerLeft {Z X Y Y' : C} (f : Z ⟶ X) (g : Z ⟶ Y) (h : Y ⟶ Y') :
    lift f g ≫ (X ◁ h) = lift f (g ≫ h) := by
  ext <;> simp

/-- Composing a lift with a right whiskering. -/
@[reassoc]
theorem lift_whiskerRight {Z X X' Y : C} (f : Z ⟶ X) (g : Z ⟶ Y) (h : X ⟶ X') :
    lift f g ≫ (h ▷ Y) = lift (f ≫ h) g := by
  ext <;> simp

/-- Composing an iterated lift with the associator. -/
@[reassoc]
theorem lift_associator_hom {Z X Y W : C} (f : Z ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ W) :
    lift (lift f g) h ≫ (α_ X Y W).hom = lift f (lift g h) := by
  ext <;> simp

variable {M X Z : C} [MonObj M] [ModObj M X]

/-- Acting by the unit does nothing, on points. -/
theorem lift_one_smul (p : Z ⟶ X) :
    lift (1 : Z ⟶ M) p ≫ ModObj.smul (M := M) (X := X) = p := by
  have h1 : lift (1 : Z ⟶ M) p = lift (toUnit Z) p ≫ (MonObj.one ▷ X) := by
    rw [lift_whiskerRight]
    rfl
  have h2 : (MonObj.one ▷ X) ≫ ModObj.smul (M := M) (X := X) = (λ_ X).hom := by simp
  rw [h1, Category.assoc, h2, leftUnitor_hom, lift_snd]

/-- Acting by a product is acting twice, on points. -/
theorem lift_mul_smul (a b : Z ⟶ M) (p : Z ⟶ X) :
    lift (a * b) p ≫ ModObj.smul (M := M) (X := X) =
      lift a (lift b p ≫ ModObj.smul (M := M) (X := X)) ≫ ModObj.smul (M := M) (X := X) := by
  have h1 : lift (a * b) p = lift (lift a b) p ≫ (MonObj.mul ▷ X) := by
    rw [lift_whiskerRight]
    rfl
  have h2 : ((MonObj.mul : M ⊗ M ⟶ M) ▷ X) ≫ ModObj.smul (M := M) (X := X) =
      (α_ M M X).hom ≫ (M ◁ ModObj.smul (M := M) (X := X)) ≫
        ModObj.smul (M := M) (X := X) := by simp
  rw [h1, Category.assoc, h2, ← Category.assoc, lift_associator_hom, ← Category.assoc,
    lift_whiskerLeft]

end CartesianCalculus

/-! ### Trivial torsors with an equivariant map -/

section TrivialTorsor

open scoped CategoryTheory.MonObj

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}

variable (G T) in
/-- The unit section of the trivial `G`-torsor over `T`. -/
noncomputable def unitSection :
    fppfYoneda.obj T ⟶ G.space.toSheaf ⊗ fppfYoneda.obj T :=
  lift 1 (𝟙 _)

/-- The first component of the unit section is the unit. -/
@[reassoc (attr := simp)]
theorem unitSection_fst : unitSection G T ≫ fst _ _ = 1 := lift_fst _ _

/-- The unit section is a section of the projection. -/
@[reassoc (attr := simp)]
theorem unitSection_snd : unitSection G T ≫ snd _ _ = 𝟙 _ := lift_snd _ _

/-- Right translation of the trivial `G`-torsor over `T` by a `T`-point of `G`. -/
noncomputable def translationMap (g : fppfYoneda.obj T ⟶ G.space.toSheaf) :
    G.space.toSheaf ⊗ fppfYoneda.obj T ⟶ G.space.toSheaf ⊗ fppfYoneda.obj T :=
  lift (fst _ _ * (snd _ _ ≫ g)) (snd _ _)

/-- The first component of a translation. -/
@[reassoc (attr := simp)]
theorem translationMap_fst (g : fppfYoneda.obj T ⟶ G.space.toSheaf) :
    translationMap g ≫ fst _ _ = fst _ _ * (snd _ _ ≫ g) :=
  lift_fst _ _

/-- A translation lies over the base. -/
@[reassoc (attr := simp)]
theorem translationMap_snd (g : fppfYoneda.obj T ⟶ G.space.toSheaf) :
    translationMap g ≫ snd _ _ = snd _ _ :=
  lift_snd _ _

/-- Whiskering on the left is a lift, in a cartesian monoidal category. -/
theorem whiskerLeft_eq_lift {C : Type*} [Category C] [CartesianMonoidalCategory C]
    (X : C) {Y Y' : C} (f : Y ⟶ Y') : X ◁ f = lift (fst _ _) (snd _ _ ≫ f) := by
  ext <;> simp

/-- Translating by the unit is the identity. -/
theorem translationMap_one :
    translationMap (1 : fppfYoneda.obj T ⟶ G.space.toSheaf) = 𝟙 _ := by
  rw [translationMap, show (snd (G.space.toSheaf) (fppfYoneda.obj T) ≫ 1) = 1 from
    (MonObj.comp_one _), mul_one, lift_fst_snd]

/-- Translations compose by multiplying the translating points. -/
theorem translationMap_comp (g g' : fppfYoneda.obj T ⟶ G.space.toSheaf) :
    translationMap g ≫ translationMap g' = translationMap (g * g') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, translationMap_fst, MonObj.comp_mul, translationMap_fst,
      ← Category.assoc, translationMap_snd, translationMap_fst, MonObj.comp_mul,
      _root_.mul_assoc]
  · rw [Category.assoc, translationMap_snd, translationMap_snd, translationMap_snd]

/-- Right translation of the trivial torsor is an isomorphism. -/
noncomputable def translationIso (g : fppfYoneda.obj T ⟶ G.space.toSheaf) :
    (G.space.toSheaf ⊗ fppfYoneda.obj T) ≅ (G.space.toSheaf ⊗ fppfYoneda.obj T) where
  hom := translationMap g
  inv := translationMap g⁻¹
  hom_inv_id := by rw [translationMap_comp, mul_inv_cancel, translationMap_one]
  inv_hom_id := by rw [translationMap_comp, inv_mul_cancel, translationMap_one]

/-- Right translation is equivariant for the left action of `G` on the trivial torsor. -/
theorem translationMap_equivariant (g : fppfYoneda.obj T ⟶ G.space.toSheaf) :
    FppfTorsor.trivialSmul G T ≫ translationMap g =
      (G.space.toSheaf ◁ translationMap g) ≫ FppfTorsor.trivialSmul G T := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, translationMap_fst, MonObj.comp_mul, FppfTorsor.trivialSmul_fst,
      FppfTorsor.trivialSmul_snd_assoc, Category.assoc, FppfTorsor.trivialSmul_fst,
      MonObj.comp_mul, whiskerLeft_fst, whiskerLeft_snd_assoc, translationMap_fst,
      MonObj.comp_mul, _root_.mul_assoc]
  · rw [Category.assoc, translationMap_snd, FppfTorsor.trivialSmul_snd, Category.assoc,
      FppfTorsor.trivialSmul_snd, whiskerLeft_snd_assoc, translationMap_snd]

/-- The trivial `G`-torsor over `T`, with the equivariant map to `U` determined by a `T`-point
`t` of `U`: on points it is `(e, s) ↦ e · t(s)`. -/
noncomputable def trivialWithPoint (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    ActionTorsor G U T where
  toFppfTorsor := FppfTorsor.trivial G T
  target := (G.space.toSheaf ◁ t) ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)
  target_equivariant := by
    change FppfTorsor.trivialSmul G T ≫ ((G.space.toSheaf ◁ t) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) =
      (G.space.toSheaf ◁ ((G.space.toSheaf ◁ t) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf))) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)
    rw [FppfTorsor.trivialSmul, lift_whiskerLeft_assoc, lift_mul_smul,
      whiskerLeft_eq_lift _ ((G.space.toSheaf ◁ t) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)),
      whiskerLeft_eq_lift _ t, comp_lift_assoc]
    simp only [Category.assoc]

/-- The equivariant map of the trivial torsor attached to a point. -/
@[simp]
theorem trivialWithPoint_target (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (trivialWithPoint t).target =
      (G.space.toSheaf ◁ t) ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) :=
  rfl

/-- The projection of the trivial torsor is the second projection. -/
@[simp]
theorem trivialWithPoint_projection (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (trivialWithPoint t).projection = snd _ _ :=
  rfl

/-- The unit section computes the point of `U` attached to a trivial torsor. -/
theorem unitSection_comp_smul (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    unitSection G T ≫ ((G.space.toSheaf ◁ t) ≫
      ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) = t := by
  rw [whiskerLeft_eq_lift, ← Category.assoc, comp_lift,
    unitSection_fst, unitSection_snd_assoc, lift_one_smul]

/-- The unit section recovers the point of the trivial torsor. -/
theorem unitSection_comp_trivialTarget (t : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    unitSection G T ≫ (trivialWithPoint t).target = t :=
  unitSection_comp_smul t

/-- Every equivariant endomorphism of the trivial torsor over `T` which lies over `T` is the
translation by the `T`-point obtained from the unit section. -/
theorem eq_translationMap {u : G.space.toSheaf ⊗ fppfYoneda.obj T ⟶
      G.space.toSheaf ⊗ fppfYoneda.obj T} (hover : u ≫ snd _ _ = snd _ _)
    (hequiv : FppfTorsor.trivialSmul G T ≫ u =
      (G.space.toSheaf ◁ u) ≫ FppfTorsor.trivialSmul G T) :
    u = translationMap (unitSection G T ≫ u ≫ fst _ _) := by
  have hk : lift (fst G.space.toSheaf (fppfYoneda.obj T))
      (snd _ _ ≫ unitSection G T) ≫ FppfTorsor.trivialSmul G T = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, FppfTorsor.trivialSmul_fst, MonObj.comp_mul, lift_fst,
        lift_snd_assoc, Category.assoc, unitSection_fst, MonObj.comp_one, mul_one,
        Category.id_comp]
    · rw [Category.assoc, FppfTorsor.trivialSmul_snd, lift_snd_assoc, Category.assoc,
        unitSection_snd, Category.comp_id, Category.id_comp]
  calc u = (lift (fst _ _) (snd _ _ ≫ unitSection G T) ≫ FppfTorsor.trivialSmul G T) ≫ u := by
        rw [hk, Category.id_comp]
    _ = lift (fst _ _) (snd _ _ ≫ unitSection G T) ≫
          ((G.space.toSheaf ◁ u) ≫ FppfTorsor.trivialSmul G T) := by
        rw [Category.assoc, hequiv]
    _ = translationMap (unitSection G T ≫ u ≫ fst _ _) := by
        rw [← Category.assoc, lift_whiskerLeft]
        apply CartesianMonoidalCategory.hom_ext
        · rw [Category.assoc, FppfTorsor.trivialSmul_fst, MonObj.comp_mul, lift_fst,
            lift_snd_assoc, translationMap_fst]
          simp only [Category.assoc]
        · rw [Category.assoc, FppfTorsor.trivialSmul_snd, lift_snd_assoc, translationMap_snd,
            Category.assoc, Category.assoc, hover, unitSection_snd, Category.comp_id]

/-- The point of `U` attached to an equivariant map over `T` of trivial torsors. -/
theorem lift_unitSection_smul {t₁ t₂ : fppfYoneda.obj T ⟶ U.space.toSheaf}
    {u : G.space.toSheaf ⊗ fppfYoneda.obj T ⟶ G.space.toSheaf ⊗ fppfYoneda.obj T}
    (hover : u ≫ snd _ _ = snd _ _)
    (htarget : u ≫ ((G.space.toSheaf ◁ t₂) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) =
      (G.space.toSheaf ◁ t₁) ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) :
    lift (unitSection G T ≫ u ≫ fst _ _) t₂ ≫
      ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = t₁ := by
  have hlift : unitSection G T ≫ u = lift (unitSection G T ≫ u ≫ fst _ _) (𝟙 _) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc]
    · rw [lift_snd, Category.assoc, hover, unitSection_snd]
  calc lift (unitSection G T ≫ u ≫ fst _ _) t₂ ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)
      = (lift (unitSection G T ≫ u ≫ fst _ _) (𝟙 _) ≫ (G.space.toSheaf ◁ t₂)) ≫
          ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) := by
        rw [lift_whiskerLeft, Category.id_comp]
    _ = unitSection G T ≫ (u ≫ ((G.space.toSheaf ◁ t₂) ≫
          ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf))) := by
        rw [← hlift, Category.assoc, Category.assoc]
    _ = unitSection G T ≫ ((G.space.toSheaf ◁ t₁) ≫
          ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) := by rw [htarget]
    _ = t₁ := unitSection_comp_smul t₁

/-- A translation carrying the second point to the first one is a map of the corresponding
trivial torsors with equivariant maps. -/
theorem translationMap_comp_smul {t₁ t₂ : fppfYoneda.obj T ⟶ U.space.toSheaf}
    (g : fppfYoneda.obj T ⟶ G.space.toSheaf)
    (hg : lift g t₂ ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = t₁) :
    translationMap g ≫ ((G.space.toSheaf ◁ t₂) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf)) =
      (G.space.toSheaf ◁ t₁) ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) := by
  rw [translationMap, lift_whiskerLeft_assoc, lift_mul_smul, ← comp_lift, Category.assoc,
    hg, whiskerLeft_eq_lift]

/-- The unit section recovers the translating point. -/
theorem unitSection_comp_translationMap_fst (g : fppfYoneda.obj T ⟶ G.space.toSheaf) :
    unitSection G T ≫ translationMap g ≫ fst _ _ = g := by
  rw [translationMap_fst, MonObj.comp_mul, unitSection_fst, unitSection_snd_assoc, one_mul]

/-- Morphisms of trivial torsors over `T` are exactly the translations by `T`-points of `G`
which carry the second point of `U` to the first one.  This is the fully faithfulness of the
comparison between the quotient groupoid and the torsor groupoid. -/
noncomputable def trivialHomEquiv (t₁ t₂ : fppfYoneda.obj T ⟶ U.space.toSheaf) :
    (trivialWithPoint t₁ ⟶ trivialWithPoint t₂) ≃
      {g : fppfYoneda.obj T ⟶ G.space.toSheaf //
        lift g t₂ ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = t₁} where
  toFun f := ⟨unitSection G T ≫ f.iso.hom ≫ fst _ _,
    lift_unitSection_smul f.over f.target⟩
  invFun g :=
    { iso := translationIso g.1
      over := translationMap_snd g.1
      equivariant := translationMap_equivariant g.1
      target := translationMap_comp_smul g.1 g.2 }
  left_inv f := ActionTorsor.Hom.ext _ _ (eq_translationMap f.over f.equivariant).symm
  right_inv g := Subtype.ext (unitSection_comp_translationMap_fst g.1)

/-- The morphism attached to a translating point is that translation. -/
@[simp]
theorem trivialHomEquiv_symm_iso_hom (t₁ t₂ : fppfYoneda.obj T ⟶ U.space.toSheaf)
    (g : {g : fppfYoneda.obj T ⟶ G.space.toSheaf //
      lift g t₂ ≫ ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) = t₁}) :
    ((trivialHomEquiv t₁ t₂).symm g).iso.hom = translationMap g.1 :=
  rfl

end TrivialTorsor

/-! ### Comparison of the quotient groupoid with trivial torsors -/

section Comparison

open scoped CategoryTheory.MonObj CategoryTheory.Obj

/-- A monoidal functor between cartesian monoidal categories is multiplicative on points of a
monoid object. -/
theorem map_mul_of_monoidal {C D : Type*} [Category C] [CartesianMonoidalCategory C]
    [Category D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] {M Z : C} [MonObj M]
    (a a' : Z ⟶ M) : F.map (a * a') = F.map a * F.map a' := by
  change F.map (lift a a' ≫ MonObj.mul) = lift (F.map a) (F.map a') ≫ MonObj.mul
  rw [F.map_comp, Functor.obj.μ_def, ← Category.assoc, Functor.Monoidal.lift_μ]

/-- A monoidal functor between cartesian monoidal categories preserves the unit point of a
monoid object. -/
theorem map_one_of_monoidal {C D : Type*} [Category C] [CartesianMonoidalCategory C]
    [Category D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] {M Z : C} [MonObj M] :
    F.map ((1 : Z ⟶ M)) = 1 := by
  change F.map (toUnit Z ≫ MonObj.one) = toUnit (F.obj Z) ≫ MonObj.one
  rw [F.map_comp, Functor.obj.η_def, ← Category.assoc, Functor.Monoidal.toUnit_ε]

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u}
variable (A : ConeAction R S F) (b : Module.Basis σ R F)
variable {B : Type u} [CommRing B]

variable (B) in
/-- The canonical ring isomorphism between `B` and the global sections of `Spec B`. -/
noncomputable def gammaMap : B →+* Γ(coneScheme B, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

/-- The canonical map to global sections is injective. -/
theorem gammaMap_injective : Function.Injective (gammaMap B) := by
  intro x y h
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom h
  simpa [gammaMap] using this

omit [CommRing S] [Algebra R S] [AddCommGroup F] [Module R F] in
/-- The `Spec B`-point of the bundle attached to a vector of `B`. -/
noncomputable def bundlePoint (v : σ → B) :
    fppfYoneda.obj (coneScheme B) ⟶ (vectorBundleGroup σ).space.toSheaf :=
  fppfYoneda.map (ofCoords fun i => gammaMap B (v i))

/-- The `Spec B`-point of the cone attached to a ring-valued point. -/
noncomputable def conePoint (φ : S →+* B) :
    fppfYoneda.obj (coneScheme B) ⟶ (coneActionSpace A b).space.toSheaf :=
  fppfYoneda.map (ofConePt ((gammaMap B).comp φ))

/-- A point of the cone is determined by its ring map. -/
theorem conePoint_injective : Function.Injective (conePoint A b (B := B)) := by
  intro φ ψ h
  have h1 : ofConePt ((gammaMap B).comp φ) = ofConePt ((gammaMap B).comp ψ) :=
    fppfYoneda.map_injective h
  have h2 := congrArg conePt h1
  rw [conePt_ofConePt, conePt_ofConePt] at h2
  exact RingHom.ext fun x => gammaMap_injective (RingHom.congr_fun h2 x)

/-- The scheme-level action of a vector on a point of the cone. -/
theorem lift_comp_actScheme (φ : S →+* B) (v : σ → B) :
    lift (ofCoords fun i => gammaMap B (v i)) (ofConePt ((gammaMap B).comp φ)) ≫
        actScheme A b = ofConePt ((gammaMap B).comp (actOn A b φ v)) := by
  refine conePt_injective ?_
  rw [conePt_comp_actScheme, lift_snd, lift_fst, conePt_ofConePt, coords_ofCoords,
    conePt_ofConePt, comp_actOn]

/-- The sheaf-level action of a vector on a point of the cone is the ring-level action. -/
theorem lift_bundlePoint_conePoint (φ : S →+* B) (v : σ → B) :
    lift (bundlePoint v) (conePoint A b φ) ≫
        ModObj.smul (M := (vectorBundleGroup σ).space.toSheaf)
          (X := (coneActionSpace A b).space.toSheaf) =
      conePoint A b (actOn A b φ v) := by
  have key : lift (fppfYoneda.map (ofCoords fun i => gammaMap B (v i)))
        (fppfYoneda.map (ofConePt ((gammaMap B).comp φ))) ≫
      (Functor.LaxMonoidal.μ fppfYoneda (bundleScheme σ) (coneScheme S) ≫
        fppfYoneda.map (actScheme A b)) =
      fppfYoneda.map (ofConePt ((gammaMap B).comp (actOn A b φ v))) := by
    rw [← Category.assoc, Functor.Monoidal.lift_μ, ← Functor.map_comp, lift_comp_actScheme]
  exact key

omit [CommRing S] [Algebra R S] [AddCommGroup F] [Module R F] in
/-- The zero vector gives the unit point of the bundle. -/
theorem bundlePoint_zero : bundlePoint (σ := σ) (0 : σ → B) = 1 := by
  have h : (ofCoords fun i : σ => gammaMap B ((0 : σ → B) i)) =
      toUnit (coneScheme B) ≫ MonObj.one := by
    refine coords_injective ?_
    funext i
    rw [coords_ofCoords]
    simp only [Pi.zero_apply]
    rw [map_zero, coords_comp, one_eq_ofCoords, coords_ofCoords]
    exact (map_zero _).symm
  rw [bundlePoint, h]
  exact map_one_of_monoidal fppfYoneda (M := bundleScheme σ) (Z := coneScheme B)

omit [CommRing S] [Algebra R S] [AddCommGroup F] [Module R F] in
/-- Adding vectors multiplies the corresponding points of the bundle. -/
theorem bundlePoint_add (v w : σ → B) :
    bundlePoint (σ := σ) (v + w) = bundlePoint v * bundlePoint w := by
  have h : (ofCoords fun i => gammaMap B ((v + w) i)) =
      (ofCoords fun i => gammaMap B (v i)) * (ofCoords fun i => gammaMap B (w i)) := by
    refine coords_injective ?_
    funext i
    rw [coords_ofCoords, coords_mul, coords_ofCoords, coords_ofCoords]
    exact map_add _ _ _
  rw [bundlePoint, bundlePoint, bundlePoint, h, map_mul_of_monoidal]
  rfl

variable (B) in
/-- The inverse of the canonical ring isomorphism `B ≅ Γ(Spec B, ⊤)`. -/
noncomputable def gammaMapInv : Γ(coneScheme B, ⊤) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom

/-- The two canonical maps between `B` and `Γ(Spec B, ⊤)` are inverse. -/
@[simp]
theorem gammaMap_gammaMapInv (x : Γ(coneScheme B, ⊤)) :
    gammaMap B (gammaMapInv B x) = x :=
  Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) x

omit [CommRing S] [Algebra R S] [AddCommGroup F] [Module R F] in
/-- Every `Spec B`-point of the bundle comes from a vector of `B`. -/
theorem bundlePoint_surjective
    (g : fppfYoneda.obj (coneScheme B) ⟶ fppfYoneda.obj (bundleScheme σ)) :
    ∃ v : σ → B, bundlePoint v = g := by
  refine ⟨fun i => gammaMapInv B (coords (fppfYoneda.preimage g) i), ?_⟩
  rw [bundlePoint]
  have h : (ofCoords fun i => gammaMap B (gammaMapInv B (coords (fppfYoneda.preimage g) i))) =
      fppfYoneda.preimage g := by
    refine coords_injective ?_
    funext i
    rw [coords_ofCoords, gammaMap_gammaMapInv]
  rw [h, Functor.map_preimage]

omit [CommRing S] [Algebra R S] [AddCommGroup F] [Module R F] in
/-- A point of the bundle is determined by its vector. -/
theorem bundlePoint_injective : Function.Injective (bundlePoint (σ := σ) (B := B)) := by
  intro v w h
  have h1 := fppfYoneda.map_injective h
  have h2 := congrArg coords h1
  funext i
  rw [coords_ofCoords, coords_ofCoords] at h2
  exact gammaMap_injective (congrFun h2 i)

variable [Algebra R B]

/-- The trivial torsor over `Spec B` attached to a `B`-point of the cone, with the equivariant
map `(e, s) ↦ e · φ(s)`. -/
noncomputable def torsorOfPoint (φ : S →+* B) :
    ActionTorsor (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) :=
  trivialWithPoint (G := vectorBundleGroup σ) (U := coneActionSpace A b) (conePoint A b φ)

/-- A translation carrying the second point of the cone to the first one gives a morphism of
the associated trivial torsors. -/
theorem torsorOfPoint_condition {x y : S →ₐ[R] B} (l : F →ₗ[R] B)
    (hl : translate A.act y l = x) :
    lift (bundlePoint ((b.constr R).symm l)) (conePoint A b (y : S →+* B)) ≫
        ModObj.smul (M := (vectorBundleGroup σ).space.toSheaf)
          (X := (coneActionSpace A b).space.toSheaf) = conePoint A b (x : S →+* B) := by
  rw [lift_bundlePoint_conePoint, actOn_eq_translate, LinearEquiv.apply_symm_apply, hl]

/-- The comparison functor: a `B`-point of the quotient `[C/E]` is sent to the trivial
`E`-torsor over `Spec B` with the equivariant map determined by the point, and a translation is
sent to the corresponding translation of the trivial torsor. -/
noncomputable def trivialTorsorFunctor :
    QuotientGroupoid A B ⥤
      ActionTorsor (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B) where
  obj x := torsorOfPoint A b (x.point : S →+* B)
  map {x y} f := (trivialHomEquiv _ _).symm
    ⟨bundlePoint ((b.constr R).symm (-f.val)),
      torsorOfPoint_condition A b (-f.val) (by
        rw [← f.translate_eq, A.act_add, add_neg_cancel, A.act_zero])⟩
  map_id x := by
    refine ActionTorsor.Hom.ext _ _ ?_
    have h1 : bundlePoint ((b.constr R).symm (-(𝟙 x : x ⟶ x).val)) = 1 := by
      rw [QuotientGroupoid.id_val, neg_zero, map_zero, bundlePoint_zero]
    have h2 : translationMap (G := vectorBundleGroup σ) (T := coneScheme B)
        (bundlePoint ((b.constr R).symm (-(𝟙 x : x ⟶ x).val))) = 𝟙 _ := by
      rw [h1, translationMap_one]
    exact h2
  map_comp {x y z} f g := by
    refine ActionTorsor.Hom.ext _ _ ?_
    have h1 : bundlePoint ((b.constr R).symm (-(f ≫ g).val)) =
        bundlePoint ((b.constr R).symm (-f.val)) *
          bundlePoint ((b.constr R).symm (-g.val)) := by
      rw [QuotientGroupoid.comp_val, neg_add, map_add, bundlePoint_add]
    have h2 : translationMap (G := vectorBundleGroup σ) (T := coneScheme B)
        (bundlePoint ((b.constr R).symm (-(f ≫ g).val))) =
        translationMap (bundlePoint ((b.constr R).symm (-f.val))) ≫
          translationMap (bundlePoint ((b.constr R).symm (-g.val))) := by
      rw [h1, translationMap_comp]
    exact h2

/-- The comparison functor on objects. -/
@[simp]
theorem trivialTorsorFunctor_obj (x : QuotientGroupoid A B) :
    (trivialTorsorFunctor A b (B := B)).obj x = torsorOfPoint A b (x.point : S →+* B) :=
  rfl

/-- The comparison functor on arrows is a translation. -/
@[simp]
theorem trivialTorsorFunctor_map_iso_hom {x y : QuotientGroupoid A B} (f : x ⟶ y) :
    ((trivialTorsorFunctor A b (B := B)).map f).iso.hom =
      translationMap (bundlePoint ((b.constr R).symm (-f.val))) :=
  rfl

/-- The comparison functor is faithful. -/
instance : (trivialTorsorFunctor A b (B := B)).Faithful where
  map_injective {x y f f'} h := by
    have h1 : translationMap (G := vectorBundleGroup σ)
          (bundlePoint ((b.constr R).symm (-f.val))) =
        translationMap (G := vectorBundleGroup σ)
          (bundlePoint ((b.constr R).symm (-f'.val))) := by
      rw [← trivialTorsorFunctor_map_iso_hom A b f, ← trivialTorsorFunctor_map_iso_hom A b f', h]
    have h2 : bundlePoint ((b.constr R).symm (-f.val)) =
        bundlePoint ((b.constr R).symm (-f'.val)) := by
      rw [← unitSection_comp_translationMap_fst (G := vectorBundleGroup σ)
          (bundlePoint ((b.constr R).symm (-f.val))),
        ← unitSection_comp_translationMap_fst (G := vectorBundleGroup σ)
          (bundlePoint ((b.constr R).symm (-f'.val))), h1]
    have h3 := bundlePoint_injective h2
    refine QuotientGroupoid.Hom.ext ?_
    have h4 : -f.val = -f'.val := by
      have := congrArg (b.constr R) h3
      rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    exact neg_injective h4

/-- The comparison functor is full: every morphism of the associated trivial torsors is a
translation coming from an arrow of the quotient groupoid. -/
instance : (trivialTorsorFunctor A b (B := B)).Full where
  map_surjective {x y} h := by
    have hprop := ((trivialHomEquiv (G := vectorBundleGroup σ) (U := coneActionSpace A b)
      (conePoint A b (x.point : S →+* B)) (conePoint A b (y.point : S →+* B))) h).2
    obtain ⟨v, hv⟩ := bundlePoint_surjective (unitSection (vectorBundleGroup σ)
      (coneScheme B) ≫ h.iso.hom ≫ fst _ _)
    have hprop' : lift (bundlePoint v) (conePoint A b (y.point : S →+* B)) ≫
        ModObj.smul (M := (vectorBundleGroup σ).space.toSheaf)
          (X := (coneActionSpace A b).space.toSheaf) =
        conePoint A b (x.point : S →+* B) := by
      rw [hv]
      exact hprop
    have hact : actOn A b (y.point : S →+* B) v = (x.point : S →+* B) := by
      refine conePoint_injective A b ?_
      rw [← lift_bundlePoint_conePoint A b]
      exact hprop'
    have htr : translate A.act y.point (b.constr R v) = x.point := by
      refine AlgHom.ext fun t => ?_
      have hrh := actOn_eq_translate A b y.point v
      rw [hact] at hrh
      exact (RingHom.congr_fun hrh t).symm
    refine ⟨⟨-(b.constr R v), ?_⟩, ?_⟩
    · rw [← htr, A.act_add, add_neg_cancel, A.act_zero]
    · refine ActionTorsor.Hom.ext _ _ ?_
      have hvv : (b.constr R).symm (-(-(b.constr R v))) = v := by
        rw [neg_neg, LinearEquiv.symm_apply_apply]
      have hgoal : translationMap (G := vectorBundleGroup σ) (T := coneScheme B)
          (bundlePoint ((b.constr R).symm (-(-(b.constr R v))))) = h.iso.hom := by
        rw [hvv, hv]
        exact (eq_translationMap h.over h.equivariant).symm
      exact hgoal

/-- The comparison functor is fully faithful: the `B`-points of the quotient groupoid `[C/E]`
are exactly the trivial `E`-torsors over `Spec B` with an equivariant map to the cone. -/
noncomputable def trivialTorsorFunctorFullyFaithful :
    (trivialTorsorFunctor A b (B := B)).FullyFaithful :=
  .ofFullyFaithful _


end Comparison

/-! ### Torsors with a global section -/

section Sections

open scoped CategoryTheory.MonObj

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T : Scheme.{u}}
variable (P : ActionTorsor G U T)

/-- The inverse principal map followed by the action is the first projection. -/
theorem inv_principalMap_smul :
    inv P.principalMap ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P) =
      Limits.pullback.fst P.projection P.projection := by
  rw [← P.principal_fst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The inverse principal map followed by the projection is the second one. -/
theorem inv_principalMap_snd :
    inv P.principalMap ≫ snd _ _ = Limits.pullback.snd P.projection P.projection := by
  rw [← P.principal_snd, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

variable (s : fppfYoneda.obj T ⟶ P.P)

/-- The map `G × T ⟶ P` attached to a section `s` of a torsor: on points `(g, t) ↦ g · s(t)`. -/
noncomputable def sectionMap : G.space.toSheaf ⊗ fppfYoneda.obj T ⟶ P.P :=
  (G.space.toSheaf ◁ s) ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P)

/-- The comparison map attached to a section, written as a lift. -/
theorem sectionMap_eq_lift :
    sectionMap P s = lift (fst _ _) (snd _ _ ≫ s) ≫
      ModObj.smul (M := G.space.toSheaf) (X := P.P) := by
  rw [sectionMap, whiskerLeft_eq_lift]

variable (hs : s ≫ P.projection = 𝟙 _)

include hs

/-- A section splits the projection of the trivial comparison map. -/
theorem sectionMap_projection : sectionMap P s ≫ P.projection = snd _ _ := by
  rw [sectionMap, Category.assoc, P.action_over, ← Category.assoc, whiskerLeft_snd,
    Category.assoc, hs, Category.comp_id]

/-- The `P`-valued pair `(p, s(π p))` used to invert the comparison map. -/
noncomputable def sectionPair : P.P ⟶ Limits.pullback P.projection P.projection :=
  Limits.pullback.lift (𝟙 P.P) (P.projection ≫ s) (by
    rw [Category.id_comp, Category.assoc, hs, Category.comp_id])

/-- The inverse of the comparison map attached to a section. -/
noncomputable def sectionInv : P.P ⟶ G.space.toSheaf ⊗ fppfYoneda.obj T :=
  lift (sectionPair P s hs ≫ inv P.principalMap ≫ fst _ _) P.projection

/-- The candidate inverse is a left inverse of the comparison map. -/
theorem sectionInv_sectionMap : sectionInv P s hs ≫ sectionMap P s = 𝟙 P.P := by
  have h1 : lift (sectionPair P s hs ≫ inv P.principalMap ≫ fst _ _) (P.projection ≫ s) =
      sectionPair P s hs ≫ inv P.principalMap := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc]
    · rw [lift_snd, Category.assoc, inv_principalMap_snd, sectionPair,
        Limits.pullback.lift_snd]
  rw [sectionInv, sectionMap, lift_whiskerLeft_assoc, h1, Category.assoc,
    inv_principalMap_smul, sectionPair, Limits.pullback.lift_fst]

/-- The candidate inverse is a right inverse of the comparison map. -/
theorem sectionMap_sectionInv : sectionMap P s ≫ sectionInv P s hs = 𝟙 _ := by
  have hm : lift (fst _ _) (snd _ _ ≫ s) ≫ P.principalMap =
      sectionMap P s ≫ sectionPair P s hs := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, P.principal_fst, Category.assoc, sectionPair,
        Limits.pullback.lift_fst, Category.comp_id, sectionMap_eq_lift]
    · rw [Category.assoc, P.principal_snd, lift_snd, Category.assoc, sectionPair,
        Limits.pullback.lift_snd, ← Category.assoc, sectionMap_projection P s hs]
  have hq : sectionMap P s ≫ sectionPair P s hs ≫ inv P.principalMap =
      lift (fst _ _) (snd _ _ ≫ s) := by
    rw [← Category.assoc, ← hm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, sectionInv, lift_fst, ← Category.assoc, ← Category.assoc,
      Category.assoc (sectionMap P s) (sectionPair P s hs) (inv P.principalMap), hq,
      lift_fst, Category.id_comp]
  · rw [Category.assoc, sectionInv, lift_snd, sectionMap_projection P s hs,
      Category.id_comp]

/-- The comparison map attached to a section is an isomorphism of sheaves. -/
noncomputable def sectionIso : (G.space.toSheaf ⊗ fppfYoneda.obj T) ≅ P.P where
  hom := sectionMap P s
  inv := sectionInv P s hs
  hom_inv_id := sectionMap_sectionInv P s hs
  inv_hom_id := sectionInv_sectionMap P s hs

omit hs in
/-- The equivariant map of trivial torsors attached to a global section. -/
theorem trivialSmul_comp_sectionMap :
    FppfTorsor.trivialSmul G T ≫ sectionMap P s =
      (G.space.toSheaf ◁ sectionMap P s) ≫ ModObj.smul (M := G.space.toSheaf) (X := P.P) := by
  rw [FppfTorsor.trivialSmul, sectionMap, lift_whiskerLeft_assoc, lift_mul_smul,
    whiskerLeft_eq_lift _ ((G.space.toSheaf ◁ s) ≫
      ModObj.smul (M := G.space.toSheaf) (X := P.P)),
    whiskerLeft_eq_lift _ s, comp_lift_assoc]
  simp only [Category.assoc]

omit hs in
/-- The comparison map is compatible with the equivariant maps to `U`. -/
theorem sectionMap_comp_target :
    sectionMap P s ≫ P.target =
      (G.space.toSheaf ◁ (s ≫ P.target)) ≫
        ModObj.smul (M := G.space.toSheaf) (X := U.space.toSheaf) := by
  rw [sectionMap, Category.assoc, P.target_equivariant, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp]

/-- A torsor with an equivariant map to `U` and a global section is isomorphic, as an object of
the torsor groupoid, to the trivial torsor with the point of `U` determined by the section. -/
noncomputable def isoTrivialOfSection : trivialWithPoint (s ≫ P.target) ≅ P :=
  (Groupoid.isoEquivHom _ _).symm
    { iso := sectionIso P s hs
      over := sectionMap_projection P s hs
      equivariant := trivialSmul_comp_sectionMap P s
      target := sectionMap_comp_target P s }

/-- Every `G`-torsor over `T` is trivial, i.e. admits a global section.  This is the vanishing
of the first fppf cohomology of `G` over `T`; it is *not* proved here, it is used only as an
explicit hypothesis. -/
def AllTorsorsTrivial (G : AlgebraicSpaceGroup.{u}) (T : Scheme.{u}) : Prop :=
  ∀ P : FppfTorsor G T, ∃ s : fppfYoneda.obj T ⟶ P.P, s ≫ P.projection = 𝟙 _

variable {T' : Scheme.{u}}

/-- A section of a torsor pulls back to a section of the base-changed torsor. -/
noncomputable def pullbackSection (b : T' ⟶ T) :
    fppfYoneda.obj T' ⟶ ((ActionTorsor.pullbackFunctor b).obj P).P :=
  Limits.pullback.lift (fppfYoneda.map b ≫ s) (𝟙 _) (by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- The pulled-back section is a section of the base-changed torsor. -/
theorem pullbackSection_projection (b : T' ⟶ T) :
    pullbackSection P s hs b ≫ ((ActionTorsor.pullbackFunctor b).obj P).projection = 𝟙 _ :=
  Limits.pullback.lift_snd _ _ _

/-- The point of `U` determined by the pulled-back section. -/
theorem pullbackSection_target (b : T' ⟶ T) :
    pullbackSection P s hs b ≫ ((ActionTorsor.pullbackFunctor b).obj P).target =
      fppfYoneda.map b ≫ s ≫ P.target := by
  rw [ActionTorsor.pullbackObj_target, ← Category.assoc, pullbackSection,
    Limits.pullback.lift_fst, Category.assoc]

end Sections

section Pullback

open scoped CategoryTheory.MonObj

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {T T' : Scheme.{u}}

/-- Base change of a trivial torsor with a point is the trivial torsor with the pulled-back
point: the object-level naturality of the comparison. -/
noncomputable def pullbackTrivialIso (t : fppfYoneda.obj T ⟶ U.space.toSheaf) (b : T' ⟶ T) :
    trivialWithPoint (fppfYoneda.map b ≫ t) ≅
      (ActionTorsor.pullbackFunctor b).obj (trivialWithPoint t) := by
  have hs : unitSection G T ≫ (trivialWithPoint t).projection = 𝟙 _ := unitSection_snd
  have h : pullbackSection (trivialWithPoint t) (unitSection G T) hs b ≫
      ((ActionTorsor.pullbackFunctor b).obj (trivialWithPoint t)).target =
      fppfYoneda.map b ≫ t := by
    have h1 := pullbackSection_target (trivialWithPoint t) (unitSection G T) hs b
    exact h1.trans (congrArg (fun k => fppfYoneda.map b ≫ k)
      (unitSection_comp_trivialTarget t))
  exact (eqToIso (congrArg trivialWithPoint h.symm)).trans
    (isoTrivialOfSection _ _ (pullbackSection_projection (trivialWithPoint t)
      (unitSection G T) hs b))

end Pullback


/-! ### Naturality in the test algebra and the essential image -/

section ComparisonNaturality

open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F] {σ : Type u}
variable (A : ConeAction R S F) (b : Module.Basis σ R F)
variable {B D : Type u} [CommRing B] [CommRing D]

omit [CommRing S] [Algebra R S] [AddCommGroup F] [Module R F] in
/-- The canonical isomorphisms `B ≅ Γ(Spec B, ⊤)` are natural. -/
theorem gammaMap_naturality (g : B →+* D) :
    ((Spec.map (CommRingCat.ofHom g)).appTop).hom.comp (gammaMap B) = (gammaMap D).comp g := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (Spec.map (CommRingCat.ofHom g)).appTop =
      CommRingCat.ofHom g ≫ (Scheme.ΓSpecIso (CommRingCat.of D)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← _root_.AlgebraicGeometry.Scheme.ΓSpecIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom h

/-- Reindexing a point of the cone along a ring map is base change of the corresponding
`Spec`-point. -/
theorem conePoint_naturality (g : B →+* D) (φ : S →+* B) :
    fppfYoneda.map (Spec.map (CommRingCat.ofHom g)) ≫ conePoint A b φ =
      conePoint A b (g.comp φ) := by
  have key : fppfYoneda.map (Spec.map (CommRingCat.ofHom g)) ≫
      fppfYoneda.map (ofConePt ((gammaMap B).comp φ)) =
      fppfYoneda.map (ofConePt ((gammaMap D).comp (g.comp φ))) := by
    rw [← Functor.map_comp]
    congr 1
    refine conePt_injective ?_
    rw [conePt_comp, conePt_ofConePt, conePt_ofConePt, ← RingHom.comp_assoc,
      gammaMap_naturality, RingHom.comp_assoc]
  exact key

variable [Algebra R B] [Algebra R D]

/-- Object-level naturality of the comparison functor: the trivial torsor attached to a
reindexed point is the base change of the trivial torsor attached to the point. -/
noncomputable def trivialTorsorFunctorNaturality (g : B →ₐ[R] D) (x : QuotientGroupoid A B) :
    (trivialTorsorFunctor A b (B := D)).obj ((QuotientGroupoid.mapQuotient A g).obj x) ≅
      (ActionTorsor.pullbackFunctor
          (Spec.map (CommRingCat.ofHom (g : B →+* D)))).obj
        ((trivialTorsorFunctor A b (B := B)).obj x) :=
  (eqToIso (congrArg trivialWithPoint
    (conePoint_naturality A b (g : B →+* D) (x.point : S →+* B)).symm)).trans
      (pullbackTrivialIso _ _)

/-- Essential surjectivity of the comparison functor, under two explicit hypotheses: every
`E`-torsor over `Spec B` is trivial (the vanishing of `H¹(Spec B, E)`, which is *not* proved
here), and every point of the cone obtained from a section lies over the given `R`-algebra
structure of `B`. -/
theorem essSurj_trivialTorsorFunctor
    (htriv : AllTorsorsTrivial (vectorBundleGroup σ) (coneScheme B))
    (hpt : ∀ (P : ActionTorsor (vectorBundleGroup σ) (coneActionSpace A b) (coneScheme B))
      (s : fppfYoneda.obj (coneScheme B) ⟶ P.P), s ≫ P.projection = 𝟙 _ →
      ∃ x : S →ₐ[R] B, conePoint A b (x : S →+* B) = s ≫ P.target) :
    (trivialTorsorFunctor A b (B := B)).EssSurj := by
  refine ⟨fun P => ?_⟩
  obtain ⟨s, hs⟩ := htriv P.toFppfTorsor
  obtain ⟨x, hx⟩ := hpt P s hs
  exact ⟨QuotientGroupoid.of A x,
    ⟨(eqToIso (congrArg trivialWithPoint hx)).trans (isoTrivialOfSection P s hs)⟩⟩

end ComparisonNaturality

end ConeQuotient

end GromovWitten.AlgebraicGeometry
