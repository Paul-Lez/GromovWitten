/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.Cones.CriteriaBundle
import GromovWitten.AlgebraicGeometry.Cones.DeformationSpaceGeometry
import GromovWitten.AlgebraicGeometry.CotangentComplex.AffinePresentation

/-!
# The intrinsic normal sheaf as `h¹/h⁰` of the dual, in the affine model

Behrend–Fantechi define the intrinsic normal sheaf of `X` as `N_X = h¹/h⁰(L_X^∨)` and prove
that for a local embedding `U ↪ M` into a smooth ambient scheme it is the quotient
`[N_{U/M} / T_M|_U]`.  This file proves the affine, functor-of-points form of that comparison:
the two constructions already present in the repository are literally isomorphic as groupoids
fibred over the affine test algebras.

## Contents

* `NormalSheafPicard.dualComplexOf d`: the two-term complex `[N → F]` attached to a linear map
  `d : N →ₗ[A] F`.  Its complex of `B`-points in the sense of `PicardCriteria.dualPoints` is
  `[Hom(F, B) → Hom(N, B)]`, `l ↦ l ∘ d`, that is, the complex of `B`-points of `T → N`.
* `NormalSheafPicard.toDualPoints`, `NormalSheafPicard.ofDualPoints`: the two comparison
  functors between the quotient groupoid `[Spec Sym N / Spec Sym F](B)` of
  `ConeQuotient.bundleTranslationAction d` and the Picard groupoid of the complex of
  `B`-points of the dual.  They are mutually inverse *on the nose*
  (`toDualPoints_comp_ofDualPoints`, `ofDualPoints_comp_toDualPoints`), so
  `NormalSheafPicard.bundleQuotientEquivDualPoints` is an isomorphism of categories, not merely
  an equivalence.
* `NormalSheafPicard.toDualPoints_naturality`: the comparison commutes strictly with reindexing
  along a map of test algebras (`ConeQuotient.QuotientGroupoid.mapQuotient` versus
  `PicardCriteria.dualPointsMap`), whence the isomorphism of prestacks
  `NormalSheafPicard.quotientPrestackIsoDualPrestack` in `CommAlgCat A ⥤ Cat`.
* `NormalSheafPicard.autEquivH0`, `NormalSheafPicard.isoClass_eq_iff`,
  `NormalSheafPicard.isoClass_surjective`: transport of the `h¹/h⁰` criteria.  Automorphisms of
  every object of the cone quotient are `h⁰` of the complex of `B`-points of the dual,
  isomorphism classes are `h¹` of it, and over the base `h⁰` and `h¹` of `dualComplexOf d` are
  `ker d` and `coker d`.
* `NormalSheafPicard.dualScaling` and
  `NormalSheafPicard.contractionFunctor_comp_toDualPoints`: the `𝔾ₘ`-contraction of the cone
  quotient corresponds to scaling of linear maps, with the unit and multiplicativity laws.
* `NormalSheafPicard.AffineIntrinsicNormalSheaf`: the specialisation to the conormal map
  `d : I/I² → (R/I) ⊗ Ω[R⁄k]`, i.e. to `AffineNormalCone.normalSheafTangentAction`.  Here
  `normalSheafQuotientEquivDualPoints` and `normalSheafPrestackIsoDualPrestack` are the affine
  intrinsic normal sheaf as `h¹/h⁰` of the dual of `conormalComplex`;
  `conormalHomotopyEquivalence` identifies `conormalComplex` with the two-term complex
  `CotangentComplex.AffinePresentation.twoTerm` of the presentation `R → R/I` (whose kernel is
  `I`, by `quotientExtension_ker`), and `normalSheafQuotientEquivPresentation` concludes:
  `[N_{U/M}/T_M|_U](B) ≌ h¹/h⁰(L^∨)(B)` for the presentation cotangent complex `L`, over every
  test algebra `B`.
* `NormalSheafPicard.symProdEquiv`: the algebra input recorded for fibre products of cone
  actions, `Sym(M × N) ≃ Sym M ⊗ Sym N`.

What is *not* proved here: the passage from the affine model to a non-affine base, the fppf
stackification of the prestack, and the identification of `conormalComplex` with the cotangent
complex `L_X` of a stack; the comparison below is with the naive two-term presentation complex.
-/

open CategoryTheory

open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

namespace NormalSheafPicard

universe u

open ConeQuotient GradedCone

/-! ## The two-term complex of a linear map and its `B`-points -/

section General

variable {A N F : Type u} [CommRing A] [AddCommGroup N] [Module A N]
  [AddCommGroup F] [Module A F]

/-- The two-term complex `[N → F]` of a linear map `d : N →ₗ[A] F`, displayed with `N` in
degree zero and `F` in degree one.  Its complex of `B`-points in the sense of
`PicardCriteria.dualPoints` is `[Hom(F, B) → Hom(N, B)]`, `l ↦ l ∘ d`: the complex of
`B`-points of the dual map, which is the differential of the vector bundles `T → N`. -/
abbrev dualComplexOf (d : N →ₗ[A] F) : LinearTwoTermComplex A where
  degreeZero := N
  degreeOne := F
  differential := d

@[simp]
theorem dualComplexOf_differential (d : N →ₗ[A] F) :
    (dualComplexOf d).differential = d :=
  rfl

/-- Cancelling a vanishing summand in degree zero of a two-term complex.  It is stated for a
general complex so that the additive structure is a genuine instance argument. -/
theorem add_eq_of_eq_zero_degreeZero {E : LinearTwoTermComplex A} (a z : E.degreeZero)
    (hz : z = 0) : a + z = a := by
  rw [hz, add_zero]

/-- Cancelling a vanishing summand in degree one of a two-term complex. -/
theorem add_eq_of_eq_zero_degreeOne {E : LinearTwoTermComplex A} (a z : E.degreeOne)
    (hz : z = 0) : a + z = a := by
  rw [hz, add_zero]

/-- Degree-zero cohomology of `[N → F]` is the kernel of `d`. -/
theorem h0_dualComplexOf (d : N →ₗ[A] F) :
    PicardCriteria.h0 (dualComplexOf d) = LinearMap.ker d :=
  rfl

/-- Degree-one cohomology of `[N → F]` is the cokernel of `d`. -/
theorem h1_dualComplexOf (d : N →ₗ[A] F) :
    PicardCriteria.h1 (dualComplexOf d) =
      (F ⧸ (LinearMap.range d : Submodule A F)) :=
  rfl

variable (d : N →ₗ[A] F) (B : Type u) [CommRing B] [Algebra A B]

/-- The differential of the complex of `B`-points is precomposition with `d`. -/
theorem dualPoints_dualComplexOf_differential :
    (PicardCriteria.dualPoints (dualComplexOf d) B).differential =
      PicardCriteria.precomp d B :=
  rfl

/-- Degree-zero cohomology of the complex of `B`-points of the dual is the kernel of
precomposition with `d`: the `B`-points of the kernel bundle of the dual map. -/
theorem h0_dualPoints :
    PicardCriteria.h0 (PicardCriteria.dualPoints (dualComplexOf d) B) =
      LinearMap.ker (PicardCriteria.precomp d B) :=
  rfl

/-- Degree-one cohomology of the complex of `B`-points of the dual is the cokernel of
precomposition with `d`. -/
theorem h1_dualPoints :
    PicardCriteria.h1 (PicardCriteria.dualPoints (dualComplexOf d) B) =
      ((N →ₗ[A] B) ⧸
        (LinearMap.range (PicardCriteria.precomp d B) : Submodule B (N →ₗ[A] B))) :=
  rfl

/-! ## The comparison of groupoids -/

/-- Reading a `B`-point of `Spec Sym N` as a linear map is compatible with reindexing. -/
theorem lift_symm_comp {C : Type u} [CommRing C] [Algebra A C] (g : B →ₐ[A] C)
    (φ : SymmetricAlgebra A N →ₐ[A] B) :
    SymmetricAlgebra.lift.symm (g.comp φ) =
      g.toLinearMap.comp (SymmetricAlgebra.lift.symm φ) := by
  rw [Equiv.symm_apply_eq, ← comp_symLift, Equiv.apply_symm_apply]

/-- Reading a `B`-point of `Spec Sym N` as a linear map turns the contraction of the cone into
scalar multiplication. -/
theorem lift_symm_scale (φ : SymmetricAlgebra A N →ₐ[A] B) (b : B) :
    SymmetricAlgebra.lift.symm (scale (symCoaction A N) φ b) =
      b • SymmetricAlgebra.lift.symm φ := by
  have h := scale_symCoaction (R := A) (F := N) (SymmetricAlgebra.lift.symm φ) b
  rw [pointsEquiv_symm_eq, pointsEquiv_symm_eq, Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]

/-- **The comparison functor.**  An object of the quotient groupoid of the translation action
of `Spec Sym F` on `Spec Sym N` along `d` is a `B`-point of `Spec Sym N`, that is, a linear map
`N →ₗ[A] B`; an arrow is a `B`-point `F →ₗ[A] B` of the acting bundle.  These are exactly the
objects and arrows of the Picard groupoid of the complex of `B`-points of the dual. -/
noncomputable def toDualPoints :
    QuotientGroupoid (bundleTranslationAction d) B ⥤
      (PicardCriteria.dualPoints (dualComplexOf d) B).quotient where
  obj x := ⟨SymmetricAlgebra.lift.symm x.point⟩
  map {x y} f := ⟨f.val, by
    change SymmetricAlgebra.lift.symm x.point + f.val.comp d =
      SymmetricAlgebra.lift.symm y.point
    have h := f.translate_eq
    rw [bundleTranslationAction_act, translate_bundleTranslationCoaction] at h
    have h2 := congrArg (⇑(SymmetricAlgebra.lift (R := A) (M := N) (A := B)).symm) h
    rwa [Equiv.symm_apply_apply] at h2⟩
  map_id x := by
    apply TwoTermQuotient.Hom.ext
    rfl
  map_comp f g := by
    apply TwoTermQuotient.Hom.ext
    rfl

@[simp]
theorem toDualPoints_obj_back (x : QuotientGroupoid (bundleTranslationAction d) B) :
    ((toDualPoints d B).obj x).back = SymmetricAlgebra.lift.symm x.point :=
  rfl

@[simp]
theorem toDualPoints_map_val {x y : QuotientGroupoid (bundleTranslationAction d) B} (f : x ⟶ y) :
    ((toDualPoints d B).map f).val = f.val :=
  rfl

/-- An object of the Picard groupoid of the complex of `B`-points of the dual, read as a linear
map `N →ₗ[A] B`, that is, as a `B`-point of `Spec Sym N`. -/
abbrev dualBackOf (x : (PicardCriteria.dualPoints (dualComplexOf d) B).quotient) : N →ₗ[A] B :=
  x.back

/-- An arrow of the Picard groupoid of the complex of `B`-points of the dual, read as a linear
map `F →ₗ[A] B`, that is, as a `B`-point of the acting bundle. -/
abbrev dualValOf {x y : (PicardCriteria.dualPoints (dualComplexOf d) B).quotient} (a : x ⟶ y) :
    F →ₗ[A] B :=
  a.val

/-- **The inverse comparison functor**, sending a linear map `N →ₗ[A] B` to the `B`-point of
`Spec Sym N` it classifies. -/
noncomputable def ofDualPoints :
    (PicardCriteria.dualPoints (dualComplexOf d) B).quotient ⥤
      QuotientGroupoid (bundleTranslationAction d) B where
  obj x := ⟨SymmetricAlgebra.lift (dualBackOf d B x)⟩
  map {x y} f := ⟨dualValOf d B f, by
    refine (translate_bundleTranslationCoaction_lift d (dualBackOf d B x)
      (dualValOf d B f)).trans (congrArg
        (⇑(SymmetricAlgebra.lift (R := A) (M := N) (A := B))) ?_)
    exact f.translate⟩
  map_id x := QuotientGroupoid.Hom.ext rfl
  map_comp f g := QuotientGroupoid.Hom.ext rfl

@[simp]
theorem ofDualPoints_obj_point (x : (PicardCriteria.dualPoints (dualComplexOf d) B).quotient) :
    ((ofDualPoints d B).obj x).point = SymmetricAlgebra.lift (dualBackOf d B x) :=
  rfl

@[simp]
theorem ofDualPoints_map_val
    {x y : (PicardCriteria.dualPoints (dualComplexOf d) B).quotient} (f : x ⟶ y) :
    ((ofDualPoints d B).map f).val = f.val :=
  rfl

/-- The comparison functors are mutually inverse on the nose, in one direction. -/
theorem toDualPoints_comp_ofDualPoints :
    toDualPoints d B ⋙ ofDualPoints d B = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun x => QuotientGroupoid.ext ?_) fun x y f => ?_
  · exact SymmetricAlgebra.lift.apply_symm_apply x.point
  · refine QuotientGroupoid.Hom.ext ?_
    simp

/-- The comparison functors are mutually inverse on the nose, in the other direction. -/
theorem ofDualPoints_comp_toDualPoints :
    ofDualPoints d B ⋙ toDualPoints d B = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun x => PicardCriteria.quotient_ext ?_) fun x y f => ?_
  · exact SymmetricAlgebra.lift.symm_apply_apply (dualBackOf d B x)
  · refine TwoTermQuotient.Hom.ext _ ?_
    simp [PicardCriteria.eqToHom_val]

/-- **The affine local comparison.**  The quotient groupoid of the translation action of
`Spec Sym F` on `Spec Sym N` along `d : N →ₗ[A] F` is equivalent — in fact isomorphic as a
category — to the Picard groupoid `h¹/h⁰` of the complex of `B`-points of the dual of
`[N → F]`. -/
noncomputable def bundleQuotientEquivDualPoints :
    QuotientGroupoid (bundleTranslationAction d) B ≌
      (PicardCriteria.dualPoints (dualComplexOf d) B).quotient :=
  CategoryTheory.Equivalence.mk (toDualPoints d B) (ofDualPoints d B)
    (eqToIso (toDualPoints_comp_ofDualPoints d B).symm)
    (eqToIso (ofDualPoints_comp_toDualPoints d B))

@[simp]
theorem bundleQuotientEquivDualPoints_functor :
    (bundleQuotientEquivDualPoints d B).functor = toDualPoints d B :=
  rfl

@[simp]
theorem bundleQuotientEquivDualPoints_inverse :
    (bundleQuotientEquivDualPoints d B).inverse = ofDualPoints d B :=
  rfl

/-- The comparison equivalence sends a `B`-point of `Spec Sym N` to the linear map it
classifies. -/
@[simp]
theorem bundleQuotientEquivDualPoints_functor_obj
    (x : QuotientGroupoid (bundleTranslationAction d) B) :
    ((bundleQuotientEquivDualPoints d B).functor.obj x).back =
      SymmetricAlgebra.lift.symm x.point :=
  rfl

/-- The comparison equivalence is the identity on arrows: an arrow of either groupoid is a
`B`-point `F →ₗ[A] B` of the acting bundle. -/
@[simp]
theorem bundleQuotientEquivDualPoints_functor_map_val
    {x y : QuotientGroupoid (bundleTranslationAction d) B} (f : x ⟶ y) :
    ((bundleQuotientEquivDualPoints d B).functor.map f).val = f.val :=
  rfl

/-! ### Compatibility with reindexing along a map of test algebras -/

variable {C : Type u} [CommRing C] [Algebra A C]

/-- **The comparison is strictly compatible with base change.**  Reindexing the cone quotient
along `g : B →ₐ[A] C` and then comparing is the same functor as comparing and then reindexing
the Picard groupoid of the dual points. -/
theorem toDualPoints_naturality (g : B →ₐ[A] C) :
    QuotientGroupoid.mapQuotient (bundleTranslationAction d) g ⋙ toDualPoints d C =
      toDualPoints d B ⋙ PicardCriteria.dualPointsMap (dualComplexOf d) B C g := by
  refine CategoryTheory.Functor.ext (fun x => PicardCriteria.quotient_ext ?_) fun x y f => ?_
  · exact lift_symm_comp B g x.point
  · refine TwoTermQuotient.Hom.ext _ ?_
    simp only [TwoTermQuotient.comp_val, PicardCriteria.eqToHom_val, Functor.comp_map,
      zero_add, add_zero]
    rfl

/-- The inverse comparison is strictly compatible with base change as well. -/
theorem ofDualPoints_naturality (g : B →ₐ[A] C) :
    PicardCriteria.dualPointsMap (dualComplexOf d) B C g ⋙ ofDualPoints d C =
      ofDualPoints d B ⋙ QuotientGroupoid.mapQuotient (bundleTranslationAction d) g := by
  refine CategoryTheory.Functor.ext (fun x => QuotientGroupoid.ext ?_) fun x y f => ?_
  · exact (comp_symLift g (dualBackOf d B x)).symm
  · refine QuotientGroupoid.Hom.ext ?_
    simp only [QuotientGroupoid.comp_val, QuotientGroupoid.eqToHom_val, Functor.comp_map,
      zero_add, add_zero]
    rfl

/-- The comparison over a single test algebra, as an isomorphism in `Cat`. -/
noncomputable def catIso (Bc : CommAlgCat.{u} A) :
    (quotientPrestack (bundleTranslationAction d)).obj Bc ≅
      (PicardCriteria.dualPrestack (dualComplexOf d)).obj Bc where
  hom := Functor.toCatHom (toDualPoints d Bc)
  inv := Functor.toCatHom (ofDualPoints d Bc)
  hom_inv_id := Cat.ext (toDualPoints_comp_ofDualPoints d Bc)
  inv_hom_id := Cat.ext (ofDualPoints_comp_toDualPoints d Bc)

/-- **The comparison of prestacks.**  The quotient prestack of the translation action of
`Spec Sym F` on `Spec Sym N` along `d` is isomorphic, as a functor
`CommAlgCat A ⥤ Cat`, to the `h¹/h⁰` prestack of the dual of `[N → F]`.  No coherence datum is
left unproved: both sides are strictly functorial and the comparison commutes on the nose. -/
noncomputable def quotientPrestackIsoDualPrestack :
    quotientPrestack (bundleTranslationAction d) ≅
      PicardCriteria.dualPrestack (dualComplexOf d) :=
  NatIso.ofComponents (fun Bc => catIso d Bc) fun {Bc _Bc'} g =>
    Cat.ext (toDualPoints_naturality d Bc g.hom)

/-! ## Transport of the `h¹/h⁰` criteria -/

/-- Arrows of the cone quotient and of the Picard groupoid of the dual points agree: both are
`B`-points of the acting bundle carrying source to target. -/
noncomputable def homEquivDualHom {x y : QuotientGroupoid (bundleTranslationAction d) B} :
    (x ⟶ y) ≃ ((toDualPoints d B).obj x ⟶ (toDualPoints d B).obj y) where
  toFun f := (toDualPoints d B).map f
  invFun a := ⟨a.val, by
    refine (translate_bundleTranslationCoaction d x.point a.val).trans ?_
    refine Eq.trans (congrArg (⇑(SymmetricAlgebra.lift (R := A) (M := N) (A := B))) ?_)
      ((SymmetricAlgebra.lift (R := A) (M := N) (A := B)).apply_symm_apply y.point)
    exact a.translate⟩
  left_inv f := QuotientGroupoid.Hom.ext rfl
  right_inv a := TwoTermQuotient.Hom.ext _ rfl

@[simp]
theorem homEquivDualHom_apply_val {x y : QuotientGroupoid (bundleTranslationAction d) B}
    (f : x ⟶ y) : (homEquivDualHom d B f).val = f.val :=
  rfl

@[simp]
theorem homEquivDualHom_symm_apply_val {x y : QuotientGroupoid (bundleTranslationAction d) B}
    (a : (toDualPoints d B).obj x ⟶ (toDualPoints d B).obj y) :
    ((homEquivDualHom d B).symm a).val = a.val :=
  rfl

/-- **Automorphisms are `h⁰` of the dual.**  The automorphism group of every object of the cone
quotient `[Spec Sym N / Spec Sym F](B)` is the degree-zero cohomology of the complex of
`B`-points of the dual, that is, the kernel of precomposition with `d`. -/
noncomputable def autEquivH0 (x : QuotientGroupoid (bundleTranslationAction d) B) :
    (x ⟶ x) ≃ PicardCriteria.h0 (PicardCriteria.dualPoints (dualComplexOf d) B) :=
  (homEquivDualHom d B).trans (PicardCriteria.autEquivKernel _)

@[simp]
theorem autEquivH0_apply_coe (x : QuotientGroupoid (bundleTranslationAction d) B) (a : x ⟶ x) :
    ((autEquivH0 d B x a : PicardCriteria.h0 (PicardCriteria.dualPoints (dualComplexOf d) B)) :
      (PicardCriteria.dualPoints (dualComplexOf d) B).degreeZero) = a.val :=
  rfl

/-- The identification of automorphisms with `h⁰` refines the description of automorphisms as
the stabiliser of a point of the cone: both send an automorphism to its translating
`B`-point. -/
theorem autEquivH0_coe_eq_stabilizer (x : QuotientGroupoid (bundleTranslationAction d) B)
    (a : x ⟶ x) :
    ((autEquivH0 d B x a : PicardCriteria.h0 (PicardCriteria.dualPoints (dualComplexOf d) B)) :
        (PicardCriteria.dualPoints (dualComplexOf d) B).degreeZero) =
      ((QuotientGroupoid.autEquivStabilizer x a :
        {l : F →ₗ[A] B // translate (bundleTranslationAction d).act x.point l = x.point}) :
        F →ₗ[A] B) :=
  rfl

/-- Under the identification of automorphisms with `h⁰`, composition is addition. -/
theorem autEquivH0_comp (x : QuotientGroupoid (bundleTranslationAction d) B) (a b : x ⟶ x) :
    autEquivH0 d B x (a ≫ b) = autEquivH0 d B x a + autEquivH0 d B x b :=
  rfl

/-- The isomorphism class of an object of the cone quotient, as an element of `h¹` of the
complex of `B`-points of the dual. -/
noncomputable def isoClass (x : QuotientGroupoid (bundleTranslationAction d) B) :
    PicardCriteria.h1 (PicardCriteria.dualPoints (dualComplexOf d) B) :=
  PicardCriteria.isoClass ((toDualPoints d B).obj x)

theorem isoClass_def (x : QuotientGroupoid (bundleTranslationAction d) B) :
    isoClass d B x =
      PicardCriteria.h1mk (PicardCriteria.dualPoints (dualComplexOf d) B)
        (SymmetricAlgebra.lift.symm x.point) :=
  rfl

/-- **Isomorphism classes are `h¹` of the dual.**  Two `B`-points of the cone lie in the same
orbit of the bundle action exactly when their classes in the cokernel of precomposition with
`d` agree. -/
theorem isoClass_eq_iff (x y : QuotientGroupoid (bundleTranslationAction d) B) :
    isoClass d B x = isoClass d B y ↔ Nonempty (x ≅ y) := by
  rw [isoClass, isoClass, PicardCriteria.isoClass_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨Groupoid.isoEquivHom _ _ |>.symm ((homEquivDualHom d B).symm e.hom)⟩
  · rintro ⟨e⟩
    exact ⟨Groupoid.isoEquivHom _ _ |>.symm (homEquivDualHom d B e.hom)⟩

/-- Every class in `h¹` of the complex of `B`-points of the dual is the class of an object of
the cone quotient. -/
theorem isoClass_surjective : Function.Surjective (isoClass d B) := by
  intro q
  obtain ⟨l, rfl⟩ := PicardCriteria.h1mk_surjective (E := PicardCriteria.dualPoints
    (dualComplexOf d) B) q
  refine ⟨⟨SymmetricAlgebra.lift l⟩, ?_⟩
  rw [isoClass_def]
  exact congrArg _ (SymmetricAlgebra.lift.symm_apply_apply l)

/-! ## The cone structure: contraction versus scaling -/

/-- Scaling of linear maps on the Picard groupoid of the complex of `B`-points of a dual: it
multiplies both the object `N →ₗ[A] B` and the arrow `F →ₗ[A] B` by `b`.  This is the
fibrewise `𝔾ₘ`-action exhibiting `h¹/h⁰(Eᵛ)` as a cone stack. -/
noncomputable abbrev dualScaling (E : LinearTwoTermComplex A) (b : B) :
    (PicardCriteria.dualPoints E B).quotient ⥤ (PicardCriteria.dualPoints E B).quotient :=
  TwoTermQuotient.contraction (PicardCriteria.dualPoints E B).differential b

/-- Scaling acts on objects by multiplying the classifying linear map. -/
theorem dualScaling_obj_back (E : LinearTwoTermComplex A) (b : B)
    (x : (PicardCriteria.dualPoints E B).quotient) :
    ((dualScaling B E b).obj x).back = b • x.back :=
  rfl

/-- Scaling acts on arrows by multiplying the translating linear map. -/
theorem dualScaling_map_val (E : LinearTwoTermComplex A) (b : B)
    {x y : (PicardCriteria.dualPoints E B).quotient} (f : x ⟶ y) :
    ((dualScaling B E b).map f).val = b • f.val :=
  rfl

/-- The unit law of the scaling action on the Picard groupoid of the dual points. -/
noncomputable def dualScalingOneIso (E : LinearTwoTermComplex A) :
    dualScaling B E 1 ≅ 𝟭 (PicardCriteria.dualPoints E B).quotient :=
  TwoTermQuotient.contractionOneIso _

/-- The multiplicativity law of the scaling action on the Picard groupoid of the dual
points. -/
noncomputable def dualScalingMulIso (E : LinearTwoTermComplex A) (b c : B) :
    dualScaling B E (b * c) ≅ dualScaling B E c ⋙ dualScaling B E b :=
  TwoTermQuotient.contractionMulIso _ b c

/-- **The comparison is compatible with the cone structures.**  The `𝔾ₘ`-contraction of the
cone quotient corresponds, under the comparison functor, to scaling of linear maps on the
Picard groupoid of the complex of `B`-points of the dual. -/
theorem contractionFunctor_comp_toDualPoints (b : B) :
    QuotientGroupoid.contractionFunctor (bundleTranslationAction d) B b ⋙ toDualPoints d B =
      toDualPoints d B ⋙ dualScaling B (dualComplexOf d) b := by
  refine CategoryTheory.Functor.ext (fun x => PicardCriteria.quotient_ext ?_) fun x y f => ?_
  · exact lift_symm_scale B x.point b
  · refine TwoTermQuotient.Hom.ext _ ?_
    simp only [TwoTermQuotient.comp_val, PicardCriteria.eqToHom_val, Functor.comp_map,
      zero_add, add_zero]
    rfl

end General

/-! ## The intrinsic normal sheaf of an affine local embedding -/

namespace AffineIntrinsicNormalSheaf

section IdealCotangent

variable {R : Type u} [CommRing R]

/-- Cotangent modules of equal ideals are canonically isomorphic. -/
def idealCotangentCongr {J J' : Ideal R} (h : J = J') :
    J.Cotangent ≃ₗ[R] J'.Cotangent := by
  subst h
  exact LinearEquiv.refl R _

@[simp]
theorem idealCotangentCongr_toCotangent {J J' : Ideal R} (h : J = J') (x : R) (hx : x ∈ J) :
    idealCotangentCongr h (Ideal.toCotangent J ⟨x, hx⟩) =
      Ideal.toCotangent J' ⟨x, h ▸ hx⟩ := by
  subst h
  rfl

end IdealCotangent

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)

/-- The two-term complex `[I/I² → (R/I) ⊗_R Ω[R⁄k]]` of `R/I`-modules attached to the
presentation `R → R/I`: the conormal module in degree zero and the restricted cotangent bundle
of the ambient affine space in degree one, with the conormal map as differential.  Its dual is
the two-term complex `[T_M|_U → N_{U/M}]` of vector bundles. -/
noncomputable abbrev conormalComplex : LinearTwoTermComplex (R ⧸ I) :=
  dualComplexOf (AffineNormalCone.conormalMap k R I)

@[simp]
theorem conormalComplex_differential :
    (conormalComplex k R I).differential = AffineNormalCone.conormalMap k R I :=
  rfl

/-- Degree-zero cohomology of the conormal complex is the kernel of the conormal map. -/
theorem h0_conormalComplex :
    PicardCriteria.h0 (conormalComplex k R I) =
      LinearMap.ker (AffineNormalCone.conormalMap k R I) :=
  rfl

/-- Degree-one cohomology of the conormal complex is the cokernel of the conormal map, that is,
the module of relative differentials of `R/I` over `k`, up to the comparison of
`CotangentComplex/AffinePresentation.lean`. -/
theorem h1_conormalComplex :
    PicardCriteria.h1 (conormalComplex k R I) =
      (((R ⧸ I) ⊗[R] Ω[R⁄k]) ⧸
        (LinearMap.range (AffineNormalCone.conormalMap k R I) :
          Submodule (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]))) :=
  rfl

variable (B : Type u) [CommRing B] [Algebra (R ⧸ I) B]

/-- **The affine intrinsic normal sheaf.**  Over every test algebra `B`, the quotient groupoid
`[N_{U/M} / T_M|_U](B)` of the affine normal sheaf `Spec Sym(I/I²)` by the restricted tangent
bundle `Spec Sym((R/I) ⊗ Ω[R⁄k])` is isomorphic to the fibre of `h¹/h⁰` of the dual of the
conormal complex.  This is the affine case of Behrend–Fantechi's description of the intrinsic
normal sheaf by a local embedding. -/
noncomputable def normalSheafQuotientEquivDualPoints :
    QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B ≌
      (PicardCriteria.dualPoints (conormalComplex k R I) B).quotient :=
  bundleQuotientEquivDualPoints (AffineNormalCone.conormalMap k R I) B

/-- The comparison sends a `B`-point of the affine normal sheaf to the linear map on `I/I²` it
classifies. -/
@[simp]
theorem normalSheafQuotientEquivDualPoints_functor_obj
    (x : QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B) :
    ((normalSheafQuotientEquivDualPoints k R I B).functor.obj x).back =
      SymmetricAlgebra.lift.symm x.point :=
  rfl

/-- The comparison is the identity on arrows: an arrow of either groupoid is a `B`-point of the
restricted tangent bundle. -/
@[simp]
theorem normalSheafQuotientEquivDualPoints_functor_map_val
    {x y : QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B} (f : x ⟶ y) :
    ((normalSheafQuotientEquivDualPoints k R I B).functor.map f).val = f.val :=
  rfl

/-- **The affine intrinsic normal sheaf as a prestack.**  The quotient prestack
`[N_{U/M} / T_M|_U]` on the affine test algebras is isomorphic to the `h¹/h⁰` prestack of the
dual of the conormal complex, compatibly with all reindexing. -/
noncomputable def normalSheafPrestackIsoDualPrestack :
    quotientPrestack (AffineNormalCone.normalSheafTangentAction k R I) ≅
      PicardCriteria.dualPrestack (conormalComplex k R I) :=
  quotientPrestackIsoDualPrestack (AffineNormalCone.conormalMap k R I)

/-- **Automorphisms in the affine intrinsic normal sheaf.**  The automorphism group of every
`B`-point of `[N_{U/M} / T_M|_U]` is `h⁰` of the complex of `B`-points of the dual conormal
complex. -/
noncomputable def normalSheafAutEquivH0
    (x : QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B) :
    (x ⟶ x) ≃ PicardCriteria.h0 (PicardCriteria.dualPoints (conormalComplex k R I) B) :=
  autEquivH0 (AffineNormalCone.conormalMap k R I) B x

/-- **Isomorphism classes in the affine intrinsic normal sheaf** are `h¹` of the complex of
`B`-points of the dual conormal complex. -/
theorem normalSheaf_isoClass_eq_iff
    (x y : QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B) :
    isoClass (AffineNormalCone.conormalMap k R I) B x =
        isoClass (AffineNormalCone.conormalMap k R I) B y ↔ Nonempty (x ≅ y) :=
  isoClass_eq_iff (AffineNormalCone.conormalMap k R I) B x y

/-- The contraction of the affine intrinsic normal sheaf corresponds to scaling of linear
maps. -/
theorem normalSheaf_contractionFunctor_comp_toDualPoints (b : B) :
    QuotientGroupoid.contractionFunctor (AffineNormalCone.normalSheafTangentAction k R I) B b ⋙
        toDualPoints (AffineNormalCone.conormalMap k R I) B =
      toDualPoints (AffineNormalCone.conormalMap k R I) B ⋙
        dualScaling B (conormalComplex k R I) b :=
  contractionFunctor_comp_toDualPoints (AffineNormalCone.conormalMap k R I) B b

/-! ### Comparison with the two-term complex of the affine presentation -/

/-- The presentation `R → R/I` as an extension of `k`-algebras: the ambient ring is `R` and the
kernel is `I`.  It is the affine local embedding `U = Spec (R/I) ↪ M = Spec R`. -/
noncomputable abbrev quotientExtension : Algebra.Extension.{u} k (R ⧸ I) where
  Ring := R
  σ := Function.surjInv (f := algebraMap R (R ⧸ I)) (Ideal.Quotient.mk_surjective (I := I))
  algebraMap_σ x := Function.surjInv_eq _ x

/-- The ambient ring of the presentation is `R`. -/
theorem quotientExtension_ring : (quotientExtension k R I).Ring = R :=
  rfl

/-- The kernel of the presentation is the ideal `I`. -/
theorem quotientExtension_ker : (quotientExtension k R I).ker = I := by
  change RingHom.ker (algebraMap R (R ⧸ I)) = I
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.mk_ker

/-- The degree-one term of the two-term complex of the presentation is the degree-one term of
the conormal complex: both are the restricted cotangent bundle `(R/I) ⊗_R Ω[R⁄k]`. -/
theorem twoTerm_degreeOne :
    (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I) (quotientExtension k R I)).degreeOne =
      (conormalComplex k R I).degreeOne :=
  rfl

/-- The degree-zero term of the two-term complex of the presentation is the conormal module
`I/I²`, up to the identification of the kernel of the presentation with `I`. -/
theorem twoTerm_degreeZero :
    (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
        (quotientExtension k R I)).degreeZero =
      (quotientExtension k R I).ker.Cotangent :=
  rfl

/-- **The differential of the presentation complex is the conormal map.**  On the class of an
element `x` of `I` both send it to `1 ⊗ dx`; since these classes generate `I/I²` this
identifies the two differentials. -/
theorem twoTerm_differential_mk (x : I) :
    (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
        (quotientExtension k R I)).differential
        (Algebra.Extension.Cotangent.mk ⟨(x : R), (quotientExtension_ker k R I).ge x.2⟩) =
      (conormalComplex k R I).differential (Ideal.toCotangent I x) :=
  rfl

/-- **The conormal module is the cotangent module of the presentation.**  The degree-zero term
`I/I²` of the conormal complex is the degree-zero term of the two-term complex of the
presentation `R → R/I`, because the kernel of that presentation is `I`. -/
noncomputable def conormalCotangentEquiv :
    I.Cotangent ≃ₗ[R ⧸ I] (quotientExtension k R I).Cotangent :=
  LinearEquiv.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
    ((idealCotangentCongr (quotientExtension_ker k R I).symm).trans
      (Algebra.Extension.cotangentEquivCotangentKer (P := quotientExtension k R I)).symm)

@[simp]
theorem conormalCotangentEquiv_toCotangent (x : I) :
    conormalCotangentEquiv k R I (Ideal.toCotangent I x) =
      Algebra.Extension.Cotangent.mk ⟨(x : R), (quotientExtension_ker k R I).ge x.2⟩ := by
  refine congrArg Algebra.Extension.Cotangent.of ?_
  exact idealCotangentCongr_toCotangent (quotientExtension_ker k R I).symm (x : R) x.2

/-- **The comparison chain map.**  The conormal complex `[I/I² → (R/I) ⊗ Ω]` is the two-term
complex of the affine presentation `R → R/I`: the degree-zero terms are identified by
`conormalCotangentEquiv`, the degree-one terms are equal, and the differentials agree. -/
noncomputable def conormalComplexHom :
    LinearTwoTermComplex.Hom (conormalComplex k R I)
      (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I) (quotientExtension k R I)) where
  degreeZero := (conormalCotangentEquiv k R I).toLinearMap
  degreeOne := LinearMap.id
  comm x := by
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I x
    change AffineNormalCone.conormalMap k R I (Ideal.toCotangent I y) =
      (quotientExtension k R I).cotangentComplex
        (conormalCotangentEquiv k R I (Ideal.toCotangent I y))
    rw [conormalCotangentEquiv_toCotangent]
    rfl

/-- The inverse comparison chain map. -/
noncomputable def conormalComplexInv :
    LinearTwoTermComplex.Hom
      (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I) (quotientExtension k R I))
      (conormalComplex k R I) where
  degreeZero := (conormalCotangentEquiv k R I).symm.toLinearMap
  degreeOne := LinearMap.id
  comm x := by
    obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    change (quotientExtension k R I).cotangentComplex (Algebra.Extension.Cotangent.mk y) =
      AffineNormalCone.conormalMap k R I ((conormalCotangentEquiv k R I).symm
        (Algebra.Extension.Cotangent.mk y))
    have hy : (conormalCotangentEquiv k R I).symm (Algebra.Extension.Cotangent.mk y) =
        Ideal.toCotangent I ⟨y.1, (quotientExtension_ker k R I).le y.2⟩ := by
      rw [LinearEquiv.symm_apply_eq, conormalCotangentEquiv_toCotangent]
    rw [hy]
    rfl

/-- **The conormal complex and the presentation complex are homotopy equivalent**, indeed
isomorphic: the comparison chain maps are mutually inverse, so the homotopies are zero. -/
noncomputable def conormalHomotopyEquivalence :
    LinearTwoTermComplex.HomotopyEquivalence (conormalComplex k R I)
      (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I) (quotientExtension k R I)) where
  hom := conormalComplexHom k R I
  inv := conormalComplexInv k R I
  unit :=
    { homotopy := 0
      degreeZero x := by
        refine ((conormalCotangentEquiv k R I).symm_apply_apply x).trans ?_
        exact (add_eq_of_eq_zero_degreeZero _ _ rfl).symm
      degreeOne x := by
        exact (add_eq_of_eq_zero_degreeOne _ _ (map_zero _)).symm }
  counit :=
    { homotopy := 0
      degreeZero x := by
        refine ((conormalCotangentEquiv k R I).apply_symm_apply x).symm.trans ?_
        exact (add_eq_of_eq_zero_degreeZero
          (E := CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
            (quotientExtension k R I)) _ _ rfl).symm
      degreeOne x := by
        exact (add_eq_of_eq_zero_degreeOne _ _ (map_zero _)).symm }

/-- **The intrinsic normal sheaf of an affine local embedding.**  Over every test algebra `B`,
the quotient groupoid `[N_{U/M} / T_M|_U](B)` of the affine normal sheaf of `I ⊆ R` by the
restricted tangent bundle of the ambient affine space is equivalent to the fibre over `Spec B`
of `h¹/h⁰` of the dual of the two-term cotangent complex of the presentation `R → R/I` of
`R/I` over `k`.  This is the affine model of Behrend–Fantechi's `N_X = h¹/h⁰(L_X^∨)`. -/
noncomputable def normalSheafQuotientEquivPresentation :
    QuotientGroupoid (AffineNormalCone.normalSheafTangentAction k R I) B ≌
      (PicardCriteria.dualPoints (CotangentComplex.AffinePresentation.twoTerm k (R ⧸ I)
        (quotientExtension k R I)) B).quotient :=
  (normalSheafQuotientEquivDualPoints k R I B).trans
    (PicardCriteria.dualQuotientEquivalence B (conormalHomotopyEquivalence k R I)).symm

end AffineIntrinsicNormalSheaf

/-! ## Symmetric algebras of products -/

section SymProd

variable (A M N : Type u) [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- The algebra map `Sym(M × N) → Sym M ⊗ Sym N` classifying `(m, n) ↦ ι m ⊗ 1 + 1 ⊗ ι n`. -/
noncomputable def symProdHom :
    SymmetricAlgebra A (M × N) →ₐ[A] SymmetricAlgebra A M ⊗[A] SymmetricAlgebra A N :=
  SymmetricAlgebra.lift
    ((Algebra.TensorProduct.includeLeft (R := A)
        (A := SymmetricAlgebra A M) (B := SymmetricAlgebra A N)).toLinearMap.comp
        ((SymmetricAlgebra.ι A M).comp (LinearMap.fst A M N)) +
      (Algebra.TensorProduct.includeRight (R := A)
        (A := SymmetricAlgebra A M) (B := SymmetricAlgebra A N)).toLinearMap.comp
        ((SymmetricAlgebra.ι A N).comp (LinearMap.snd A M N)))

@[simp]
theorem symProdHom_ι (m : M) (n : N) :
    symProdHom A M N (SymmetricAlgebra.ι A (M × N) (m, n)) =
      SymmetricAlgebra.ι A M m ⊗ₜ[A] 1 + 1 ⊗ₜ[A] SymmetricAlgebra.ι A N n := by
  rw [symProdHom, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The algebra map `Sym M ⊗ Sym N → Sym(M × N)` induced by the two inclusions. -/
noncomputable def symProdInv :
    SymmetricAlgebra A M ⊗[A] SymmetricAlgebra A N →ₐ[A] SymmetricAlgebra A (M × N) :=
  Algebra.TensorProduct.lift
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × N)).comp (LinearMap.inl A M N)))
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (M × N)).comp (LinearMap.inr A M N)))
    fun _ _ => Commute.all _ _

@[simp]
theorem symProdInv_left (m : M) :
    symProdInv A M N (SymmetricAlgebra.ι A M m ⊗ₜ[A] 1) =
      SymmetricAlgebra.ι A (M × N) (m, 0) := by
  rw [symProdInv, Algebra.TensorProduct.lift_tmul, map_one, mul_one,
    SymmetricAlgebra.lift_ι_apply]
  rfl

@[simp]
theorem symProdInv_right (n : N) :
    symProdInv A M N (1 ⊗ₜ[A] SymmetricAlgebra.ι A N n) =
      SymmetricAlgebra.ι A (M × N) (0, n) := by
  rw [symProdInv, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    SymmetricAlgebra.lift_ι_apply]
  rfl

/-- **The symmetric algebra of a product is the tensor product of the symmetric algebras.**
This is the algebra input required for fibre products of affine cones and of cone actions:
`Spec Sym(M × N) = Spec Sym M ×_{Spec A} Spec Sym N`. -/
noncomputable def symProdEquiv :
    SymmetricAlgebra A (M × N) ≃ₐ[A]
      SymmetricAlgebra A M ⊗[A] SymmetricAlgebra A N :=
  AlgEquiv.ofAlgHom (symProdHom A M N) (symProdInv A M N)
    (by
      refine tensor_ext ?_ ?_
      · refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
        change symProdHom A M N (symProdInv A M N
          (SymmetricAlgebra.ι A M m ⊗ₜ[A] 1)) = _
        rw [symProdInv_left, symProdHom_ι, map_zero, TensorProduct.tmul_zero, add_zero]
        rfl
      · refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun n => ?_)
        change symProdHom A M N (symProdInv A M N
          (1 ⊗ₜ[A] SymmetricAlgebra.ι A N n)) = _
        rw [symProdInv_right, symProdHom_ι, map_zero, TensorProduct.zero_tmul, zero_add]
        rfl)
    (by
      refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
      change symProdInv A M N (symProdHom A M N (SymmetricAlgebra.ι A (M × N) x)) = _
      have hx : ((x.1, (0 : N)) + ((0 : M), x.2) : M × N) = x := by simp
      rw [show x = (x.1, x.2) from rfl, symProdHom_ι, map_add, symProdInv_left,
        symProdInv_right, ← map_add, hx]
      rfl)

@[simp]
theorem symProdEquiv_ι (m : M) (n : N) :
    symProdEquiv A M N (SymmetricAlgebra.ι A (M × N) (m, n)) =
      SymmetricAlgebra.ι A M m ⊗ₜ[A] 1 + 1 ⊗ₜ[A] SymmetricAlgebra.ι A N n :=
  symProdHom_ι A M N m n

end SymProd

end NormalSheafPicard

end GromovWitten.AlgebraicGeometry
