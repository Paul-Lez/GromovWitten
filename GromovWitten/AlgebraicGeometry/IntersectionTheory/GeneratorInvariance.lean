/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalizationExact
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysin

/-!
# Invariance of a principal divisor under the choice of its generator

A `RationalFunctionGenerator X` is an integral closed subscheme `V ⊆ X` together with a unit of
its function field.  Two generators built from different presentations of the *same* closed
subvariety (for instance the closures of the same subvariety computed on two different affine
charts) are different terms of that structure, but they define the same principal divisor.  This
file makes that precise: a generator is determined, as far as its divisor is concerned, by

* the image `genericPointImage` in `X` of the generic point of its subscheme, and
* the image of its rational function in the residue field `κ(genericPointImage)` of `X` at that
  point (`residueFunction`).

## Main definitions

* `IntegralClosedSubscheme.genericPointImage`: the image in `X` of the generic point.
* `IntegralClosedSubscheme.functionFieldEquivResidueField`: the canonical ring isomorphism
  from the function field of the subscheme onto `X.residueField genericPointImage`.
* `RationalFunctionGenerator.residueFunction`: the unit of `X.residueField genericPointImage`
  obtained by transporting the rational function along that isomorphism.

## Main results

* `IntegralClosedSubscheme.ker_eq_ker_of_genericPointImage_eq`: two integral closed subschemes
  with the same generic point image are cut out by the same ideal sheaf, so
  `IntegralClosedSubscheme.compare` is an isomorphism over `X`.
* `IntegralClosedSubscheme.functionFieldIso_comm`: the identification of the function field with
  the residue field of the ambient scheme is natural for a dominant morphism of integral closed
  subschemes lying over a morphism of ambient schemes.
* `RationalFunctionGenerator.divisor_eq_of_residueFunction_eq`: two generators with the same
  generic point image and the same residue function have the same principal divisor.
* `RationalFunctionGenerator.divisor_mul`, `divisor_inv`: multiplicativity of the divisor in the
  rational function.
* `RationalFunctionGenerator.residueFunction_restrictOpen` and `residueFunction_closureIn`:
  the residue function is compatible with restriction to an open subscheme and with taking the
  closure of a generator, under the residue field map of the open immersion.
* `VectorBundle.genericPointImage_elementGenerator` and
  `VectorBundle.genericPointImage_sectionGenerator_eq_basePoint`: the generic point images of the
  affine generators of `BundleSectionGysin.lean`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Residue fields at generic points -/

section ResidueIso

variable {X Y : Scheme.{u}}

/-- The residue field map of a morphism which is surjective on stalks is an isomorphism: it is a
homomorphism of fields, hence injective, and it is surjective because the composite with the
surjective residue map of the target is. -/
instance isIso_residueFieldMap_of_surjectiveOnStalks (f : Y ⟶ X)
    [_root_.AlgebraicGeometry.SurjectiveOnStalks f] (y : Y) :
    IsIso (f.residueFieldMap y) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨RingHom.injective (f.residueFieldMap y).hom, fun b ↦ ?_⟩
  obtain ⟨a, ha⟩ := Y.residue_surjective y b
  obtain ⟨c, hc⟩ := f.stalkMap_surjective y a
  refine ⟨(X.residue (f.base y)).hom c, ?_⟩
  have h := ConcreteCategory.congr_hom
    (_root_.AlgebraicGeometry.Scheme.residue_residueFieldMap (f := f) y) c
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  rw [show ((X.residue (f.base y)).hom c) = (X.residue (f.base y)) c from rfl, h, hc, ha]

/-- On an integral scheme the stalk at the generic point is a field, so the residue map at the
generic point is an isomorphism onto the residue field. -/
instance isIso_residue_genericPoint (Y : Scheme.{u})
    [_root_.AlgebraicGeometry.IsIntegral Y] :
    IsIso (Y.residue (genericPoint Y)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨RingHom.injective (Y.residue (genericPoint Y)).hom, Y.residue_surjective _⟩

end ResidueIso

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (V : IntegralClosedSubscheme X)

/-- The image in `X` of the generic point of an integral closed subscheme.  Since the subscheme
is integral its underlying space is irreducible, and this point is the generic point of the
closed subset that the subscheme supports. -/
noncomputable abbrev genericPointImage : X :=
  V.inclusion.base (genericPoint V.scheme)

/-- The canonical isomorphism between the function field of an integral closed subscheme and the
residue field of `X` at the image of its generic point.  It is the residue map at the generic
point followed by the inverse of the residue field map of the closed immersion. -/
noncomputable def functionFieldIso :
    V.scheme.functionField ≅ X.residueField V.genericPointImage :=
  asIso (V.scheme.residue (genericPoint V.scheme)) ≪≫
    (asIso (V.inclusion.residueFieldMap (genericPoint V.scheme))).symm

/-- The ring isomorphism underlying `IntegralClosedSubscheme.functionFieldIso`. -/
noncomputable def functionFieldEquivResidueField :
    V.scheme.functionField ≃+* X.residueField V.genericPointImage :=
  V.functionFieldIso.commRingCatIsoToRingEquiv

/-- `functionFieldEquivResidueField` is given by the underlying map of `functionFieldIso`. -/
@[simp]
theorem functionFieldEquivResidueField_apply (f : V.scheme.functionField) :
    V.functionFieldEquivResidueField f = V.functionFieldIso.hom f := rfl

/-- The defining property of `functionFieldIso`: composed with the stalk map of the closed
immersion at the generic point it is the residue map of `X`. -/
theorem stalkMap_functionFieldIso (a : X.presheaf.stalk V.genericPointImage) :
    V.functionFieldIso.hom (V.inclusion.stalkMap (genericPoint V.scheme) a) =
      X.residue V.genericPointImage a := by
  have h := ConcreteCategory.congr_hom
    (_root_.AlgebraicGeometry.Scheme.residue_residueFieldMap
      (f := V.inclusion) (genericPoint V.scheme)) a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  change (asIso (V.inclusion.residueFieldMap (genericPoint V.scheme))).inv
    (V.scheme.residue (genericPoint V.scheme)
      (V.inclusion.stalkMap (genericPoint V.scheme) a)) = _
  rw [← h]
  have h2 := ConcreteCategory.congr_hom
    (IsIso.hom_inv_id (V.inclusion.residueFieldMap (genericPoint V.scheme)))
    (X.residue V.genericPointImage a)
  rw [CommRingCat.comp_apply] at h2
  exact h2

/-! ### Transport of stalks along equalities -/

end IntegralClosedSubscheme

section StalkTransport

variable {X : Scheme.{u}}

/-- Two successive transports of an element of a ring along equalities of rings compose to the
single transport. -/
theorem eqToHom_trans_apply {A B C : CommRingCat.{u}} (h₁ : A = B) (h₂ : B = C) (h : A = C)
    (a : A) : (eqToHom h₂) ((eqToHom h₁) a) = (eqToHom h) a := by
  subst h₁
  subst h₂
  rfl

/-- Moving the base point along an equality commutes with the stalk map of a morphism. -/
theorem stalkMap_eqToHom {Y : Scheme.{u}} (j : Y ⟶ X) {y y' : Y} (h : y = y')
    (a : X.presheaf.stalk (j.base y)) :
    (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) h)) ((j.stalkMap y) a) =
      (j.stalkMap y') ((eqToHom (congrArg (fun z ↦ X.presheaf.stalk z)
        (show j.base y = j.base y' by rw [h]))) a) := by
  subst h
  simp

/-- Two equal morphisms of schemes have the same stalk maps, up to the transport of the image
point along the induced equality. -/
theorem stalkMap_congr_hom' {Y : Scheme.{u}} {j j' : Y ⟶ X} (h : j = j') (y : Y)
    (a : X.presheaf.stalk (j.base y)) :
    (j.stalkMap y) a =
      (j'.stalkMap y) ((eqToHom (congrArg (fun z ↦ X.presheaf.stalk z)
        (show j.base y = j'.base y by rw [h]))) a) := by
  subst h
  simp

/-- The residue field map of a morphism, applied to a residue class, is the residue class of the
image under the stalk map. -/
theorem residue_residueFieldMap_apply {Y : Scheme.{u}} (j : X ⟶ Y) (x : X)
    (c : Y.presheaf.stalk (j.base x)) :
    (j.residueFieldMap x) (Y.residue (j.base x) c) = X.residue x (j.stalkMap x c) := by
  have h := ConcreteCategory.congr_hom
    (_root_.AlgebraicGeometry.Scheme.residue_residueFieldMap (f := j) x) c
  rwa [CommRingCat.comp_apply, CommRingCat.comp_apply] at h

/-- The residue map commutes with the transport of a point along an equality. -/
theorem residue_residueFieldCongr_apply {x y : X} (h : x = y) (a : X.presheaf.stalk x) :
    (X.residueFieldCongr h).hom (X.residue x a) =
      X.residue y ((eqToHom (congrArg (fun z ↦ X.presheaf.stalk z) h)) a) := by
  subst h
  simp

end StalkTransport

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (V : IntegralClosedSubscheme X)

/-! ### The kernel ideal sheaf of an integral closed subscheme -/

/-- The kernel ideal sheaf of the inclusion of an integral closed subscheme is radical, because
the sections of an integral scheme form a reduced ring. -/
theorem radical_ker : V.inclusion.ker.radical = V.inclusion.ker := by
  refine _root_.AlgebraicGeometry.Scheme.IdealSheafData.ext (funext fun U ↦ ?_)
  rw [_root_.AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal,
    _root_.AlgebraicGeometry.Scheme.Hom.ker_apply]
  refine le_antisymm ?_ (Ideal.le_radical (I := RingHom.ker (V.inclusion.app U).hom))
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker] at hn ⊢
  refine IsReduced.eq_zero _ ⟨n, ?_⟩
  rw [← map_pow]
  exact hn

/-- The support of the kernel ideal sheaf of an integral closed subscheme is the closure of the
image of its generic point. -/
theorem coe_support_ker :
    (V.inclusion.ker.support : Set X) = closure {V.genericPointImage} := by
  rw [_root_.AlgebraicGeometry.Scheme.Hom.support_ker V.inclusion]
  rw [← Set.image_univ, ← genericPoint_closure (α := V.scheme),
    closure_image_closure V.inclusion.base.hom.continuous, Set.image_singleton]

/-- The kernel ideal sheaf of an integral closed subscheme is the vanishing ideal sheaf of the
closure of the image of its generic point; in particular it depends only on that point. -/
theorem ker_eq_vanishingIdeal :
    V.inclusion.ker = _root_.AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {V.genericPointImage}, isClosed_closure⟩ := by
  have h : (⟨closure {V.genericPointImage}, isClosed_closure⟩ : Closeds X) =
      V.inclusion.ker.support := SetLike.coe_injective V.coe_support_ker.symm
  rw [h, _root_.AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support, V.radical_ker]

/-- Two integral closed subschemes whose generic points have the same image in `X` have the same
kernel ideal sheaf, hence define the same closed subscheme. -/
theorem ker_eq_ker_of_genericPointImage_eq (V' : IntegralClosedSubscheme X)
    (h : V.genericPointImage = V'.genericPointImage) :
    V.inclusion.ker = V'.inclusion.ker := by
  rw [V.ker_eq_vanishingIdeal, V'.ker_eq_vanishingIdeal, h]

/-! ### Comparison of two integral closed subschemes with the same generic point -/

/-- The canonical morphism between two integral closed subschemes of `X` whose generic points
have the same image: both are cut out by the same ideal sheaf, so each inclusion factors through
the other. -/
noncomputable def compare (V₁ V₂ : IntegralClosedSubscheme X)
    (h : V₁.genericPointImage = V₂.genericPointImage) : V₁.scheme ⟶ V₂.scheme :=
  _root_.AlgebraicGeometry.IsClosedImmersion.lift V₂.inclusion V₁.inclusion
    (V₂.ker_eq_ker_of_genericPointImage_eq V₁ h.symm).le

/-- The comparison morphism is a morphism over `X`. -/
@[simp]
theorem compare_inclusion (V₁ V₂ : IntegralClosedSubscheme X)
    (h : V₁.genericPointImage = V₂.genericPointImage) :
    compare V₁ V₂ h ≫ V₂.inclusion = V₁.inclusion :=
  _root_.AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _

/-- The comparison morphism is an isomorphism. -/
instance isIso_compare (V₁ V₂ : IntegralClosedSubscheme X)
    (h : V₁.genericPointImage = V₂.genericPointImage) : IsIso (compare V₁ V₂ h) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.isIso_lift V₂.inclusion V₁.inclusion
    (V₂.ker_eq_ker_of_genericPointImage_eq V₁ h.symm)

/-- Two integral closed subschemes related by an isomorphism over `X` have the same generic
point image. -/
theorem genericPointImage_eq_of_iso {V₁ V₂ : IntegralClosedSubscheme X}
    (ε : V₁.scheme ≅ V₂.scheme) (hfac : ε.hom ≫ V₂.inclusion = V₁.inclusion) :
    V₁.genericPointImage = V₂.genericPointImage := by
  have hgen : ε.hom.base (genericPoint V₁.scheme) = genericPoint V₂.scheme :=
    _root_.AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion ε.hom
  have hV : V₁.genericPointImage =
      (ε.hom ≫ V₂.inclusion).base (genericPoint V₁.scheme) := by rw [hfac]
  rw [hV]
  change V₂.inclusion.base (ε.hom.base (genericPoint V₁.scheme)) = _
  rw [hgen]

/-- The identification of the function field with the residue field of `X` at the generic point
image is compatible with an isomorphism of integral closed subschemes over `X`. -/
theorem functionFieldIso_dominantFunctionFieldMap {V₁ V₂ : IntegralClosedSubscheme X}
    (ε : V₁.scheme ≅ V₂.scheme) (hfac : ε.hom ≫ V₂.inclusion = V₁.inclusion)
    (f : V₁.scheme.functionField) :
    V₂.functionFieldIso.hom
        (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap ε.inv f) =
      (X.residueFieldCongr (genericPointImage_eq_of_iso ε hfac)).hom
        (V₁.functionFieldIso.hom f) := by
  obtain ⟨a, rfl⟩ := V₁.inclusion.stalkMap_surjective (genericPoint V₁.scheme) f
  have hinv : ε.inv ≫ V₁.inclusion = V₂.inclusion := by
    rw [← hfac, Iso.inv_hom_id_assoc]
  have he := (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant ε.inv).symm
  have hd : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap ε.inv
        ((V₁.inclusion.stalkMap (genericPoint V₁.scheme)) a) =
      (V₂.inclusion.stalkMap (genericPoint V₂.scheme))
        ((eqToHom (congrArg (fun z ↦ X.presheaf.stalk z)
          (genericPointImage_eq_of_iso ε hfac))) a) := by
    have h0 : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap ε.inv
          ((V₁.inclusion.stalkMap (genericPoint V₁.scheme)) a) =
        (ε.inv.stalkMap (genericPoint V₂.scheme))
          ((eqToHom (congrArg (fun z ↦ V₁.scheme.presheaf.stalk z) he))
            ((V₁.inclusion.stalkMap (genericPoint V₁.scheme)) a)) := rfl
    rw [h0, stalkMap_eqToHom V₁.inclusion he a, ← CommRingCat.comp_apply,
      ← _root_.AlgebraicGeometry.Scheme.Hom.stalkMap_comp ε.inv V₁.inclusion
        (genericPoint V₂.scheme)]
    refine (stalkMap_congr_hom' hinv (genericPoint V₂.scheme) _).trans ?_
    congr 1
    exact eqToHom_trans_apply _ _ _ a
  rw [hd, V₂.stalkMap_functionFieldIso, V₁.stalkMap_functionFieldIso,
    residue_residueFieldCongr_apply]

/-! ### Comparison over a morphism of ambient schemes -/

/-- If `φ` is a dominant morphism from an integral closed subscheme of `X` to one of `Y` lying
over a morphism `j : X ⟶ Y`, then the generic point image upstairs is the image of the generic
point image downstairs. -/
theorem genericPointImage_eq_of_over {Y : Scheme.{u}} (j : X ⟶ Y)
    (V : IntegralClosedSubscheme X) (W : IntegralClosedSubscheme Y)
    (φ : V.scheme ⟶ W.scheme) [hφ : _root_.AlgebraicGeometry.IsDominant φ]
    (hfac : φ ≫ W.inclusion = V.inclusion ≫ j) :
    W.genericPointImage = j.base V.genericPointImage := by
  have he := (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant φ).symm
  change W.inclusion.base (genericPoint W.scheme) = _
  rw [he]
  change (φ ≫ W.inclusion).base (genericPoint V.scheme) = _
  rw [hfac]
  rfl

/-- The canonical identification of the function field with the residue field of the ambient
scheme is compatible with a dominant morphism of integral closed subschemes lying over a
morphism `j : X ⟶ Y` of ambient schemes. -/
theorem functionFieldIso_comm {Y : Scheme.{u}} (j : X ⟶ Y)
    (V : IntegralClosedSubscheme X) (W : IntegralClosedSubscheme Y)
    (φ : V.scheme ⟶ W.scheme) [hφ : _root_.AlgebraicGeometry.IsDominant φ]
    (hfac : φ ≫ W.inclusion = V.inclusion ≫ j) (f : W.scheme.functionField) :
    V.functionFieldIso.hom
        (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap φ f) =
      (j.residueFieldMap V.genericPointImage)
        ((Y.residueFieldCongr (genericPointImage_eq_of_over j V W φ hfac)).hom
          (W.functionFieldIso.hom f)) := by
  obtain ⟨b, rfl⟩ := W.inclusion.stalkMap_surjective (genericPoint W.scheme) f
  have he := (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant φ).symm
  have hd : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap φ
        ((W.inclusion.stalkMap (genericPoint W.scheme)) b) =
      (V.inclusion.stalkMap (genericPoint V.scheme))
        ((j.stalkMap V.genericPointImage)
          ((eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z)
            (genericPointImage_eq_of_over j V W φ hfac))) b)) := by
    have h0 : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap φ
          ((W.inclusion.stalkMap (genericPoint W.scheme)) b) =
        (φ.stalkMap (genericPoint V.scheme))
          ((eqToHom (congrArg (fun z ↦ W.scheme.presheaf.stalk z) he))
            ((W.inclusion.stalkMap (genericPoint W.scheme)) b)) := rfl
    rw [h0, stalkMap_eqToHom W.inclusion he b, ← CommRingCat.comp_apply,
      ← _root_.AlgebraicGeometry.Scheme.Hom.stalkMap_comp φ W.inclusion
        (genericPoint V.scheme)]
    refine (stalkMap_congr_hom' hfac (genericPoint V.scheme) _).trans ?_
    rw [_root_.AlgebraicGeometry.Scheme.Hom.stalkMap_comp V.inclusion j
      (genericPoint V.scheme)]
    exact congrArg (V.inclusion.stalkMap (genericPoint V.scheme))
      (congrArg (j.stalkMap V.genericPointImage) (eqToHom_trans_apply _ _ _ b))
  rw [hd, V.stalkMap_functionFieldIso, W.stalkMap_functionFieldIso,
    residue_residueFieldCongr_apply, residue_residueFieldMap_apply]

end IntegralClosedSubscheme

namespace RationalFunctionGenerator

variable {X : Scheme.{u}}

/-- The rational function of a generator, viewed as a unit of the residue field of `X` at the
image of the generic point of its subscheme. -/
noncomputable def residueFunction (g : RationalFunctionGenerator X) :
    (X.residueField g.subspace.genericPointImage)ˣ :=
  Units.map g.subspace.functionFieldEquivResidueField.toMonoidHom g.function

/-- The value of `residueFunction` is the image of the rational function under
`functionFieldIso`. -/
@[simp]
theorem residueFunction_val (g : RationalFunctionGenerator X) :
    (g.residueFunction : X.residueField g.subspace.genericPointImage) =
      g.subspace.functionFieldIso.hom (g.function : g.subspace.scheme.functionField) := rfl

/-! ### Invariance of the principal divisor -/

/-- Two generators whose integral closed subschemes are isomorphic over `X`, with corresponding
rational functions, have the same principal divisor. -/
theorem divisor_eq_of_iso (dim : DimensionFunction X) (g g' : RationalFunctionGenerator X)
    (ε : g.subspace.scheme ≅ g'.subspace.scheme)
    (hfac : ε.hom ≫ g'.subspace.inclusion = g.subspace.inclusion)
    (hfun : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap ε.inv
        (g.function : g.subspace.scheme.functionField) =
      (g'.function : g'.subspace.scheme.functionField)) :
    g.divisor dim = g'.divisor dim := by
  have h1 : g.divisor dim =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ε.hom ≫ g'.subspace.inclusion)
        (fun x ↦ (dim : X → ℤ) ((ε.hom ≫ g'.subspace.inclusion).base x)) (dim : X → ℤ)
        (g.subspace.scheme.principalCycle (g.function : _)) :=
    AlgebraicCycle.map_congr_hom hfac.symm (dim : X → ℤ) _
  have h2 := AlgebraicCycle.map_comp_of_isClosedImmersion ε.hom g'.subspace.inclusion
    ((DimensionFunction.comapClosedImmersion g'.subspace.inclusion dim : _ → ℤ))
    (dim : X → ℤ) (g.subspace.scheme.principalCycle (g.function : _))
  have h3 := map_isIso_principalCycle ε
    (DimensionFunction.comapClosedImmersion g'.subspace.inclusion dim)
    (g.function : g.subspace.scheme.functionField)
  rw [h3, hfun] at h2
  exact h1.trans h2.symm

/-- **Invariance of the principal divisor.**  A generator is determined, as far as its principal
divisor is concerned, by the image in `X` of the generic point of its integral closed subscheme
together with the image of its rational function in the residue field of `X` at that point. -/
theorem divisor_eq_of_residueFunction_eq (dim : DimensionFunction X)
    (g g' : RationalFunctionGenerator X)
    (hξ : g.subspace.genericPointImage = g'.subspace.genericPointImage)
    (hf : Units.map (X.residueFieldCongr hξ).hom.hom.toMonoidHom g.residueFunction =
      g'.residueFunction) :
    g.divisor dim = g'.divisor dim := by
  have hfac : (asIso (IntegralClosedSubscheme.compare g.subspace g'.subspace hξ)).hom ≫
      g'.subspace.inclusion = g.subspace.inclusion :=
    IntegralClosedSubscheme.compare_inclusion _ _ hξ
  refine divisor_eq_of_iso dim g g'
    (asIso (IntegralClosedSubscheme.compare g.subspace g'.subspace hξ)) hfac ?_
  have hcomp := IntegralClosedSubscheme.functionFieldIso_dominantFunctionFieldMap
    (asIso (IntegralClosedSubscheme.compare g.subspace g'.subspace hξ)) hfac
    (g.function : g.subspace.scheme.functionField)
  have hval := congrArg Units.val hf
  refine g'.subspace.functionFieldEquivResidueField.injective ?_
  rw [IntegralClosedSubscheme.functionFieldEquivResidueField_apply,
    IntegralClosedSubscheme.functionFieldEquivResidueField_apply, hcomp]
  exact hval

/-! ### Multiplicativity in the rational function -/

variable (dim : DimensionFunction X) (V : IntegralClosedSubscheme X)

/-- The principal divisor of a product of rational functions on a fixed integral closed
subscheme is the sum of the principal divisors. -/
theorem divisor_mul (f f' : V.scheme.functionFieldˣ) :
    (RationalFunctionGenerator.mk V (f * f')).divisor dim =
      (RationalFunctionGenerator.mk V f).divisor dim +
        (RationalFunctionGenerator.mk V f').divisor dim := by
  change V.pushforward dim (V.scheme.principalCycle ((f * f' : V.scheme.functionFieldˣ) : _)) = _
  rw [Units.val_mul, _root_.AlgebraicGeometry.Scheme.principalCycle_mul f.ne_zero f'.ne_zero]
  exact (AlgebraicCycle.mapLinear V.inclusion
    (fun z ↦ (dim : X → ℤ) (V.inclusion.base z)) (dim : X → ℤ)).map_add _ _

/-- The principal divisor of the inverse of a rational function is the negative of its principal
divisor. -/
theorem divisor_inv (f : V.scheme.functionFieldˣ) :
    (RationalFunctionGenerator.mk V f⁻¹).divisor dim =
      -(RationalFunctionGenerator.mk V f).divisor dim := by
  change V.pushforward dim (V.scheme.principalCycle ((f⁻¹ : V.scheme.functionFieldˣ) : _)) = _
  rw [Units.val_inv_eq_inv_val,
    _root_.AlgebraicGeometry.Scheme.principalCycle_inv f.ne_zero]
  exact (AlgebraicCycle.mapLinear V.inclusion
    (fun z ↦ (dim : X → ℤ) (V.inclusion.base z)) (dim : X → ℤ)).map_neg _

/-! ### Compatibilities of `residueFunction` -/

/-- The generic point image of the closed image of an integral closed subscheme. -/
@[simp]
theorem genericPointImage_closedImage {Y : Scheme.{u}} (Z : IntegralClosedSubscheme X)
    (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsClosedImmersion f] :
    (Z.closedImage f).genericPointImage = f.base Z.genericPointImage := rfl

/-- The generic point image of the trace of a generator on an open subscheme. -/
theorem genericPointImage_restrictOpen (g : RationalFunctionGenerator X) (U : X.Opens)
    [Nonempty (g.subspace.inclusion ⁻¹ᵁ U)] :
    g.subspace.genericPointImage =
      U.ι.base (g.subspace.restrictOpen U).genericPointImage := by
  have hdom : _root_.AlgebraicGeometry.IsDominant ((g.subspace.inclusion ⁻¹ᵁ U).ι) :=
    _root_.AlgebraicGeometry.Scheme.isDominant_opens_ι _
  exact IntegralClosedSubscheme.genericPointImage_eq_of_over U.ι (g.subspace.restrictOpen U)
    g.subspace (g.subspace.inclusion ⁻¹ᵁ U).ι (hφ := hdom)
    (_root_.AlgebraicGeometry.morphismRestrict_ι g.subspace.inclusion U).symm

/-- The residue function of the trace of a generator on an open subscheme corresponds to the
original residue function under the residue field map of the open immersion (an isomorphism). -/
theorem residueFunction_restrictOpen (g : RationalFunctionGenerator X) (U : X.Opens)
    [Nonempty (g.subspace.inclusion ⁻¹ᵁ U)] :
    ((g.restrictOpen U).residueFunction :
        U.toScheme.residueField (g.restrictOpen U).subspace.genericPointImage) =
      (U.ι.residueFieldMap (g.subspace.restrictOpen U).genericPointImage)
        ((X.residueFieldCongr (genericPointImage_restrictOpen g U)).hom
          (g.residueFunction : X.residueField g.subspace.genericPointImage)) := by
  have hdom : _root_.AlgebraicGeometry.IsDominant ((g.subspace.inclusion ⁻¹ᵁ U).ι) :=
    _root_.AlgebraicGeometry.Scheme.isDominant_opens_ι _
  exact IntegralClosedSubscheme.functionFieldIso_comm U.ι (g.subspace.restrictOpen U) g.subspace
    (g.subspace.inclusion ⁻¹ᵁ U).ι (hφ := hdom)
    (_root_.AlgebraicGeometry.morphismRestrict_ι g.subspace.inclusion U).symm
    (g.function : g.subspace.scheme.functionField)

/-- The generic point image of the closure of a generator on an open subscheme. -/
theorem genericPointImage_closureIn [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    (U : X.Opens) (g : RationalFunctionGenerator U.toScheme)
    [_root_.AlgebraicGeometry.QuasiCompact (g.subspace.inclusion ≫ U.ι)] :
    (g.closureIn U).subspace.genericPointImage = U.ι.base g.subspace.genericPointImage := by
  have hdom : _root_.AlgebraicGeometry.IsDominant ((g.subspace.inclusion ≫ U.ι).toImage) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsDominant
      ((g.subspace.inclusion ≫ U.ι).toImage))
  exact IntegralClosedSubscheme.genericPointImage_eq_of_over U.ι g.subspace
    (g.subspace.closureIn U) ((g.subspace.inclusion ≫ U.ι).toImage) (hφ := hdom)
    (_root_.AlgebraicGeometry.Scheme.Hom.toImage_imageι _)

/-- The residue function of a generator on an open subscheme is the image of the residue
function of its closure under the residue field map of the open immersion. -/
theorem residueFunction_closureIn [_root_.AlgebraicGeometry.IsLocallyNoetherian X]
    (U : X.Opens) (g : RationalFunctionGenerator U.toScheme)
    [_root_.AlgebraicGeometry.QuasiCompact (g.subspace.inclusion ≫ U.ι)] :
    (g.residueFunction : U.toScheme.residueField g.subspace.genericPointImage) =
      (U.ι.residueFieldMap g.subspace.genericPointImage)
        ((X.residueFieldCongr (genericPointImage_closureIn U g)).hom
          ((g.closureIn U).residueFunction :
            X.residueField (g.closureIn U).subspace.genericPointImage)) := by
  have hdom : _root_.AlgebraicGeometry.IsDominant ((g.subspace.inclusion ≫ U.ι).toImage) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsDominant
      ((g.subspace.inclusion ≫ U.ι).toImage))
  have h := IntegralClosedSubscheme.functionFieldIso_comm U.ι g.subspace
    (g.subspace.closureIn U) ((g.subspace.inclusion ≫ U.ι).toImage) (hφ := hdom)
    (_root_.AlgebraicGeometry.Scheme.Hom.toImage_imageι _)
    ((g.closureIn U).function : (g.closureIn U).subspace.scheme.functionField)
  have key : (g.function : g.subspace.scheme.functionField) =
      _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        ((g.subspace.inclusion ≫ U.ι).toImage)
        ((g.closureIn U).function : (g.closureIn U).subspace.scheme.functionField) :=
    (dominantFunctionFieldMap_closureIn_function U g).symm
  rw [residueFunction_val, key]
  exact h

end RationalFunctionGenerator

/-! ## Generic points of the affine generators -/

/-- The generic point of the spectrum of a domain is the zero ideal. -/
theorem genericPoint_asIdeal_eq_bot (B : Type u) [CommRing B] [IsDomain B] :
    ((genericPoint (Spec (CommRingCat.of B)) : ↥(Spec (CommRingCat.of B))) :
        PrimeSpectrum B).asIdeal = ⊥ := by
  have h : IsGenericPoint (show PrimeSpectrum B from ⟨⊥, Ideal.isPrime_bot⟩) Set.univ := by
    change closure _ = _
    rw [PrimeSpectrum.closure_singleton]
    simp
  rw [(genericPoint_spec (Spec (CommRingCat.of B))).eq h]

namespace VectorBundle

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The generic point image of the subvariety `V(P)` of `Spec R[T]` is the point `P`. -/
theorem genericPointImage_quotientSubscheme (P : Ideal (Polynomial R)) [P.IsPrime] :
    (((quotientSubscheme P).genericPointImage :
        ↥(Spec (CommRingCat.of (Polynomial R)))) :
      PrimeSpectrum (Polynomial R)).asIdeal = P := by
  have h : (((quotientSubscheme P).genericPointImage :
        ↥(Spec (CommRingCat.of (Polynomial R)))) :
      PrimeSpectrum (Polynomial R)).asIdeal =
      Ideal.comap (Ideal.Quotient.mk P)
        ((genericPoint (Spec (CommRingCat.of (Polynomial R ⧸ P))) :
          PrimeSpectrum (Polynomial R ⧸ P)).asIdeal) := rfl
  rw [h, genericPoint_asIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- The generic point image of the subvariety of an `elementGenerator` is the prime it is built
from. -/
theorem genericPointImage_elementGenerator (P : Ideal (Polynomial R)) [P.IsPrime]
    (a : Polynomial R) (ha : a ∉ P) :
    (((elementGenerator P a ha).subspace.genericPointImage :
        ↥(Spec (CommRingCat.of (Polynomial R)))) :
      PrimeSpectrum (Polynomial R)).asIdeal = P :=
  genericPointImage_quotientSubscheme P

variable (c : R)

omit [IsNoetherianRing R] in
/-- For a prime containing `T - c`, the contraction along the constants agrees with the image
under evaluation at `c`; both describe the point of `Spec R` underlying `V(Q)`. -/
theorem map_evalRingHom_eq_comap_C (Q : Ideal (Polynomial R)) (hQ : sectionPoly c ∈ Q) :
    Q.map (Polynomial.evalRingHom c) = Q.comap (Polynomial.C : R →+* Polynomial R) := by
  ext r
  constructor
  · intro hr
    have h1 : Polynomial.C r ∈ (Q.map (Polynomial.evalRingHom c)).comap
        (Polynomial.evalRingHom c) := by simpa using hr
    rw [comap_map_evalRingHom c Q hQ] at h1
    exact h1
  · intro hr
    have h2 : Polynomial.evalRingHom c (Polynomial.C r) ∈
        Q.map (Polynomial.evalRingHom c) := Ideal.mem_map_of_mem _ hr
    simpa using h2

/-- The generic point image of the subvariety of a `sectionGenerator` is the point of `Spec R`
cut out by the contraction of `Q` to the constants, i.e. the base point of `Q`. -/
theorem genericPointImage_sectionGenerator (Q : Ideal (Polynomial R)) [Q.IsPrime]
    (hQ : sectionPoly c ∈ Q) (a : Polynomial R) (ha : a ∉ Q) :
    (((sectionGenerator c Q hQ a ha).subspace.genericPointImage :
        ↥(Spec (CommRingCat.of R))) : PrimeSpectrum R).asIdeal =
      Q.comap (Polynomial.C : R →+* Polynomial R) := by
  have h : (((sectionGenerator c Q hQ a ha).subspace.genericPointImage :
        ↥(Spec (CommRingCat.of R))) : PrimeSpectrum R).asIdeal =
      Ideal.comap (sectionQuotientHom Q)
        ((genericPoint (Spec (CommRingCat.of (Polynomial R ⧸ Q))) :
          PrimeSpectrum (Polynomial R ⧸ Q)).asIdeal) := rfl
  rw [h, genericPoint_asIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  ext r
  simp only [RingHom.mem_ker, sectionQuotientHom, RingHom.comp_apply, Ideal.mem_comap]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The generic point image of a `sectionGenerator` is the base point of `Q`. -/
theorem genericPointImage_sectionGenerator_eq_basePoint (Q : Ideal (Polynomial R)) [Q.IsPrime]
    (hQ : sectionPoly c ∈ Q) (a : Polynomial R) (ha : a ∉ Q) :
    ((sectionGenerator c Q hQ a ha).subspace.genericPointImage :
        ↥(Spec (CommRingCat.of R))) =
      basePoint c (show PrimeSpectrum (Polynomial R) from ⟨Q, ‹Q.IsPrime›⟩) hQ := by
  apply PrimeSpectrum.ext
  rw [genericPointImage_sectionGenerator c Q hQ a ha]
  change _ = Q.map (Polynomial.evalRingHom c)
  rw [map_evalRingHom_eq_comap_C c Q hQ]

end VectorBundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory
