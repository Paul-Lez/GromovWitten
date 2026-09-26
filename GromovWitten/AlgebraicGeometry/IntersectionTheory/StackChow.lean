/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.StabilizerWeight
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup
import GromovWitten.AlgebraicGeometry.IntersectionTheory.Gysin
import GromovWitten.AlgebraicGeometry.Stacks.Algebraic
import GromovWitten.AlgebraicGeometry.Stacks.Scheme
import GromovWitten.AlgebraicGeometry.Stacks.TwoPullback
import GromovWitten.AlgebraicGeometry.Sites.Comparison
import Mathlib.AlgebraicGeometry.Birational.Composition
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Rational Chow groups of Deligne--Mumford stacks

The active portion constructs actual representably closed Deligne--Mumford cycle generators,
rational functions on them, and atlas divisors with proved overlap compatibility.  A general
dense-image certificate is still missing, so the rational-equivalence quotient and all general
proper-pushforward, flat-pullback, and degree APIs are retired below and are not exported as
Vistoli Chow theory.
-/

open CategoryTheory Order

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

noncomputable section

/-- An actual integral closed Deligne--Mumford substack.  Closedness is representable, while
integrality and local Noetherianity are witnessed on a genuine etale-surjective scheme atlas.
The dimension is not a label: it is certified by `PureStackDimension`. -/
structure IntegralClosedDMSubstack (X : DeligneMumfordStack.{u}) where
  stack : DeligneMumfordStack.{u}
  inclusion : StackHom stack.toStack X.toStack
  inclusion_closed : inclusion.ClosedImmersion
  /-- Integrality and local Noetherianity are properties: an atlas witnessing them exists, but
  its choice is not part of the identity of a cycle generator. -/
  integralPresentation : ∃ A : StackChart stack.toStack,
    A.IsEtaleSurjective ∧
      _root_.AlgebraicGeometry.IsIntegral A.scheme ∧
      _root_.AlgebraicGeometry.IsNoetherian A.scheme
  dimension : ℤ
  pureDimension : PureStackDimension stack.toAlgebraicStack dimension

namespace IntegralClosedDMSubstack

variable {X : DeligneMumfordStack.{u}} (Z : IntegralClosedDMSubstack X)

/-- A witness atlas chosen internally from the intrinsic integrality property.  Changing the
witness cannot change the enclosing `IntegralClosedDMSubstack`, because the existence proof is
proof-irrelevant. -/
noncomputable def integralAtlas : StackChart Z.stack.toStack :=
  Classical.choose Z.integralPresentation

theorem integralAtlas_etaleSurjective : Z.integralAtlas.IsEtaleSurjective :=
  (Classical.choose_spec Z.integralPresentation).1

noncomputable instance integralAtlas_integral :
    _root_.AlgebraicGeometry.IsIntegral Z.integralAtlas.scheme :=
  (Classical.choose_spec Z.integralPresentation).2.1

noncomputable instance integralAtlas_locallyNoetherian :
    _root_.AlgebraicGeometry.IsLocallyNoetherian Z.integralAtlas.scheme :=
  (Classical.choose_spec Z.integralPresentation).2.2.toIsLocallyNoetherian

noncomputable instance integralAtlas_noetherian :
    _root_.AlgebraicGeometry.IsNoetherian Z.integralAtlas.scheme :=
  (Classical.choose_spec Z.integralPresentation).2.2

/-- The actual represented self-overlap `U ×_Z U` of the internally chosen integral atlas
`U → Z`, retained together with the etale-surjective property of its first projection.  The
same property for the second projection is derived below from the overlap involution. -/
private noncomputable def integralAtlasSelfOverlapWithProperty :
    {p : Z.integralAtlas.PullbackPresentation Z.integralAtlas.scheme
        (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme)) //
      ((@_root_.AlgebraicGeometry.Etale ⊓
          @_root_.AlgebraicGeometry.Surjective) : MorphismProperty Scheme.{u}) p.fst} :=
  let h := Z.integralAtlas_etaleSurjective
  let p := Classical.choice <| h.1 Z.integralAtlas.scheme
    (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme))
  ⟨p, h.2 Z.integralAtlas.scheme
    (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme)) p⟩

/-- The fixed scheme groupoid overlap of the integral atlas.  Unlike an auxiliary relation
type, this scheme comes from the representability clause in the actual etale atlas. -/
noncomputable def integralAtlasSelfOverlap :
    Z.integralAtlas.PullbackPresentation Z.integralAtlas.scheme
      (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme)) :=
  (Z.integralAtlasSelfOverlapWithProperty).1

theorem integralAtlasSelfOverlap_fst_etale :
    _root_.AlgebraicGeometry.Etale Z.integralAtlasSelfOverlap.fst :=
  (Z.integralAtlasSelfOverlapWithProperty).2.1

theorem integralAtlasSelfOverlap_fst_surjective :
    _root_.AlgebraicGeometry.Surjective Z.integralAtlasSelfOverlap.fst :=
  (Z.integralAtlasSelfOverlapWithProperty).2.2

/-- The second self-overlap projection is etale because the swapped pullback presentation is
another presentation to which representable etaleness applies. -/
theorem integralAtlasSelfOverlap_snd_etale :
    _root_.AlgebraicGeometry.Etale Z.integralAtlasSelfOverlap.snd := by
  exact (Z.integralAtlas_etaleSurjective.2 Z.integralAtlas.scheme
    (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme))
    Z.integralAtlasSelfOverlap.selfSwap).1

/-- The second self-overlap projection is surjective by the same swapped-presentation
argument. -/
theorem integralAtlasSelfOverlap_snd_surjective :
    _root_.AlgebraicGeometry.Surjective Z.integralAtlasSelfOverlap.snd := by
  exact (Z.integralAtlas_etaleSurjective.2 Z.integralAtlas.scheme
    (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme))
    Z.integralAtlasSelfOverlap.selfSwap).2

/-- A map into the represented overlap gives the actual comparison between the two atlas
objects classified by its projections.  This is assembled from chart pseudonaturality and the
pullback presentation's universal 2-cell; it is not separately supplied descent data. -/
noncomputable def integralAtlasSelfOverlapComparison
    {T : Scheme.{u}} (m : T ⟶ Z.integralAtlasSelfOverlap.space) :
    Z.integralAtlas.obj T (m ≫ Z.integralAtlasSelfOverlap.fst) ≅
      Z.integralAtlas.obj T (m ≫ Z.integralAtlasSelfOverlap.snd) :=
  (Z.integralAtlas.objIsoOfEq (by simp)).trans
    ((Z.integralAtlas.objPullbackIso
      (m ≫ Z.integralAtlasSelfOverlap.fst) (𝟙 Z.integralAtlas.scheme)).trans
        (Z.integralAtlas.inducedComparison
          Z.integralAtlasSelfOverlap.fst Z.integralAtlasSelfOverlap.snd
          Z.integralAtlasSelfOverlap.comparison m).symm)

/-- Pullback of the atlas's identity object along a map to the atlas is canonically the object
classified by that map. -/
private noncomputable def integralAtlasIdentityPullbackComparison
    {T : Scheme.{u}} (first : T ⟶ Z.integralAtlas.scheme) :
    Z.integralAtlas.obj T first ≅
      (stackPullback Z.stack.toStack first).obj
        (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme)) :=
  (Z.integralAtlas.objIsoOfEq (by simp)).trans
    (Z.integralAtlas.objPullbackIso first (𝟙 Z.integralAtlas.scheme))

/-- An integral pure-dimensional DM stack as a closed substack of itself.  The inclusion is the
actual identity stack morphism, whose representable closed-immersion property is constructed
from the identity scheme presentations. -/
noncomputable def whole (X : DeligneMumfordStack.{u})
    (atlas : StackChart X.toStack) (atlasEtaleSurjective : atlas.IsEtaleSurjective)
    [atlasIntegral : _root_.AlgebraicGeometry.IsIntegral atlas.scheme]
    [atlasNoetherian : _root_.AlgebraicGeometry.IsNoetherian atlas.scheme]
    (dimension : ℤ) (pureDimension : PureStackDimension X.toAlgebraicStack dimension) :
    IntegralClosedDMSubstack X where
  stack := X
  inclusion := Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor
  inclusion_closed := StackHom.id_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}) X.toStack
  integralPresentation := ⟨atlas, atlasEtaleSurjective,
    atlasIntegral, atlasNoetherian⟩
  dimension := dimension
  pureDimension := pureDimension

@[simp]
theorem whole_dimension (X : DeligneMumfordStack.{u})
    (atlas : StackChart X.toStack) (atlasEtaleSurjective : atlas.IsEtaleSurjective)
    [atlasIntegral : _root_.AlgebraicGeometry.IsIntegral atlas.scheme]
    [atlasNoetherian : _root_.AlgebraicGeometry.IsNoetherian atlas.scheme]
    (dimension : ℤ) (pureDimension : PureStackDimension X.toAlgebraicStack dimension) :
    (whole X atlas atlasEtaleSurjective dimension pureDimension).dimension = dimension :=
  rfl

/-- The value in the function field of the integral atlas represented by a rational map to the
absolute affine line.  This uses Mathlib's restriction of a rational map to the generic point,
the affine-line/global-sections equivalence, and the canonical `Gamma(Spec K) = K`
isomorphism; it is not an independently chosen element. -/
noncomputable def rationalMapValue
    (f : Z.integralAtlas.scheme.RationalMap Sites.absoluteAffineLine) :
    Z.integralAtlas.scheme.functionField :=
  (_root_.AlgebraicGeometry.Scheme.ΓSpecIso
    Z.integralAtlas.scheme.functionField).hom
    (Sites.globalSectionsEquiv
      (_root_.AlgebraicGeometry.Spec Z.integralAtlas.scheme.functionField)
      f.fromFunctionField)

/-- Turn an element of the atlas function field into the corresponding rational map to the
absolute affine line.  This is Mathlib's spreading-out construction over `Spec (ULift Z)`, not
a chosen inverse with no geometric content. -/
private abbrev absoluteBase : Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec (.of (ULift.{u} ℤ))

/-- The canonical structural map from a scheme to `Spec (ULift Z)`. -/
private noncomputable def toAbsoluteBase (T : Scheme.{u}) : T ⟶ absoluteBase :=
  T.toSpecΓ ≫ _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    ((algebraMap ℤ _).comp ULift.ringEquiv.toRingHom))

/-- The polynomial affine line over the absolute base. -/
private def affineLineToAbsoluteBase : Sites.absoluteAffineLine ⟶ absoluteBase :=
  _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : ULift.{u} ℤ →+*
      MvPolynomial Sites.RegularFunctionIndex (ULift.{u} ℤ)))

private theorem hom_toAbsoluteBase_unique (T : Scheme.{u})
    (f g : T ⟶ absoluteBase) : f = g := by
  apply (_root_.AlgebraicGeometry.ΓSpec.adjunction.homEquiv T
    (Opposite.op (.of (ULift.{u} ℤ)))).symm.injective
  apply Quiver.Hom.unop_inj
  ext x
  obtain ⟨x⟩ := x
  have hx : (ULift.up x : ULift.{u} ℤ) = (x : ULift.{u} ℤ) := by
    ext
    simp
  rw [hx, map_intCast, map_intCast]

private theorem affineLineToAbsoluteBase_locallyOfFiniteType :
    _root_.AlgebraicGeometry.LocallyOfFiniteType
      (affineLineToAbsoluteBase : Sites.absoluteAffineLine ⟶ absoluteBase) := by
  unfold affineLineToAbsoluteBase absoluteBase Sites.absoluteAffineLine
  rw [_root_.AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @_root_.AlgebraicGeometry.LocallyOfFiniteType)]
  change RingHom.FiniteType (algebraMap _ _)
  rw [RingHom.finiteType_algebraMap]
  infer_instance

private theorem globalSectionsEquiv_comp {S T : Scheme.{u}} (f : S ⟶ T)
    (g : T ⟶ Sites.absoluteAffineLine) :
    Sites.globalSectionsEquiv S (f ≫ g) =
      f.appTop (Sites.globalSectionsEquiv T g) :=
  _root_.AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp
    (n := Sites.RegularFunctionIndex) f g default

/-- Restriction of a composite rational map to the generic point is composition with the
canonical map of function fields.  This is the scheme-theoretic bridge between Mathlib's
partial-map composition and pullback of rational functions. -/
private theorem fromFunctionField_comp_toRationalMap
    {S T V : Scheme.{u}} [si : _root_.AlgebraicGeometry.IsIntegral S]
    [ti : _root_.AlgebraicGeometry.IsIntegral T]
    (h : S ⟶ T) [hd : _root_.AlgebraicGeometry.IsDominant h]
    (p : T.PartialMap V) :
    (h.toRationalMap.comp p.toRationalMap).fromFunctionField =
      _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap h)) ≫
        p.fromFunctionField := by
  let W : ((⊤ : S.Opens).toScheme).Opens :=
    (TopologicalSpace.Opens.map (S.topIso.hom ≫ h).base).obj p.domain
  let U : S.Opens :=
    (_root_.AlgebraicGeometry.Scheme.Hom.opensFunctor
      (⊤ : S.Opens).ι).obj W
  let lift : U.toScheme ⟶ p.domain :=
    ((⊤ : S.Opens).ι.isoImage W).inv ≫
      (S.topIso.hom ≫ h) ∣_ p.domain
  have hp : genericPoint T ∈ p.domain :=
    (genericPoint_specializes _).mem_open p.domain.2
      p.dense_domain.nonempty.choose_spec
  let q : S.PartialMap V := h.toPartialMap.comp p
  have hq : genericPoint S ∈ q.domain :=
    (genericPoint_specializes _).mem_open q.domain.2
      q.dense_domain.nonempty.choose_spec
  have hU : genericPoint S ∈ U := by
    change genericPoint S ∈ q.domain
    exact hq
  let lhsLift : _root_.AlgebraicGeometry.Spec S.functionField ⟶ p.domain :=
    U.fromSpecStalkOfMem (genericPoint S) hU ≫ lift
  let rhsLift : _root_.AlgebraicGeometry.Spec S.functionField ⟶ p.domain :=
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap h)) ≫
      p.domain.fromSpecStalkOfMem (genericPoint T) hp
  have hliftι : lift ≫ p.domain.ι = U.ι ≫ h := by
    dsimp only [lift, U, W]
    rw [Category.assoc,
      _root_.AlgebraicGeometry.morphismRestrict_ι]
    simp only [_root_.AlgebraicGeometry.Scheme.topIso_hom]
    exact (⊤ : S.Opens).ι.isoImage_inv_ι_assoc W h
  have hlhs : lhsLift ≫ p.domain.ι =
      S.fromSpecStalk (genericPoint S) ≫ h := by
    dsimp only [lhsLift]
    rw [Category.assoc, hliftι]
    rw [← Category.assoc, U.fromSpecStalkOfMem_ι]
  have hrhs : rhsLift ≫ p.domain.ι =
      S.fromSpecStalk (genericPoint S) ≫ h := by
    dsimp only [rhsLift]
    rw [Category.assoc, p.domain.fromSpecStalkOfMem_ι]
    exact _root_.AlgebraicGeometry.Scheme.Spec_map_dominantFunctionFieldMap_fromSpecStalk h
  have hlift : lhsLift = rhsLift := by
    rw [← cancel_mono p.domain.ι, hlhs, hrhs]
  change (h.toPartialMap.toRationalMap.comp p.toRationalMap).fromFunctionField = _
  rw [_root_.AlgebraicGeometry.Scheme.RationalMap.toRationalMap_comp,
    _root_.AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_toRationalMap]
  change lhsLift ≫ p.hom = rhsLift ≫ p.hom
  exact congrArg
    (fun k : _root_.AlgebraicGeometry.Spec S.functionField ⟶ p.domain ↦ k ≫ p.hom)
    hlift

noncomputable def rationalMapOfValue
    (a : Z.integralAtlas.scheme.functionField) :
    Z.integralAtlas.scheme.RationalMap Sites.absoluteAffineLine :=
  letI : _root_.AlgebraicGeometry.LocallyOfFiniteType affineLineToAbsoluteBase :=
    affineLineToAbsoluteBase_locallyOfFiniteType
  _root_.AlgebraicGeometry.Scheme.RationalMap.ofFunctionField
    (toAbsoluteBase Z.integralAtlas.scheme)
    affineLineToAbsoluteBase
    ((Sites.globalSectionsEquiv
      (_root_.AlgebraicGeometry.Spec Z.integralAtlas.scheme.functionField)).symm
        ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso
          Z.integralAtlas.scheme.functionField).inv a))
    (hom_toAbsoluteBase_unique _ _ _)

@[simp]
theorem rationalMapValue_rationalMapOfValue
    (a : Z.integralAtlas.scheme.functionField) :
    Z.rationalMapValue (Z.rationalMapOfValue a) = a := by
  rw [rationalMapValue, rationalMapOfValue,
    _root_.AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_ofFunctionField]
  simp

/-- The everywhere-defined map represented by the constant regular function `1`. -/
private noncomputable def regularOneRationalMap :
    Z.integralAtlas.scheme.RationalMap Sites.absoluteAffineLine :=
  ((Sites.globalSectionsEquiv Z.integralAtlas.scheme).symm 1).toRationalMap

private theorem rationalMapOfValue_one_eq_regularOne :
    Z.rationalMapOfValue 1 = Z.regularOneRationalMap := by
  apply _root_.AlgebraicGeometry.Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [rationalMapOfValue,
    _root_.AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_ofFunctionField]
  apply (Sites.globalSectionsEquiv
    (_root_.AlgebraicGeometry.Spec Z.integralAtlas.scheme.functionField)).injective
  rw [Equiv.apply_symm_apply]
  unfold regularOneRationalMap
  rw [_root_.AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_toRationalMap]
  change _ = Sites.globalSectionsEquiv _
    (((Sites.globalSectionsEquiv Z.integralAtlas.scheme).symm 1).toPartialMap.fromSpecStalkOfMem
      (x := _root_.genericPoint Z.integralAtlas.scheme) trivial)
  rw [_root_.AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap]
  change
    (_root_.AlgebraicGeometry.Scheme.ΓSpecIso
      Z.integralAtlas.scheme.functionField).inv 1 =
      Sites.globalSectionsEquiv
        (_root_.AlgebraicGeometry.Spec Z.integralAtlas.scheme.functionField)
        (Z.integralAtlas.scheme.fromSpecStalk
            (_root_.genericPoint Z.integralAtlas.scheme) ≫
          (Sites.globalSectionsEquiv Z.integralAtlas.scheme).symm 1)
  rw [globalSectionsEquiv_comp, Equiv.apply_symm_apply]
  simp

private theorem pullback_regularOne_eq
    {T : Scheme.{u}} [ti : _root_.AlgebraicGeometry.IsIntegral T]
    (first second : T ⟶ Z.integralAtlas.scheme)
    [firstDominant : _root_.AlgebraicGeometry.IsDominant first]
    [secondDominant : _root_.AlgebraicGeometry.IsDominant second] :
    first.toRationalMap.comp Z.regularOneRationalMap =
      second.toRationalMap.comp Z.regularOneRationalMap := by
  unfold regularOneRationalMap
  rw [_root_.AlgebraicGeometry.Scheme.RationalMap.comp_toRationalMap,
    _root_.AlgebraicGeometry.Scheme.RationalMap.comp_toRationalMap]
  change
    (first ≫ (Sites.globalSectionsEquiv Z.integralAtlas.scheme).symm 1).toRationalMap =
      (second ≫ (Sites.globalSectionsEquiv Z.integralAtlas.scheme).symm 1).toRationalMap
  congr 1
  apply (Sites.globalSectionsEquiv T).injective
  rw [globalSectionsEquiv_comp, globalSectionsEquiv_comp,
    Equiv.apply_symm_apply]
  simp

/-- A rational function on an integral Deligne--Mumford stack is a nonzero function on its
genuine etale atlas whose two pullbacks agree on the actual represented self-overlap.  Because
rational maps are defined through function fields, the equality is tested after every integral
scheme mapping dominantly to both atlas legs; this covers the integral generic pieces on which
orders of vanishing are compared. -/
structure RationalFunction where
  map : Z.integralAtlas.scheme.RationalMap Sites.absoluteAffineLine
  nonzero : Z.rationalMapValue map ≠ 0
  overlapDescent {T : Scheme.{u}} [ti : _root_.AlgebraicGeometry.IsIntegral T]
      (m : T ⟶ Z.integralAtlasSelfOverlap.space)
      [fstDominant : _root_.AlgebraicGeometry.IsDominant
        (m ≫ Z.integralAtlasSelfOverlap.fst)]
      [sndDominant : _root_.AlgebraicGeometry.IsDominant
        (m ≫ Z.integralAtlasSelfOverlap.snd)] :
    (m ≫ Z.integralAtlasSelfOverlap.fst).toRationalMap.comp map =
      (m ≫ Z.integralAtlasSelfOverlap.snd).toRationalMap.comp map

/-- Equality on the fixed groupoid overlap implies the presentation-independent formulation:
any two dominant atlas maps defining isomorphic stack objects pull back the rational function
equally.  The mediating map is constructed by the overlap's universal property. -/
theorem RationalFunction.descent (f : Z.RationalFunction)
    {T : Scheme.{u}} [ti : _root_.AlgebraicGeometry.IsIntegral T]
    (first second : T ⟶ Z.integralAtlas.scheme)
    [firstDominant : _root_.AlgebraicGeometry.IsDominant first]
    [secondDominant : _root_.AlgebraicGeometry.IsDominant second]
    (comparison : Z.integralAtlas.obj T first ≅ Z.integralAtlas.obj T second) :
    first.toRationalMap.comp f.map = second.toRationalMap.comp f.map := by
  let overlapComparison : Z.integralAtlas.obj T second ≅
      (stackPullback Z.stack.toStack first).obj
        (Z.integralAtlas.obj Z.integralAtlas.scheme (𝟙 Z.integralAtlas.scheme)) :=
    comparison.symm.trans (Z.integralAtlasIdentityPullbackComparison first)
  let m : T ⟶ Z.integralAtlasSelfOverlap.space :=
    Z.integralAtlasSelfOverlap.lift first second overlapComparison
  have hfst : m ≫ Z.integralAtlasSelfOverlap.fst = first :=
    Z.integralAtlasSelfOverlap.lift_fst first second overlapComparison
  have hsnd : m ≫ Z.integralAtlasSelfOverlap.snd = second :=
    Z.integralAtlasSelfOverlap.lift_snd first second overlapComparison
  let _ : _root_.AlgebraicGeometry.IsDominant
      (m ≫ Z.integralAtlasSelfOverlap.fst) := by
    rw [hfst]
    infer_instance
  let _ : _root_.AlgebraicGeometry.IsDominant
      (m ≫ Z.integralAtlasSelfOverlap.snd) := by
    rw [hsnd]
    infer_instance
  simpa only [hfst, hsnd] using f.overlapDescent m

/-- The function-field value of a rational map to the absolute affine line on any integral
scheme.  This is the same generic-point evaluation used for the atlas value above. -/
noncomputable def rationalMapGenericValue
    {T : Scheme.{u}} [ti : _root_.AlgebraicGeometry.IsIntegral T]
    (f : T.RationalMap Sites.absoluteAffineLine) : T.functionField :=
  (_root_.AlgebraicGeometry.Scheme.ΓSpecIso T.functionField).hom
    (Sites.globalSectionsEquiv (_root_.AlgebraicGeometry.Spec T.functionField)
      f.fromFunctionField)

/-- Generic evaluation of a rational function commutes with pullback along a dominant scheme
morphism.  The proof unfolds rational-map composition through its dense open domain and uses the
canonical generic-point square above; it does not assume a compatibility of function fields. -/
theorem rationalMapGenericValue_comp
    {S T : Scheme.{u}} [si : _root_.AlgebraicGeometry.IsIntegral S]
    [ti : _root_.AlgebraicGeometry.IsIntegral T]
    (h : S ⟶ T) [hd : _root_.AlgebraicGeometry.IsDominant h]
    (f : T.RationalMap Sites.absoluteAffineLine) :
    rationalMapGenericValue (h.toRationalMap.comp f) =
      _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap h
        (rationalMapGenericValue f) := by
  obtain ⟨p, rfl⟩ := f.exists_rep
  unfold rationalMapGenericValue
  rw [fromFunctionField_comp_toRationalMap, globalSectionsEquiv_comp]
  rw [← ConcreteCategory.comp_apply,
    _root_.AlgebraicGeometry.Scheme.ΓSpecIso_naturality]
  rfl

/-- For a dominant etale morphism, generic evaluation is the pullback along the local
fraction-field map at any chosen point.  Independence of that point is a theorem above. -/
theorem rationalMapGenericValue_comp_etale
    {S T : Scheme.{u}} [si : _root_.AlgebraicGeometry.IsIntegral S]
    [ti : _root_.AlgebraicGeometry.IsIntegral T]
    (h : S ⟶ T) [hd : _root_.AlgebraicGeometry.IsDominant h]
    [he : _root_.AlgebraicGeometry.Etale h] (x : S)
    (f : T.RationalMap Sites.absoluteAffineLine) :
    rationalMapGenericValue (h.toRationalMap.comp f) =
      _root_.AlgebraicGeometry.Scheme.etaleLocalFunctionFieldMap h x
        (rationalMapGenericValue f) := by
  rw [rationalMapGenericValue_comp,
    _root_.AlgebraicGeometry.Scheme.etaleLocalFunctionFieldMap_eq_dominantFunctionFieldMap]

/-- Descent on the represented overlap gives literal equality of the two pulled-back
function-field elements.  This is the equality to which etale invariance of local orders will
be applied. -/
theorem RationalFunction.overlapPullbackValue_eq (f : Z.RationalFunction)
    {T : Scheme.{u}} [ti : _root_.AlgebraicGeometry.IsIntegral T]
    (m : T ⟶ Z.integralAtlasSelfOverlap.space)
    [fstDominant : _root_.AlgebraicGeometry.IsDominant
      (m ≫ Z.integralAtlasSelfOverlap.fst)]
    [sndDominant : _root_.AlgebraicGeometry.IsDominant
      (m ≫ Z.integralAtlasSelfOverlap.snd)] :
    rationalMapGenericValue
        ((m ≫ Z.integralAtlasSelfOverlap.fst).toRationalMap.comp f.map) =
      rationalMapGenericValue
        ((m ≫ Z.integralAtlasSelfOverlap.snd).toRationalMap.comp f.map) :=
  congrArg rationalMapGenericValue (f.overlapDescent m)

/-- The multiplicative identity is an actual descended nonzero rational function on every
integral closed DM substack. -/
noncomputable def RationalFunction.one : Z.RationalFunction where
  map := Z.rationalMapOfValue 1
  nonzero := by
    rw [Z.rationalMapValue_rationalMapOfValue]
    exact one_ne_zero
  overlapDescent := by
    intro T _ m _ _
    rw [Z.rationalMapOfValue_one_eq_regularOne]
    exact Z.pullback_regularOne_eq
      (m ≫ Z.integralAtlasSelfOverlap.fst)
      (m ≫ Z.integralAtlasSelfOverlap.snd)

instance : One (RationalFunction Z) :=
  ⟨RationalFunction.one Z⟩

instance : Nonempty (RationalFunction Z) :=
  ⟨1⟩

/-- The generic-point object of an integral closed DM substack, obtained by pulling its actual
atlas object back along `Spec K(Z) → U`. -/
noncomputable def genericObject :
    StackFiber Z.stack.toStack
      (_root_.AlgebraicGeometry.Spec (.of Z.integralAtlas.scheme.functionField)) :=
  Z.integralAtlas.obj
    (_root_.AlgebraicGeometry.Spec (.of Z.integralAtlas.scheme.functionField))
    (Z.integralAtlas.scheme.fromSpecStalk
      (_root_.genericPoint Z.integralAtlas.scheme))

/-- The actual automorphism group at the generic object of an integral DM substack. -/
abbrev genericInertia := Z.genericObject ⟶ Z.genericObject

/-- The principal divisor computed on the genuine integral etale atlas.  Its coefficients are
Mathlib's orders of vanishing and its local finiteness is the theorem proved for scheme
principal cycles; no stack-cycle coefficients are supplied here. -/
noncomputable def RationalFunction.atlasPrincipalCycle
    (f : RationalFunction Z) :
    AlgebraicCycle Z.integralAtlas.scheme ℚ :=
  Z.integralAtlas.scheme.principalCycle (Z.rationalMapValue f.map)

/-- On the chosen Noetherian atlas the locally finite principal cycle has finite global
support, hence determines an honest `Finsupp`. -/
noncomputable def RationalFunction.atlasPrincipalFinsupp
    (f : RationalFunction Z) : Z.integralAtlas.scheme →₀ ℚ :=
  Finsupp.ofSupportFinite f.atlasPrincipalCycle (by
    have h := f.atlasPrincipalCycle.locallyFiniteSupport
      |>.finite_inter_support_of_isCompact
        (W := Set.univ) CompactSpace.isCompact_univ
    change (Function.support f.atlasPrincipalCycle.toFun).Finite
    simpa only [Set.univ_inter] using h)

@[simp]
theorem RationalFunction.atlasPrincipalFinsupp_apply
    (f : RationalFunction Z) (x : Z.integralAtlas.scheme) :
    (atlasPrincipalFinsupp Z f) x = (atlasPrincipalCycle Z f) x :=
  rfl

@[simp]
theorem RationalFunction.atlasPrincipalCycle_one :
    (1 : RationalFunction Z).atlasPrincipalCycle = 0 := by
  rw [RationalFunction.atlasPrincipalCycle]
  change Z.integralAtlas.scheme.principalCycle
    (Z.rationalMapValue (Z.rationalMapOfValue 1)) = 0
  rw [Z.rationalMapValue_rationalMapOfValue]
  exact _root_.AlgebraicGeometry.Scheme.principalCycle_one

end IntegralClosedDMSubstack

/-- Two presentations define the same integral closed substack when an equivalence of their
source stacks identifies the two closed immersions into the ambient stack.  Dimension equality
is included because the present development has not yet proved atlas-independence of
`PureStackDimension`; it is a proposition, not a selectable cycle label. -/
def IntegralClosedDMSubstack.ModelEquivalent
    {X : DeligneMumfordStack.{u}}
    (Z W : IntegralClosedDMSubstack X) : Prop :=
  ∃ e : StackEquivalenceData Z.stack.toStack W.stack.toStack,
    Nonempty (StackIso2
      (Pseudofunctor.StrongTrans.vcomp e.hom W.inclusion) Z.inclusion) ∧
      Z.dimension = W.dimension

/-- The actual cycle-generator type: integral closed DM substacks modulo equivalence over the
ambient stack.  In particular, replacing a source stack by an equivalent model cannot create a
new basis vector.  We use the equivalence relation generated by displayed equivalences, avoiding
any hidden choice of symmetry or composition coherence. -/
abbrev StackCycleGenerator (X : DeligneMumfordStack.{u}) : Type (u + 2) :=
  Quotient (Relation.EqvGen.setoid
    (@IntegralClosedDMSubstack.ModelEquivalent X))

namespace StackCycleGenerator

variable {X : DeligneMumfordStack.{u}}

/-- Send an actual closed-substack presentation to its presentation-independent cycle
generator. -/
def mk (Z : IntegralClosedDMSubstack X) : StackCycleGenerator X :=
  Quotient.mk _ Z

/-- A displayed equivalence over the ambient stack identifies the corresponding cycle
generators. -/
theorem mk_eq_of_modelEquivalent {Z W : IntegralClosedDMSubstack X}
    (h : Z.ModelEquivalent W) : mk Z = mk W :=
  Quotient.sound (Relation.EqvGen.rel Z W h)

/-- An internal representative of a cycle generator.  It is used only to recover geometric
objects on which invariants are computed; the public generator itself remains the quotient. -/
noncomputable def representative (Z : StackCycleGenerator X) :
    IntegralClosedDMSubstack X :=
  Quotient.out Z

/-- Equivalent closed-substack models have the same certified dimension. -/
private theorem dimension_eq_of_eqvGen
    {Z W : IntegralClosedDMSubstack X}
    (h : Relation.EqvGen
      (@IntegralClosedDMSubstack.ModelEquivalent X) Z W) :
    Z.dimension = W.dimension := by
  exact Relation.EqvGen.eqvGen_le
    (r' := fun A B : IntegralClosedDMSubstack X ↦ A.dimension = B.dimension)
    (by
      intro A B hAB
      exact hAB.choose_spec.2) Z W h

/-- Dimension descends to the quotient of equivalent closed-substack presentations. -/
def dimension : StackCycleGenerator X → ℤ :=
  Quotient.lift (fun Z : IntegralClosedDMSubstack X ↦ Z.dimension)
    (fun _ _ h ↦ dimension_eq_of_eqvGen h)

@[simp]
theorem dimension_mk (Z : IntegralClosedDMSubstack X) :
    dimension (mk Z) = Z.dimension :=
  rfl

@[simp]
theorem mk_representative (Z : StackCycleGenerator X) :
    mk Z.representative = Z :=
  Quotient.out_eq Z

@[simp]
theorem representative_dimension (Z : StackCycleGenerator X) :
    Z.representative.dimension = Z.dimension := by
  rw [← dimension_mk Z.representative, mk_representative]

/-- The generator of the whole integral stack is independent of the etale atlas used to prove
integrality and local Noetherianity. -/
theorem mk_whole_independent
    (X : DeligneMumfordStack.{u})
    (A B : StackChart X.toStack)
    (hA : A.IsEtaleSurjective) (hB : B.IsEtaleSurjective)
    [aIntegral : _root_.AlgebraicGeometry.IsIntegral A.scheme]
    [aNoetherian : _root_.AlgebraicGeometry.IsNoetherian A.scheme]
    [bIntegral : _root_.AlgebraicGeometry.IsIntegral B.scheme]
    [bNoetherian : _root_.AlgebraicGeometry.IsNoetherian B.scheme]
    (d : ℤ) (pure : PureStackDimension X.toAlgebraicStack d) :
    mk (IntegralClosedDMSubstack.whole X A hA d pure) =
      mk (IntegralClosedDMSubstack.whole X B hB d pure) := by
  apply mk_eq_of_modelEquivalent
  refine ⟨StackEquivalenceData.refl X.toStack, ?_, rfl⟩
  exact ⟨StackIso2.leftUnitor
    (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor)⟩

/-- The chosen representative's integral atlas. -/
noncomputable def integralAtlas (Z : StackCycleGenerator X) :
    StackChart Z.representative.stack.toStack :=
  Z.representative.integralAtlas

noncomputable instance integralAtlas_integral (Z : StackCycleGenerator X) :
    _root_.AlgebraicGeometry.IsIntegral Z.integralAtlas.scheme :=
  Z.representative.integralAtlas_integral

noncomputable instance integralAtlas_locallyNoetherian (Z : StackCycleGenerator X) :
    _root_.AlgebraicGeometry.IsLocallyNoetherian Z.integralAtlas.scheme :=
  Z.representative.integralAtlas_locallyNoetherian

noncomputable instance integralAtlas_noetherian (Z : StackCycleGenerator X) :
    _root_.AlgebraicGeometry.IsNoetherian Z.integralAtlas.scheme :=
  Z.representative.integralAtlas_noetherian

/-- The chosen representative's generic object. -/
noncomputable def genericObject (Z : StackCycleGenerator X) :
    StackFiber Z.representative.stack.toStack
      (_root_.AlgebraicGeometry.Spec
        (.of Z.integralAtlas.scheme.functionField)) :=
  Z.representative.genericObject

/-- The actual inertia group of the chosen representative at its generic atlas object. -/
abbrev genericInertia (Z : StackCycleGenerator X) :=
  Z.genericObject ⟶ Z.genericObject

/-- `Z` is contained in `W` when the closed immersion representing `Z` factors through the
closed immersion representing `W`, up to a 2-isomorphism over the ambient stack.  The quotient
generator has one fixed internal representative, so this predicate cannot distinguish two
equivalent presentations of the same substack. -/
def FactorsThrough (Z W : StackCycleGenerator X) : Prop :=
  ∃ factor : StackHom Z.representative.stack.toStack W.representative.stack.toStack,
    Nonempty (StackIso2
      (Pseudofunctor.StrongTrans.vcomp factor W.representative.inclusion)
      Z.representative.inclusion)

/-- An irreducible component is a maximal integral closed substack.  Integrality and closedness
are already part of every `StackCycleGenerator`; this predicate supplies precisely maximality,
instead of allowing a caller to choose a list of purported components. -/
def IsIrreducibleComponent (Z : StackCycleGenerator X) : Prop :=
  ∀ W : StackCycleGenerator X, Z.FactorsThrough W → W = Z

end StackCycleGenerator

/-- A principal-divisor generator: an actual integral closed DM substack together with a
nonzero rational function satisfying descent on its integral etale atlas.  The type is fixed by
`X`; a Chow presentation cannot replace it by `Empty`, omit a generator by withholding a
dimension proof, or use an unrelated private carrier. -/
structure StackRationalFunctionGenerator (X : DeligneMumfordStack.{u}) where
  substack : StackCycleGenerator X
  function : substack.representative.RationalFunction

namespace StackRationalFunctionGenerator

variable {X : DeligneMumfordStack.{u}} (g : StackRationalFunctionGenerator X)

/-- The Noetherian integral atlas on which the descended rational function is represented. -/
abbrev atlasScheme := g.substack.integralAtlas.scheme

/-- The finite scheme principal divisor on that atlas. -/
noncomputable def atlasDivisor : g.atlasScheme →₀ ℚ :=
  IntegralClosedDMSubstack.RationalFunction.atlasPrincipalFinsupp
    g.substack.representative g.function

/-- A nonzero prime of the atlas divisor. -/
abbrev AtlasSupport := {x : g.atlasScheme // x ∈ g.atlasDivisor.support}

theorem atlasSupport_ne_zero (x : g.AtlasSupport) : g.atlasDivisor x ≠ 0 :=
  Finsupp.mem_support_iff.mp x.property

/-- Two supported atlas primes joined at a codimension-one point of an integral overlap chart
have equal coefficients.  Generic evaluation under composition and etale invariance of order
are both derived above, so neither function-field nor order compatibility is an input. -/
theorem atlasDivisor_eq_of_overlap_point
    (x y : g.AtlasSupport)
    {T : Scheme.{u}} [ti : _root_.AlgebraicGeometry.IsIntegral T]
    [tn : _root_.AlgebraicGeometry.IsLocallyNoetherian T]
    (m : T ⟶ g.substack.representative.integralAtlasSelfOverlap.space)
    [fstDominant : _root_.AlgebraicGeometry.IsDominant
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.fst)]
    [sndDominant : _root_.AlgebraicGeometry.IsDominant
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.snd)]
    [fstEtale : _root_.AlgebraicGeometry.Etale
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.fst)]
    [sndEtale : _root_.AlgebraicGeometry.Etale
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.snd)]
    (t : T)
    (ht : coheight t = 1)
    (hfstPoint : (m ≫ g.substack.representative.integralAtlasSelfOverlap.fst).base t = x.1)
    (hsndPoint : (m ≫ g.substack.representative.integralAtlasSelfOverlap.snd).base t = y.1) :
    g.atlasDivisor x = g.atlasDivisor y := by
  have hxheight : coheight x.1 = 1 := by
    by_contra hxheight
    apply g.atlasSupport_ne_zero x
    change (g.substack.representative.integralAtlas.scheme.ord
      (g.substack.representative.rationalMapValue g.function.map) x.1 : ℚ) = 0
    rw [g.substack.representative.integralAtlas.scheme.ord_eq_zero_of_coheight_neq_one
      hxheight]
    norm_num
  have hyheight : coheight y.1 = 1 := by
    by_contra hyheight
    apply g.atlasSupport_ne_zero y
    change (g.substack.representative.integralAtlas.scheme.ord
      (g.substack.representative.rationalMapValue g.function.map) y.1 : ℚ) = 0
    rw [g.substack.representative.integralAtlas.scheme.ord_eq_zero_of_coheight_neq_one
      hyheight]
    norm_num
  have hxorder : g.atlasDivisor x =
      (T.ord (IntegralClosedDMSubstack.rationalMapGenericValue
        ((m ≫ g.substack.representative.integralAtlasSelfOverlap.fst).toRationalMap.comp
          g.function.map)) t : ℚ) := by
    change (g.substack.representative.integralAtlas.scheme.ord
      (g.substack.representative.rationalMapValue g.function.map) x.1 : ℚ) = _
    have hfstValue := IntegralClosedDMSubstack.rationalMapGenericValue_comp_etale
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.fst) t g.function.map
    rw [hfstValue]
    have hfstHeight :
        coheight ((m ≫ g.substack.representative.integralAtlasSelfOverlap.fst).base t) = 1 := by
      rw [hfstPoint]
      exact hxheight
    have h := _root_.AlgebraicGeometry.Scheme.ord_etaleLocalFunctionFieldMap
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.fst) t
      ht hfstHeight (g.substack.representative.rationalMapValue g.function.map)
    rw [hfstPoint] at h
    exact_mod_cast h.symm
  have hyorder : g.atlasDivisor y =
      (T.ord (IntegralClosedDMSubstack.rationalMapGenericValue
        ((m ≫ g.substack.representative.integralAtlasSelfOverlap.snd).toRationalMap.comp
          g.function.map)) t : ℚ) := by
    change (g.substack.representative.integralAtlas.scheme.ord
      (g.substack.representative.rationalMapValue g.function.map) y.1 : ℚ) = _
    have hsndValue := IntegralClosedDMSubstack.rationalMapGenericValue_comp_etale
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.snd) t g.function.map
    rw [hsndValue]
    have hsndHeight :
        coheight ((m ≫ g.substack.representative.integralAtlasSelfOverlap.snd).base t) = 1 := by
      rw [hsndPoint]
      exact hyheight
    have h := _root_.AlgebraicGeometry.Scheme.ord_etaleLocalFunctionFieldMap
      (m ≫ g.substack.representative.integralAtlasSelfOverlap.snd) t
      ht hsndHeight (g.substack.representative.rationalMapValue g.function.map)
    rw [hsndPoint] at h
    exact_mod_cast h.symm
  rw [hxorder, hyorder]
  exact_mod_cast congrArg (fun a ↦ T.ord a t)
    (IntegralClosedDMSubstack.RationalFunction.overlapPullbackValue_eq
      g.substack.representative g.function m)

end StackRationalFunctionGenerator

/-
Retired provisional stack divisor descent and Chow quotient.  The code below constructs useful
coefficient descent once dense-image certificates are present, but there is not yet a theorem
producing such a certificate for every rational function.  Consequently its relation space can
be too small and must not be exposed as Vistoli Chow.  The active part of this file stops with
the actual stack-cycle generators, rational functions, and their atlas divisors.

/-- The dense stack-theoretic image of one prime in the atlas divisor.  Its generic residue
field point is identified, inside the ambient stack, with a dominant generic point of the
displayed integral closed substack.  Thus `image` cannot be an unrelated cycle label. -/
structure StackDivisorPrimeImage
    {X : DeligneMumfordStack.{u}} (g : StackRationalFunctionGenerator X)
    (x : g.AtlasSupport) where
  image : StackCycleGenerator X
  genericMap :
    _root_.AlgebraicGeometry.Spec (g.atlasScheme.residueField x.1) ⟶
      image.integralAtlas.scheme
  genericMap_dominant : _root_.AlgebraicGeometry.IsDominant genericMap
  comparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom (g.atlasScheme.fromSpecResidueField x.1))
        g.substack.integralAtlas.map)
      g.substack.representative.inclusion)
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom genericMap) image.integralAtlas.map)
      image.representative.inclusion)
  image_dimension : image.dimension = g.substack.dimension - 1

/-- Concrete overlap geometry joining two supported atlas primes.  The witness contains an
actual integral locally Noetherian scheme, an actual map to the represented self-overlap, and a
codimension-one point mapping to the two specified primes.  The etale and dominant hypotheses
are precisely those consumed by the local-order comparison theorem above. -/
structure StackDivisorPrimeConnection
    {X : DeligneMumfordStack.{u}} (g : StackRationalFunctionGenerator X)
    (x y : g.AtlasSupport) where
  scheme : Scheme.{u}
  [integral : _root_.AlgebraicGeometry.IsIntegral scheme]
  [locallyNoetherian : _root_.AlgebraicGeometry.IsLocallyNoetherian scheme]
  map : scheme ⟶ g.substack.representative.integralAtlasSelfOverlap.space
  [fstDominant : _root_.AlgebraicGeometry.IsDominant
    (map ≫ g.substack.representative.integralAtlasSelfOverlap.fst)]
  [sndDominant : _root_.AlgebraicGeometry.IsDominant
    (map ≫ g.substack.representative.integralAtlasSelfOverlap.snd)]
  [fstEtale : _root_.AlgebraicGeometry.Etale
    (map ≫ g.substack.representative.integralAtlasSelfOverlap.fst)]
  [sndEtale : _root_.AlgebraicGeometry.Etale
    (map ≫ g.substack.representative.integralAtlasSelfOverlap.snd)]
  point : scheme
  point_coheight : coheight point = 1
  fst_point :
    (map ≫ g.substack.representative.integralAtlasSelfOverlap.fst).base point = x.1
  snd_point :
    (map ≫ g.substack.representative.integralAtlasSelfOverlap.snd).base point = y.1

attribute [instance] StackDivisorPrimeConnection.integral
  StackDivisorPrimeConnection.locallyNoetherian
  StackDivisorPrimeConnection.fstDominant
  StackDivisorPrimeConnection.sndDominant
  StackDivisorPrimeConnection.fstEtale
  StackDivisorPrimeConnection.sndEtale

/-- Geometric dense images of the finitely many nonzero atlas valuations, together with concrete
overlap witnesses joining any two primes with the same dense image.  No coefficient or
equality-of-orders assertion is stored: equality is proved below from each witness. -/
structure StackPrincipalDivisorGeometry
    {X : DeligneMumfordStack.{u}} (g : StackRationalFunctionGenerator X) where
  primeImage (x : g.AtlasSupport) : StackDivisorPrimeImage g x
  sameImageConnection (x y : g.AtlasSupport)
      (h : (primeImage x).image = (primeImage y).image) :
    StackDivisorPrimeConnection g x y

namespace StackPrincipalDivisorGeometry

variable {X : DeligneMumfordStack.{u}} {g : StackRationalFunctionGenerator X}

local instance : DecidableEq (StackCycleGenerator X) :=
  Classical.decEq _

/-- The image of a supported atlas prime. -/
noncomputable def supportImage (G : StackPrincipalDivisorGeometry g)
    (x : g.AtlasSupport) : StackCycleGenerator X :=
  (G.primeImage x).image

/-- The finite set of stack-prime images occurring in the divisor. -/
noncomputable def imageFinset (G : StackPrincipalDivisorGeometry g) :
    Finset (StackCycleGenerator X) := by
  classical
  exact Finset.univ.image G.supportImage

private theorem supportImage_mem_imageFinset
    (G : StackPrincipalDivisorGeometry g) (x : g.AtlasSupport) :
    G.supportImage x ∈ G.imageFinset := by
  classical
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem imageFinset_dimension (G : StackPrincipalDivisorGeometry g)
    {W : StackCycleGenerator X} (hW : W ∈ G.imageFinset) :
    W.dimension = g.substack.dimension - 1 := by
  classical
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hW
  exact (G.primeImage x).image_dimension

/-- The finite fibre of supported atlas primes having a specified dense stack image. -/
noncomputable def fiberFinset (G : StackPrincipalDivisorGeometry g)
    (W : StackCycleGenerator X) : Finset g.AtlasSupport := by
  classical
  exact Finset.univ.filter (fun x ↦ G.supportImage x = W)

@[simp]
theorem mem_fiberFinset (G : StackPrincipalDivisorGeometry g)
    (W : StackCycleGenerator X) (x : g.AtlasSupport) :
    x ∈ G.fiberFinset W ↔ G.supportImage x = W := by
  classical
  simp [fiberFinset]

/-- Every image-support prime has a nonempty finite fibre above it. -/
theorem fiberFinset_nonempty (G : StackPrincipalDivisorGeometry g)
    {W : StackCycleGenerator X} (hW : W ∈ G.imageFinset) :
    (G.fiberFinset W).Nonempty := by
  classical
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hW
  exact ⟨x, (G.mem_fiberFinset W x).mpr hx⟩

private theorem fiberFinset_eq_empty_of_not_mem_imageFinset
    (G : StackPrincipalDivisorGeometry g) {W : StackCycleGenerator X}
    (hW : W ∉ G.imageFinset) : G.fiberFinset W = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hW
  exact Finset.mem_image.mpr
    ⟨x, Finset.mem_univ _, (G.mem_fiberFinset W x).mp hx⟩

/-- Concrete overlap connectivity proves equality of the two atlas orders above a common dense
stack image. -/
theorem atlasDivisor_eq_of_supportImage_eq (G : StackPrincipalDivisorGeometry g)
    (x y : g.AtlasSupport) (h : G.supportImage x = G.supportImage y) :
    g.atlasDivisor x = g.atlasDivisor y := by
  let C := G.sameImageConnection x y h
  exact g.atlasDivisor_eq_of_overlap_point x y C.map C.point
    C.point_coheight C.fst_point C.snd_point

/-- A supported atlas prime chosen from a nonempty fibre.  Its coefficient is independent of
this choice by `atlasDivisor_eq_of_supportImage_eq`. -/
private noncomputable def fiberRepresentative (G : StackPrincipalDivisorGeometry g)
    (W : StackCycleGenerator X) (hW : W ∈ G.imageFinset) : g.AtlasSupport :=
  (G.fiberFinset_nonempty hW).choose

private theorem fiberRepresentative_mem (G : StackPrincipalDivisorGeometry g)
    (W : StackCycleGenerator X) (hW : W ∈ G.imageFinset) :
    G.fiberRepresentative W hW ∈ G.fiberFinset W :=
  (G.fiberFinset_nonempty hW).choose_spec

/-- The coefficient of a stack prime is the order at any supported atlas prime with that dense
image.  Independence of the internal representative is a theorem from overlap descent, rather
than an averaging convention. -/
noncomputable def coefficient (G : StackPrincipalDivisorGeometry g)
    (W : StackCycleGenerator X) : ℚ :=
  if hW : W ∈ G.imageFinset then
    g.atlasDivisor (G.fiberRepresentative W hW)
  else 0

theorem coefficient_eq_zero_of_not_mem_imageFinset
    (G : StackPrincipalDivisorGeometry g) {W : StackCycleGenerator X}
    (hW : W ∉ G.imageFinset) : G.coefficient W = 0 := by
  simp [coefficient, hW]

/-- At every supported prime over `W`, the constructed coefficient is its actual atlas order. -/
theorem coefficient_eq_atlasDivisor (G : StackPrincipalDivisorGeometry g)
    {W : StackCycleGenerator X} (hW : W ∈ G.imageFinset)
    (x : g.AtlasSupport) (hx : x ∈ G.fiberFinset W) :
    G.coefficient W = g.atlasDivisor x := by
  rw [coefficient, dif_pos hW]
  apply G.atlasDivisor_eq_of_supportImage_eq
  exact ((G.mem_fiberFinset W (G.fiberRepresentative W hW)).mp
    (G.fiberRepresentative_mem W hW)).trans
      ((G.mem_fiberFinset W x).mp hx).symm

/-- The descended principal divisor.  Its finite support and every coefficient are constructed
from the atlas principal cycle and dense-image geometry. -/
noncomputable def cycle (G : StackPrincipalDivisorGeometry g) :
    StackCycleGenerator X →₀ ℚ := by
  classical
  exact Finsupp.onFinset G.imageFinset G.coefficient (by
    intro W hnonzero
    by_cases hW : W ∈ G.imageFinset
    · exact hW
    · exact (hnonzero (G.coefficient_eq_zero_of_not_mem_imageFinset hW)).elim)

/-- At an image-support prime, the constructed cycle has the order at every atlas prime above
that image. -/
@[simp]
theorem cycle_apply_image (G : StackPrincipalDivisorGeometry g)
    {W : StackCycleGenerator X} (hW : W ∈ G.imageFinset)
    (x : g.AtlasSupport) (hx : x ∈ G.fiberFinset W) :
    G.cycle W = g.atlasDivisor x := by
  classical
  rw [cycle, Finsupp.onFinset_apply]
  exact G.coefficient_eq_atlasDivisor hW x hx

/-- The constructed divisor is concentrated in codimension one inside its integral source
substack.  Homogeneity follows from the dimensions of the dense prime images rather than from a
caller-supplied premise. -/
theorem cycle_dimension (G : StackPrincipalDivisorGeometry g) :
    ∀ W : StackCycleGenerator X,
      W.dimension ≠ g.substack.dimension - 1 → G.cycle W = 0 := by
  intro W hdimension
  classical
  by_cases hW : W ∈ G.imageFinset
  · exact (hdimension (G.imageFinset_dimension hW)).elim
  · rw [cycle, Finsupp.onFinset_apply]
    exact G.coefficient_eq_zero_of_not_mem_imageFinset hW

end StackPrincipalDivisorGeometry

/-- A stack principal divisor is a rational function together with concrete dense-image and
overlap descent geometry.  Rational equivalence below ranges over *all* such certificates, so a
Chow presentation cannot select a favorable geometry or omit another certified divisor. -/
structure StackPrincipalDivisorCertificate (X : DeligneMumfordStack.{u}) where
  function : StackRationalFunctionGenerator X
  geometry : StackPrincipalDivisorGeometry function

/-- Geometric generators and principal divisors for Vistoli's cycle complex on a separated DM
stack.  The integral-substack carrier and its dimension function are fixed by geometry below. -/
structure VistoliCyclePresentation (X : DeligneMumfordStack.{u}) where
  /-- Vistoli's rational Chow theory is used on separated Deligne--Mumford stacks. -/
  separated : DiagonalHasProperty X.toStack
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})

namespace VistoliCyclePresentation

variable {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)

/-- The Chow presentation is canonically determined by separatedness: its generators and
relations range over intrinsic closed substacks and all certified principal divisors. -/
theorem ofSeparated
    (h : DiagonalHasProperty X.toStack
      (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})) :
    VistoliCyclePresentation X :=
  ⟨h⟩

/-- The principal divisor constructed from a rational function and its concrete dense-image
descent certificate. -/
noncomputable def divisor (_V : VistoliCyclePresentation X)
    (g : StackPrincipalDivisorCertificate X) :
    StackCycleGenerator X →₀ ℚ :=
  g.geometry.cycle

/-- The cycle basis is fixed once `X` is fixed; it is not selected by `V`. -/
abbrev IntegralClosedSubstack (_V : VistoliCyclePresentation X) :=
  StackCycleGenerator X

/-- Geometrically certified dimension of an integral closed substack. -/
abbrev dimension (_V : VistoliCyclePresentation X)
    (Z : StackCycleGenerator X) : ℤ := Z.dimension

/-- Rational cycles concentrated in stack dimension `i`. -/
def cycles (i : ℤ) : Submodule ℚ
    (V.IntegralClosedSubstack →₀ ℚ) where
  carrier := {z | ∀ Z, V.dimension Z ≠ i → z Z = 0}
  zero_mem' Z _ := by simp
  add_mem' ha hb Z hZ := by simp [ha Z hZ, hb Z hZ]
  smul_mem' q z hz Z hZ := by simp [hz Z hZ]

/-- The principal divisor in its forced codimension-one grading. -/
noncomputable def divisorCycle (g : StackPrincipalDivisorCertificate X) :
    V.cycles (g.function.substack.dimension - 1) :=
  ⟨V.divisor g, g.geometry.cycle_dimension⟩

/-- The dimension-graded cycle supported with coefficient one on a single integral closed
substack. -/
def point {i : ℤ} (Z : V.IntegralClosedSubstack) (hZ : V.dimension Z = i) :
    V.cycles i := by
  classical
  refine ⟨Finsupp.single Z 1, ?_⟩
  intro W hW
  by_cases h : W = Z
  · subst W
    exact (hW hZ).elim
  · simp [h]

@[simp]
theorem point_apply_self {i : ℤ} (Z : V.IntegralClosedSubstack)
    (hZ : V.dimension Z = i) :
    (V.point Z hZ :
      V.IntegralClosedSubstack →₀ ℚ) Z = 1 := by
  simp [point]

@[simp]
theorem point_apply_of_ne {i : ℤ} (Z W : V.IntegralClosedSubstack)
    (hZ : V.dimension Z = i) (h : W ≠ Z) :
    (V.point Z hZ :
      V.IntegralClosedSubstack →₀ ℚ) W = 0 := by
  simp [point, h]

/-- The ungraded rational-equivalence space generated by every constructed stack principal
divisor. -/
def totalRelations : Submodule ℚ (V.IntegralClosedSubstack →₀ ℚ) :=
  Submodule.span ℚ (Set.range V.divisor)

/-- A principal-divisor generator whose forced codimension-one degree is `i`. -/
abbrev GradedRationalFunctionGenerator (i : ℤ) :=
  {g : StackPrincipalDivisorCertificate X //
    g.function.substack.dimension - 1 = i}

/-- A principal divisor placed in its certified degree. -/
noncomputable def gradedDivisor {i : ℤ}
    (g : GradedRationalFunctionGenerator (X := X) i) : V.cycles i :=
  g.property ▸ V.divisorCycle g.1

/-- Dimension-`i` rational equivalence is generated directly by the principal divisors whose
geometrically forced degree is `i`.  This graded presentation makes it possible to prove that a
cycle operation descends by checking actual divisor generators, rather than assuming an opaque
inclusion between two relation submodules. -/
def relations (i : ℤ) : Submodule ℚ (V.cycles i) :=
  Submodule.span ℚ (Set.range V.gradedDivisor)

/-- Vistoli's dimension-graded rational Chow group. -/
abbrev chow (i : ℤ) := V.cycles i ⧸ V.relations i

/-- Quotient a cycle by rational equivalence. -/
abbrev quotientMap (i : ℤ) : V.cycles i →ₗ[ℚ] V.chow i :=
  (V.relations i).mkQ

/-- Transport a Chow class along equality of dimension indices. -/
def cast {i j : ℤ} (h : i = j) : V.chow i →ₗ[ℚ] V.chow j := by
  subst j
  exact LinearMap.id

/-- Transport a cycle along equality of dimension indices. -/
def cyclesCast {i j : ℤ} (h : i = j) : V.cycles i →ₗ[ℚ] V.cycles j := by
  subst j
  exact LinearMap.id

@[simp]
theorem coe_cyclesCast {i j : ℤ} (h : i = j) (z : V.cycles i) :
    ((V.cyclesCast h z : V.cycles j) : V.IntegralClosedSubstack →₀ ℚ) = z := by
  subst j
  rfl

@[simp]
theorem cyclesCast_apply_self {i : ℤ} (h : i = i) (z : V.cycles i) :
    V.cyclesCast h z = z := by
  rw [Subsingleton.elim h rfl]
  rfl

@[simp]
theorem quotientMap_cyclesCast {i j : ℤ} (h : i = j) (z : V.cycles i) :
    V.quotientMap j (V.cyclesCast h z) = V.cast h (V.quotientMap i z) := by
  subst j
  rfl

theorem cyclesCast_mem_relations {i j : ℤ} (h : i = j) (z : V.cycles i) :
    V.cyclesCast h z ∈ V.relations j ↔ z ∈ V.relations i := by
  subst j
  simp

@[simp]
theorem cast_rfl (i : ℤ) : V.cast (rfl : i = i) = LinearMap.id :=
  rfl

/-- Proof irrelevance makes transport along any self-equality act as the identity. -/
@[simp]
theorem cast_apply_self {i : ℤ} (h : i = i) (z : V.chow i) : V.cast h z = z := by
  rw [Subsingleton.elim h rfl]
  rfl

@[simp]
theorem cast_cast {i j k : ℤ} (h : i = j) (h' : j = k) (z : V.chow i) :
    V.cast h' (V.cast h z) = V.cast (h.trans h') z := by
  subst j
  subst k
  rfl

@[simp]
theorem quotientMap_divisor (g : StackPrincipalDivisorCertificate X) :
    V.quotientMap (g.function.substack.dimension - 1) (V.divisorCycle g) = 0 := by
  change (Submodule.Quotient.mk
    (V.divisorCycle g) : V.chow (g.function.substack.dimension - 1)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Set.mem_range_self
    (⟨g, rfl⟩ : GradedRationalFunctionGenerator (X := X)
      (g.function.substack.dimension - 1)))

/-- Every displayed graded principal divisor belongs to rational equivalence. -/
theorem gradedDivisor_mem_relations {i : ℤ}
    (g : GradedRationalFunctionGenerator (X := X) i) :
    V.gradedDivisor g ∈ V.relations i :=
  Submodule.subset_span (Set.mem_range_self g)

/-- A linear cycle operation preserves rational equivalence once it carries every actual
graded principal-divisor generator into the target relation space. -/
theorem mapsRelations_of_maps_gradedDivisors
    {Y : DeligneMumfordStack.{u}} (W : VistoliCyclePresentation Y)
    {i j : ℤ} (L : V.cycles i →ₗ[ℚ] W.cycles j)
    (hL : ∀ g : GradedRationalFunctionGenerator (X := X) i,
      L (V.gradedDivisor g) ∈ W.relations j) :
    V.relations i ≤ Submodule.comap L (W.relations j) := by
  rw [relations, Submodule.span_le]
  rintro z ⟨g, rfl⟩
  exact hL g

/-- Fundamental cycle of an integral pure-dimensional DM stack.  It is the coefficient-one
cycle on the whole stack, built from the identity closed immersion rather than supplied as an
arbitrary Chow class. -/
noncomputable def integralFundamentalCycle
    (atlas : StackChart X.toStack) (atlasEtaleSurjective : atlas.IsEtaleSurjective)
    [atlasIntegral : _root_.AlgebraicGeometry.IsIntegral atlas.scheme]
    [atlasNoetherian : _root_.AlgebraicGeometry.IsNoetherian atlas.scheme]
    (i : ℤ) (pureDimension : PureStackDimension X.toAlgebraicStack i) :
    V.cycles i :=
  V.point (StackCycleGenerator.mk
    (IntegralClosedDMSubstack.whole X atlas atlasEtaleSurjective i pureDimension)) rfl

/-- Chow class of the constructed integral fundamental cycle. -/
noncomputable def integralFundamentalClass
    (atlas : StackChart X.toStack) (atlasEtaleSurjective : atlas.IsEtaleSurjective)
    [atlasIntegral : _root_.AlgebraicGeometry.IsIntegral atlas.scheme]
    [atlasNoetherian : _root_.AlgebraicGeometry.IsNoetherian atlas.scheme]
    (i : ℤ) (pureDimension : PureStackDimension X.toAlgebraicStack i) :
    V.chow i :=
  V.quotientMap i (V.integralFundamentalCycle atlas atlasEtaleSurjective i pureDimension)

end VistoliCyclePresentation

/-- An etale-atlas presentation of the generic local ring along an integral component.  The
chosen point is an actual generic point of a Noetherian atlas, and its residual object is
identified with a dominant generic object of the displayed component inside the ambient stack.
Consequently its local-ring length is geometric data of the ambient stack, rather than a
caller-supplied numerical multiplicity. -/
structure StackComponentGenericPresentation
    (X : DeligneMumfordStack.{u}) (Z : StackCycleGenerator X) where
  atlas : StackChart X.toStack
  atlas_etaleSurjective : atlas.IsEtaleSurjective
  [atlas_noetherian : _root_.AlgebraicGeometry.IsNoetherian atlas.scheme]
  point : atlas.scheme
  point_isGeneric : IsMax point
  genericMap :
    _root_.AlgebraicGeometry.Spec (atlas.scheme.residueField point) ⟶
      Z.integralAtlas.scheme
  genericMap_dominant : _root_.AlgebraicGeometry.IsDominant genericMap
  comparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom (atlas.scheme.fromSpecResidueField point)) atlas.map)
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        (FppfStack.mapOfSchemeHom genericMap) Z.integralAtlas.map)
      Z.representative.inclusion)

attribute [instance] StackComponentGenericPresentation.atlas_noetherian

namespace StackComponentGenericPresentation

variable {X : DeligneMumfordStack.{u}} {Z : StackCycleGenerator X}

noncomputable instance atlas_locallyNoetherian
    (P : StackComponentGenericPresentation X Z) :
    _root_.AlgebraicGeometry.IsLocallyNoetherian P.atlas.scheme :=
  P.atlas_noetherian.toIsLocallyNoetherian

/-- The generic multiplicity read from the ambient atlas local ring. -/
noncomputable def multiplicity (P : StackComponentGenericPresentation X Z) : ℕ :=
  P.atlas.scheme.genericLength P.point

/-- An honest generic presentation always has positive multiplicity. -/
theorem multiplicity_pos (P : StackComponentGenericPresentation X Z) :
    0 < P.multiplicity :=
  P.atlas.scheme.genericLength_pos P.point P.point_isGeneric

end StackComponentGenericPresentation

/-
Retired provisional general stack-cycle and operation packages.  The former
`StackFundamentalCycleGeometry`, `ProperPushforward`, `FlatPullback`, and `ProperDegree` records
accepted component-existence, atlas-independence, divisor preservation, or degree descent as
fields.  They are inactive until those results are proved from stack geometry.  The actual stack
cycle type, certified principal-divisor quotient, and the integral pure-stack fundamental class
constructed above remain active.

/-- The geometric facts needed to form the fundamental cycle of a possibly nonreduced,
reducible pure-dimensional Deligne--Mumford stack.  It certifies finiteness and purity of the
actual maximal integral closed substacks and supplies honest generic atlas presentations, but
it cannot provide coefficients or an arbitrary Chow class.  Multiplicities are computed as
generic local-ring lengths. -/
structure StackFundamentalCycleGeometry
    (X : DeligneMumfordStack.{u}) (i : ℤ) : Prop where
  components_finite :
    Set.Finite {Z : StackCycleGenerator X | Z.IsIrreducibleComponent}
  /-- Every integral closed substack lies in a maximal one.  This prevents a nonempty stack
  from being assigned an empty component set merely to make its fundamental cycle zero. -/
  components_cover : ∀ W : StackCycleGenerator X,
    ∃ Z : StackCycleGenerator X, Z.IsIrreducibleComponent ∧ W.FactorsThrough Z
  component_dimension : ∀ Z : StackCycleGenerator X,
    Z.IsIrreducibleComponent → Z.dimension = i
  /-- Every component is reached by a generic point of an actual Noetherian etale atlas of the
  ambient stack. -/
  genericPresentation_exists (Z : StackCycleGenerator X) :
    Z.IsIrreducibleComponent → Nonempty (StackComponentGenericPresentation X Z)
  /-- Etale invariance of generic local-ring length.  This is a uniqueness property of honest
  atlas presentations, not a selectable coefficient. -/
  genericLength_compatible (Z : StackCycleGenerator X)
      (hZ : Z.IsIrreducibleComponent)
      (P Q : StackComponentGenericPresentation X Z) :
    P.multiplicity = Q.multiplicity

namespace StackFundamentalCycleGeometry

variable {X : DeligneMumfordStack.{u}} {i : ℤ}

/-- An internally chosen honest generic presentation of an irreducible component. -/
noncomputable def genericPresentation (G : StackFundamentalCycleGeometry X i)
    (Z : StackCycleGenerator X) (hZ : Z.IsIrreducibleComponent) :
    StackComponentGenericPresentation X Z :=
  Classical.choice (G.genericPresentation_exists Z hZ)

/-- The component multiplicity, forced to be the length of the ambient local ring at a generic
atlas point. -/
noncomputable def multiplicity (G : StackFundamentalCycleGeometry X i)
    (Z : StackCycleGenerator X) (hZ : Z.IsIrreducibleComponent) : ℕ :=
  (G.genericPresentation Z hZ).multiplicity

theorem multiplicity_pos (G : StackFundamentalCycleGeometry X i)
    (Z : StackCycleGenerator X) (hZ : Z.IsIrreducibleComponent) :
    0 < G.multiplicity Z hZ :=
  (G.genericPresentation Z hZ).multiplicity_pos

/-- The ungraded generic-length-weighted sum of all irreducible components. -/
noncomputable def rawCycle (G : StackFundamentalCycleGeometry X i) :
    StackCycleGenerator X →₀ ℚ := by
  classical
  let components : Finset (StackCycleGenerator X) := G.components_finite.toFinset
  let componentCoefficients : StackCycleGenerator X → ℚ :=
    fun Z ↦ if hZ : Z.IsIrreducibleComponent then (G.multiplicity Z hZ : ℚ) else 0
  have supportContained : ∀ Z, componentCoefficients Z ≠ 0 → Z ∈ components := by
    intro Z hnonzero
    by_cases hcomponent : Z.IsIrreducibleComponent
    · simpa [components] using hcomponent
    · simp [componentCoefficients, hcomponent] at hnonzero
  exact Finsupp.onFinset components componentCoefficients supportContained

/-- The coefficient at an irreducible component is its generic local-ring length. -/
@[simp]
theorem rawCycle_apply_of_component (G : StackFundamentalCycleGeometry X i)
    (Z : StackCycleGenerator X) (hZ : Z.IsIrreducibleComponent) :
    G.rawCycle Z = (G.multiplicity Z hZ : ℚ) := by
  classical
  simp [rawCycle, hZ]

/-- Non-components have coefficient zero. -/
@[simp]
theorem rawCycle_apply_of_not_component (G : StackFundamentalCycleGeometry X i)
    (Z : StackCycleGenerator X) (hZ : ¬ Z.IsIrreducibleComponent) :
    G.rawCycle Z = 0 := by
  classical
  simp [rawCycle, hZ]

/-- Every irreducible component genuinely occurs with nonzero coefficient. -/
theorem rawCycle_apply_ne_zero (G : StackFundamentalCycleGeometry X i)
    (Z : StackCycleGenerator X) (hZ : Z.IsIrreducibleComponent) :
    G.rawCycle Z ≠ 0 := by
  rw [G.rawCycle_apply_of_component Z hZ]
  exact_mod_cast (ne_of_gt (G.multiplicity_pos Z hZ))

/-- The generic-length-weighted sum of all irreducible components.  Its support is forced by
geometric maximality and finiteness, while its coefficients are forced by ambient local-ring
lengths. -/
noncomputable def cycle (G : StackFundamentalCycleGeometry X i)
    (V : VistoliCyclePresentation X) : V.cycles i := by
  classical
  refine ⟨G.rawCycle, ?_⟩
  intro Z hdimension
  by_cases hcomponent : Z.IsIrreducibleComponent
  · exact (hdimension (G.component_dimension Z hcomponent)).elim
  · simp [rawCycle, hcomponent]

/-- The canonical Chow class of the generic-length-weighted fundamental cycle. -/
noncomputable def fundamentalClass (G : StackFundamentalCycleGeometry X i)
    (V : VistoliCyclePresentation X) : V.chow i :=
  V.quotientMap i (G.cycle V)

end StackFundamentalCycleGeometry

/-- A grading-respecting operation on stack cycles which preserves rational equivalence. -/
structure StackChowMap
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (i j : ℤ) where
  onCycles : VX.cycles i →ₗ[ℚ] VY.cycles j
  mapsRelations : VX.relations i ≤ Submodule.comap onCycles (VY.relations j)

namespace StackChowMap

variable {X Y Z : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
  {VZ : VistoliCyclePresentation Z} {i j k : ℤ}

@[ext]
theorem ext {f g : StackChowMap VX VY i j} (h : f.onCycles = g.onCycles) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The induced rational-linear map on Chow groups. -/
def induced (f : StackChowMap VX VY i j) : VX.chow i →ₗ[ℚ] VY.chow j :=
  Submodule.mapQ (VX.relations i) (VY.relations j) f.onCycles f.mapsRelations

@[simp]
theorem induced_quotientMap (f : StackChowMap VX VY i j) (z : VX.cycles i) :
    f.induced (VX.quotientMap i z) = VY.quotientMap j (f.onCycles z) :=
  rfl

/-- Identity operation. -/
def id (V : VistoliCyclePresentation X) (i : ℤ) : StackChowMap V V i i where
  onCycles := LinearMap.id
  mapsRelations := by intro z hz; exact hz

/-- Composition of operations preserving rational equivalence. -/
def comp (g : StackChowMap VY VZ j k) (f : StackChowMap VX VY i j) :
    StackChowMap VX VZ i k where
  onCycles := g.onCycles.comp f.onCycles
  mapsRelations := by
    intro z hz
    exact g.mapsRelations (f.mapsRelations hz)

@[simp]
theorem induced_id (V : VistoliCyclePresentation X) (i : ℤ) :
    (id V i).induced = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨z⟩
  rfl

@[simp]
theorem induced_comp (g : StackChowMap VY VZ j k) (f : StackChowMap VX VY i j) :
    (comp g f).induced = g.induced.comp f.induced := by
  apply LinearMap.ext
  rintro ⟨z⟩
  rfl

end StackChowMap

/-
Retired provisional comparison APIs.  `VistoliPresentationComparison` became unnecessary once a
presentation retained only separatedness, while `VistoliSchemeComparison` merely stored the
scheme/stack cycle equivalence and both directions of relation preservation.  The former is
replaced by canonical equality transport below; the latter remains a theorem to construct.

/-- Comparison of two atlas presentations of the same Vistoli Chow theory.  The cycle
equivalence preserves rational-equivalence subspaces and induces the displayed equivalence on
quotients. -/
structure VistoliPresentationComparison
    {X : DeligneMumfordStack.{u}}
    (V W : VistoliCyclePresentation X) where
  cyclesIso (i : ℤ) : V.cycles i ≃ₗ[ℚ] W.cycles i
  relations_forward (i : ℤ) :
    V.relations i ≤ Submodule.comap (cyclesIso i).toLinearMap (W.relations i)
  relations_backward (i : ℤ) :
    W.relations i ≤ Submodule.comap (cyclesIso i).symm.toLinearMap (V.relations i)

namespace VistoliPresentationComparison

variable {X : DeligneMumfordStack.{u}} {V W : VistoliCyclePresentation X}

/-- The cycle equivalence carries the rational-equivalence subspace exactly onto the other
presentation's relation subspace. -/
theorem relations_map_eq (e : VistoliPresentationComparison V W) (i : ℤ) :
    Submodule.map (e.cyclesIso i).toLinearMap (V.relations i) = W.relations i := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact e.relations_forward i
  · rw [Submodule.map_equiv_eq_comap_symm]
    exact e.relations_backward i

/-- The quotient equivalence is constructed from the cycle equivalence and exact transport of
the relation subspaces; it is not independent comparison data. -/
noncomputable def chowIso (e : VistoliPresentationComparison V W) (i : ℤ) :
    V.chow i ≃ₗ[ℚ] W.chow i :=
  Submodule.Quotient.equiv (V.relations i) (W.relations i)
    (e.cyclesIso i) (e.relations_map_eq i)

@[simp]
theorem quotient_compat (e : VistoliPresentationComparison V W)
    (i : ℤ) (z : V.cycles i) :
    e.chowIso i (V.quotientMap i z) = W.quotientMap i (e.cyclesIso i z) :=
  rfl

end VistoliPresentationComparison

/-- Agreement of the stack definition with the dimension-graded rational Chow group of a
scheme under the fully faithful represented-stack embedding. -/
structure VistoliSchemeComparison
    (S : Scheme.{u}) (dimension : DimensionFunction S)
    (R : RationalChowGrading S dimension)
    (V : VistoliCyclePresentation (FppfStack.ofSchemeDeligneMumfordStack S)) where
  cyclesIso (i : ℤ) : cyclesOfDimension S dimension i ≃ₗ[ℚ] V.cycles i
  relations_forward (i : ℤ) :
    (R i).relations ≤ Submodule.comap (cyclesIso i).toLinearMap (V.relations i)
  relations_backward (i : ℤ) :
    V.relations i ≤ Submodule.comap (cyclesIso i).symm.toLinearMap (R i).relations

namespace VistoliSchemeComparison

variable {S : Scheme.{u}} {dimension : DimensionFunction S}
  {R : RationalChowGrading S dimension}
  {V : VistoliCyclePresentation (FppfStack.ofSchemeDeligneMumfordStack S)}

/-- Agreement on cycles carries the canonical scheme rational-equivalence subspace exactly to
the stack relation subspace. -/
theorem relations_map_eq (e : VistoliSchemeComparison S dimension R V) (i : ℤ) :
    Submodule.map (e.cyclesIso i).toLinearMap (R i).relations = V.relations i := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact e.relations_forward i
  · rw [Submodule.map_equiv_eq_comap_symm]
    exact e.relations_backward i

/-- Scheme/stack Chow agreement is induced from the cycle equivalence and relation transport,
not supplied as a second unrelated equivalence. -/
noncomputable def chowIso (e : VistoliSchemeComparison S dimension R V) (i : ℤ) :
    R.group i ≃ₗ[ℚ] V.chow i :=
  Submodule.Quotient.equiv (R i).relations (V.relations i)
    (e.cyclesIso i) (e.relations_map_eq i)

@[simp]
theorem quotient_compat (e : VistoliSchemeComparison S dimension R V)
    (i : ℤ) (z : cyclesOfDimension S dimension i) :
    e.chowIso i ((R i).quotientMap z) = V.quotientMap i (e.cyclesIso i z) :=
  rfl

end VistoliSchemeComparison

-/

namespace VistoliCyclePresentation

variable {X : DeligneMumfordStack.{u}}

/-- Cycle groups attached to any two proofs of separatedness are canonically equivalent. -/
noncomputable def cyclesIso (V W : VistoliCyclePresentation X) (i : ℤ) :
    V.cycles i ≃ₗ[ℚ] W.cycles i := by
  rw [Subsingleton.elim V W]

/-- Chow groups attached to any two proofs of separatedness are canonically equivalent.  This
is equality transport, not an independently supplied relation-preservation comparison. -/
noncomputable def chowIso (V W : VistoliCyclePresentation X) (i : ℤ) :
    V.chow i ≃ₗ[ℚ] W.chow i := by
  rw [Subsingleton.elim V W]

@[simp]
theorem chowIso_quotientMap (V W : VistoliCyclePresentation X)
    (i : ℤ) (z : V.cycles i) :
    chowIso V W i (V.quotientMap i z) =
      W.quotientMap i (cyclesIso V W i z) := by
  rw [Subsingleton.elim V W]
  rfl

end VistoliCyclePresentation

/-- The stabilizer order is the cardinality of the actual generic inertia group.  A finiteness
proof is geometric data; the numerical value cannot be chosen independently. -/
noncomputable def genericStabilizerOrder
    {X : DeligneMumfordStack.{u}}
    (finite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia)
    (Z : StackCycleGenerator X) : ℕ := by
  letI := finite Z
  exact Fintype.card Z.genericInertia

theorem genericStabilizerOrder_pos
    {X : DeligneMumfordStack.{u}}
    (finite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia)
    (Z : StackCycleGenerator X) : 0 < genericStabilizerOrder finite Z := by
  let _ := finite Z
  let : Nonempty Z.genericInertia := ⟨𝟙 Z.genericObject⟩
  exact Fintype.card_pos

/-- The scheme-theoretic image data for one integral generator under a stack morphism.  The
factorization is tied to `f` by an invertible 2-cell, and the atlas map is dominant, so the
target is a dense integral closed image rather than an arbitrary closed overstack. -/
structure ProperGeneratorImage
    {X Y : DeligneMumfordStack.{u}} (f : StackHom X.toStack Y.toStack)
    (Z : StackCycleGenerator X) where
  image : StackCycleGenerator Y
  factor : StackHom Z.representative.stack.toStack image.representative.stack.toStack
  factorization : StackIso2
    (Pseudofunctor.StrongTrans.vcomp Z.representative.inclusion f)
    (Pseudofunctor.StrongTrans.vcomp factor image.representative.inclusion)
  atlasMap : Z.integralAtlas.scheme ⟶ image.integralAtlas.scheme
  atlasComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom atlasMap) image.integralAtlas.map)
    (Pseudofunctor.StrongTrans.vcomp Z.integralAtlas.map factor)
  atlasMap_dominant : _root_.AlgebraicGeometry.IsDominant atlasMap

/-- Transport a dense-image factorization across an invertible 2-cell on the ambient
morphism.  The image, factor, and dominant atlas map are unchanged; only the outer
factorization cell is whiskered. -/
noncomputable def ProperGeneratorImage.transport
    {X Y : DeligneMumfordStack.{u}} {f g : StackHom X.toStack Y.toStack}
    {Z : StackCycleGenerator X} (e : StackIso2 f g)
    (I : ProperGeneratorImage g Z) : ProperGeneratorImage f Z where
  image := I.image
  factor := I.factor
  factorization :=
    (StackIso2.whiskerLeft Z.representative.inclusion e).trans I.factorization
  atlasMap := I.atlasMap
  atlasComparison := I.atlasComparison
  atlasMap_dominant := I.atlasMap_dominant

/-- Generic residue degree of the actual dominant atlas map presenting a proper image. -/
noncomputable def ProperGeneratorImage.residueDegree
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    {Z : StackCycleGenerator X} (I : ProperGeneratorImage f Z) : ℕ :=
  I.atlasMap.residueDegree (_root_.genericPoint Z.integralAtlas.scheme)

/-- The dense image of a generator under the identity stack morphism is the generator itself.
All comparison cells are the bicategorical unitors, and the atlas map is the identity scheme
morphism. -/
noncomputable def properIdentityGeneratorImage
    {X : DeligneMumfordStack.{u}} (Z : StackCycleGenerator X) :
    ProperGeneratorImage
      (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor) Z where
  image := Z
  factor := Pseudofunctor.StrongTrans.id
    Z.representative.stack.toStack.toPseudofunctor
  factorization :=
    (StackIso2.rightUnitor Z.representative.inclusion).trans
      (StackIso2.leftUnitor Z.representative.inclusion).symm
  atlasMap := 𝟙 Z.integralAtlas.scheme
  atlasComparison :=
    ((FppfStack.mapOfSchemeHom_id_iso Z.integralAtlas.scheme).whiskerRight
        Z.integralAtlas.map).trans
      ((StackIso2.leftUnitor Z.integralAtlas.map).trans
        (StackIso2.rightUnitor Z.integralAtlas.map).symm)
  atlasMap_dominant := inferInstance

@[simp]
theorem properIdentityGeneratorImage_image
    {X : DeligneMumfordStack.{u}} (Z : StackCycleGenerator X) :
    (properIdentityGeneratorImage Z).image = Z :=
  rfl

@[simp]
theorem properIdentityGeneratorImage_residueDegree
    {X : DeligneMumfordStack.{u}} (Z : StackCycleGenerator X) :
    (properIdentityGeneratorImage Z).residueDegree = 1 := by
  exact _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_id
    (_root_.genericPoint Z.integralAtlas.scheme)

@[simp]
theorem ProperGeneratorImage.transport_residueDegree
    {X Y : DeligneMumfordStack.{u}} {f g : StackHom X.toStack Y.toStack}
    {Z : StackCycleGenerator X} (e : StackIso2 f g)
    (I : ProperGeneratorImage g Z) :
    (I.transport e).residueDegree = I.residueDegree :=
  rfl

/-- The proper-pushforward coefficient computed from the actual generic residue extension and
the generic inertia orders of source and image. -/
noncomputable def properGeneratorCoefficient
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    (image : (Z : StackCycleGenerator X) → ProperGeneratorImage f Z)
    (sourceFinite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia)
    (imageFinite : (Z : StackCycleGenerator X) →
      Fintype (image Z).image.genericInertia)
    (Z : StackCycleGenerator X) : ℚ := by
  letI := sourceFinite Z
  letI := imageFinite Z
  exact (image Z).residueDegree *
    (Fintype.card (image Z).image.genericInertia : ℚ) /
      Fintype.card Z.genericInertia

/-- For the identity image, residue degree and stabilizer ratio are both one. -/
@[simp]
theorem properGeneratorCoefficient_identity
    {X : DeligneMumfordStack.{u}}
    (finite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia)
    (Z : StackCycleGenerator X) :
    properGeneratorCoefficient (fun W ↦ properIdentityGeneratorImage W)
      finite finite Z = 1 := by
  let _ := finite Z
  let _ : Nonempty Z.genericInertia := ⟨𝟙 Z.genericObject⟩
  have hcardNat : Fintype.card Z.genericInertia ≠ 0 :=
    Fintype.card_ne_zero
  have hcardRat : (Fintype.card Z.genericInertia : ℚ) ≠ 0 := by
    exact_mod_cast hcardNat
  simp [properGeneratorCoefficient, hcardRat]

/-- The forced proper-pushforward image of one integral cycle generator. -/
noncomputable def properGeneratorCycle
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    {f : StackHom X.toStack Y.toStack}
    (image : (Z : VX.IntegralClosedSubstack) → ProperGeneratorImage f Z)
    (sourceFinite : (Z : VX.IntegralClosedSubstack) → Fintype Z.genericInertia)
    (imageFinite : (Z : VX.IntegralClosedSubstack) →
      Fintype (image Z).image.genericInertia)
    (i : ℤ) (Z : VX.IntegralClosedSubstack) : VY.cycles i :=
  if hY : VY.dimension (image Z).image = i then
    properGeneratorCoefficient image sourceFinite imageFinite Z •
      VY.point (image Z).image hY
  else 0

/-- Proper pushforward on cycles, obtained by linear extension of the mandatory
residue-degree/stabilizer formula. -/
noncomputable def properCycleMap
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    {f : StackHom X.toStack Y.toStack}
    (image : (Z : VX.IntegralClosedSubstack) → ProperGeneratorImage f Z)
    (sourceFinite : (Z : VX.IntegralClosedSubstack) → Fintype Z.genericInertia)
    (imageFinite : (Z : VX.IntegralClosedSubstack) →
      Fintype (image Z).image.genericInertia)
    (i : ℤ) : VX.cycles i →ₗ[ℚ] VY.cycles i :=
  (Finsupp.linearCombination ℚ
    (fun Z ↦ properGeneratorCycle VX VY image sourceFinite imageFinite i Z)).comp
      (VX.cycles i).subtype

/-- Proper pushforward along the identity has the identity cycle map; in particular its
preservation of principal divisors is a theorem, not extra input. -/
theorem properCycleMap_identity
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    (finite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia)
    (i : ℤ) (z : V.cycles i) :
    properCycleMap V V (fun Z ↦ properIdentityGeneratorImage Z)
      finite finite i z = z := by
  classical
  apply Subtype.ext
  simp only [properCycleMap, LinearMap.coe_comp, Submodule.coe_subtype,
    Function.comp_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum, Submodule.coe_sum]
  conv_rhs => rw [← Finsupp.sum_single z.1, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro Z hsupport
  have hdimension : V.dimension Z = i := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hsupport) (z.property Z h)
  simp [properGeneratorCycle, hdimension,
    VistoliCyclePresentation.point]

/-- Transporting all dense-image factorizations across a 2-isomorphism leaves the forced proper
cycle map unchanged. -/
theorem properCycleMap_transport
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    {f g : StackHom X.toStack Y.toStack} (e : StackIso2 f g)
    (image : (Z : VX.IntegralClosedSubstack) → ProperGeneratorImage g Z)
    (sourceFinite : (Z : VX.IntegralClosedSubstack) → Fintype Z.genericInertia)
    (imageFinite : (Z : VX.IntegralClosedSubstack) →
      Fintype (image Z).image.genericInertia)
    (i : ℤ) :
    properCycleMap VX VY (fun Z ↦ (image Z).transport e)
      sourceFinite imageFinite i =
        properCycleMap VX VY image sourceFinite imageFinite i :=
  rfl

/-- Proper pushforward data, including the residue/stabilizer weight on every integral
generator.  Its cycle map is the forced linear extension above. -/
structure ProperPushforward
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (f : StackHom X.toStack Y.toStack) (i : ℤ) where
  proper : f.Proper
  generatorImage (Z : VX.IntegralClosedSubstack) : ProperGeneratorImage f Z
  sourceStabilizerFinite (Z : VX.IntegralClosedSubstack) : Fintype Z.genericInertia
  imageStabilizerFinite (Z : VX.IntegralClosedSubstack) :
    Fintype (generatorImage Z).image.genericInertia
  /-- Proper pushforward carries each actual graded principal divisor to rational equivalence.
  The full submodule inclusion is derived by linear span below. -/
  mapsGradedDivisor (g : VistoliCyclePresentation.GradedRationalFunctionGenerator
      (X := X) i) :
    properCycleMap VX VY generatorImage sourceStabilizerFinite
        imageStabilizerFinite i (VX.gradedDivisor g) ∈ VY.relations i

namespace ProperPushforward

variable {X Y : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
  {f : StackHom X.toStack Y.toStack} {i : ℤ}

/-- The proper Chow map has the uniquely forced cycle-level formula. -/
noncomputable def map (P : ProperPushforward VX VY f i) : StackChowMap VX VY i i where
  onCycles := properCycleMap VX VY P.generatorImage P.sourceStabilizerFinite
    P.imageStabilizerFinite i
  mapsRelations := VX.mapsRelations_of_maps_gradedDivisors VY _ P.mapsGradedDivisor

/-- Proper pushforward along the identity is constructed without a relation-preservation
hypothesis: the identity cycle formula proves preservation of every principal divisor. -/
noncomputable def identity
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    (finite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia)
    (i : ℤ) : ProperPushforward V V
      (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor) i where
  proper := StackHom.id_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) X.toStack
  generatorImage Z := properIdentityGeneratorImage Z
  sourceStabilizerFinite Z := finite Z
  imageStabilizerFinite Z := finite Z
  mapsGradedDivisor g := by
    rw [properCycleMap_identity]
    exact V.gradedDivisor_mem_relations g

/-- Transport proper pushforward across an invertible 2-cell.  Dense images and numerical
weights are unchanged, so the principal-divisor proof follows from equality of cycle maps. -/
noncomputable def ofIso
    {g : StackHom X.toStack Y.toStack} (e : StackIso2 f g)
    (P : ProperPushforward VX VY g i) : ProperPushforward VX VY f i where
  proper := (StackHom.hasRepresentableProperty_congr
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) e).2 P.proper
  generatorImage Z := (P.generatorImage Z).transport e
  sourceStabilizerFinite Z := P.sourceStabilizerFinite Z
  imageStabilizerFinite Z := P.imageStabilizerFinite Z
  mapsGradedDivisor g := by
    rw [properCycleMap_transport]
    exact P.mapsGradedDivisor g

@[simp]
theorem ofIso_map_induced
    {g : StackHom X.toStack Y.toStack} (e : StackIso2 f g)
    (P : ProperPushforward VX VY g i) :
    (ofIso e P).map.induced = P.map.induced := by
  have hcycles : (ofIso e P).map.onCycles = P.map.onCycles := by
    exact properCycleMap_transport VX VY e P.generatorImage
      P.sourceStabilizerFinite P.imageStabilizerFinite i
  have hmap : (ofIso e P).map = P.map := StackChowMap.ext hcycles
  rw [hmap]

@[simp]
theorem identity_map_induced
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    (finite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia)
    (i : ℤ) :
    (identity V finite i).map.induced = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change V.quotientMap i
      (properCycleMap V V (fun Z ↦ properIdentityGeneratorImage Z)
        finite finite i z) = V.quotientMap i z
  rw [properCycleMap_identity]

/-- The dense integral image of a generator, extracted from its geometric factorization. -/
def image (P : ProperPushforward VX VY f i) (Z : VX.IntegralClosedSubstack) :
    VY.IntegralClosedSubstack :=
  (P.generatorImage Z).image

/-- Generic residue degree, computed from the dominant atlas map in the factorization. -/
noncomputable def residueDegree (P : ProperPushforward VX VY f i)
    (Z : VX.IntegralClosedSubstack) : ℕ :=
  (P.generatorImage Z).residueDegree

/-- Generic source inertia order. -/
noncomputable def sourceStabilizerOrder (P : ProperPushforward VX VY f i)
    (Z : VX.IntegralClosedSubstack) : ℕ :=
  genericStabilizerOrder P.sourceStabilizerFinite Z

/-- Generic image inertia order. -/
noncomputable def imageStabilizerOrder (P : ProperPushforward VX VY f i)
    (Z : VX.IntegralClosedSubstack) : ℕ := by
  exact @Fintype.card (P.generatorImage Z).image.genericInertia
    (P.imageStabilizerFinite Z)

/-- Proper pushforward uses the residue/stabilizer coefficient on an integral generator.
When the image has smaller dimension its contribution to the fixed degree is zero. -/
theorem map_on_generator (P : ProperPushforward VX VY f i)
    (Z : VX.IntegralClosedSubstack) (hZ : VX.dimension Z = i) :
    P.map.onCycles (VX.point Z hZ) =
      if hY : VY.dimension (P.image Z) = i then
        ((P.residueDegree Z : ℚ) * P.imageStabilizerOrder Z /
          P.sourceStabilizerOrder Z) •
          VY.point (P.image Z) hY
      else 0 := by
  classical
  simp only [map, properCycleMap, properGeneratorCycle, properGeneratorCoefficient,
    VistoliCyclePresentation.point, LinearMap.coe_comp, Submodule.coe_subtype,
    Function.comp_apply, Finsupp.linearCombination_single, smul_dite, one_smul,
    smul_zero, image, residueDegree, imageStabilizerOrder, sourceStabilizerOrder,
    genericStabilizerOrder, SetLike.mk_smul_mk, Finsupp.smul_single, smul_eq_mul,
    mul_one]
  split
  · apply Subtype.ext
    ext W
    simp
  · rfl

/-- The coefficient of an integral generator is forced by its residue degree and the actual
generic inertia orders; it is not extra pushforward data. -/
noncomputable def coefficient (P : ProperPushforward VX VY f i)
    (Z : VX.IntegralClosedSubstack) : ℚ :=
  (P.residueDegree Z : ℚ) * P.imageStabilizerOrder Z /
    P.sourceStabilizerOrder Z

@[simp]
theorem coefficient_formula (P : ProperPushforward VX VY f i)
    (Z : VX.IntegralClosedSubstack) :
    P.coefficient Z = (P.residueDegree Z : ℚ) * P.imageStabilizerOrder Z /
      P.sourceStabilizerOrder Z :=
  rfl

end ProperPushforward

/-- Geometric inverse image of one integral closed substack under a flat stack morphism.  The
fibre product is genuine, its representing DM stack maps as a closed substack of the source,
and its fundamental cycle weights its actual components by their generic local-ring lengths. -/
structure FlatGeneratorPullbackGeometry
    {X Y : DeligneMumfordStack.{u}}
    (f : StackHom X.toStack Y.toStack) (relativeDimension : ℕ)
    (Z : StackCycleGenerator Y) where
  pullback : StackTwoPullback.Genuine Z.representative.inclusion f
  fiber : DeligneMumfordStack.{u}
  fiberEquivalence : StackEquivalenceData fiber.toStack pullback.pullback
  fiberToSource : StackHom fiber.toStack X.toStack
  fiberToSourceComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp fiberEquivalence.hom pullback.snd)
    fiberToSource
  /-- Every integral component maps to the source as an actual closed immersion.  This is a
  property of the cartesian inverse image, not selectable cycle data. -/
  componentToSource_closed (W : StackCycleGenerator fiber) :
    StackHom.ClosedImmersion
      (Pseudofunctor.StrongTrans.vcomp W.representative.inclusion fiberToSource)
  fundamentalGeometry : StackFundamentalCycleGeometry fiber
    (Z.dimension + (relativeDimension : ℤ))

namespace FlatGeneratorPullbackGeometry

variable {X Y : DeligneMumfordStack.{u}}
  {f : StackHom X.toStack Y.toStack} {relativeDimension : ℕ}
  {Z : StackCycleGenerator Y}

/-- An irreducible component of the cartesian inverse image, regarded as a closed integral
substack of the source. -/
noncomputable def componentInSource
    (G : FlatGeneratorPullbackGeometry f relativeDimension Z)
    (W : StackCycleGenerator G.fiber) : StackCycleGenerator X :=
  StackCycleGenerator.mk
    { stack := W.representative.stack
      inclusion := Pseudofunctor.StrongTrans.vcomp W.representative.inclusion
        G.fiberToSource
      inclusion_closed := G.componentToSource_closed W
      integralPresentation := W.representative.integralPresentation
      dimension := W.dimension
      pureDimension := by
        simpa only [W.representative_dimension] using W.representative.pureDimension }

@[simp]
theorem componentInSource_dimension
    (G : FlatGeneratorPullbackGeometry f relativeDimension Z)
    (W : StackCycleGenerator G.fiber) :
    (G.componentInSource W).dimension = W.dimension :=
  rfl

/-- The flat inverse-image cycle of one integral generator.  Its coefficients are the generic
local-ring lengths of the irreducible components of the genuine fibre product. -/
noncomputable def cycle
    (G : FlatGeneratorPullbackGeometry f relativeDimension Z)
    (VX : VistoliCyclePresentation X) (i : ℤ) (hZ : Z.dimension = i) :
    VX.cycles (i + (relativeDimension : ℤ)) := by
  classical
  exact Finsupp.linearCombination ℚ (fun W ↦
    if hW : W.IsIrreducibleComponent then
      VX.point (G.componentInSource W) (by
        change (G.componentInSource W).dimension = i + (relativeDimension : ℤ)
        rw [G.componentInSource_dimension]
        exact (G.fundamentalGeometry.component_dimension W hW).trans
          (congrArg (fun d : ℤ ↦ d + (relativeDimension : ℤ)) hZ))
    else 0) G.fundamentalGeometry.rawCycle

end FlatGeneratorPullbackGeometry

/-- The only permitted constructions of a generator-level flat inverse image: the exact
identity, an actual cartesian inverse image, or transport across an invertible 2-cell.  There is
no constructor accepting a coefficient function. -/
inductive FlatGeneratorCycleGeometry :
    {X Y : DeligneMumfordStack.{u}} →
      StackHom X.toStack Y.toStack → ℕ →
      (Z : StackCycleGenerator Y) → Type (u + 2)
  | identity {X : DeligneMumfordStack.{u}} (Z : StackCycleGenerator X) :
      FlatGeneratorCycleGeometry
        (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor) 0 Z
  | pullback {X Y : DeligneMumfordStack.{u}}
      {f : StackHom X.toStack Y.toStack} {relativeDimension : ℕ}
      {Z : StackCycleGenerator Y}
      (geometry : FlatGeneratorPullbackGeometry f relativeDimension Z) :
      FlatGeneratorCycleGeometry f relativeDimension Z
  | identityTransport {X : DeligneMumfordStack.{u}}
      {f : StackHom X.toStack X.toStack}
      (comparison : StackIso2 f
        (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor))
      (Z : StackCycleGenerator X) :
      FlatGeneratorCycleGeometry f 0 Z
  | pullbackTransport {X Y : DeligneMumfordStack.{u}}
      {f g : StackHom X.toStack Y.toStack} {relativeDimension : ℕ}
      {Z : StackCycleGenerator Y}
      (comparison : StackIso2 f g)
      (geometry : FlatGeneratorPullbackGeometry g relativeDimension Z) :
      FlatGeneratorCycleGeometry f relativeDimension Z

namespace FlatGeneratorCycleGeometry

/-- Transport a forced generator cycle across an invertible 2-cell, composing comparisons if
the construction had already been transported. -/
def transport
    {X Y : DeligneMumfordStack.{u}} {f g : StackHom X.toStack Y.toStack}
    {relativeDimension : ℕ} {Z : StackCycleGenerator Y}
    (e : StackIso2 f g) (G : FlatGeneratorCycleGeometry g relativeDimension Z) :
    FlatGeneratorCycleGeometry f relativeDimension Z := by
  cases G with
  | identity Z => exact .identityTransport e Z
  | pullback geometry => exact .pullbackTransport e geometry
  | identityTransport comparison Z =>
      exact .identityTransport (e.trans comparison) Z
  | pullbackTransport comparison geometry =>
      exact .pullbackTransport (e.trans comparison) geometry

/-- The graded cycle forced by a permitted geometric construction. -/
noncomputable def cycle
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    {relativeDimension : ℕ} {Z : StackCycleGenerator Y}
    (G : FlatGeneratorCycleGeometry f relativeDimension Z)
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (i : ℤ) (hZ : VY.dimension Z = i) :
    VX.cycles (i + (relativeDimension : ℤ)) := by
  cases G with
  | identity Z =>
      exact VX.point Z (by simpa using hZ)
  | pullback geometry =>
      exact geometry.cycle VX i hZ
  | identityTransport comparison Z =>
      exact VX.point Z (by simpa using hZ)
  | pullbackTransport comparison geometry =>
      exact geometry.cycle VX i hZ

@[simp]
theorem cycle_identity
    {X : DeligneMumfordStack.{u}} (Z : StackCycleGenerator X)
    (VX VY : VistoliCyclePresentation X) (i : ℤ)
    (hZ : VY.dimension Z = i) :
    (FlatGeneratorCycleGeometry.identity Z).cycle VX VY i hZ =
      VX.point Z (by simpa using hZ) := by
  simp [FlatGeneratorCycleGeometry.cycle]

@[simp]
theorem cycle_pullback
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    {relativeDimension : ℕ} {Z : StackCycleGenerator Y}
    (G : FlatGeneratorPullbackGeometry f relativeDimension Z)
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (i : ℤ) (hZ : VY.dimension Z = i) :
    (FlatGeneratorCycleGeometry.pullback G).cycle VX VY i hZ =
      G.cycle VX i hZ := by
  simp [FlatGeneratorCycleGeometry.cycle]

@[simp]
theorem cycle_transport
    {X Y : DeligneMumfordStack.{u}} {f g : StackHom X.toStack Y.toStack}
    {relativeDimension : ℕ} {Z : StackCycleGenerator Y}
    (e : StackIso2 f g) (G : FlatGeneratorCycleGeometry g relativeDimension Z)
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (i : ℤ) (hZ : VY.dimension Z = i) :
    (G.transport e).cycle VX VY i hZ =
      G.cycle VX VY i hZ := by
  cases G <;> simp [transport, FlatGeneratorCycleGeometry.cycle]

end FlatGeneratorCycleGeometry

/-- Flat pullback on cycles, defined by linear extension of the geometrically forced inverse
images of integral generators. -/
noncomputable def flatCycleMap
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    {f : StackHom X.toStack Y.toStack}
    (relativeDimension : ℕ) (i : ℤ)
    (geometry : (Z : VY.IntegralClosedSubstack) →
      FlatGeneratorCycleGeometry f relativeDimension Z) :
    VY.cycles i →ₗ[ℚ] VX.cycles (i + (relativeDimension : ℤ)) :=
  (Finsupp.linearCombination ℚ (fun Z ↦
    if hZ : VY.dimension Z = i then
      (geometry Z).cycle VX VY i hZ
    else 0)).comp (VY.cycles i).subtype

/-- Transporting generator geometry across a 2-isomorphism does not alter its forced cycle
map. -/
theorem flatCycleMap_transport
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    {f g : StackHom X.toStack Y.toStack} (e : StackIso2 f g)
    (relativeDimension : ℕ) (i : ℤ)
    (geometry : (Z : VY.IntegralClosedSubstack) →
      FlatGeneratorCycleGeometry g relativeDimension Z) :
    flatCycleMap VX VY relativeDimension i
        (fun Z ↦ (geometry Z).transport e) =
      flatCycleMap VX VY relativeDimension i geometry := by
  unfold flatCycleMap
  congr 1
  apply congrArg (Finsupp.linearCombination ℚ)
  funext Z
  split
  · apply FlatGeneratorCycleGeometry.cycle_transport
  · rfl

/-- The cycle map constructed by the identity geometry is the identity. -/
theorem flatCycleMap_identity
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    (i : ℤ) (z : V.cycles i) :
    flatCycleMap V V 0 i (fun Z ↦ FlatGeneratorCycleGeometry.identity Z) z =
      V.cyclesCast (by omega) z := by
  classical
  apply Subtype.ext
  rw [VistoliCyclePresentation.coe_cyclesCast]
  simp only [flatCycleMap, LinearMap.coe_comp, Submodule.coe_subtype,
    Function.comp_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum, Submodule.coe_sum]
  conv_rhs => rw [← Finsupp.sum_single z.1, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro Z hsupport
  have hdimension : V.dimension Z = i := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hsupport) (z.property Z h)
  simp [hdimension, FlatGeneratorCycleGeometry.cycle,
    VistoliCyclePresentation.point]

/-- Flat pullback data with its relative-dimension shift and actual geometric inverse images
of every integral generator.  Its linear cycle map is forced by those cartesian constructions. -/
structure FlatPullback
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (f : StackHom X.toStack Y.toStack) (relativeDimension : ℕ) (i : ℤ) where
  flat : f.Flat
  /-- The grading shift is the fibre dimension of the displayed morphism, not an unrelated
  integer label. -/
  pureRelativeDimension : f.HasPureRelativeDimension relativeDimension
  generatorGeometry (Z : VY.IntegralClosedSubstack) :
    FlatGeneratorCycleGeometry f relativeDimension Z
  /-- The geometrically constructed inverse image of every actual graded principal divisor is
  rationally equivalent to zero.  Preservation of the entire span is derived below. -/
  mapsGradedDivisor (g : VistoliCyclePresentation.GradedRationalFunctionGenerator
      (X := Y) i) :
    flatCycleMap VX VY relativeDimension i generatorGeometry (VY.gradedDivisor g) ∈
      VX.relations (i + (relativeDimension : ℤ))

namespace FlatPullback

variable {X Y : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
  {f : StackHom X.toStack Y.toStack} {relativeDimension : ℕ} {i : ℤ}

/-- The induced flat Chow map constructed from the multiplicity cycles. -/
noncomputable def map (P : FlatPullback VX VY f relativeDimension i) :
    StackChowMap VY VX i (i + (relativeDimension : ℤ)) where
  onCycles := flatCycleMap VX VY relativeDimension i P.generatorGeometry
  mapsRelations := VY.mapsRelations_of_maps_gradedDivisors VX _ P.mapsGradedDivisor

/-- Transport a flat pullback across an invertible 2-cell.  Representable flatness and pure
relative dimension are defined as 2-isomorphism-invariant geometric predicates, while the
cycle multiplicities themselves are unchanged. -/
noncomputable def ofIso
    {g : StackHom X.toStack Y.toStack} (e : StackIso2 f g)
    (P : FlatPullback VX VY g relativeDimension i) :
    FlatPullback VX VY f relativeDimension i where
  flat := (StackHom.hasRepresentableProperty_congr
    (@_root_.AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) e).2 P.flat
  pureRelativeDimension :=
    (StackHom.hasPureRelativeDimension_congr e).2 P.pureRelativeDimension
  generatorGeometry Z := .transport e (P.generatorGeometry Z)
  mapsGradedDivisor g := by
    rw [flatCycleMap_transport]
    exact P.mapsGradedDivisor g

@[simp]
theorem ofIso_map_induced
    {g : StackHom X.toStack Y.toStack} (e : StackIso2 f g)
    (P : FlatPullback VX VY g relativeDimension i) :
    (ofIso e P).map.induced = P.map.induced := by
  have hcycles : (ofIso e P).map.onCycles = P.map.onCycles := by
    exact flatCycleMap_transport VX VY e relativeDimension i P.generatorGeometry
  have hmap : (ofIso e P).map = P.map := StackChowMap.ext hcycles
  rw [hmap]

/-- The identity stack morphism has a constructed flat pullback with Kronecker
multiplicities. -/
noncomputable def identity
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X) (i : ℤ) :
    FlatPullback V V
      (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor) 0 i where
  flat := StackHom.id_hasRepresentableProperty
    (@_root_.AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) X.toStack
  pureRelativeDimension := StackHom.id_hasPureRelativeDimension X.toStack
  generatorGeometry Z := .identity Z
  mapsGradedDivisor g := by
    have hz : V.gradedDivisor g ∈ V.relations i :=
      V.gradedDivisor_mem_relations g
    change flatCycleMap V V 0 i
      (fun Z ↦ FlatGeneratorCycleGeometry.identity Z) (V.gradedDivisor g) ∈
        V.relations (i + (0 : ℤ))
    rw [flatCycleMap_identity]
    exact (V.cyclesCast_mem_relations (by omega) (V.gradedDivisor g)).2 hz

@[simp]
theorem identity_map_induced
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X) (i : ℤ) :
    (identity V i).map.induced = V.cast (by omega) := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change V.quotientMap (i + (0 : ℤ))
      (flatCycleMap V V 0 i
        (fun Z ↦ FlatGeneratorCycleGeometry.identity Z) z) =
          V.cast (by omega) (V.quotientMap i z)
  rw [flatCycleMap_identity]
  exact VistoliCyclePresentation.quotientMap_cyclesCast V _ z

/-- The constructed flat pullback has the prescribed multiplicity cycle on every integral
generator. -/
theorem map_on_generator (P : FlatPullback VX VY f relativeDimension i)
    (Z : VY.IntegralClosedSubstack) (hZ : VY.dimension Z = i) :
    P.map.onCycles (VY.point Z hZ) =
      (P.generatorGeometry Z).cycle VX VY i hZ := by
  classical
  simp [map, flatCycleMap, VistoliCyclePresentation.point, hZ]

end FlatPullback

/-- The map from the integral atlas of a closed substack to the ground scheme, extracted from
the actual composite of represented-stack morphisms. -/
noncomputable def integralAtlasStructureMap
    {X : DeligneMumfordStack.{u}} {K : Type u} [Field K]
    (structureMap : StackHom X.toStack
      (representedStack (_root_.AlgebraicGeometry.Spec (.of K))))
    (Z : StackCycleGenerator X) :
    Z.integralAtlas.scheme ⟶ _root_.AlgebraicGeometry.Spec (.of K) :=
  FppfStack.schemeHomOfMap <|
    Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp Z.integralAtlas.map Z.representative.inclusion)
      structureMap

/-- The generic residue degree is computed from the actual atlas-to-ground scheme morphism. -/
noncomputable def genericResidueDegree
    {X : DeligneMumfordStack.{u}} {K : Type u} [Field K]
    (structureMap : StackHom X.toStack
      (representedStack (_root_.AlgebraicGeometry.Spec (.of K))))
    (Z : StackCycleGenerator X) : ℕ :=
  (integralAtlasStructureMap structureMap Z).residueDegree
    (_root_.genericPoint Z.integralAtlas.scheme)

/-- Degree on zero-cycles, obtained by linear extension of the geometrically computed generic
residue degree divided by the actual generic inertia order. -/
noncomputable def properDegreeCycleMap
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    {K : Type u} [Field K]
    (structureMap : StackHom X.toStack
      (representedStack (_root_.AlgebraicGeometry.Spec (.of K))))
    (stabilizerFinite : (Z : V.IntegralClosedSubstack) → Fintype Z.genericInertia) :
    V.cycles 0 →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ (fun Z ↦
    if V.dimension Z = 0 then
      (genericResidueDegree structureMap Z : ℚ) /
        genericStabilizerOrder stabilizerFinite Z
    else 0)).comp (V.cycles 0).subtype

/-- Degree of zero-cycles on a proper DM stack.  Its cycle-level functional is fixed by the
residue/stabilizer formula rather than stored as arbitrary linear data. -/
structure ProperDegree {X : DeligneMumfordStack.{u}}
    (V : VistoliCyclePresentation X) where
  GroundField : Type u
  [groundField : Field GroundField]
  structureMap : StackHom X.toStack
    (representedStack (_root_.AlgebraicGeometry.Spec (.of GroundField)))
  proper : structureMap.Proper
  stabilizerFinite (Z : V.IntegralClosedSubstack) : Fintype Z.genericInertia
  /-- Every actual zero-dimensional principal divisor has degree zero.  Vanishing on the whole
  rational-equivalence span is derived by linearity. -/
  killsGradedDivisor (g : VistoliCyclePresentation.GradedRationalFunctionGenerator
      (X := X) 0) :
    properDegreeCycleMap V structureMap stabilizerFinite (V.gradedDivisor g) = 0

attribute [instance] ProperDegree.groundField

namespace ProperDegree

variable {X : DeligneMumfordStack.{u}} {V : VistoliCyclePresentation X}

/-- The geometrically forced cycle-level degree map. -/
noncomputable def onCycles (D : ProperDegree V) : V.cycles 0 →ₗ[ℚ] ℚ :=
  properDegreeCycleMap V D.structureMap D.stabilizerFinite

/-- Residue degree of an integral generator, derived from the displayed structure morphism. -/
noncomputable def residueDegree (D : ProperDegree V)
    (Z : V.IntegralClosedSubstack) : ℕ :=
  genericResidueDegree D.structureMap Z

/-- Generic stabilizer order of an integral generator, derived from its actual inertia group. -/
noncomputable def stabilizerOrder (D : ProperDegree V)
    (Z : V.IntegralClosedSubstack) : ℕ :=
  genericStabilizerOrder D.stabilizerFinite Z

theorem stabilizerOrder_pos (D : ProperDegree V)
    (Z : V.IntegralClosedSubstack) : 0 < D.stabilizerOrder Z :=
  genericStabilizerOrder_pos D.stabilizerFinite Z

/-- Degree descends to rational equivalence. -/
def degree (D : ProperDegree V) : V.chow 0 →ₗ[ℚ] ℚ :=
  (V.relations 0).liftQ D.onCycles <| by
    rw [VistoliCyclePresentation.relations, Submodule.span_le]
    rintro z ⟨g, rfl⟩
    exact D.killsGradedDivisor g

/-- Degree of an integral zero-dimensional generator is its residue degree divided by its
stabilizer order. -/
@[simp]
theorem onCycles_point (D : ProperDegree V) (Z : V.IntegralClosedSubstack)
    (hZ : V.dimension Z = 0) :
    D.onCycles (V.point Z hZ) =
      (D.residueDegree Z : ℚ) / D.stabilizerOrder Z := by
  classical
  simp [onCycles, properDegreeCycleMap, residueDegree, stabilizerOrder,
    VistoliCyclePresentation.point, hZ]

@[simp]
theorem degree_quotientMap (D : ProperDegree V) (z : V.cycles 0) :
    D.degree (V.quotientMap 0 z) = D.onCycles z :=
  rfl

end ProperDegree

-/

-/

end

end GromovWitten.AlgebraicGeometry.IntersectionTheory
