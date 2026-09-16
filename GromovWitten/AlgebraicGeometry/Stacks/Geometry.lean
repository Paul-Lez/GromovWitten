/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStack
import GromovWitten.AlgebraicGeometry.Stacks.Scheme
import GromovWitten.AlgebraicGeometry.Stacks.Properties
import GromovWitten.AlgebraicGeometry.Stacks.TwoPullbackBilimit
import Mathlib.Topology.Constructions

/-!
# Geometric calculus for algebraic stacks

Representable properties are defined by every scheme base change.  Their composition theorem,
including the composite universal presentation and pseudofunctorial pasting proof, lives in
`Stacks.Properties`; invariance under changes of source and target by equivalence lives in
`Stacks.EquivalenceProperties`; and base change along an arbitrary genuine two-pullback lives in
`Stacks.GenuineBaseChange`.  General atlas refinements, the unramified-diagonal criterion, and
dimension comparisons remain incomplete.  The underlying topological space is constructed from
the internally chosen atlas rather than supplied as presentation data.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

/-- The canonical cone used to define a relative diagonal. Both legs are identities, and the
comparison is the identity 2-cell on their common composite with `f`. -/
noncomputable def relativeDiagonalCone {X Y : FppfStack.{u}} (f : StackHom X Y) :
    StackTwoPullback.Cone (f := f) (g := f) X where
  fst := Pseudofunctor.StrongTrans.id X.toPseudofunctor
  snd := Pseudofunctor.StrongTrans.id X.toPseudofunctor
  comparison := StackIso2.refl _

/-- The relative diagonal is the lift of the canonical identity cone through the proved
bicategorical universal property of the self-pullback. -/
noncomputable def StackTwoPullback.Genuine.relativeDiagonal
    {X Y : FppfStack.{u}} {f : StackHom X Y}
    (P : StackTwoPullback.Genuine f f) : StackHom X P.pullback :=
  P.bilimit.lift (relativeDiagonalCone f)

/-- The first projection of the constructed relative diagonal is the identity. -/
noncomputable def StackTwoPullback.Genuine.relativeDiagonalFstComparison
    {X Y : FppfStack.{u}} {f : StackHom X Y}
    (P : StackTwoPullback.Genuine f f) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp P.relativeDiagonal P.fst)
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) :=
  P.bilimit.lift_fst (relativeDiagonalCone f)

/-- The second projection of the constructed relative diagonal is the identity. -/
noncomputable def StackTwoPullback.Genuine.relativeDiagonalSndComparison
    {X Y : FppfStack.{u}} {f : StackHom X Y}
    (P : StackTwoPullback.Genuine f f) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp P.relativeDiagonal P.snd)
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor) :=
  P.bilimit.lift_snd (relativeDiagonalCone f)

/-- The constructed relative diagonal classifies the entire identity cone, including its
comparison face. -/
theorem StackTwoPullback.Genuine.relativeDiagonalClassifies
    {X Y : FppfStack.{u}} {f : StackHom X Y}
    (P : StackTwoPullback.Genuine f f) :
    StackTwoPullback.ConeLiftClassifies P.toStackTwoPullback
      (relativeDiagonalCone f) P.relativeDiagonal
      P.relativeDiagonalFstComparison P.relativeDiagonalSndComparison :=
  P.bilimit.lift_compatible (relativeDiagonalCone f)

/-- A morphism is of relative Deligne--Mumford type when its canonically constructed relative
diagonal into the canonical genuine self 2-pullback is representably unramified. -/
structure RelativeDeligneMumfordMorphism
    {X Y : FppfStack.{u}} (f : StackHom X Y) where
  diagonal_unramified :
    (StackTwoPullback.canonicalGenuine f f).relativeDiagonal.Unramified

namespace RelativeDeligneMumfordMorphism

/-- The self-pullback used by a relative Deligne--Mumford morphism is constructed canonically;
it is not supplied by the caller. -/
noncomputable def selfPullback {X Y : FppfStack.{u}} {f : StackHom X Y}
    (_ : RelativeDeligneMumfordMorphism f) : StackTwoPullback.Genuine f f :=
  StackTwoPullback.canonicalGenuine f f

end RelativeDeligneMumfordMorphism

/-
Retired provisional representable-property calculus.  Its composition, base-change, and
equivalence laws were supplied as fields rather than proved from `MorphismProperty`.  The active
theorems in `Properties`, `GenuineBaseChange`, and `EquivalenceProperties` now construct these
three operations for multiplicative representable properties.

/-- The composition, equivalence, and base-change laws for a representable scheme-morphism
property.  Identity stability is constructed universally in
`StackHom.id_hasRepresentableProperty` and is therefore not supplied as a field. -/
structure StackRepresentablePropertyCalculus
  (P : MorphismProperty Scheme.{u}) where
  composition {X Y Z : FppfStack.{u}} (f : StackHom X Y) (g : StackHom Y Z) :
    f.HasRepresentableProperty P → g.HasRepresentableProperty P →
      StackHom.HasRepresentableProperty
        (Pseudofunctor.StrongTrans.vcomp f g : StackHom X Z) P
  baseChange {X Y Z : FppfStack.{u}} (f : StackHom X Z) (g : StackHom Y Z)
    (sq : StackTwoPullback.Genuine f g) :
    f.HasRepresentableProperty P → sq.snd.HasRepresentableProperty P
  invariantUnderEquivalence {X Y X' Y' : FppfStack.{u}}
    (f : StackHom X Y) (f' : StackHom X' Y')
    (source : StackEquivalenceData X X') (target : StackEquivalenceData Y Y')
    (compatible : StackIso2
      (Pseudofunctor.StrongTrans.vcomp source.hom f')
      (Pseudofunctor.StrongTrans.vcomp f target.hom)) :
    f.HasRepresentableProperty P ↔ f'.HasRepresentableProperty P

namespace StackRepresentablePropertyCalculus

/-- Identity stability is canonical and independent of the remaining geometric calculus. -/
theorem identity (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    (X : FppfStack.{u}) :
    StackHom.HasRepresentableProperty
      (Pseudofunctor.StrongTrans.id X.toPseudofunctor : StackHom X X) P :=
  StackHom.id_hasRepresentableProperty P X

end StackRepresentablePropertyCalculus

-/

/-- Existence of an etale atlas for an algebraic stack. -/
def HasEtaleAtlas (X : AlgebraicStack.{u}) : Prop :=
  ∃ A : StackChart X.toStack, A.IsEtaleSurjective

/-
Retired provisional Deligne--Mumford criterion.  The equivalence between an etale atlas and an
unramified diagonal was a field, so this was not a proof of the criterion.

/-- The intrinsic Deligne--Mumford criterion for an algebraic stack. -/
structure DeligneMumfordCriterion (X : AlgebraicStack.{u}) where
  etaleAtlas_iff_unramifiedDiagonal :
    HasEtaleAtlas X ↔
      DiagonalHasProperty X.toStack
        (@GromovWitten.AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u})

namespace DeligneMumfordCriterion

/-- Construct a Deligne--Mumford stack from the unramified diagonal criterion. -/
noncomputable def toDeligneMumfordStack {X : AlgebraicStack.{u}}
    (C : DeligneMumfordCriterion X)
    (h : DiagonalHasProperty X.toStack
      (@GromovWitten.AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u})) :
    DeligneMumfordStack.{u} where
  toAlgebraicStack := X
  etaleAtlas := C.etaleAtlas_iff_unramifiedDiagonal.mpr h
  diagonal_unramified := h

end DeligneMumfordCriterion

-/

/-- A common refinement of two stack atlases, retaining both maps and their comparison
2-isomorphism on objects. -/
structure AtlasCommonRefinement {X : FppfStack.{u}}
    (A B : StackChart X) where
  refinement : StackChart X
  toLeft : refinement.scheme ⟶ A.scheme
  toRight : refinement.scheme ⟶ B.scheme
  toLeftComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom toLeft) A.map)
    refinement.map
  toRightComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom toRight) B.map)
    refinement.map
  smoothSurjective : refinement.IsSmoothSurjective

/-- A common refinement of three atlases, with all three comparison cells based on the same
source chart and an explicit cocycle equality. -/
structure AtlasTripleRefinement {X : FppfStack.{u}}
    (A B C : StackChart X) where
  refinement : StackChart X
  toFirst : refinement.scheme ⟶ A.scheme
  toSecond : refinement.scheme ⟶ B.scheme
  toThird : refinement.scheme ⟶ C.scheme
  firstComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom toFirst) A.map)
    refinement.map
  secondComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom toSecond) B.map)
    refinement.map
  thirdComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom toThird) C.map)
    refinement.map
  cocycle :
    Pseudofunctor.StrongTrans.Modification.vcomp
        (Pseudofunctor.StrongTrans.Modification.vcomp
          firstComparison.hom secondComparison.inv)
        (Pseudofunctor.StrongTrans.Modification.vcomp
          secondComparison.hom thirdComparison.inv) =
      Pseudofunctor.StrongTrans.Modification.vcomp
        firstComparison.hom thirdComparison.inv
  smoothSurjective : refinement.IsSmoothSurjective

/-
Retired provisional atlas-refinement existence theorem.  `AtlasCommonRefinement` and
`AtlasTripleRefinement` remain honest witness types, but a construction for arbitrary atlases
must not be supplied as a field.

/-- Presentation-independent atlas refinement theory. -/
structure AtlasRefinementTheory (X : AlgebraicStack.{u}) where
  common (A B : StackChart X.toStack)
    (hA : A.IsSmoothSurjective) (hB : B.IsSmoothSurjective) :
    AtlasCommonRefinement A B
  triple (A B C : StackChart X.toStack)
    (hA : A.IsSmoothSurjective) (hB : B.IsSmoothSurjective)
    (hC : C.IsSmoothSurjective) : AtlasTripleRefinement A B C

-/

/-- A fixed smooth-surjective atlas chosen from the existence theorem in the definition of an
algebraic stack.  The choice is internal to the construction below; callers cannot replace its
point set or topology. -/
noncomputable def AlgebraicStack.chosenSmoothAtlas (X : AlgebraicStack.{u}) :
    StackChart X.toStack :=
  Classical.choose X.smoothAtlas

theorem AlgebraicStack.chosenSmoothAtlas_isSmoothSurjective (X : AlgebraicStack.{u}) :
    X.chosenSmoothAtlas.IsSmoothSurjective :=
  Classical.choose_spec X.smoothAtlas

/-- The actual scheme representing the self-overlap `U ×_X U` of the chosen atlas. -/
noncomputable def AlgebraicStack.chosenAtlasSelfOverlap (X : AlgebraicStack.{u}) :
    X.chosenSmoothAtlas.PullbackPresentation X.chosenSmoothAtlas.scheme
      (X.chosenSmoothAtlas.obj X.chosenSmoothAtlas.scheme
        (𝟙 X.chosenSmoothAtlas.scheme)) :=
  (Classical.choice <|
    X.chosenSmoothAtlas_isSmoothSurjective.1 X.chosenSmoothAtlas.scheme
      (X.chosenSmoothAtlas.obj X.chosenSmoothAtlas.scheme
        (𝟙 X.chosenSmoothAtlas.scheme)))

/-- Two points of the chosen atlas are elementarily related when an actual point of the
self-overlap maps to them under its two projections. -/
noncomputable def AlgebraicStack.atlasPointRelation (X : AlgebraicStack.{u})
    (x y : X.chosenSmoothAtlas.scheme) : Prop :=
  ∃ r : X.chosenAtlasSelfOverlap.space,
    X.chosenAtlasSelfOverlap.fst.base r = x ∧
      X.chosenAtlasSelfOverlap.snd.base r = y

/-- The underlying point type of an algebraic stack: the quotient of points of a smooth atlas
by the equivalence relation generated by its genuine groupoid overlap. -/
noncomputable def UnderlyingStackPoint (X : AlgebraicStack.{u}) : Type u :=
  Quotient (Relation.EqvGen.setoid X.atlasPointRelation)

noncomputable instance (X : AlgebraicStack.{u}) :
    TopologicalSpace (UnderlyingStackPoint X) :=
  TopologicalSpace.coinduced
    (fun x : X.chosenSmoothAtlas.scheme ↦
      Quotient.mk (Relation.EqvGen.setoid X.atlasPointRelation) x :
        X.chosenSmoothAtlas.scheme → UnderlyingStackPoint X)
    inferInstance

/-- The quotient map from the chosen atlas to the constructed underlying stack space. -/
noncomputable def AlgebraicStack.atlasPointMap (X : AlgebraicStack.{u}) :
    X.chosenSmoothAtlas.scheme → UnderlyingStackPoint X :=
  Quotient.mk (Relation.EqvGen.setoid X.atlasPointRelation)

/-- Every constructed stack point has a representative in the chosen atlas. -/
theorem AlgebraicStack.atlasPointMap_surjective (X : AlgebraicStack.{u}) :
    Function.Surjective X.atlasPointMap := by
  intro x
  refine Quotient.inductionOn x (fun u ↦ ?_)
  exact ⟨u, rfl⟩

/-
Retired provisional topology-invariance theorem.  The point equivalence and openness theorem
were fields; the quotient topology above remains the actual construction.

/-- Equivalence of stacks induces an equivalence of their constructed geometric point spaces.
The point equivalence and its topological compatibility remain geometric theorems to prove from
the displayed stack equivalence; unlike the former interface, the two topologies themselves are
fixed constructions. -/
structure StackTopologyEquivalence {X Y : AlgebraicStack.{u}}
    (e : StackEquivalenceData X.toStack Y.toStack) where
  pointEquiv : UnderlyingStackPoint X ≃ UnderlyingStackPoint Y
  isOpen_iff (U : Set (UnderlyingStackPoint X)) :
    IsOpen U ↔ IsOpen (pointEquiv '' U)

-/

/-
Retired provisional product presentation and dimension calculus.  `StackProductPresentation`
asked the caller to supply an algebraic stack `XY` together with the hard equivalence identifying
it with a two-pullback.  Products of algebraic stacks must instead be constructed from the
canonical two-pullback and proved algebraic.  The dimension-calculus record likewise stored the
desired product, smooth, and quotient formulas as fields.

/-- A proposed product of algebraic stacks over the spectrum of a field.  This remains inactive
until algebraicity of the canonical two-pullback is constructed. -/
structure StackProductPresentation
    (X Y XY : AlgebraicStack.{u}) where
  GroundField : Type u
  [groundField : Field GroundField]
  ground : Scheme.{u}
  groundIso : ground ≅ _root_.AlgebraicGeometry.Spec (.of GroundField)
  left : StackHom X.toStack (representedStack ground)
  right : StackHom Y.toStack (representedStack ground)
  pullback : StackTwoPullback.Genuine left right
  productEquivalence : StackEquivalenceData XY.toStack pullback.pullback

attribute [instance] StackProductPresentation.groundField

/-- Product and smooth-morphism identities for stack dimension. -/
structure StackDimensionCalculus where
  productDimension (X Y XY : AlgebraicStack.{u}) (d e : ℤ)
    (product : StackProductPresentation X Y XY) :
    PureStackDimension X d → PureStackDimension Y e →
      PureStackDimension XY (d + e)
  smoothDimension {X Y : AlgebraicStack.{u}} (f : StackHom X.toStack Y.toStack)
    (r : ℕ) (d : ℤ) :
    f.Smooth → f.HasPureRelativeDimension r → PureStackDimension Y d →
      PureStackDimension X (d + r)
  quotientDimension (Q : SmoothQuotientDimension) :
    Q.quotientDimension = Q.spaceDimension - Q.groupDimension

namespace StackDimensionCalculus

@[simp]
theorem quotient_dimension_formula (D : StackDimensionCalculus)
    (Q : SmoothQuotientDimension) :
    Q.quotientDimension = Q.spaceDimension - Q.groupDimension :=
  D.quotientDimension Q

end StackDimensionCalculus

-/

end GromovWitten.AlgebraicGeometry
