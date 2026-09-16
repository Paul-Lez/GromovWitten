/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntrinsicNormalCone.Basic
import GromovWitten.AlgebraicGeometry.Stacks.Geometry

/-!
# Relative intrinsic normal cones

This module records the intended relative intrinsic-cone interface as an inactive checklist.
Its former relative Picard target, closed cone, purity, and base-change packages supplied the
required geometry as fields and are retired below.  No general relative intrinsic cone is
currently exported.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry.IntrinsicNormalCone

universe u

/-
Retired provisional relative intrinsic-cone API.  It supplied the relative derived Picard stack,
closed cone, purity, and every base-change comparison as fields.  These declarations are
inactive until they can be constructed from the relative cotangent complex and actual cartesian
squares.

/-- Relative intrinsic normal geometry over a smooth pure-dimensional base. -/
structure RelativeGeometry
    (X : DeligneMumfordStack.{u}) (Y : AlgebraicStack.{u})
    (f : StackHom X.toStack Y.toStack)
    (O : FppfScalarRings.{u}) where
  relativeDM : RelativeDeligneMumfordMorphism f
  /-- The smooth base is relative to an explicit ground scheme. -/
  ground : Scheme.{u}
  GroundField : Type u
  [groundField : Field GroundField]
  groundIso : ground ≅ _root_.AlgebraicGeometry.Spec (.of GroundField)
  baseToGround : StackHom Y.toStack (representedStack ground)
  baseSmooth : baseToGround.Smooth
  baseDimension : ℤ
  basePureDimension : PureStackDimension Y baseDimension
  ModuleCategory : Type u
  [moduleCategory : Category.{u} ModuleCategory]
  [moduleAbelian : Abelian ModuleCategory]
  [moduleDerived : HasDerivedCategory.{u} ModuleCategory]
  Coherent : ModuleCategory → Prop
  FiniteLocallyFree : ModuleCategory → Prop
  IsPerfect : DerivedCategory ModuleCategory → Prop
  relativeCotangentComplex : CotangentComplex.GeometricCotangentComplex Coherent
  normalConstruction : DerivedPicardStack X.toStack O relativeCotangentComplex.object
    FiniteLocallyFree IsPerfect
  /-- The relative cone lies directly in the derived Picard construction; no second normal
  sheaf can be supplied and merely declared isomorphic to it. -/
  cone : ClosedConeSubstack normalConstruction.stack.toConeStack
  coneAlgebraic : AlgebraicStack.{u}
  coneAlgebraic_eq : coneAlgebraic.toStack = cone.cone.total
  /-- When `Y` is smooth pure `d`-dimensional, the relative cone is pure `d`-dimensional. -/
  pureDimension : PureStackDimension coneAlgebraic baseDimension

attribute [instance] RelativeGeometry.groundField RelativeGeometry.moduleCategory
  RelativeGeometry.moduleAbelian RelativeGeometry.moduleDerived

/-- The relative intrinsic normal sheaf is definitionally the derived Picard stack of the
relative cotangent complex. -/
abbrev RelativeGeometry.normalSheaf
    {X : DeligneMumfordStack.{u}} {Y : AlgebraicStack.{u}}
    {f : StackHom X.toStack Y.toStack} {O : FppfScalarRings.{u}}
    (N : RelativeGeometry X Y f O) : AbelianConeStack X.toStack O :=
  N.normalConstruction.stack

/-- Relative intrinsic normal geometry over the canonical fppf structure sheaf. -/
abbrev CanonicalRelativeGeometry
    (X : DeligneMumfordStack.{u}) (Y : AlgebraicStack.{u})
    (f : StackHom X.toStack Y.toStack) :=
  RelativeGeometry X Y f canonicalFppfScalarRings

namespace RelativeGeometry

variable {X : DeligneMumfordStack.{u}} {Y : AlgebraicStack.{u}}
  {f : StackHom X.toStack Y.toStack} {O : FppfScalarRings.{u}}

theorem cone_isClosed (N : RelativeGeometry X Y f O) :
    N.cone.inclusion.toStackHom.ClosedImmersion :=
  N.cone.inclusion_closed

theorem cone_pure_baseDimension (N : RelativeGeometry X Y f O) :
    PureStackDimension N.coneAlgebraic N.baseDimension :=
  N.pureDimension

/-- The base of the relative theory is genuinely smooth and pure-dimensional. -/
theorem base_smooth_and_pure (N : RelativeGeometry X Y f O) :
    N.baseToGround.Smooth ∧
      PureStackDimension Y N.baseDimension :=
  ⟨N.baseSmooth, N.basePureDimension⟩

end RelativeGeometry

/-- Canonical comparison under an arbitrary cartesian base change. -/
structure RelativeBaseChange
    {X X' : DeligneMumfordStack.{u}} {Y Y' : AlgebraicStack.{u}}
    {f : StackHom X.toStack Y.toStack}
    {f' : StackHom X'.toStack Y'.toStack}
    {O : FppfScalarRings.{u}}
    (N : RelativeGeometry X Y f O) (N' : RelativeGeometry X' Y' f' O) where
  baseMap : StackHom Y'.toStack Y.toStack
  sourceMap : StackHom X'.toStack X.toStack
  squareComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp sourceMap f)
    (Pseudofunctor.StrongTrans.vcomp f' baseMap)
  sourcePullback : StackTwoPullback.Genuine f baseMap
  sourceEquivalence : StackEquivalenceData X'.toStack sourcePullback.pullback
  targetPullback : StackTwoPullback.Genuine
    (Pseudofunctor.StrongTrans.vcomp N.cone.cone.projection f) baseMap
  coneMap : StackHom N'.cone.cone.total targetPullback.pullback
  /-- General base change gives a closed immersion. -/
  coneMap_closed : coneMap.ClosedImmersion

/-- Flat base change upgrades the canonical comparison to an equivalence. -/
structure FlatRelativeBaseChange
    {X X' : DeligneMumfordStack.{u}} {Y Y' : AlgebraicStack.{u}}
    {f : StackHom X.toStack Y.toStack}
    {f' : StackHom X'.toStack Y'.toStack}
    {O : FppfScalarRings.{u}}
    (N : RelativeGeometry X Y f O) (N' : RelativeGeometry X' Y' f' O)
    extends RelativeBaseChange N N' where
  baseMap_flat : baseMap.Flat
  coneEquivalence : StackEquivalenceData N'.cone.cone.total targetPullback.pullback
  normalPullback : StackTwoPullback.Genuine
    (Pseudofunctor.StrongTrans.vcomp N.normalSheaf.projection f) baseMap
  normalEquivalence : StackEquivalenceData N'.normalSheaf.total normalPullback.pullback

/-- Exact cone-stack sequence induced by an lci morphism. -/
structure IntrinsicPullbackSequence
    {X Y : DeligneMumfordStack.{u}} {O : FppfScalarRings.{u}}
    (NX : ConeStack X.toStack O) (NY : ConeStack X.toStack O) where
  relativeNormal : AbelianConeStack X.toStack O
  first : ConeStack.Hom NX NY
  second : ConeStack.Hom NY relativeNormal.toConeStack
  compositeIso : StackIso2
    (Pseudofunctor.StrongTrans.vcomp first.toStackHom second.toStackHom)
    (Pseudofunctor.StrongTrans.vcomp NX.projection relativeNormal.vertex)

-/

end GromovWitten.AlgebraicGeometry.IntrinsicNormalCone
