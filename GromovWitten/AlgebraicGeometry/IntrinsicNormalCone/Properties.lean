/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Geometry
import GromovWitten.AlgebraicGeometry.IntrinsicNormalCone.Relative
import GromovWitten.AlgebraicGeometry.Stacks.Scheme

/-!
# Invariance and specializations of the intrinsic normal cone

This module is an inactive checklist for invariance, field extension, local-complete-intersection,
smooth-specialization, and product properties of a future intrinsic normal cone.  The former
records stored the desired comparison isomorphisms as fields, so none of these general theorems
is currently exported.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry.IntrinsicNormalCone

universe u

/-
Retired provisional theorem containers.  Each record below stored the desired invariance,
specialization, or product isomorphism as a field.  No downstream construction used them, so
they are deliberately unavailable until the corresponding comparisons are constructed.

/-- Invariance under an equivalence of Deligne--Mumford stacks. -/
structure EquivalenceInvariance
    {X Y : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}}
    (NX : Geometry X ground O) (NY : Geometry Y ground O)
    (e : StackEquivalenceData X.toStack Y.toStack) where
  normalPullback : StackTwoPullback.Genuine NX.normalSheaf.projection e.inv
  conePullback : StackTwoPullback.Genuine NX.cone.cone.projection e.inv
  transportedNormalSheaf : ConeStack Y.toStack O
  transportedCone : ConeStack Y.toStack O
  transportedNormalEquivalence :
    StackEquivalenceData transportedNormalSheaf.total normalPullback.pullback
  transportedConeEquivalence :
    StackEquivalenceData transportedCone.total conePullback.pullback
  normalIso : ConeStack.Iso transportedNormalSheaf NY.normalSheaf.toConeStack
  coneIso : ConeStack.Iso transportedCone NY.cone.cone
  closedImmersionCompatible :
    transportedCone.total = NY.cone.cone.total

/-- Scalar-extension comparison for intrinsic normal geometry. -/
structure ScalarExtensionInvariance
    {X X' : DeligneMumfordStack.{u}} {k k' : Scheme.{u}}
    {O : FppfScalarRings.{u}}
    (N : Geometry X k O) (N' : Geometry X' k' O) where
  groundMap : k' ⟶ k
  baseChange : StackHom X'.toStack X.toStack
  structureSquare : StackIso2
    (Pseudofunctor.StrongTrans.vcomp baseChange N.structureMap)
    (Pseudofunctor.StrongTrans.vcomp N'.structureMap
      (FppfStack.mapOfSchemeHom groundMap))
  normalPullback : StackTwoPullback.Genuine N.normalSheaf.projection baseChange
  conePullback : StackTwoPullback.Genuine N.cone.cone.projection baseChange
  normalBaseChange : ConeStack X'.toStack O
  coneBaseChange : ConeStack X'.toStack O
  normalPullbackEquivalence :
    StackEquivalenceData normalBaseChange.total normalPullback.pullback
  conePullbackEquivalence :
    StackEquivalenceData coneBaseChange.total conePullback.pullback
  normalIso : ConeStack.Iso normalBaseChange N'.normalSheaf.toConeStack
  coneIso : ConeStack.Iso coneBaseChange N'.cone.cone

/-- The local-complete-intersection characterization `C_X = N_X`. -/
structure LCISpecialization
    {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}} (N : Geometry X ground O) where
  structureMap_lci : N.structureMap.HasRepresentableProperty
    (@GromovWitten.AlgebraicGeometry.LocallyCompleteIntersection :
      MorphismProperty Scheme.{u})
  coneEqualsNormal : ConeStack.Iso N.cone.cone N.normalSheaf.toConeStack

/-- Product formula for intrinsic normal sheaves and cones. -/
structure ProductFormula
    {X Y XY : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}}
    (NX : Geometry X ground O) (NY : Geometry Y ground O)
    (NXY : Geometry XY ground O) where
  baseProduct : StackTwoPullback.Genuine NX.structureMap NY.structureMap
  baseProductEquivalence : StackEquivalenceData XY.toStack baseProduct.pullback
  normalProduct : StackTwoPullback.Genuine
    (Pseudofunctor.StrongTrans.vcomp NX.normalSheaf.projection NX.structureMap)
    (Pseudofunctor.StrongTrans.vcomp NY.normalSheaf.projection NY.structureMap)
  coneProduct : StackTwoPullback.Genuine
    (Pseudofunctor.StrongTrans.vcomp NX.cone.cone.projection NX.structureMap)
    (Pseudofunctor.StrongTrans.vcomp NY.cone.cone.projection NY.structureMap)
  productNormalSheaf : AbelianConeStack XY.toStack O
  productCone : ConeStack XY.toStack O
  productNormalEquivalence :
    StackEquivalenceData productNormalSheaf.total normalProduct.pullback
  productConeEquivalence : StackEquivalenceData productCone.total coneProduct.pullback
  normalIso : ConeStack.Iso productNormalSheaf.toConeStack NXY.normalSheaf.toConeStack
  coneIso : ConeStack.Iso productCone NXY.cone.cone
  pureDimension : PureStackDimension NXY.coneAlgebraic 0

/-- Smooth intrinsic normal geometry is the classifying stack of the tangent bundle. -/
def smooth_cone_eq_classifying_tangent
    {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}} {N : Geometry X ground O}
    (S : SmoothSpecialization N) :
    ConeStack.Iso N.cone.cone S.classifyingTangent :=
  S.coneIso

/-- For an lci stack the intrinsic cone is its intrinsic normal sheaf. -/
def lci_cone_eq_normalSheaf
    {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}} {N : Geometry X ground O}
    (S : LCISpecialization N) :
    ConeStack.Iso N.cone.cone N.normalSheaf.toConeStack :=
  S.coneEqualsNormal

-/

end GromovWitten.AlgebraicGeometry.IntrinsicNormalCone
