/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Geometry
import GromovWitten.AlgebraicGeometry.Stacks.Scheme

/-!
# The intrinsic normal sheaf and intrinsic normal cone

The active declaration in this file is the geometric type of a local etale chart embedded as a
closed subscheme of a smooth ambient scheme.  The former global intrinsic-normal-sheaf, cone,
refinement, purity, and independence packages supplied those constructions or conclusions as
fields and are retired below.  A general intrinsic normal cone is not exported here.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

namespace IntrinsicNormalCone

/-- A local embedding of an etale chart into a scheme smooth over the ground scheme. -/
structure LocalEmbedding (X : DeligneMumfordStack.{u}) (ground : Scheme.{u}) where
  chart : StackChart X.toStack
  chart_etale : chart.IsEtaleSurjective
  ambient : Scheme.{u}
  embedding : chart.scheme ⟶ ambient
  embedding_closed :
    (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}) embedding
  ambientToGround : ambient ⟶ ground
  ambient_smooth :
    (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) ambientToGround

/-
Retired provisional intrinsic-cone construction.  `LocalPresentation`, `Refinement`, and
`Geometry` supplied the local cones, quotient presentations, descent equivalences, cocycles,
purity, and abelian-hull comparison as fields.  `LocalEmbedding` above remains an honest
geometric input.  The declarations below are inactive until those objects and comparisons are
constructed from each embedding and then descended.

/-- Cone-stack objects furnished by one specified local embedding.  The embedding is an index,
not a replaceable field, so a presentation cannot claim to describe a different chart. -/
structure LocalPresentation (X : DeligneMumfordStack.{u})
    (ground : Scheme.{u}) (O : FppfScalarRings.{u})
    (embedding : LocalEmbedding X ground) where
  normalSheaf : AbelianConeStack (representedStack embedding.chart.scheme) O
  normalCone : ClosedConeSubstack normalSheaf.toConeStack
  tangentBundle : AbelianConeStack (representedStack embedding.chart.scheme) O
  tangentAction : ConeStackAction tangentBundle normalCone.cone
  quotientCone : ConeStack (representedStack embedding.chart.scheme) O
  quotientPresentation :
    ConeQuotientPresentation tangentBundle normalCone.cone
  quotient_identification :
    ConeStack.Iso quotientPresentation.quotient quotientCone

namespace LocalPresentation

/-- Recover the local embedding indexing a presentation. -/
abbrev embedding {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}} {e : LocalEmbedding X ground}
    (_P : LocalPresentation X ground O e) : LocalEmbedding X ground := e

end LocalPresentation

/-- A refinement between local embedding presentations.  Both the cone and normal-sheaf
comparisons are equivariant equivalences, and the tangent quotient is retained explicitly. -/
structure Refinement {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}}
    {p q : LocalEmbedding X ground}
    (P : LocalPresentation X ground O p)
    (Q : LocalPresentation X ground O q) where
  chartMap : P.embedding.chart.scheme ⟶ Q.embedding.chart.scheme
  ambientMap : P.embedding.ambient ⟶ Q.embedding.ambient
  embedding_square : P.embedding.embedding ≫ ambientMap =
    chartMap ≫ Q.embedding.embedding
  chartComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      (FppfStack.mapOfSchemeHom chartMap) Q.embedding.chart.map)
    P.embedding.chart.map
  targetConePullback : ConeStackBaseChange Q.quotientCone
    (FppfStack.mapOfSchemeHom chartMap)
  targetSheafPullback : ConeStackBaseChange Q.normalSheaf.toConeStack
    (FppfStack.mapOfSchemeHom chartMap)
  coneComparison : ConeStack.Iso P.quotientCone targetConePullback.pullback
  sheafComparison :
    ConeStack.Iso P.normalSheaf.toConeStack targetSheafPullback.pullback

/-- The globally glued intrinsic normal geometry of a DM stack. -/
structure Geometry (X : DeligneMumfordStack.{u}) (ground : Scheme.{u})
    (O : FppfScalarRings.{u}) where
  /-- The ground scheme is the spectrum of an actual field. -/
  GroundField : Type u
  [groundField : Field GroundField]
  groundIso : ground ≅ _root_.AlgebraicGeometry.Spec (.of GroundField)
  /-- The stack is locally of finite type over that ground. -/
  structureMap : StackHom X.toStack (representedStack ground)
  locallyOfFiniteType : structureMap.LocallyOfFiniteType
  /-- The small-etale derived module category in which the cotangent complex lives. -/
  ModuleCategory : Type u
  [moduleCategory : Category.{u} ModuleCategory]
  [moduleAbelian : Abelian ModuleCategory]
  [moduleDerived : HasDerivedCategory.{u} ModuleCategory]
  Coherent : ModuleCategory → Prop
  FiniteLocallyFree : ModuleCategory → Prop
  IsPerfect : DerivedCategory ModuleCategory → Prop
  cotangentComplex : CotangentComplex.GeometricCotangentComplex Coherent
  normalConstruction : DerivedPicardStack X.toStack O cotangentComplex.object
    FiniteLocallyFree IsPerfect
  /-- The intrinsic normal cone is a closed subcone of the derived Picard stack itself; there is
  no second caller-selected cone stack merely declared isomorphic to it. -/
  cone : ClosedConeSubstack normalConstruction.stack.toConeStack
  /-- A local embedding exists.  All local embeddings—not a caller-selected subfamily—index the
  construction and its descent comparisons below. -/
  localEmbeddingExists : Nonempty (LocalEmbedding X ground)
  localPresentation (p : LocalEmbedding X ground) : LocalPresentation X ground O p
  /-- Genuine restrictions of the global cone and normal sheaf to each chart. -/
  localConePullback (p : LocalEmbedding X ground) : ConeStackBaseChange cone.cone
    (localPresentation p).embedding.chart.map
  localSheafPullback (p : LocalEmbedding X ground) :
    ConeStackBaseChange normalConstruction.stack.toConeStack
    (localPresentation p).embedding.chart.map
  /-- Identification of every local quotient cone with the restriction of the global cone. -/
  localConeIso (p : LocalEmbedding X ground) :
    ConeStack.Iso (localPresentation p).quotientCone (localConePullback p).pullback
  /-- Identification of every local normal quotient with the intrinsic normal sheaf. -/
  localSheafIso (p : LocalEmbedding X ground) :
    ConeStack.Iso (localPresentation p).normalSheaf.toConeStack
      (localSheafPullback p).pullback
  /-- Any two local embeddings have a common refinement. -/
  commonRefinement (p q : LocalEmbedding X ground) : LocalEmbedding X ground
  refinementToLeft (p q : LocalEmbedding X ground) :
    Refinement (localPresentation (commonRefinement p q)) (localPresentation p)
  refinementToRight (p q : LocalEmbedding X ground) :
    Refinement (localPresentation (commonRefinement p q)) (localPresentation q)
  /-- Pulling the left and right local-to-global identifications to the common chart gives the
  same restricted global cone model. -/
  refinementConeToGlobalLeft (p q : LocalEmbedding X ground) : ConeStack.Iso
    (refinementToLeft p q).targetConePullback.pullback
    (localConePullback (commonRefinement p q)).pullback
  refinementConeToGlobalRight (p q : LocalEmbedding X ground) : ConeStack.Iso
    (refinementToRight p q).targetConePullback.pullback
    (localConePullback (commonRefinement p q)).pullback
  refinementSheafToGlobalLeft (p q : LocalEmbedding X ground) : ConeStack.Iso
    (refinementToLeft p q).targetSheafPullback.pullback
    (localSheafPullback (commonRefinement p q)).pullback
  refinementSheafToGlobalRight (p q : LocalEmbedding X ground) : ConeStack.Iso
    (refinementToRight p q).targetSheafPullback.pullback
    (localSheafPullback (commonRefinement p q)).pullback
  /-- The global comparison agrees with the route through the left leg of a common refinement. -/
  refinementCompatibilityLeft (p q : LocalEmbedding X ground) : StackIso2
    (localConeIso (commonRefinement p q)).hom.toStackHom
    (Pseudofunctor.StrongTrans.vcomp
      (refinementToLeft p q).coneComparison.hom.toStackHom
      (refinementConeToGlobalLeft p q).hom.toStackHom)
  /-- The global comparison agrees with the route through the right leg of a common
  refinement.  Together with the preceding field this is the cocycle comparison between the
  two local embeddings. -/
  refinementCompatibilityRight (p q : LocalEmbedding X ground) : StackIso2
    (localConeIso (commonRefinement p q)).hom.toStackHom
    (Pseudofunctor.StrongTrans.vcomp
      (refinementToRight p q).coneComparison.hom.toStackHom
      (refinementConeToGlobalRight p q).hom.toStackHom)
  refinementSheafCompatibilityLeft (p q : LocalEmbedding X ground) : StackIso2
    (localSheafIso (commonRefinement p q)).hom.toStackHom
    (Pseudofunctor.StrongTrans.vcomp
      (refinementToLeft p q).sheafComparison.hom.toStackHom
      (refinementSheafToGlobalLeft p q).hom.toStackHom)
  refinementSheafCompatibilityRight (p q : LocalEmbedding X ground) : StackIso2
    (localSheafIso (commonRefinement p q)).hom.toStackHom
    (Pseudofunctor.StrongTrans.vcomp
      (refinementToRight p q).sheafComparison.hom.toStackHom
      (refinementSheafToGlobalRight p q).hom.toStackHom)
  /-- An algebraic-stack model of the cone total space. -/
  coneAlgebraic : AlgebraicStack.{u}
  coneAlgebraic_eq : coneAlgebraic.toStack = cone.cone.total
  /-- The intrinsic cone is pure of stack dimension zero. -/
  pureDimensionZero : PureStackDimension coneAlgebraic 0
  /-- Its abelian hull. -/
  abelianHull : AbelianHull cone.cone
  /-- The abelian hull is the intrinsic normal sheaf. -/
  abelianHullIso :
    ConeStack.Iso abelianHull.hull.toConeStack normalConstruction.stack.toConeStack

attribute [instance] Geometry.groundField Geometry.moduleCategory Geometry.moduleAbelian
  Geometry.moduleDerived

/-- The intrinsic normal sheaf is definitionally the resolution-independent derived Picard
stack of the cotangent complex. -/
abbrev Geometry.normalSheaf
    {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}} (N : Geometry X ground O) :
    AbelianConeStack X.toStack O :=
  N.normalConstruction.stack

/-- Intrinsic normal geometry formed over the canonical sheaf of regular functions. -/
abbrev CanonicalGeometry (X : DeligneMumfordStack.{u}) (ground : Scheme.{u}) :=
  Geometry X ground canonicalFppfScalarRings

namespace Geometry

variable {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
  {O : FppfScalarRings.{u}}

/-- The intrinsic normal cone is a representable closed substack of the normal sheaf. -/
theorem cone_isClosed (N : Geometry X ground O) :
    N.cone.inclusion.toStackHom.ClosedImmersion :=
  N.cone.inclusion_closed

/-- The absolute intrinsic geometry is over a field and locally of finite type. -/
theorem locallyOfFiniteType_over_ground (N : Geometry X ground O) :
    N.structureMap.LocallyOfFiniteType :=
  N.locallyOfFiniteType

/-- Recomputing from any chosen local embedding gives an equivariantly equivalent cone stack. -/
def local_independence (N : Geometry X ground O) (p : LocalEmbedding X ground) :
    ConeStack.Iso (N.localPresentation p).quotientCone (N.localConePullback p).pullback :=
  N.localConeIso p

/-- The local-presentation system is nonempty. -/
theorem presentation_exists (N : Geometry X ground O) :
    Nonempty (LocalEmbedding X ground) :=
  N.localEmbeddingExists

/-- Two local presentations have an explicit common refinement. -/
theorem common_refinement_exists (N : Geometry X ground O)
    (p q : LocalEmbedding X ground) :
    Nonempty (LocalEmbedding X ground) :=
  ⟨N.commonRefinement p q⟩

/-- The intrinsic cone has stack dimension zero independently of the chosen atlas. -/
theorem pure_dimension_zero (N : Geometry X ground O) :
    PureStackDimension N.coneAlgebraic 0 :=
  N.pureDimensionZero

/-- The intrinsic normal sheaf is the abelian hull of the intrinsic cone. -/
def abelian_hull_identification (N : Geometry X ground O) :
    ConeStack.Iso N.abelianHull.hull.toConeStack N.normalSheaf.toConeStack :=
  N.abelianHullIso

end Geometry

-/

/-
Retired provisional theorem containers.  `ProductComparison` and `SmoothSpecialization` stored
the product and smooth-specialization identifications instead of constructing them from the
intrinsic cone.  They remain future theorems, not accepted input structures.

/-- Product comparison for intrinsic normal geometry.  Both the base product and the cone
product are genuine bicategorical pullbacks; the supplied model over `XY` is identified with
those pullbacks before it is compared with the intrinsic cone of `XY`. -/
structure ProductComparison
    {X Y XY : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}}
    (NX : Geometry X ground O) (NY : Geometry Y ground O)
    (NXY : Geometry XY ground O) where
  baseProduct : StackTwoPullback.Genuine NX.structureMap NY.structureMap
  baseProductEquivalence : StackEquivalenceData XY.toStack baseProduct.pullback
  coneProduct : StackTwoPullback.Genuine
    (Pseudofunctor.StrongTrans.vcomp NX.cone.cone.projection NX.structureMap)
    (Pseudofunctor.StrongTrans.vcomp NY.cone.cone.projection NY.structureMap)
  productCone : ConeStack XY.toStack O
  productConeEquivalence : StackEquivalenceData productCone.total coneProduct.pullback
  comparison : ConeStack.Iso productCone NXY.cone.cone

/-- Smooth specialization data identifying the intrinsic cone with the classifying stack of the
tangent bundle. -/
structure SmoothSpecialization {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
    {O : FppfScalarRings.{u}} (N : Geometry X ground O) where
  smooth : N.structureMap.Smooth
  tangent : AbelianConeStack X.toStack O
  classifyingTangent : ConeStack X.toStack O
  coneIso : ConeStack.Iso N.cone.cone classifyingTangent
  sheafIso : ConeStack.Iso N.normalSheaf.toConeStack classifyingTangent

-/

end IntrinsicNormalCone

end GromovWitten.AlgebraicGeometry
