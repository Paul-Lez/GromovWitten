/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntrinsicNormalCone.Basic
import GromovWitten.AlgebraicGeometry.ObstructionTheory.Perfect

/-!
# Geometric realization of obstruction theories

The active portion supplies only isomorphisms between obstruction theories over a fixed derived
target.  The former induced closed immersion, intrinsic-cone image, square-zero interpretation,
and perfect geometric realization supplied their essential geometry as fields and are retired
below.  Those general constructions are not exported.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry.DerivedObstructionTheory

open IntrinsicNormalCone

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
  {O : FppfScalarRings.{u}} {L : DerivedCategory C}

/-- A derived isomorphism of obstruction theories, including compatibility with their maps to
the cotangent object. -/
structure Iso {T T' : ObstructionTheory L} where
  sourceIso : T.E ≅ T'.E
  comm : sourceIso.hom ≫ T'.φ = T.φ

namespace Iso

variable {T T' T'' : ObstructionTheory L}

/-- Identity isomorphism of obstruction theories. -/
noncomputable def refl (T : ObstructionTheory L) : Iso (T := T) (T' := T) where
  sourceIso := CategoryTheory.Iso.refl _
  comm := by simp

/-- Composition of isomorphisms of obstruction theories. -/
noncomputable def trans (e : Iso (T := T) (T' := T'))
    (e' : Iso (T := T') (T' := T'')) : Iso (T := T) (T' := T'') where
  sourceIso := e.sourceIso.trans e'.sourceIso
  comm := by simp only [CategoryTheory.Iso.trans_hom, Category.assoc, e'.comm, e.comm]

end Iso

/-
Retired provisional geometric-realization API.  It supplied the derived Picard target, induced
normal map, closedness, cone image, purity, perfect presentation, and deformation comparison as
fields.  These declarations are inactive until those maps and theorems are derived from the
actual obstruction-theory morphism.  The categorical obstruction-theory `Iso` above remains
active and constructed.

/-- The geometric cone-stack data induced by an obstruction theory. -/
structure GeometricRealization
    (N : IntrinsicNormalCone.Geometry X ground O) (T : ObstructionTheory L) where
  /-- Comparison with the small-etale derived category used by the intrinsic geometry. -/
  derivedComparison : DerivedCategory C ≌ DerivedCategory N.ModuleCategory
  cotangentComparison : derivedComparison.functor.obj L ≅ N.cotangentComplex.object
  obstructionTargetConstruction : DerivedPicardStack X.toStack O
    (derivedComparison.functor.obj T.E) N.FiniteLocallyFree N.IsPerfect
  /-- The dual map induced by `E → L_X`, landing in the derived Picard construction itself
  rather than a second caller-selected cone stack declared isomorphic to it. -/
  normalMap : ConeStack.Hom N.normalSheaf.toConeStack
    obstructionTargetConstruction.stack.toConeStack
  /-- The cohomological obstruction-theory conditions make this map a closed immersion. -/
  normalMap_closed : normalMap.toStackHom.ClosedImmersion
  /-- Image of the intrinsic normal cone in the obstruction target. -/
  obstructionCone : ClosedConeSubstack obstructionTargetConstruction.stack.toConeStack
  /-- The intrinsic cone and its image are equivalent as cone stacks. -/
  coneImageIso : ConeStack.Iso N.cone.cone obstructionCone.cone
  /-- An algebraic model used to state purity. -/
  coneAlgebraic : AlgebraicStack.{u}
  coneAlgebraic_eq : coneAlgebraic.toStack = obstructionCone.cone.total
  pureDimensionZero : PureStackDimension coneAlgebraic 0

/-- The obstruction target is definitionally the derived Picard stack of the obstruction
complex. -/
abbrev GeometricRealization.obstructionTarget
    {N : IntrinsicNormalCone.Geometry X ground O} {T : ObstructionTheory L}
    (G : GeometricRealization N T) : AbelianConeStack X.toStack O :=
  G.obstructionTargetConstruction.stack

namespace GeometricRealization

variable {N : IntrinsicNormalCone.Geometry X ground O} {T : ObstructionTheory L}

/-- The induced map of normal sheaves is a representable closed immersion. -/
theorem normal_closed (G : GeometricRealization N T) :
    G.normalMap.toStackHom.ClosedImmersion :=
  G.normalMap_closed

/-- The obstruction cone is closed in `h¹/h⁰(E^∨)`. -/
theorem cone_closed (G : GeometricRealization N T) :
    G.obstructionCone.inclusion.toStackHom.ClosedImmersion :=
  G.obstructionCone.inclusion_closed

/-- The obstruction cone is pure of stack dimension zero. -/
theorem cone_pure_dimension_zero (G : GeometricRealization N T) :
    PureStackDimension G.coneAlgebraic 0 :=
  G.pureDimensionZero

end GeometricRealization

/-- Invariance data under a derived isomorphism of obstruction theories. -/
structure GeometricIso
    {N : IntrinsicNormalCone.Geometry X ground O}
    {T T' : ObstructionTheory L}
    (e : Iso (T := T) (T' := T'))
    (G : GeometricRealization N T) (G' : GeometricRealization N T') where
  targetIso : ConeStack.Iso G.obstructionTarget.toConeStack G'.obstructionTarget.toConeStack
  coneIso : ConeStack.Iso G.obstructionCone.cone G'.obstructionCone.cone
  compatible : StackIso2
    (Pseudofunctor.StrongTrans.vcomp
      G.normalMap.toStackHom targetIso.hom.toStackHom)
    G'.normalMap.toStackHom

/-- Geometric realization of a perfect obstruction theory.  The target is a vector-bundle
stack, while a global two-term resolution remains a separate later hypothesis. -/
structure PerfectGeometricRealization
    (IsPerfect : DerivedCategory C → Prop)
    (N : IntrinsicNormalCone.Geometry X ground O)
    (T : PerfectObstructionTheory IsPerfect L) where
  geometry : GeometricRealization N T.toObstructionTheory
  /-- Perfectness after transport to the intrinsic geometry's derived module category.  This is
  proposition-valued; the vector-bundle target and its comparison are then forced by the single
  `DerivedPicardStack` construction rather than supplied independently. -/
  transportedPerfect : PerfectData N.IsPerfect
    (geometry.derivedComparison.functor.obj T.E)

namespace PerfectGeometricRealization

variable {IsPerfect : DerivedCategory C → Prop}
  {N : IntrinsicNormalCone.Geometry X ground O}
  {T : PerfectObstructionTheory IsPerfect L}

/-- The vector-bundle presentation selected by the derived Picard construction from the
transported perfectness proof. -/
noncomputable def vectorBundleTarget (G : PerfectGeometricRealization IsPerfect N T) :
    VectorBundleStack X.toStack O :=
  G.geometry.obstructionTargetConstruction.perfectPresentation G.transportedPerfect

/-- The canonical comparison from the derived obstruction target to its forced vector-bundle
presentation. -/
noncomputable def targetIso (G : PerfectGeometricRealization IsPerfect N T) :
    ConeStack.Iso G.geometry.obstructionTarget.toConeStack
      G.vectorBundleTarget.toConeStack :=
  (G.geometry.obstructionTargetConstruction.perfectPresentationIso
    G.transportedPerfect).symm

/-- The map from the intrinsic cone to the vector-bundle obstruction target is the composite of
the intrinsic-cone inclusion, the map induced by the obstruction theory, and the canonical
derived-Picard presentation comparison. -/
noncomputable def coneToVectorBundleTarget
    (G : PerfectGeometricRealization IsPerfect N T) :
    StackHom N.cone.cone.total G.vectorBundleTarget.total :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp N.cone.inclusion.toStackHom
      G.geometry.normalMap.toStackHom)
    G.targetIso.hom.toStackHom

/-- The virtual rank is determined by the rank of the geometric obstruction target. -/
noncomputable def virtualRank (G : PerfectGeometricRealization IsPerfect N T) : ℤ :=
  -G.vectorBundleTarget.stackRank

/-- The geometric rank formula is definitional, rather than supplied theorem data. -/
@[simp] theorem rank_eq (G : PerfectGeometricRealization IsPerfect N T) :
    G.virtualRank = -G.vectorBundleTarget.stackRank :=
  rfl

end PerfectGeometricRealization

/-- Comparison between the cotangent obstruction and the obstruction class obtained by
precomposing with `E → L_X`. -/
structure DeformationRealization
    (T : ObstructionTheory L) (J : DerivedCategory C) where
  cotangentProblem : CotangentComplex.SquareZeroLiftingProblem L J
  theoryProblem : CotangentComplex.SquareZeroLiftingProblem T.E J
  obstruction_formula :
    theoryProblem.obstruction = T.φ ≫ cotangentProblem.obstruction
  liftEquivalence : cotangentProblem.Lift ≌ theoryProblem.Lift

namespace DeformationRealization

variable {T : ObstructionTheory L} {J : DerivedCategory C}

/-- The obstruction supplied by `E` vanishes whenever the cotangent obstruction vanishes. -/
theorem theory_obstruction_zero_of_cotangent_zero
    (D : DeformationRealization T J) (h : D.cotangentProblem.obstruction = 0) :
    D.theoryProblem.obstruction = 0 := by
  rw [D.obstruction_formula, h]
  simp

/-- Existence of a lift is invariant under the obstruction-theory description. -/
theorem cotangent_hasLift_iff_theory_hasLift (D : DeformationRealization T J) :
    Nonempty D.cotangentProblem.Lift ↔ Nonempty D.theoryProblem.Lift := by
  constructor
  · rintro ⟨x⟩
    exact ⟨D.liftEquivalence.functor.obj x⟩
  · rintro ⟨x⟩
    exact ⟨D.liftEquivalence.inverse.obj x⟩

end DeformationRealization

-/

end GromovWitten.AlgebraicGeometry.DerivedObstructionTheory
