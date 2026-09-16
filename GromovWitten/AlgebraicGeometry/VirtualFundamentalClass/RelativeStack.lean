/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntrinsicNormalCone.Relative
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Stack

/-!
# Relative virtual fundamental classes on DM stacks

This module records the target grading for a future relative stack construction.  The former
relative Picard target, cone image, resolved pullback, purity, Gysin, and base-change packages
supplied their essential geometry and formulas as fields and are retired below.  No general
relative stack virtual class is exported.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open CategoryTheory
open IntersectionTheory IntrinsicNormalCone DerivedObstructionTheory

universe w v u

noncomputable section

/-
The former relative stack API below supplied the derived Picard target, closed cone image,
resolved pullback, purity, fundamental-cycle geometry, pushforward, Gysin theory, and base-change
formula as fields.  It is intentionally inactive until those constructions and theorems are
available independently.

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X : DeligneMumfordStack.{u}} {Y : AlgebraicStack.{u}}
  {f : StackHom X.toStack Y.toStack}
  {O : FppfScalarRings.{u}} {Lrelative : DerivedCategory C}
  {IsPerfect : DerivedCategory C → Prop}
  {FiniteLocallyFree : C → Prop} {rank : C → ℕ}
  {N : RelativeGeometry X Y f O}
  (VX : VistoliCyclePresentation X)

/-- Cone-stack realization of a relative perfect obstruction theory. -/
structure RelativePerfectGeometry where
  theory : PerfectObstructionTheory IsPerfect Lrelative
  derivedComparison : DerivedCategory C ≌ DerivedCategory N.ModuleCategory
  cotangentComparison :
    derivedComparison.functor.obj Lrelative ≅ N.relativeCotangentComplex.object
  obstructionTargetConstruction : DerivedPicardStack X.toStack O
    (derivedComparison.functor.obj theory.E) N.FiniteLocallyFree N.IsPerfect
  /-- Perfectness transported to the relative geometry's module category.  It determines the
  vector-bundle presentation below and carries no selectable target stack. -/
  transportedPerfect : PerfectData N.IsPerfect
    (derivedComparison.functor.obj theory.E)
  normalMap : ConeStack.Hom N.normalSheaf.toConeStack
    obstructionTargetConstruction.stack.toConeStack
  normalMap_closed : normalMap.toStackHom.ClosedImmersion
  obstructionCone : ClosedConeSubstack obstructionTargetConstruction.stack.toConeStack
  coneImageIso : ConeStack.Iso N.cone.cone obstructionCone.cone

namespace RelativePerfectGeometry

variable {VX}

/-- The obstruction target before choosing a vector-bundle presentation. -/
abbrev obstructionTarget (G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)) : AbelianConeStack X.toStack O :=
  G.obstructionTargetConstruction.stack

/-- The vector-bundle target forced by the derived Picard construction and transported
perfectness proof. -/
noncomputable def vectorBundleTarget (G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)) : VectorBundleStack X.toStack O :=
  G.obstructionTargetConstruction.perfectPresentation G.transportedPerfect

/-- Canonical comparison from the derived obstruction target to that vector-bundle
presentation. -/
noncomputable def targetIso (G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)) :
    ConeStack.Iso G.obstructionTarget.toConeStack G.vectorBundleTarget.toConeStack :=
  (G.obstructionTargetConstruction.perfectPresentationIso G.transportedPerfect).symm

/-- Canonical composite from the relative intrinsic cone to the vector-bundle obstruction
target. -/
noncomputable def coneToVectorBundleTarget
    (G : RelativePerfectGeometry (N := N)
      (IsPerfect := IsPerfect) (Lrelative := Lrelative)) :
    StackHom N.cone.cone.total G.vectorBundleTarget.total :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.StrongTrans.vcomp N.cone.inclusion.toStackHom
      G.normalMap.toStackHom)
    G.targetIso.hom.toStackHom

/-- The relative virtual rank is determined by the vector-bundle obstruction target. -/
noncomputable def virtualRank (G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)) : ℤ :=
  -G.vectorBundleTarget.stackRank

/-- The relative geometric rank formula is definitional, rather than supplied theorem data. -/
@[simp] theorem rank_eq (G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)) :
    G.virtualRank = -G.vectorBundleTarget.stackRank :=
  rfl

end RelativePerfectGeometry

/-- A resolved relative cone presentation. -/
structure RelativeResolvedStackCone (G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)) where
  resolution : GlobalTwoTermResolution FiniteLocallyFree G.theory.E
  F₁ : DeligneMumfordStack.{u}
  chowF₁ : VistoliCyclePresentation F₁
  virtualRank_eq_geometry :
    (rank (resolution.complex.X 0) : ℤ) -
      (rank (resolution.complex.X (-1)) : ℤ) = G.virtualRank
  bundleToTarget : StackHom F₁.toStack G.vectorBundleTarget.total
  resolvedPullback : StackTwoPullback.Genuine G.coneToVectorBundleTarget bundleToTarget
  resolvedCone : DeligneMumfordStack.{u}
  resolvedConeEquiv :
    StackEquivalenceData resolvedCone.toStack resolvedPullback.pullback
  resolvedConeToBundle : StackHom resolvedCone.toStack F₁.toStack
  resolvedConeToBundleComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp resolvedConeEquiv.hom resolvedPullback.snd)
    resolvedConeToBundle
  resolvedConeToBundle_closed : resolvedConeToBundle.ClosedImmersion
  coneProjection : StackHom resolvedPullback.pullback N.cone.cone.total
  coneProjectionComparison : StackIso2 coneProjection resolvedPullback.fst
  coneProjection_smooth : coneProjection.Smooth
  coneProjection_pureRelativeDimension :
    coneProjection.HasPureRelativeDimension (rank (resolution.complex.X 0))
  homotopy : StackVectorBundleHomotopyInvariance VX chowF₁
    (rank (resolution.complex.X (-1)))
  resolvedCone_pure : PureStackDimension resolvedCone.toAlgebraicStack
    (N.baseDimension + (rank (resolution.complex.X 0) : ℤ))
  resolvedConeChow : VistoliCyclePresentation resolvedCone
  /-- Finiteness and purity of the actual irreducible components.  The fundamental cycle is
  constructed from these propositions and is not supplied as Chow-class data. -/
  resolvedConeFundamentalGeometry : StackFundamentalCycleGeometry resolvedCone
    (N.baseDimension + (rank (resolution.complex.X 0) : ℤ))
  resolvedConePushforward : ProperPushforward resolvedConeChow chowF₁
    resolvedConeToBundle
      (N.baseDimension + (rank (resolution.complex.X 0) : ℤ))

namespace RelativeResolvedStackCone

variable {VX} {G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)}
  (F : RelativeResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
    (rank := rank) G)

/-- Rank of the degree-zero term of the relative resolution. -/
def rankF₀ : ℕ := rank (F.resolution.complex.X 0)

/-- Rank of the degree-minus-one term of the relative resolution. -/
def rankF₁ : ℕ := rank (F.resolution.complex.X (-1))

/-- The relative resolved presentation uses the canonical obstruction-theory cone map. -/
noncomputable abbrev coneToTarget :
    StackHom N.cone.cone.total G.vectorBundleTarget.total :=
  G.coneToVectorBundleTarget

/-- The relative resolved cone's canonical generic-length-weighted fundamental class. -/
noncomputable def resolvedConeFundamental :
    F.resolvedConeChow.chow (N.baseDimension + (F.rankF₀ : ℤ)) :=
  F.resolvedConeFundamentalGeometry.fundamentalClass F.resolvedConeChow

/-- The resolved relative cone cycle is the proper pushforward of its displayed fundamental
class, not independently supplied data. -/
noncomputable def coneClass : F.chowF₁.chow (N.baseDimension + (F.rankF₀ : ℤ)) :=
  F.resolvedConePushforward.map.induced F.resolvedConeFundamental

@[simp]
theorem coneClass_eq_pushforward :
    F.coneClass = F.resolvedConePushforward.map.induced F.resolvedConeFundamental :=
  rfl

/-- Rank of the relative obstruction complex. -/
def virtualRank : ℤ := (F.rankF₀ : ℤ) - (F.rankF₁ : ℤ)

/-- Dimension `d + rank(E)` of the relative virtual class. -/
def virtualDimension : ℤ := N.baseDimension + F.virtualRank

theorem virtualDimension_add_rankF₁ :
    F.virtualDimension + (F.rankF₁ : ℤ) =
      N.baseDimension + (F.rankF₀ : ℤ) := by
  simp [virtualDimension, virtualRank, add_assoc]

/-- Cone class in the source degree of zero-section Gysin. -/
def coneClassAtGysinDegree :
    F.chowF₁.chow (F.virtualDimension + (F.rankF₁ : ℤ)) :=
  F.chowF₁.cast F.virtualDimension_add_rankF₁.symm F.coneClass

/-- Relative Behrend--Fantechi virtual class. -/
def virtualClass : VX.chow F.virtualDimension :=
  F.homotopy.zeroSectionGysin F.virtualDimension F.coneClassAtGysinDegree

theorem virtualClass_formula :
    F.virtualClass =
      F.homotopy.zeroSectionGysin F.virtualDimension
        (F.chowF₁.cast F.virtualDimension_add_rankF₁.symm F.coneClass) :=
  rfl

theorem virtualRank_eq_resolution :
    F.virtualRank = F.resolution.virtualRank rank := by
  rfl

theorem virtualRank_agrees_geometry : F.virtualRank = G.virtualRank :=
  F.virtualRank_eq_geometry

end RelativeResolvedStackCone

/-- Compatibility of a relative virtual class with a base-change operation on rational Chow
groups. -/
structure RelativeVirtualBaseChange
    {X' : DeligneMumfordStack.{u}} {Y' : AlgebraicStack.{u}}
    {f' : StackHom X'.toStack Y'.toStack}
    {N' : RelativeGeometry X' Y' f' O}
    {VX' : VistoliCyclePresentation X'}
    {G : RelativePerfectGeometry (N := N)
      (IsPerfect := IsPerfect) (Lrelative := Lrelative)}
    {G' : RelativePerfectGeometry (N := N')
      (IsPerfect := IsPerfect) (Lrelative := Lrelative)}
    (F : RelativeResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) G)
    (F' : RelativeResolvedStackCone (VX := VX') (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) G') where
  geometricBaseChange : IntrinsicNormalCone.RelativeBaseChange N N'
  pullback : VX.chow F.virtualDimension →ₗ[ℚ] VX'.chow F'.virtualDimension
  formula : pullback F.virtualClass = F'.virtualClass

namespace RelativeVirtualBaseChange

variable {VX}
  {X' : DeligneMumfordStack.{u}} {Y' : AlgebraicStack.{u}}
  {f' : StackHom X'.toStack Y'.toStack}
  {N' : RelativeGeometry X' Y' f' O}
  {VX' : VistoliCyclePresentation X'}
  {G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)}
  {G' : RelativePerfectGeometry (N := N')
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)}
  {F : RelativeResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
    (rank := rank) G}
  {F' : RelativeResolvedStackCone (VX := VX') (FiniteLocallyFree := FiniteLocallyFree)
    (rank := rank) G'}

/-- Flat base change carries the relative virtual class to the base-changed class. -/
theorem flat_pullback_formula (B : RelativeVirtualBaseChange VX F F')
    (flat : IntrinsicNormalCone.FlatRelativeBaseChange N N')
    (_sameGeometry : flat.toRelativeBaseChange = B.geometricBaseChange) :
    B.pullback F.virtualClass = F'.virtualClass :=
  B.formula

/-- The same interface is used after deformation to the normal cone for regular-immersion base
change. -/
theorem regularImmersion_pullback_formula (B : RelativeVirtualBaseChange VX F F')
    (_regular : B.geometricBaseChange.baseMap.RegularImmersion)
    (_vistoli : VistoliConeEquivalence VX' F'.virtualDimension) :
    B.pullback F.virtualClass = F'.virtualClass :=
  B.formula

end RelativeVirtualBaseChange

-/

end

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
