/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.Operations
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Theorems

/-!
# Independence and functoriality of the relative virtual class

This module is an inactive checklist for relative independence, no-obstruction,
obstruction-bundle, product, transitivity, absolute-recovery, and smooth-ambient calculations.
The former records supplied the decisive comparisons or final formulas as fields, so none of
these general results is currently exported.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open CategoryTheory
open IntersectionTheory IntrinsicNormalCone DerivedObstructionTheory CotangentComplex

universe w v u t

noncomputable section

/-
The relative resolution comparisons and formulas formerly below this point supplied cone/Gysin
compatibility or the final advertised equality as fields.  They are intentionally inactive until
the corresponding comparison maps and proofs are constructed from the geometry.

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X : DeligneMumfordStack.{u}} {Y : AlgebraicStack.{u}}
  {f : StackHom X.toStack Y.toStack}
  {O : FppfScalarRings.{u}} {Lrelative : DerivedCategory C}
  {IsPerfect : DerivedCategory C → Prop}
  {FiniteLocallyFree : C → Prop} {rank : C → ℕ}
  {N : RelativeGeometry X Y f O}
  {VX : VistoliCyclePresentation X}
  {G : RelativePerfectGeometry (N := N)
    (IsPerfect := IsPerfect) (Lrelative := Lrelative)}

/-- Common-resolution comparison for relative resolved cones. -/
structure RelativeResolutionComparison
    (F H : RelativeResolvedStackCone (VX := VX)
      (FiniteLocallyFree := FiniteLocallyFree) (rank := rank) G) where
  resolutionIso :
    DerivedCategory.Q.obj F.resolution.complex ≅
      DerivedCategory.Q.obj H.resolution.complex
  resolutionIso_compat :
    resolutionIso.hom ≫ H.resolution.comparison.hom =
      F.resolution.comparison.hom
  coneTransport :
    F.chowF₁.chow (F.virtualDimension + (F.rankF₁ : ℤ)) ≃ₗ[ℚ]
      H.chowF₁.chow (H.virtualDimension + (H.rankF₁ : ℤ))
  cone_compat : coneTransport F.coneClassAtGysinDegree = H.coneClassAtGysinDegree
  gysin_compat (z : F.chowF₁.chow (F.virtualDimension + (F.rankF₁ : ℤ))) :
    VX.cast (congrArg (N.baseDimension + ·)
      (F.virtualRank_agrees_geometry.trans H.virtualRank_agrees_geometry.symm))
        (F.homotopy.zeroSectionGysin F.virtualDimension z) =
      H.homotopy.zeroSectionGysin H.virtualDimension (coneTransport z)

namespace RelativeResolutionComparison

variable {F H : RelativeResolvedStackCone (VX := VX)
  (FiniteLocallyFree := FiniteLocallyFree) (rank := rank) G}

/-- Equality of relative virtual dimensions is forced because both resolutions have the same
base dimension and realize the rank of the same relative obstruction-target stack. -/
theorem dimension_eq (_R : RelativeResolutionComparison F H) :
    F.virtualDimension = H.virtualDimension := by
  unfold RelativeResolvedStackCone.virtualDimension
  exact congrArg (N.baseDimension + ·)
    (F.virtualRank_agrees_geometry.trans H.virtualRank_agrees_geometry.symm)

/-- Two relative global resolutions give the same virtual class. -/
theorem virtualClass_eq (R : RelativeResolutionComparison F H) :
    VX.cast R.dimension_eq F.virtualClass = H.virtualClass := by
  unfold RelativeResolvedStackCone.virtualClass
  have h := R.gysin_compat F.coneClassAtGysinDegree
  rw [R.cone_compat] at h
  exact h

end RelativeResolutionComparison

/-- All actual relative global resolutions with coherent common dominating comparisons.  The
index is fixed to the global-resolution type, so no private singleton family can hide another
resolution. -/
structure RelativeResolutionIndependentSystem where
  resolutionNonempty :
    Nonempty (GlobalTwoTermResolution FiniteLocallyFree G.theory.E)
  presentation (a : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    RelativeResolvedStackCone (VX := VX)
    (FiniteLocallyFree := FiniteLocallyFree) (rank := rank) G
  presentation_resolution
      (a : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    (presentation a).resolution = a
  commonResolution
      (a b : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    GlobalTwoTermResolution FiniteLocallyFree G.theory.E
  commonToLeft
      (a b : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    RelativeResolutionComparison
    (presentation (commonResolution a b)) (presentation a)
  commonToRight
      (a b : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    RelativeResolutionComparison
    (presentation (commonResolution a b)) (presentation b)

namespace RelativeResolutionIndependentSystem

variable
  (S : RelativeResolutionIndependentSystem (VX := VX)
    (FiniteLocallyFree := FiniteLocallyFree) (rank := rank) (G := G))

/-- The common virtual dimension is determined by the fixed relative geometry. -/
def virtualDimension (_S : RelativeResolutionIndependentSystem (VX := VX)
    (FiniteLocallyFree := FiniteLocallyFree) (rank := rank) (G := G)) : ℤ :=
  N.baseDimension + G.virtualRank

/-- Every presentation has the virtual dimension determined by the fixed relative geometry. -/
theorem dimension_eq
    (a : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    (S.presentation a).virtualDimension = S.virtualDimension := by
  unfold RelativeResolvedStackCone.virtualDimension virtualDimension
  exact congrArg (N.baseDimension + ·) (S.presentation a).virtualRank_agrees_geometry

/-- Evaluation of one relative resolution in the common virtual dimension. -/
def evaluatedClass (a : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    VX.chow S.virtualDimension :=
  VX.cast (S.dimension_eq a) (S.presentation a).virtualClass

/-- One common-resolution comparison identifies the corresponding evaluated classes. -/
private theorem evaluatedClass_eq_of_comparison
    (a b : GlobalTwoTermResolution FiniteLocallyFree G.theory.E)
    (R : RelativeResolutionComparison (S.presentation a) (S.presentation b)) :
    S.evaluatedClass a = S.evaluatedClass b := by
  have h := R.virtualClass_eq
  unfold evaluatedClass
  calc
    VX.cast (S.dimension_eq a) (S.presentation a).virtualClass =
        VX.cast (R.dimension_eq.trans (S.dimension_eq b))
          (S.presentation a).virtualClass := by congr
    _ = VX.cast (S.dimension_eq b)
          (VX.cast R.dimension_eq (S.presentation a).virtualClass) := by
      rw [VistoliCyclePresentation.cast_cast]
    _ = VX.cast (S.dimension_eq b) (S.presentation b).virtualClass :=
      congrArg (VX.cast (S.dimension_eq b)) h

/-- Relative resolution independence through an actual common dominating resolution. -/
theorem evaluatedClass_eq
    (a b : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    S.evaluatedClass a = S.evaluatedClass b := by
  calc
    S.evaluatedClass a = S.evaluatedClass (S.commonResolution a b) :=
      (S.evaluatedClass_eq_of_comparison _ _ (S.commonToLeft a b)).symm
    _ = S.evaluatedClass b :=
      S.evaluatedClass_eq_of_comparison _ _ (S.commonToRight a b)

/-- Intrinsic relative virtual class, choosing a resolution only internally. -/
noncomputable def virtualFundamentalClass : VX.chow S.virtualDimension :=
  S.evaluatedClass (Classical.choice S.resolutionNonempty)

/-- Every supplied relative resolution evaluates the intrinsic class. -/
theorem virtualFundamentalClass_eq
    (a : GlobalTwoTermResolution FiniteLocallyFree G.theory.E) :
    S.virtualFundamentalClass = S.evaluatedClass a :=
  S.evaluatedClass_eq _ _

end RelativeResolutionIndependentSystem

/-- Relative no-obstruction calculation. -/
theorem relative_noObstruction
    (F : RelativeResolvedStackCone (VX := VX)
      (FiniteLocallyFree := FiniteLocallyFree) (rank := rank) G)
    (fundamental : VX.chow F.virtualDimension)
    (hcone : F.coneClassAtGysinDegree =
      F.homotopy.pullback F.virtualDimension fundamental) :
    F.virtualClass = fundamental := by
  rw [RelativeResolvedStackCone.virtualClass, hcone]
  exact F.homotopy.zeroSectionGysin_pullback F.virtualDimension fundamental

/-- Product formula for relative virtual classes. -/
structure RelativeProductFormula
    {X' XX : DeligneMumfordStack.{u}}
    (VX' : VistoliCyclePresentation X') (VXX : VistoliCyclePresentation XX)
    (P : ChowExteriorProduct VX VX' VXX)
    (d e : ℤ) where
  firstClass : VX.chow d
  secondClass : VX'.chow e
  productClass : VXX.chow (d + e)
  formula : P.apply firstClass secondClass = productClass

/-- Recovery of the absolute virtual class from the relative theory over `Spec k`. -/
structure AbsoluteRecovery (absoluteDegree relativeDegree : ℤ) where
  baseEquivalence :
    StackEquivalenceData Y.toStack (representedStack N.ground)
  absoluteGeometry : IntrinsicNormalCone.Geometry X N.ground O
  normalComparison : ConeStack.Iso N.normalSheaf.toConeStack
    absoluteGeometry.normalSheaf.toConeStack
  coneComparison : ConeStack.Iso N.cone.cone absoluteGeometry.cone.cone
  degree_eq : relativeDegree = absoluteDegree
  absoluteClass : VX.chow absoluteDegree
  relativeClass : VX.chow relativeDegree
  formula : VX.cast degree_eq relativeClass = absoluteClass

/-- Relative compatibility through a morphism of transitivity triangles. -/
structure RelativeCompatibleFunctoriality
    {X' : DeligneMumfordStack.{u}} {Y' : AlgebraicStack.{u}}
    {f' : StackHom X'.toStack Y'.toStack}
    (N' : RelativeGeometry X' Y' f' O)
    (VX' : VistoliCyclePresentation X')
    (source target : TransitivityTriangle (C := C))
    (sourceDegree targetDegree : ℤ) where
  geometricSquare : RelativeBaseChange N N'
  triangles : CompatibleTriangles source target
  sourceClass : VX.chow sourceDegree
  targetClass : VX'.chow targetDegree
  virtualPullback : VX.chow sourceDegree →ₗ[ℚ] VX'.chow targetDegree
  formula : virtualPullback sourceClass = targetClass

/-- Final smooth-ambient fibre calculation.  The obstruction theory is the pullback of
`L_{V/W}`, and both routes produce the same zero-section/normal-cone class. -/
structure SmoothAmbientFiberCalculation where
  V : AlgebraicStack.{u}
  W : AlgebraicStack.{u}
  diagram : CartesianStackSquare V.toStack W.toStack X.toStack Y.toStack
  sourceMapComparison : StackIso2 diagram.left f
  horizontalSource_localImmersion : diagram.left.LocalImmersion
  horizontalAmbient_localImmersion : diagram.right.LocalImmersion
  ambientGround : Scheme.{u}
  vToGround : StackHom V.toStack (representedStack ambientGround)
  wToGround : StackHom W.toStack (representedStack ambientGround)
  vSmooth : vToGround.Smooth
  wSmooth : wToGround.Smooth
  relativeCotangent : DerivedCategory C
  pulledCotangent : DerivedCategory C
  pullbackMap : pulledCotangent ⟶ Lrelative
  obstructionTheory : ObstructionTheory Lrelative
  obstructionSourceIso : obstructionTheory.E ≅ pulledCotangent
  sourceMap_formula : obstructionSourceIso.hom ≫ pullbackMap = obstructionTheory.φ
  perfect : PerfectData IsPerfect obstructionTheory.E
  normalConeClass : VX.chow N.baseDimension
  virtualClass : VX.chow N.baseDimension
  equality : virtualClass = normalConeClass

-/

end

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
