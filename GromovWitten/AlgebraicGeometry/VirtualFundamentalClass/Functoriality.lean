/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Properties
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.RelativeStack

/-!
# Compatible virtual pullback and functoriality

This module currently retains only genuinely cartesian squares of stacks and their isomorphisms.
The former obstruction-triangle and Chow-theoretic virtual-pullback, composition, product, and
graph packages were caller-supplied fields and are therefore inactive until they are constructed
from actual cotangent, Chow/Gysin, and normal-cone comparisons.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open CategoryTheory
open IntersectionTheory CotangentComplex

universe w v u

noncomputable section

/-- The cone displayed by a 2-commutative square of fppf stacks. -/
def cartesianStackSquareCone
    {X Y X' Y' : FppfStack.{u}}
    (top : StackHom X' X) (left : StackHom X' Y')
    (right : StackHom X Y) (bottom : StackHom Y' Y)
    (comparison : StackIso2
      (Pseudofunctor.StrongTrans.vcomp top right)
      (Pseudofunctor.StrongTrans.vcomp left bottom)) :
    StackTwoPullback.Cone (f := right) (g := bottom) X' where
  fst := top
  snd := left
  comparison := comparison

/-- A cartesian square in the 2-category of fppf stacks. The final three fields require the
chosen equivalence with the pullback to induce the displayed top and left maps and to preserve
the square's comparison face; a bare equivalence of the underlying stacks is insufficient. -/
structure CartesianStackSquare
    (X Y X' Y' : FppfStack.{u}) where
  top : StackHom X' X
  left : StackHom X' Y'
  right : StackHom X Y
  bottom : StackHom Y' Y
  comparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp top right)
    (Pseudofunctor.StrongTrans.vcomp left bottom)
  pullback : StackTwoPullback.Genuine right bottom
  pullbackEquivalence : StackEquivalenceData X' pullback.pullback
  pullbackFstComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp pullbackEquivalence.hom pullback.fst) top
  pullbackSndComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp pullbackEquivalence.hom pullback.snd) left
  pullbackEquivalenceClassifies : StackTwoPullback.ConeLiftClassifies
    pullback.toStackTwoPullback
    (cartesianStackSquareCone top left right bottom comparison)
    pullbackEquivalence.hom pullbackFstComparison pullbackSndComparison

/-- Isomorphism of cartesian-square presentations, expressed by invertible modifications on all
four sides. -/
structure CartesianStackSquareIso
    {X Y X' Y' : FppfStack.{u}}
    (A B : CartesianStackSquare X Y X' Y') where
  top : StackIso2 A.top B.top
  left : StackIso2 A.left B.left
  right : StackIso2 A.right B.right
  bottom : StackIso2 A.bottom B.bottom
  /-- The four side isomorphisms identify the two specified comparison faces. -/
  comparisonCompatibility (U : Scheme.{u}) (x : StackFiber X' U) :
    (((StackHom.appFunctor A.right U).mapIso ((top.appIso U).app x)).trans
        ((right.appIso U).app ((StackHom.appFunctor B.top U).obj x))).trans
          ((B.comparison.appIso U).app x) =
      (((A.comparison.appIso U).app x).trans
        ((StackHom.appFunctor A.bottom U).mapIso ((left.appIso U).app x))).trans
          ((bottom.appIso U).app ((StackHom.appFunctor B.left U).obj x))

/-
The declarations formerly below this point packaged the virtual-pullback, product, and graph
formulas as fields.  They are intentionally inactive: a formula supplied by a caller is not a
proof of Behrend--Fantechi functoriality.  `CartesianStackSquare` and
`CartesianStackSquareIso` above remain useful honest geometric inputs.  The virtual operations
and cotangent-triangle compatibility will be restored here only when they are constructed from
cotangent complexes, Chow/Gysin operations, and the actual normal-cone comparison.

/-- A virtual pullback comparison in exact dimension gradings. -/
structure VirtualPullbackComparison
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (sourceDegree targetDegree : ℤ) where
  pullback : VY.chow sourceDegree →ₗ[ℚ] VX.chow targetDegree
  sourceClass : VY.chow sourceDegree
  targetClass : VX.chow targetDegree
  formula : pullback sourceClass = targetClass

namespace VirtualPullbackComparison

variable {X Y Z : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
  {VZ : VistoliCyclePresentation Z} {i j k : ℤ}

/-- Composition of compatible virtual pullbacks. -/
def comp (P : VirtualPullbackComparison VX VY j k)
    (Q : VirtualPullbackComparison VY VZ i j)
    (hmiddle : Q.targetClass = P.sourceClass) :
    VirtualPullbackComparison VX VZ i k where
  pullback := P.pullback.comp Q.pullback
  sourceClass := Q.sourceClass
  targetClass := P.targetClass
  formula := by
    rw [LinearMap.comp_apply, Q.formula, hmiddle, P.formula]

@[simp]
theorem comp_formula (P : VirtualPullbackComparison VX VY j k)
    (Q : VirtualPullbackComparison VY VZ i j)
    (hmiddle : Q.targetClass = P.sourceClass) :
    (comp P Q hmiddle).pullback Q.sourceClass = P.targetClass :=
  (comp P Q hmiddle).formula

end VirtualPullbackComparison

/-- A virtual-pullback comparison attached to an actual cartesian square and an actual morphism
of the two obstruction-theory transitivity triangles. -/
structure CartesianVirtualPullbackComparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X X' : DeligneMumfordStack.{u}}
    (Y Y' : DeligneMumfordStack.{u})
    (VX : VistoliCyclePresentation X) (VX' : VistoliCyclePresentation X')
    (sourceDegree targetDegree : ℤ) where
  square : CartesianStackSquare X.toStack Y.toStack X'.toStack Y'.toStack
  sourceTriangle : TransitivityTriangle (C := C)
  targetTriangle : TransitivityTriangle (C := C)
  compatibility : CompatibleTriangles sourceTriangle targetTriangle
  comparison : VirtualPullbackComparison VX' VX sourceDegree targetDegree

namespace CartesianVirtualPullbackComparison

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X X' : DeligneMumfordStack.{u}}
  {Y Y' : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VX' : VistoliCyclePresentation X'}
  {i j : ℤ}

/-- Replacing a cartesian square by an isomorphic presentation leaves its triangle and Chow
comparison unchanged. -/
def replaceSquare
    (P : CartesianVirtualPullbackComparison (C := C) Y Y' VX VX' i j)
    (square' : CartesianStackSquare X.toStack Y.toStack X'.toStack Y'.toStack)
    (_e : CartesianStackSquareIso P.square square') :
    CartesianVirtualPullbackComparison (C := C) Y Y' VX VX' i j where
  square := square'
  sourceTriangle := P.sourceTriangle
  targetTriangle := P.targetTriangle
  compatibility := P.compatibility
  comparison := P.comparison

@[simp]
theorem replaceSquare_formula
    (P : CartesianVirtualPullbackComparison (C := C) Y Y' VX VX' i j)
    (square' : CartesianStackSquare X.toStack Y.toStack X'.toStack Y'.toStack)
    (e : CartesianStackSquareIso P.square square') :
    (P.replaceSquare square' e).comparison.pullback
        (P.replaceSquare square' e).comparison.sourceClass =
      (P.replaceSquare square' e).comparison.targetClass :=
  P.comparison.formula

end CartesianVirtualPullbackComparison

/-- The smooth virtual-pullback theorem, with smoothness imposed on the actual base morphism of
the cartesian square rather than recorded as an informal label on a linear map. -/
structure SmoothVirtualPullbackComparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X X' : DeligneMumfordStack.{u}}
    (Y Y' : DeligneMumfordStack.{u})
    (VX : VistoliCyclePresentation X) (VX' : VistoliCyclePresentation X')
    (sourceDegree targetDegree : ℤ)
    extends CartesianVirtualPullbackComparison (C := C) Y Y' VX VX'
      sourceDegree targetDegree where
  base_smooth : square.bottom.Smooth

namespace SmoothVirtualPullbackComparison

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X Y X' Y' : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VX' : VistoliCyclePresentation X'}
  {i j : ℤ}

/-- Flat pullback and zero-section Gysin give the smooth base-change formula. -/
theorem formula (P : SmoothVirtualPullbackComparison (C := C) Y Y' VX VX' i j) :
    P.comparison.pullback P.comparison.sourceClass = P.comparison.targetClass :=
  P.comparison.formula

end SmoothVirtualPullbackComparison

/-- The regular-immersion virtual-pullback theorem, including the actual regular base morphism
and Vistoli's rational equivalence used to descend the normal-cone comparison. -/
structure RegularImmersionVirtualPullbackComparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X X' : DeligneMumfordStack.{u}}
    (Y Y' : DeligneMumfordStack.{u})
    (VX : VistoliCyclePresentation X) (VX' : VistoliCyclePresentation X')
    (sourceDegree targetDegree : ℤ)
    extends CartesianVirtualPullbackComparison (C := C) Y Y' VX VX'
      sourceDegree targetDegree where
  base_regularImmersion : square.bottom.RegularImmersion
  vistoliComparison : VistoliConeEquivalence VX' targetDegree

namespace RegularImmersionVirtualPullbackComparison

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X Y X' Y' : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VX' : VistoliCyclePresentation X'}
  {i j : ℤ}

/-- Refined Gysin carries the original virtual class to the base-changed class. -/
theorem formula
    (P : RegularImmersionVirtualPullbackComparison (C := C) Y Y' VX VX' i j) :
    P.comparison.pullback P.comparison.sourceClass = P.comparison.targetClass :=
  P.comparison.formula

end RegularImmersionVirtualPullbackComparison

/-- Exterior product on rational Chow groups, with exact addition of dimension indices. -/
structure ExteriorProduct
    {X Y XY : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (VXY : VistoliCyclePresentation XY) where
  product (i j : ℤ) : VX.chow i →ₗ[ℚ] VY.chow j →ₗ[ℚ] VXY.chow (i + j)

/-- Product formula data for two virtual classes. -/
structure VirtualProductFormula
    {X Y XY : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
    {VXY : VistoliCyclePresentation XY}
    (P : ExteriorProduct VX VY VXY) (i j : ℤ) where
  firstClass : VX.chow i
  secondClass : VY.chow j
  productClass : VXY.chow (i + j)
  formula : P.product i j firstClass secondClass = productClass

namespace VirtualProductFormula

variable {X Y XY : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
  {VXY : VistoliCyclePresentation XY}
  {P : ExteriorProduct VX VY VXY} {i j : ℤ}

/-- The virtual class of a product is the exterior product of virtual classes, and the target
degree is definitionally the sum of virtual dimensions. -/
theorem virtualClass_product (F : VirtualProductFormula P i j) :
    P.product i j F.firstClass F.secondClass = F.productClass :=
  F.formula

end VirtualProductFormula

/-- Compatible functoriality through factorization by a graph and a smooth projection. -/
structure GraphFactorizationFunctoriality
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
    {VZ : VistoliCyclePresentation Z} {i j k : ℤ} where
  /-- The regular graph step and smooth projection step are actual stack morphisms. -/
  graphMap : StackHom Y.toStack Z.toStack
  graph_regularImmersion : graphMap.RegularImmersion
  projectionMap : StackHom X.toStack Y.toStack
  projection_smooth : projectionMap.Smooth
  compositeMap : StackHom X.toStack Z.toStack
  factorization : StackIso2
    (Pseudofunctor.StrongTrans.vcomp projectionMap graphMap) compositeMap
  graphSourceTriangle : TransitivityTriangle (C := C)
  graphTargetTriangle : TransitivityTriangle (C := C)
  graphCompatibility : CompatibleTriangles graphSourceTriangle graphTargetTriangle
  projectionSourceTriangle : TransitivityTriangle (C := C)
  projectionTargetTriangle : TransitivityTriangle (C := C)
  projectionCompatibility :
    CompatibleTriangles projectionSourceTriangle projectionTargetTriangle
  graph : VirtualPullbackComparison VY VZ i j
  projection : VirtualPullbackComparison VX VY j k
  middle_compat : graph.targetClass = projection.sourceClass

namespace GraphFactorizationFunctoriality

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X Y Z : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
  {VZ : VistoliCyclePresentation Z} {i j k : ℤ}

/-- Full Behrend--Fantechi functoriality obtained by composing graph and projection formulas. -/
theorem formula (F : GraphFactorizationFunctoriality
    (C := C) (VX := VX) (VY := VY) (VZ := VZ) (i := i) (j := j) (k := k)) :
    (F.projection.pullback.comp F.graph.pullback) F.graph.sourceClass =
      F.projection.targetClass := by
  rw [LinearMap.comp_apply, F.graph.formula, F.middle_compat, F.projection.formula]

end GraphFactorizationFunctoriality

-/

end

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
