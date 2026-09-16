/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.StackGysin
import GromovWitten.AlgebraicGeometry.Stacks.Geometry

/-!
# Functorial operations in rational Chow theory

This file is currently a design checklist for the identities required downstream of Vistoli's
cycle construction.  Its former localization, exterior-product, Chern, and refined-Gysin
packages supplied their principal theorems as fields and are therefore retired below.  No such
general operation is exported from this module yet.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

noncomputable section

/-
Retired provisional intersection-operation packages.  These records supplied localization,
exterior products, functoriality, Whitney sum, excess intersection, and bivariant compatibility
as fields.  They are deliberately inactive until the underlying Chow, Chern, and deformation
constructions prove those laws.

/-- Exact localization for a closed substack and its open complement. -/
structure ChowLocalization
    {Z X U : DeligneMumfordStack.{u}}
    (VZ : VistoliCyclePresentation Z) (VX : VistoliCyclePresentation X)
    (VU : VistoliCyclePresentation U) where
  closedInclusion : StackHom Z.toStack X.toStack
  closed : closedInclusion.ClosedImmersion
  openInclusion : StackHom U.toStack X.toStack
  open_immersion : openInclusion.OpenImmersion
  closedPushforward (i : ℤ) : VZ.chow i →ₗ[ℚ] VX.chow i
  openPullback (i : ℤ) : VX.chow i →ₗ[ℚ] VU.chow i
  exact (i : ℤ) : Function.Exact (closedPushforward i) (openPullback i)

namespace ChowLocalization

variable {Z X U : DeligneMumfordStack.{u}}
  {VZ : VistoliCyclePresentation Z} {VX : VistoliCyclePresentation X}
  {VU : VistoliCyclePresentation U}

/-- A class restricts to zero precisely when it is pushed forward from the closed complement. -/
theorem openPullback_eq_zero_iff (L : ChowLocalization VZ VX VU) (i : ℤ)
    (z : VX.chow i) :
    L.openPullback i z = 0 ↔ z ∈ LinearMap.range (L.closedPushforward i) := by
  change L.openPullback i z = 0 ↔ ∃ y, L.closedPushforward i y = z
  exact L.exact i z

/-- Consecutive localization maps compose to zero. -/
theorem comp_eq_zero (L : ChowLocalization VZ VX VU) (i : ℤ) :
    (L.openPullback i).comp (L.closedPushforward i) = 0 := by
  apply LinearMap.ext
  intro z
  exact (L.exact i (L.closedPushforward i z)).2 ⟨z, rfl⟩

end ChowLocalization

/-- Exterior product on dimension-graded rational Chow groups. -/
structure ChowExteriorProduct
    {X Y XY : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (VXY : VistoliCyclePresentation XY) where
  geometry : StackProductPresentation X.toAlgebraicStack Y.toAlgebraicStack
    XY.toAlgebraicStack
  product (i j : ℤ) : VX.chow i →ₗ[ℚ] (VY.chow j →ₗ[ℚ] VXY.chow (i + j))

namespace ChowExteriorProduct

variable {X Y XY : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
  {VXY : VistoliCyclePresentation XY}

/-- Notation-level evaluation of the bilinear exterior product. -/
def apply (P : ChowExteriorProduct VX VY VXY) {i j : ℤ}
    (x : VX.chow i) (y : VY.chow j) : VXY.chow (i + j) :=
  P.product i j x y

@[simp]
theorem zero_left (P : ChowExteriorProduct VX VY VXY) {i j : ℤ}
    (y : VY.chow j) : P.apply (0 : VX.chow i) y = 0 := by
  simp [apply]

@[simp]
theorem zero_right (P : ChowExteriorProduct VX VY VXY) {i j : ℤ}
    (x : VX.chow i) : P.apply x (0 : VY.chow j) = 0 := by
  simp [apply]

end ChowExteriorProduct

/-- Compatibility of exterior product with two proper pushforwards. -/
structure ExteriorProductProperCompatibility
    {X Y X' Y' XY X'Y' : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
    {VX' : VistoliCyclePresentation X'} {VY' : VistoliCyclePresentation Y'}
    {VXY : VistoliCyclePresentation XY} {VX'Y' : VistoliCyclePresentation X'Y'}
    (P : ChowExteriorProduct VX VY VXY) (P' : ChowExteriorProduct VX' VY' VX'Y') where
  pushX (i : ℤ) : VX.chow i →ₗ[ℚ] VX'.chow i
  pushY (j : ℤ) : VY.chow j →ₗ[ℚ] VY'.chow j
  pushProduct (n : ℤ) : VXY.chow n →ₗ[ℚ] VX'Y'.chow n
  formula (i j : ℤ) (x : VX.chow i) (y : VY.chow j) :
    pushProduct (i + j) (P.apply x y) = P'.apply (pushX i x) (pushY j y)

/-- Functoriality of a sequence of proper pushforwards. -/
structure ProperPushforwardComposition
    {X Y Z : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (VZ : VistoliCyclePresentation Z) where
  firstMorphism : StackHom X.toStack Y.toStack
  secondMorphism : StackHom Y.toStack Z.toStack
  compositeMorphism : StackHom X.toStack Z.toStack
  compositeComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp firstMorphism secondMorphism)
    compositeMorphism
  firstProper : firstMorphism.Proper
  secondProper : secondMorphism.Proper
  compositeProper : compositeMorphism.Proper
  first (i : ℤ) : VX.chow i →ₗ[ℚ] VY.chow i
  second (i : ℤ) : VY.chow i →ₗ[ℚ] VZ.chow i
  composite (i : ℤ) : VX.chow i →ₗ[ℚ] VZ.chow i
  functorial (i : ℤ) : composite i = (second i).comp (first i)

/-- Functoriality of flat pullback, including addition of relative dimensions. -/
structure FlatPullbackComposition
    {X Y Z : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (VZ : VistoliCyclePresentation Z) (d e : ℤ) where
  firstMorphism : StackHom Y.toStack Z.toStack
  secondMorphism : StackHom X.toStack Y.toStack
  compositeMorphism : StackHom X.toStack Z.toStack
  compositeComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp secondMorphism firstMorphism)
    compositeMorphism
  firstFlat : firstMorphism.Flat
  secondFlat : secondMorphism.Flat
  compositeFlat : compositeMorphism.Flat
  first (i : ℤ) : VZ.chow i →ₗ[ℚ] VY.chow (i + e)
  second (i : ℤ) : VY.chow i →ₗ[ℚ] VX.chow (i + d)
  composite (i : ℤ) : VZ.chow i →ₗ[ℚ] VX.chow (i + (d + e))
  functorial (i : ℤ) (z : VZ.chow i) :
    composite i z = VX.cast (by omega)
      (second (i + e) (first i z))

/-- Whitney sum for Chern operations of a short exact sequence of vector bundles. -/
structure WhitneySumFormula
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    (subRank quotientRank : ℕ)
    (sub : ChernOperations V subRank)
    (quotient : ChernOperations V quotientRank)
    (sum : ChernOperations V (subRank + quotientRank)) where
  formula (j : ℕ) (i : ℤ) (z : V.chow i) :
    sum.c j i z =
      ∑ p : Fin (j + 1),
        V.cast (by
          have hp : (p : ℕ) ≤ j := Nat.le_of_lt_succ p.isLt
          omega)
          (sub.c p (i - ((j - (p : ℕ) : ℕ) : ℤ))
            (quotient.c (j - p) i z))

/-- Pullback compatibility for a complete system of Chern operations. -/
structure ChernPullbackCompatibility
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    {rank : ℕ} (CX : ChernOperations VX rank) (CY : ChernOperations VY rank)
    (relativeDimension : ℤ) where
  pullback (i : ℤ) : VY.chow i →ₗ[ℚ] VX.chow (i + relativeDimension)
  commutes (j : ℕ) (i : ℤ) (z : VY.chow i) :
    pullback (i - j) (CY.c j i z) =
      VX.cast (by omega) (CX.c j (i + relativeDimension) (pullback i z))

/-- Composition law for refined Gysin maps. -/
structure RefinedGysinComposition
    {X Y Z : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
    {VZ : VistoliCyclePresentation Z}
    {c d : ℕ}
    (g : RefinedGysin VX VY c) (h : RefinedGysin VY VZ d)
    (composite : RefinedGysin VX VZ (c + d)) where
  immersionComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp g.immersion h.immersion)
    composite.immersion
  formula (i : ℤ) (z : VZ.chow i) :
    composite.pullback i z = VX.cast (by omega)
      (g.pullback (i - d) (h.pullback i z))

/-- Excess-intersection formula. -/
structure ExcessIntersectionFormula
    {X Y : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
    {codim excessRank : ℕ}
    (expected : RefinedGysin VX VY codim)
    (actual : RefinedGysin VX VY (codim - excessRank))
    (excessChern : ChernOperations VX excessRank) where
  excess_le : excessRank ≤ codim
  formula (i : ℤ) (z : VY.chow i) :
    expected.pullback i z = VX.cast (by omega)
      (excessChern.topChern (i - ((codim - excessRank : ℕ) : ℤ))
        (actual.pullback i z))

/-- Compatibility of refined Gysin with proper pushforward in a cartesian square. -/
structure RefinedGysinProperCompatibility
    {X Y X' Y' : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
    {VX' : VistoliCyclePresentation X'} {VY' : VistoliCyclePresentation Y'}
    {codim : ℕ}
    (g : RefinedGysin VX VY codim) (g' : RefinedGysin VX' VY' codim) where
  sourceMap : StackHom X.toStack X'.toStack
  targetMap : StackHom Y.toStack Y'.toStack
  sourceProper : sourceMap.Proper
  targetProper : targetMap.Proper
  squareComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp g.immersion targetMap)
    (Pseudofunctor.StrongTrans.vcomp sourceMap g'.immersion)
  pullbackSquare : StackTwoPullback.Genuine g'.immersion targetMap
  sourceEquivalence : StackEquivalenceData X.toStack pullbackSquare.pullback
  pushY (i : ℤ) : VY.chow i →ₗ[ℚ] VY'.chow i
  pushX (i : ℤ) : VX.chow i →ₗ[ℚ] VX'.chow i
  commutes (i : ℤ) (z : VY.chow i) :
    g'.pullback i (pushY i z) = pushX (i - codim) (g.pullback i z)

/-- A genuine base-change test for a fixed stack morphism `f : X -> Y`.  The source is
identified with a bicategorical pullback, so the square cannot be an unrelated diagram carrying
the desired Chow groups by name only. -/
structure BivariantTest
    {X Y : DeligneMumfordStack.{u}} (f : StackHom X.toStack Y.toStack) where
  base : DeligneMumfordStack.{u}
  source : DeligneMumfordStack.{u}
  baseProjection : StackHom base.toStack Y.toStack
  pulledMorphism : StackHom source.toStack base.toStack
  sourceProjection : StackHom source.toStack X.toStack
  squareComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp pulledMorphism baseProjection)
    (Pseudofunctor.StrongTrans.vcomp sourceProjection f)
  pullback : StackTwoPullback.Genuine f baseProjection
  sourceEquivalence : StackEquivalenceData source.toStack pullback.pullback
  baseChow : VistoliCyclePresentation base
  sourceChow : VistoliCyclePresentation source

namespace BivariantTest

variable {X Y : DeligneMumfordStack.{u}}

/-- The identity base change is a genuine bivariant test.  Its pullback square is the
constructed bicategorical pullback of `f` along `id_Y`, not a postulated inhabitant of the test
type. -/
noncomputable def identity (VX : VistoliCyclePresentation X)
    (VY : VistoliCyclePresentation Y) (f : StackHom X.toStack Y.toStack) :
    BivariantTest f where
  base := Y
  source := X
  baseProjection := Pseudofunctor.StrongTrans.id Y.toStack.toPseudofunctor
  pulledMorphism := f
  sourceProjection := Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor
  squareComparison := (StackTwoPullback.rightIdentity f).comparison.symm
  pullback := StackTwoPullback.rightIdentity f
  sourceEquivalence := StackEquivalenceData.refl X.toStack
  baseChow := VY
  sourceChow := VX

/-- In the presence of the source and target Chow theories used by a bivariant class, the type
of genuine base-change tests is inhabited. -/
theorem nonempty (VX : VistoliCyclePresentation X)
    (VY : VistoliCyclePresentation Y) (f : StackHom X.toStack Y.toStack) :
    Nonempty (BivariantTest f) :=
  ⟨identity VX VY f⟩

end BivariantTest

/-- A morphism between two genuine base-change tests, commuting over both `X` and `Y` up to
specified invertible 2-cells. -/
structure BivariantTestMap
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    (A B : BivariantTest f) where
  baseMap : StackHom A.base.toStack B.base.toStack
  sourceMap : StackHom A.source.toStack B.source.toStack
  pullbackComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp A.pulledMorphism baseMap)
    (Pseudofunctor.StrongTrans.vcomp sourceMap B.pulledMorphism)
  baseComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp baseMap B.baseProjection)
    A.baseProjection
  sourceComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp sourceMap B.sourceProjection)
    A.sourceProjection

/-- Proper transition between actual bivariant tests, equipped with the already constructed
proper pushforwards on the two horizontal Chow theories. -/
structure BivariantProperTestMap
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    (A B : BivariantTest f) where
  toTestMap : BivariantTestMap A B
  basePushforward (i : ℤ) : ProperPushforward A.baseChow B.baseChow
    toTestMap.baseMap i
  sourcePushforward (i : ℤ) : ProperPushforward A.sourceChow B.sourceChow
    toTestMap.sourceMap i

/-- Flat transition between actual bivariant tests.  The same geometric relative dimension is
used on the base and on its cartesian pullback. -/
structure BivariantFlatTestMap
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    (A B : BivariantTest f) where
  toTestMap : BivariantTestMap A B
  relativeDimension : ℕ
  basePullback (i : ℤ) : FlatPullback A.baseChow B.baseChow
    toTestMap.baseMap relativeDimension i
  sourcePullback (i : ℤ) : FlatPullback A.sourceChow B.sourceChow
    toTestMap.sourceMap relativeDimension i

/-- Regular-immersion transition between actual bivariant tests.  The refined Gysin morphisms
are required to be the two maps displayed by the test transition. -/
structure BivariantRegularTestMap
    {X Y : DeligneMumfordStack.{u}} {f : StackHom X.toStack Y.toStack}
    (A B : BivariantTest f) where
  toTestMap : BivariantTestMap A B
  codimension : ℕ
  baseGysin : RefinedGysin A.baseChow B.baseChow codimension
  sourceGysin : RefinedGysin A.sourceChow B.sourceChow codimension
  baseImmersionComparison : StackIso2 baseGysin.immersion toTestMap.baseMap
  sourceImmersionComparison : StackIso2 sourceGysin.immersion toTestMap.sourceMap

/-- A bivariant Chow class of degree `degree`: a grading-correct operation after every genuine
base change, compatible with actual proper pushforward, flat pullback, and regular refined
Gysin maps.  There are no caller-selected test or square types that can be set to `Empty`. -/
structure BivariantClass
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (f : StackHom X.toStack Y.toStack) (degree : ℤ) where
  operation (T : BivariantTest f) (i : ℤ) :
    T.baseChow.chow i →ₗ[ℚ] T.sourceChow.chow (i + degree)
  proper_compat (A B : BivariantTest f) (s : BivariantProperTestMap A B)
      (i : ℤ) (z : A.baseChow.chow i) :
    (s.sourcePushforward (i + degree)).map.induced (operation A i z) =
      operation B i ((s.basePushforward i).map.induced z)
  flat_compat (A B : BivariantTest f) (s : BivariantFlatTestMap A B)
      (i : ℤ) (z : B.baseChow.chow i) :
    (s.sourcePullback (i + degree)).map.induced (operation B i z) =
      A.sourceChow.cast (by omega)
        (operation A (i + (s.relativeDimension : ℤ))
          ((s.basePullback i).map.induced z))
  regular_compat (A B : BivariantTest f) (s : BivariantRegularTestMap A B)
      (i : ℤ) (z : B.baseChow.chow i) :
    s.sourceGysin.pullback (i + degree) (operation B i z) =
      A.sourceChow.cast (by omega)
        (operation A (i - s.codimension)
          (s.baseGysin.pullback i z))

/-- An orientation is a bivariant class assigned to a specified geometric morphism. -/
structure BivariantOrientation
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (codimension : ℕ) where
  morphism : StackHom X.toStack Y.toStack
  bivariantClass : BivariantClass VX VY morphism (-codimension)

-/

end

end GromovWitten.AlgebraicGeometry.IntersectionTheory
