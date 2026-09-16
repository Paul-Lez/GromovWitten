/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Stack

/-!
# Basic properties of the virtual class

This module is an inactive checklist for the general no-obstruction,
local-complete-intersection, and degree calculations.  Its former conditional consequences used
retired caller-supplied cone/Gysin packages.  The independently constructed rank-zero
proper-point calculation lives in `Basic` and `Examples`.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open CategoryTheory
open IntersectionTheory IntrinsicNormalCone DerivedObstructionTheory

universe w v u

noncomputable section

/-
These conditional consequences depended on the retired resolved-stack theorem package.  They
are inactive until the resolved cone and its Chow/Gysin comparison are constructed rather than
supplied.  The fully constructed proper-point calculation lives in `Basic` and `Examples`.

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
  {O : FppfScalarRings.{u}} {L : DerivedCategory C}
  {IsPerfect : DerivedCategory C → Prop}
  {FiniteLocallyFree : C → Prop} {rank : C → ℕ}
  {N : IntrinsicNormalCone.Geometry X ground O}
  {T : PerfectObstructionTheory IsPerfect L}
  {G : PerfectGeometricRealization IsPerfect N T}
  {VX : VistoliCyclePresentation X}

/-- If the resolved cone is the flat pullback of a base cycle, the resolved virtual class is
that cycle. -/
theorem ResolvedStackCone.virtualClass_eq_of_coneClass_eq_pullback
    (F : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) (N := N) (T := T) (G := G))
    (fundamental : VX.chow F.virtualRank)
    (hcone : F.coneClassAtGysinDegree = F.homotopy.pullback F.virtualRank fundamental) :
    F.virtualClass = fundamental := by
  rw [ResolvedStackCone.virtualClass, hcone]
  exact F.homotopy.zeroSectionGysin_pullback F.virtualRank fundamental

/-- No-obstruction formula: once smoothness identifies the resolved cone with the bundle
pullback of the ordinary fundamental class, the virtual class is ordinary. -/
theorem noObstruction_virtualClass_eq_fundamental
    (F : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) (N := N) (T := T) (G := G))
    (fundamental : VX.chow F.virtualRank)
    (smoothCone :
      F.coneClassAtGysinDegree = F.homotopy.pullback F.virtualRank fundamental) :
    F.virtualClass = fundamental :=
  F.virtualClass_eq_of_coneClass_eq_pullback fundamental smoothCone

/-- The canonical cotangent-complex obstruction theory on an lci object has ordinary
fundamental class whenever its resolved normal cone is the vector-bundle pullback. -/
theorem lci_virtualClass_eq_fundamental
    (F : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) (N := N) (T := T) (G := G))
    (fundamental : VX.chow F.virtualRank)
    (regularCone :
      F.coneClassAtGysinDegree = F.homotopy.pullback F.virtualRank fundamental) :
    F.virtualClass = fundamental :=
  F.virtualClass_eq_of_coneClass_eq_pullback fundamental regularCone

/-- Numerical virtual degree for a proper stack of virtual dimension zero. -/
def virtualDegree (D : ProperDegree VX) (z : VX.chow 0) : ℚ :=
  D.degree z

theorem virtualDegree_congr (D : ProperDegree VX) {z z' : VX.chow 0} (h : z = z') :
    virtualDegree D z = virtualDegree D z' :=
  congrArg D.degree h

/-- Resolution independence also gives independence of every downstream proper degree. -/
theorem resolutionIndependent_virtualDegree
    (S : StackResolutionIndependentSystem (VX := VX)
      (FiniteLocallyFree := FiniteLocallyFree) (rank := rank)
      (N := N) (T := T) (G := G))
    (hzero : S.virtualRank = 0) (D : ProperDegree VX)
    (a b : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    D.degree (VX.cast hzero (S.evaluatedClass a)) =
      D.degree (VX.cast hzero (S.evaluatedClass b)) := by
  rw [S.evaluatedClass_eq a b]

-/

end

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
