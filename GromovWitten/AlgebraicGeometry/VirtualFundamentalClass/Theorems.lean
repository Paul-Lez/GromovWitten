/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.Operations
import GromovWitten.AlgebraicGeometry.ObstructionTheory.Properties
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Functoriality

/-!
# Calculation and invariance theorems for virtual classes

This module is an inactive checklist for top-Chern, acyclic-summand, equivalence-invariance, and
zero-dimensional-length calculations.  The former records accepted the desired formulas or
comparisons as fields and are retired below; no corresponding general theorem is exported.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open CategoryTheory
open IntersectionTheory IntrinsicNormalCone DerivedObstructionTheory

universe w v u

noncomputable section

/-
The former declarations below accepted the top-Chern formula, acyclic-summand comparison,
equivalence invariance, or zero-dimensional length formula as structure fields and then exposed
those same fields as the advertised theorem.  They are kept only as historical design notes and
are deliberately inactive.  These theorems will be restored only from constructed cone/Gysin
comparisons.

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
  {O : FppfScalarRings.{u}} {L : DerivedCategory C}
  {IsPerfect : DerivedCategory C → Prop}
  {FiniteLocallyFree : C → Prop} {rank : C → ℕ}
  {N : IntrinsicNormalCone.Geometry X ground O}
  {T : PerfectObstructionTheory IsPerfect L}
  {G : PerfectGeometricRealization IsPerfect N T}
  {VX : VistoliCyclePresentation X}

/-- Data identifying a smooth obstruction cone with the zero section of a locally free
obstruction bundle. -/
structure ObstructionBundleCalculation
    (F : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) (N := N) (T := T) (G := G)) where
  chern : ChernOperations VX F.rankF₁
  selfIntersection : ZeroSectionSelfIntersection F.homotopy chern
  fundamental : VX.chow (F.virtualRank + (F.rankF₁ : ℤ))
  cone_is_zeroSection :
    F.coneClassAtGysinDegree =
      (selfIntersection.zeroPushforward
        (F.virtualRank + (F.rankF₁ : ℤ))).map.induced fundamental

namespace ObstructionBundleCalculation

variable {F : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
  (rank := rank) (N := N) (T := T) (G := G)}

/-- On a smooth stack with locally free obstruction sheaf, the virtual class is the top Chern
class of that obstruction sheaf capped with the fundamental class. -/
theorem virtualClass_eq_topChern (B : ObstructionBundleCalculation F) :
    F.virtualClass = VX.cast (by omega)
      (B.chern.topChern (F.virtualRank + (F.rankF₁ : ℤ)) B.fundamental) := by
  rw [ResolvedStackCone.virtualClass, B.cone_is_zeroSection]
  let i : ℤ := F.virtualRank + (F.rankF₁ : ℤ)
  let z := (B.selfIntersection.zeroPushforward i).map.induced B.fundamental
  have hi : i - (F.rankF₁ : ℤ) = F.virtualRank := by
    dsimp [i]
    omega
  have hp : i = i - (F.rankF₁ : ℤ) + (F.rankF₁ : ℤ) := by omega
  have hself := B.selfIntersection.formula i B.fundamental
  have htransport := F.homotopy.cast_zeroSectionGysin hi (F.chowF₁.cast hp z)
  calc
    F.homotopy.zeroSectionGysin F.virtualRank z =
        F.homotopy.zeroSectionGysin F.virtualRank
          (F.chowF₁.cast (congrArg (fun k : ℤ ↦ k + F.rankF₁) hi)
            (F.chowF₁.cast hp z)) := by
      rw [VistoliCyclePresentation.cast_cast]
      simp
    _ = VX.cast hi
          (F.homotopy.zeroSectionGysin (i - F.rankF₁) (F.chowF₁.cast hp z)) :=
      htransport.symm
    _ = VX.cast hi (B.chern.topChern i B.fundamental) :=
      congrArg (VX.cast hi) hself
    _ = VX.cast (by omega)
          (B.chern.topChern (F.virtualRank + (F.rankF₁ : ℤ)) B.fundamental) := by
      rfl

end ObstructionBundleCalculation

/-- Comparison obtained after adjoining an acyclic summand `[K ≅ K]` to a resolution. -/
structure AcyclicSummandComparison
    (F Fplus : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) (N := N) (T := T) (G := G)) where
  summandRank : ℕ
  rankF₀_formula : Fplus.rankF₀ = F.rankF₀ + summandRank
  rankF₁_formula : Fplus.rankF₁ = F.rankF₁ + summandRank
  comparison : StackResolutionComparison VX F Fplus
  comparison_rank : comparison.rank_eq = by
    simp [ResolvedStackCone.virtualRank, rankF₀_formula, rankF₁_formula]

namespace AcyclicSummandComparison

variable {F Fplus : ResolvedStackCone (VX := VX)
  (FiniteLocallyFree := FiniteLocallyFree) (rank := rank)
  (N := N) (T := T) (G := G)}

/-- Adding `[K ≅ K]` changes both bundle ranks by `rank K` and leaves the zero-section class
unchanged. -/
theorem virtualClass_eq (A : AcyclicSummandComparison F Fplus) :
    VX.cast A.comparison.rank_eq F.virtualClass = Fplus.virtualClass :=
  A.comparison.virtualClass_eq

end AcyclicSummandComparison

/-- Invariance of a virtual class under derived isomorphism of obstruction theories and
equivalence of Deligne--Mumford stacks. -/
structure EquivalenceInvariance
    {Y : DeligneMumfordStack.{u}} (VY : VistoliCyclePresentation Y)
    (degree : ℤ) where
  stackEquivalence : StackEquivalenceData X.toStack Y.toStack
  chowEquivalence : VX.chow degree ≃ₗ[ℚ] VY.chow degree
  sourceClass : VX.chow degree
  targetClass : VY.chow degree
  formula : chowEquivalence sourceClass = targetClass

/-- Proper virtual-dimension-zero calculation by scheme-theoretic length. -/
structure ProperZeroDimensionalLength where
  scheme : Scheme.{u}
  schemeComparison : StackEquivalenceData X.toStack (representedStack scheme)
  GroundField : Type u
  [groundField : Field GroundField]
  structureMap : scheme ⟶ _root_.AlgebraicGeometry.Spec (.of GroundField)
  proper : _root_.AlgebraicGeometry.IsProper structureMap
  lci : GromovWitten.AlgebraicGeometry.LocallyCompleteIntersection structureMap
  degree : ProperDegree VX
  virtualClass : VX.chow 0
  fundamentalClass : VX.chow 0
  lciFormula : virtualClass = fundamentalClass
  schemeTheoreticLength : ℕ
  degreeFundamental : degree.degree fundamentalClass = schemeTheoreticLength

attribute [instance] ProperZeroDimensionalLength.groundField

namespace ProperZeroDimensionalLength

/-- For a proper zero-dimensional lci scheme, virtual degree equals ordinary length after
rationalization. -/
theorem virtualDegree_eq_length (Z : ProperZeroDimensionalLength (VX := VX)) :
    Z.degree.degree Z.virtualClass = Z.schemeTheoreticLength := by
  rw [Z.lciFormula, Z.degreeFundamental]

end ProperZeroDimensionalLength

-/

end


end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
