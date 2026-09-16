/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.StackGysin
import GromovWitten.AlgebraicGeometry.ObstructionTheory.Geometric
import GromovWitten.AlgebraicGeometry.Stacks.TwoPullback

/-!
# The Behrend--Fantechi virtual class on a DM stack

This module is an inactive checklist for the general Behrend--Fantechi construction.  Its former
resolved-cone, two-pullback, cycle, Gysin, and common-resolution packages supplied the decisive
geometry or independence comparisons as fields and are retired below.  The only currently
exported virtual-class construction is the separate proper-point example.
-/

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass

open CategoryTheory
open IntersectionTheory IntrinsicNormalCone DerivedObstructionTheory

universe w v u t

noncomputable section

/-
This former resolved-stack API accepted the pullback realization, closedness, purity,
fundamental-cycle geometry, proper pushforward, homotopy invariance, and all resolution
comparisons as fields.  It is deliberately inactive: choosing such a record is not a
construction of a virtual class or a proof of resolution independence.  The code is retained as
a checklist for the genuine construction that must replace it.

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X : DeligneMumfordStack.{u}} {ground : Scheme.{u}}
  {O : FppfScalarRings.{u}} {L : DerivedCategory C}
  {IsPerfect : DerivedCategory C → Prop}
  {FiniteLocallyFree : C → Prop} {rank : C → ℕ}
  {N : IntrinsicNormalCone.Geometry X ground O}
  {T : PerfectObstructionTheory IsPerfect L}
  {G : PerfectGeometricRealization IsPerfect N T}
  (VX : VistoliCyclePresentation X)

/-- One global-resolution presentation of the obstruction cone inside `F₁`. -/
structure ResolvedStackCone where
  /-- The chosen global two-term resolution; global resolvability is not part of perfectness. -/
  resolution : GlobalTwoTermResolution FiniteLocallyFree T.E
  /-- Total space of `F₁=(F⁻¹)^∨`. -/
  F₁ : DeligneMumfordStack.{u}
  /-- Rational Chow theory on `F₁`. -/
  chowF₁ : VistoliCyclePresentation F₁
  virtualRank_eq_geometry :
    (rank (resolution.complex.X 0) : ℤ) -
      (rank (resolution.complex.X (-1)) : ℤ) = G.virtualRank
  /-- Atlas map from the vector bundle `F₁` to `[F₁/F₀]`. -/
  bundleToTarget : StackHom F₁.toStack G.vectorBundleTarget.total
  /-- Genuine two-pullback defining the resolved cone. -/
  resolvedPullback : StackTwoPullback.Genuine G.coneToVectorBundleTarget bundleToTarget
  /-- The resolved pullback is represented by a separated Deligne--Mumford stack. -/
  resolvedCone : DeligneMumfordStack.{u}
  resolvedConeEquiv :
    StackEquivalenceData resolvedCone.toStack resolvedPullback.pullback
  /-- The pullback projection realizes the resolved cone as a closed substack of `F₁`. -/
  resolvedConeToBundle : StackHom resolvedCone.toStack F₁.toStack
  resolvedConeToBundleComparison : StackIso2
    (Pseudofunctor.StrongTrans.vcomp resolvedConeEquiv.hom resolvedPullback.snd)
    resolvedConeToBundle
  resolvedConeToBundle_closed : resolvedConeToBundle.ClosedImmersion
  /-- Homotopy invariance for the vector bundle `F₁ → X`. -/
  homotopy : StackVectorBundleHomotopyInvariance VX chowF₁
    (rank (resolution.complex.X (-1)))
  /-- The resolved cone is pure of the rank forced by the smooth pullback from `𝔠_X`. -/
  resolvedCone_pure : PureStackDimension resolvedCone.toAlgebraicStack
    (rank (resolution.complex.X 0) : ℤ)
  resolvedConeChow : VistoliCyclePresentation resolvedCone
  /-- Finiteness and purity of the actual irreducible components.  The fundamental cycle is
  constructed from these propositions and is not supplied as Chow-class data. -/
  resolvedConeFundamentalGeometry : StackFundamentalCycleGeometry resolvedCone
    (rank (resolution.complex.X 0) : ℤ)
  resolvedConePushforward : ProperPushforward resolvedConeChow chowF₁
    resolvedConeToBundle (rank (resolution.complex.X 0) : ℤ)
  /-- Smoothness of `C(F•) → 𝔠_X` and its relative dimension. -/
  coneProjection : StackHom resolvedPullback.pullback N.cone.cone.total
  coneProjectionComparison : StackIso2 coneProjection resolvedPullback.fst
  coneProjection_smooth : coneProjection.Smooth
  coneProjection_pureRelativeDimension :
    coneProjection.HasPureRelativeDimension (rank (resolution.complex.X 0))

namespace ResolvedStackCone

variable {VX} (F : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
  (rank := rank) (N := N) (T := T) (G := G))

/-- Rank of `F₀=(F⁰)^∨`, computed from the degree-zero term of the resolution. -/
def rankF₀ : ℕ := rank (F.resolution.complex.X 0)

/-- Rank of `F₁=(F⁻¹)^∨`, computed from the degree-minus-one term of the resolution. -/
def rankF₁ : ℕ := rank (F.resolution.complex.X (-1))

/-- The resolved presentation uses the canonical composite induced by the obstruction theory;
there is no independently supplied cone-to-target map. -/
noncomputable abbrev coneToTarget : StackHom N.cone.cone.total G.vectorBundleTarget.total :=
  G.coneToVectorBundleTarget

/-- The resolved cone's fundamental class is the canonical sum of all its irreducible
components weighted by their generic local-ring lengths. -/
noncomputable def resolvedConeFundamental :
    F.resolvedConeChow.chow (F.rankF₀ : ℤ) :=
  F.resolvedConeFundamentalGeometry.fundamentalClass F.resolvedConeChow

/-- Fundamental cycle of `C(F•)` pushed through its displayed closed immersion into `F₁`.
This is defined from the geometric pushforward rather than retained as a second caller-selected
Chow class. -/
noncomputable def coneClass : F.chowF₁.chow (F.rankF₀ : ℤ) :=
  F.resolvedConePushforward.map.induced F.resolvedConeFundamental

@[simp]
theorem coneClass_eq_pushforward :
    F.coneClass = F.resolvedConePushforward.map.induced F.resolvedConeFundamental :=
  rfl

/-- Virtual rank `rank(F₀)-rank(F₁)`. -/
def virtualRank : ℤ := (F.rankF₀ : ℤ) - (F.rankF₁ : ℤ)

theorem virtualRank_add_rankF₁ :
    F.virtualRank + (F.rankF₁ : ℤ) = (F.rankF₀ : ℤ) := by
  simp [virtualRank]

/-- Cone class regraded to the source of zero-section Gysin. -/
def coneClassAtGysinDegree :
    F.chowF₁.chow (F.virtualRank + (F.rankF₁ : ℤ)) :=
  F.chowF₁.cast F.virtualRank_add_rankF₁.symm F.coneClass

/-- The resolved Behrend--Fantechi formula. -/
def virtualClass : VX.chow F.virtualRank :=
  F.homotopy.zeroSectionGysin F.virtualRank F.coneClassAtGysinDegree

theorem virtualClass_formula :
    F.virtualClass =
      F.homotopy.zeroSectionGysin F.virtualRank
        (F.chowF₁.cast F.virtualRank_add_rankF₁.symm F.coneClass) :=
  rfl

/-- The virtual rank agrees with the cohomological rank of the chosen derived resolution. -/
theorem virtualRank_eq_resolution :
    F.virtualRank = F.resolution.virtualRank rank := by
  rfl

/-- The presentation rank agrees with the intrinsic vector-bundle-stack rank. -/
theorem virtualRank_agrees_geometry : F.virtualRank = G.virtualRank :=
  F.virtualRank_eq_geometry

end ResolvedStackCone

/-- Common-resolution comparison between two resolved cone presentations. -/
structure StackResolutionComparison
    (F H : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) (N := N) (T := T) (G := G)) where
  resolutionIso :
    DerivedCategory.Q.obj F.resolution.complex ≅
      DerivedCategory.Q.obj H.resolution.complex
  resolutionIso_compat :
    resolutionIso.hom ≫ H.resolution.comparison.hom =
      F.resolution.comparison.hom
  coneTransport :
    F.chowF₁.chow (F.virtualRank + (F.rankF₁ : ℤ)) ≃ₗ[ℚ]
      H.chowF₁.chow (H.virtualRank + (H.rankF₁ : ℤ))
  cone_compat : coneTransport F.coneClassAtGysinDegree = H.coneClassAtGysinDegree
  gysin_compat
      (z : F.chowF₁.chow (F.virtualRank + (F.rankF₁ : ℤ))) :
    VX.cast (F.virtualRank_agrees_geometry.trans H.virtualRank_agrees_geometry.symm)
        (F.homotopy.zeroSectionGysin F.virtualRank z) =
      H.homotopy.zeroSectionGysin H.virtualRank (coneTransport z)

namespace StackResolutionComparison

variable {VX}
  {F H : ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
    (rank := rank) (N := N) (T := T) (G := G)}

/-- Equality of virtual ranks is forced because both resolutions realize the rank of the same
intrinsic obstruction-target stack. -/
theorem rank_eq (_e : StackResolutionComparison VX F H) :
    F.virtualRank = H.virtualRank :=
  F.virtualRank_agrees_geometry.trans H.virtualRank_agrees_geometry.symm

/-- Common-resolution compatibility proves equality of the two resolved virtual classes. -/
theorem virtualClass_eq (e : StackResolutionComparison VX F H) :
    VX.cast e.rank_eq F.virtualClass = H.virtualClass := by
  rw [ResolvedStackCone.virtualClass, ResolvedStackCone.virtualClass, e.gysin_compat]
  exact congrArg (H.homotopy.zeroSectionGysin H.virtualRank) e.cone_compat

end StackResolutionComparison

/-- All actual global resolutions of a fixed perfect obstruction theory, equipped with coherent
common dominating-resolution comparisons.  The index is fixed to the geometric resolution type;
a caller cannot use a singleton private type to hide other resolutions. -/
structure StackResolutionIndependentSystem where
  resolutionNonempty :
    Nonempty (GlobalTwoTermResolution FiniteLocallyFree T.E)
  presentation (a : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    ResolvedStackCone (VX := VX) (FiniteLocallyFree := FiniteLocallyFree)
      (rank := rank) (N := N) (T := T) (G := G)
  /-- The resolved presentation is built from the resolution indexing it. -/
  presentation_resolution (a : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    (presentation a).resolution = a
  /-- An actual common dominating global resolution for each pair. -/
  commonResolution (a b : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    GlobalTwoTermResolution FiniteLocallyFree T.E
  commonToLeft (a b : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    StackResolutionComparison VX
    (presentation (commonResolution a b)) (presentation a)
  commonToRight (a b : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    StackResolutionComparison VX
    (presentation (commonResolution a b)) (presentation b)

namespace StackResolutionIndependentSystem

variable {VX}
  (S : StackResolutionIndependentSystem (VX := VX)
    (FiniteLocallyFree := FiniteLocallyFree) (rank := rank)
    (N := N) (T := T) (G := G))

/-- The common virtual rank is the rank of the fixed intrinsic obstruction-target stack. -/
def virtualRank (_S : StackResolutionIndependentSystem (VX := VX)
    (FiniteLocallyFree := FiniteLocallyFree) (rank := rank)
    (N := N) (T := T) (G := G)) : ℤ :=
  G.virtualRank

/-- Every presentation has the forced intrinsic virtual rank. -/
theorem rank_eq (a : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    (S.presentation a).virtualRank = S.virtualRank :=
  (S.presentation a).virtualRank_agrees_geometry

/-- The class computed by one resolution, transported to the intrinsic virtual degree. -/
def evaluatedClass (a : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    VX.chow S.virtualRank :=
  VX.cast (S.rank_eq a) (S.presentation a).virtualClass

/-- A single common-resolution comparison identifies the two evaluated classes. -/
private theorem evaluatedClass_eq_of_comparison
    (a b : GlobalTwoTermResolution FiniteLocallyFree T.E)
    (e : StackResolutionComparison VX (S.presentation a) (S.presentation b)) :
    S.evaluatedClass a = S.evaluatedClass b := by
  have h := e.virtualClass_eq
  unfold evaluatedClass
  calc
    VX.cast (S.rank_eq a) (S.presentation a).virtualClass =
        VX.cast (e.rank_eq.trans (S.rank_eq b))
          (S.presentation a).virtualClass := by congr
    _ = VX.cast (S.rank_eq b)
          (VX.cast e.rank_eq (S.presentation a).virtualClass) := by
      rw [VistoliCyclePresentation.cast_cast]
    _ = VX.cast (S.rank_eq b) (S.presentation b).virtualClass :=
      congrArg (VX.cast (S.rank_eq b)) h

/-- Every two resolutions compute the same class, through their displayed common dominating
resolution. -/
theorem evaluatedClass_eq
    (a b : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    S.evaluatedClass a = S.evaluatedClass b := by
  calc
    S.evaluatedClass a = S.evaluatedClass (S.commonResolution a b) :=
      (S.evaluatedClass_eq_of_comparison _ _ (S.commonToLeft a b)).symm
    _ = S.evaluatedClass b :=
      S.evaluatedClass_eq_of_comparison _ _ (S.commonToRight a b)

/-- The intrinsic virtual fundamental class, chosen only from existence of a global resolution. -/
noncomputable def virtualFundamentalClass : VX.chow S.virtualRank :=
  S.evaluatedClass (Classical.choice S.resolutionNonempty)

/-- Any supplied global resolution evaluates the intrinsic class. -/
theorem virtualFundamentalClass_eq
    (a : GlobalTwoTermResolution FiniteLocallyFree T.E) :
    S.virtualFundamentalClass = S.evaluatedClass a :=
  S.evaluatedClass_eq _ _

end StackResolutionIndependentSystem

-/

end


end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass
