/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Stack
import GromovWitten.AlgebraicGeometry.IntersectionTheory.StackChow
import GromovWitten.AlgebraicGeometry.Stacks.TwoPullback

/-!
# Gysin maps and Chern operations on rational stack Chow groups

This file currently records the intended grading-correct stack Gysin interface as an inactive
checklist.  The former homotopy-invariance, zero-section, refined-Gysin, and Chern packages
accepted their essential theorems as fields and are retired below.  Only the honest scheme-level
rank-zero calculation used by the proper-point example is available elsewhere.
-/

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open CategoryTheory

universe u

noncomputable section

/-
Retired provisional stack Gysin API.  The records below accepted general homotopy invariance,
Chern operations, self-intersection, refined Gysin maps, and their base-change formulas as
fields.  They are inactive until those operations are constructed from deformation spaces and
the projective-bundle formula.  Rank-zero identity calculations remain available in the honest
scheme-level `IntersectionTheory.Gysin` API used by the proper-point example.

/-- Homotopy invariance for an actual rank-`rank` vector bundle over a separated DM stack.

The total DM stack is identified with a vector-bundle cone stack whose local two-term
presentation has zero degree-zero term and degree-one rank `rank`.  Hence the bundle projection
and its rank are geometric data; only the homotopy-invariance equivalence remains the theorem
asserted by this structure. -/
structure StackVectorBundleHomotopyInvariance
    {X E : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VE : VistoliCyclePresentation E)
    (rank : ℕ) where
  bundle : CanonicalVectorBundleStack X.toStack
  totalEquivalence : StackEquivalenceData E.toStack bundle.total
  degreeZero_eq_zero : bundle.presentation.rankDegreeZero = 0
  degreeOne_eq_rank : bundle.presentation.rankDegreeOne = rank
  /-- The cycle-theoretic map is the actual flat pullback along the displayed bundle
  projection. -/
  flatPullback (i : ℤ) : FlatPullback VE VX
    (Pseudofunctor.StrongTrans.vcomp totalEquivalence.hom bundle.projection)
    rank i
  /-- Homotopy invariance is the theorem that this geometrically specified pullback is
  bijective, rather than an independently supplied equivalence. -/
  pullback_bijective (i : ℤ) : Function.Bijective (flatPullback i).map.induced

namespace StackVectorBundleHomotopyInvariance

variable {X E : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X} {VE : VistoliCyclePresentation E}
  {rank : ℕ} (H : StackVectorBundleHomotopyInvariance VX VE rank)

/-- The bundle projection transported from the actual cone-stack presentation. -/
def projection : StackHom E.toStack X.toStack :=
  Pseudofunctor.StrongTrans.vcomp H.totalEquivalence.hom H.bundle.projection

/-- The zero section transported back to the stated total DM stack. -/
def zeroSection : StackHom X.toStack E.toStack :=
  Pseudofunctor.StrongTrans.vcomp H.bundle.vertex H.totalEquivalence.inv

/-- The homotopy-invariance equivalence derived from the actual flat pullback. -/
noncomputable def pullback (i : ℤ) : VX.chow i ≃ₗ[ℚ] VE.chow (i + rank) :=
  LinearEquiv.ofBijective (H.flatPullback i).map.induced (H.pullback_bijective i)

/-- Zero-section Gysin as the inverse of homotopy-invariant pullback. -/
def zeroSectionGysin (i : ℤ) : VE.chow (i + rank) →ₗ[ℚ] VX.chow i :=
  (H.pullback i).symm.toLinearMap

@[simp]
theorem zeroSectionGysin_pullback (i : ℤ) (z : VX.chow i) :
    H.zeroSectionGysin i (H.pullback i z) = z :=
  (H.pullback i).symm_apply_apply z

@[simp]
theorem pullback_zeroSectionGysin (i : ℤ) (z : VE.chow (i + rank)) :
    H.pullback i (H.zeroSectionGysin i z) = z :=
  (H.pullback i).apply_symm_apply z

/-- Zero-section Gysin commutes with transport of an equal grading index. -/
theorem cast_zeroSectionGysin {i j : ℤ} (h : i = j)
    (z : VE.chow (i + rank)) :
    VX.cast h (H.zeroSectionGysin i z) =
      H.zeroSectionGysin j
        (VE.cast (congrArg (fun k : ℤ ↦ k + rank) h) z) := by
  subst j
  simp

/-- Uniqueness of zero-section Gysin. -/
theorem zeroSectionGysin_unique (i : ℤ)
    (g : VE.chow (i + rank) →ₗ[ℚ] VX.chow i)
    (hg : g.comp (H.pullback i).toLinearMap = LinearMap.id) :
    g = H.zeroSectionGysin i := by
  apply LinearMap.ext
  intro z
  rw [← H.pullback_zeroSectionGysin i z]
  simpa using DFunLike.congr_fun hg (H.zeroSectionGysin i z)

/-- Homotopy invariance for the rank-zero vector bundle is constructed from the identity flat
pullback.  The bundle itself is the explicit zero two-term quotient stack, and the only
transport is across the bicategorical left unitor `id ≫ id ≅ id`. -/
noncomputable def identity
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X) :
    StackVectorBundleHomotopyInvariance V V 0 where
  bundle := zeroVectorBundleStack X.asAlgebraicStack
  totalEquivalence := StackEquivalenceData.refl X.toStack
  degreeZero_eq_zero := rfl
  degreeOne_eq_rank := rfl
  flatPullback i := by
    apply FlatPullback.ofIso
      (StackIso2.leftUnitor
        (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor))
    exact FlatPullback.identity V i
  pullback_bijective i := by
    change Function.Bijective (FlatPullback.identity V i).map.induced
    rw [FlatPullback.identity_map_induced]
    let h : i = i + (0 : ℕ) := by omega
    change Function.Bijective (V.cast h)
    constructor
    · apply Function.LeftInverse.injective (g := fun z ↦ V.cast h.symm z)
      intro z
      change V.cast h.symm (V.cast h z) = z
      rw [VistoliCyclePresentation.cast_cast,
        VistoliCyclePresentation.cast_apply_self]
    · apply Function.RightInverse.surjective (g := fun z ↦ V.cast h.symm z)
      intro z
      change V.cast h (V.cast h.symm z) = z
      rw [VistoliCyclePresentation.cast_cast,
        VistoliCyclePresentation.cast_apply_self]

end StackVectorBundleHomotopyInvariance

/-- A comparison of two vector-bundle Chow presentations. -/
structure VectorBundleComparison
    {X E E' : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X}
    {VE : VistoliCyclePresentation E} {VE' : VistoliCyclePresentation E'}
    {rank : ℕ}
    (H : StackVectorBundleHomotopyInvariance VX VE rank)
    (H' : StackVectorBundleHomotopyInvariance VX VE' rank) where
  totalIso (i : ℤ) : VE.chow (i + rank) ≃ₗ[ℚ] VE'.chow (i + rank)
  pullback_compat (i : ℤ) (z : VX.chow i) :
    totalIso i (H.pullback i z) = H'.pullback i z

namespace VectorBundleComparison

variable {X E E' : DeligneMumfordStack.{u}}
  {VX : VistoliCyclePresentation X}
  {VE : VistoliCyclePresentation E} {VE' : VistoliCyclePresentation E'}
  {rank : ℕ}
  {H : StackVectorBundleHomotopyInvariance VX VE rank}
  {H' : StackVectorBundleHomotopyInvariance VX VE' rank}

/-- Zero-section Gysin is invariant under vector-bundle isomorphism. -/
theorem zeroSectionGysin_compat (e : VectorBundleComparison H H')
    (i : ℤ) (z : VE.chow (i + rank)) :
    H'.zeroSectionGysin i (e.totalIso i z) = H.zeroSectionGysin i z := by
  apply (H'.pullback i).injective
  rw [H'.pullback_zeroSectionGysin, ← e.pullback_compat]
  simp

end VectorBundleComparison

/-- Chern operations for an actual rank-`rank` vector bundle on a dimension-graded stack Chow
theory.  The operations themselves remain to be constructed from the projective-bundle formula,
but neither their bundle nor its rank can be supplied as unrelated labels. -/
structure ChernOperations {X : DeligneMumfordStack.{u}}
    (V : VistoliCyclePresentation X) (rank : ℕ) where
  bundle : CanonicalVectorBundleStack X.toStack
  degreeZero_eq_zero : bundle.presentation.rankDegreeZero = 0
  degreeOne_eq_rank : bundle.presentation.rankDegreeOne = rank
  c (j : ℕ) (i : ℤ) : V.chow i →ₗ[ℚ] V.chow (i - j)
  c_zero (i : ℤ) : c 0 i = V.cast (by omega : i = i - (0 : ℕ))
  c_above_rank (j : ℕ) (hj : rank < j) (i : ℤ) : c j i = 0

namespace ChernOperations

variable {X : DeligneMumfordStack.{u}} {V : VistoliCyclePresentation X}
  {rank : ℕ} (C : ChernOperations V rank)

/-- Top Chern class cap product. -/
abbrev topChern (i : ℤ) : V.chow i →ₗ[ℚ] V.chow (i - rank) :=
  C.c rank i

/-- Chern operations of the actual rank-zero bundle: `c₀` is grading transport and every
positive Chern operation is zero. -/
noncomputable def zero
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X) :
    ChernOperations V 0 where
  bundle := zeroVectorBundleStack X.asAlgebraicStack
  degreeZero_eq_zero := rfl
  degreeOne_eq_rank := rfl
  c j i := if h : j = 0 then V.cast (by omega) else 0
  c_zero i := by
    simp
  c_above_rank j hj i := by
    have hj0 : j ≠ 0 := Nat.ne_of_gt hj
    simp [hj0]

end ChernOperations

/-- The self-intersection identity for a zero section. -/
structure ZeroSectionSelfIntersection
    {X E : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VE : VistoliCyclePresentation E}
    {rank : ℕ}
    (H : StackVectorBundleHomotopyInvariance VX VE rank)
    (C : ChernOperations VX rank) where
  bundle_eq : C.bundle = H.bundle
  zeroPushforward (i : ℤ) : ProperPushforward VX VE H.zeroSection i
  formula (i : ℤ) (z : VX.chow i) :
    H.zeroSectionGysin (i - rank)
      (VE.cast (by omega : i = i - rank + (rank : ℤ))
        ((zeroPushforward i).map.induced z)) =
      C.topChern i z

namespace ZeroSectionSelfIntersection

set_option backward.isDefEq.respectTransparency false in
/-- The rank-zero zero bundle satisfies self-intersection by construction.  Its zero section is
2-isomorphic to the identity, so the proper pushforward is transported from the derived identity
pushforward above; both Gysin and top Chern are grading transports. -/
noncomputable def zero
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    (finite : (Z : StackCycleGenerator X) → Fintype Z.genericInertia) :
    ZeroSectionSelfIntersection
      (StackVectorBundleHomotopyInvariance.identity V)
      (ChernOperations.zero V) where
  bundle_eq := rfl
  zeroPushforward i :=
    ProperPushforward.ofIso
      (StackIso2.leftUnitor
        (Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor))
      (ProperPushforward.identity V finite i)
  formula i z := by
    rw [ProperPushforward.ofIso_map_induced,
      ProperPushforward.identity_map_induced]
    let H := StackVectorBundleHomotopyInvariance.identity V
    let q : V.chow (i - (0 : ℕ)) := V.cast (by omega) z
    have h := H.zeroSectionGysin_pullback (i - (0 : ℕ)) q
    convert h using 1 <;>
      simp [H, q, StackVectorBundleHomotopyInvariance.pullback,
        StackVectorBundleHomotopyInvariance.identity,
        ChernOperations.topChern, ChernOperations.zero]

end ZeroSectionSelfIntersection

/-- Refined Gysin pullback for a regular immersion of codimension `codim`. -/
structure RefinedGysin
    {X Y : DeligneMumfordStack.{u}}
    (VX : VistoliCyclePresentation X) (VY : VistoliCyclePresentation Y)
    (codim : ℕ) where
  immersion : StackHom X.toStack Y.toStack
  regular : immersion.RegularImmersion
  pullback (i : ℤ) : VY.chow i →ₗ[ℚ] VX.chow (i - codim)

namespace RefinedGysin

/-- The codimension-zero refined Gysin map for the identity immersion. -/
noncomputable def identity
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X) :
    RefinedGysin V V 0 where
  immersion := Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor
  regular := by
    refine ⟨Pseudofunctor.StrongTrans.id X.toStack.toPseudofunctor,
      ⟨StackIso2.refl _⟩, ?_⟩
    intro T y
    exact ⟨⟨StackHom.identityPresentation X.toStack T y,
      ⟨(inferInstance : _root_.AlgebraicGeometry.IsClosedImmersion (𝟙 T)),
        GromovWitten.AlgebraicGeometry.LocallyCompleteIntersection.id T⟩⟩⟩
  pullback i := V.cast (by omega)

@[simp]
theorem identity_pullback
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X)
    (i : ℤ) (z : V.chow i) :
    (identity V).pullback i z = V.cast (by omega) z :=
  rfl

end RefinedGysin

/-- Base-change compatibility of refined Gysin with a pair of flat pullbacks. -/
structure RefinedGysinBaseChange
    {X Y X' Y' : DeligneMumfordStack.{u}}
    {VX : VistoliCyclePresentation X} {VY : VistoliCyclePresentation Y}
    {VX' : VistoliCyclePresentation X'} {VY' : VistoliCyclePresentation Y'}
    {codim : ℕ}
    (g : RefinedGysin VX VY codim) (g' : RefinedGysin VX' VY' codim) where
  baseMap : StackHom Y'.toStack Y.toStack
  sourceMap : StackHom X'.toStack X.toStack
  baseMap_flat : baseMap.Flat
  sourceMap_flat : sourceMap.Flat
  square : StackIso2
    (Pseudofunctor.StrongTrans.vcomp sourceMap g.immersion)
    (Pseudofunctor.StrongTrans.vcomp g'.immersion baseMap)
  pullbackSquare : StackTwoPullback.Genuine g.immersion baseMap
  sourceEquivalence : StackEquivalenceData X'.toStack pullbackSquare.pullback
  pullY (i : ℤ) : VY.chow i →ₗ[ℚ] VY'.chow i
  pullX (i : ℤ) : VX.chow i →ₗ[ℚ] VX'.chow i
  commutes (i : ℤ) (z : VY.chow i) :
    g'.pullback i (pullY i z) = pullX (i - codim) (g.pullback i z)

/-- Vistoli's canonical rational equivalence between the two normal-cone routes in a regular
base-change square, together with invariance under the tangent action used in descent. -/
structure VistoliConeEquivalence
    {X : DeligneMumfordStack.{u}} (V : VistoliCyclePresentation X) (i : ℤ) where
  firstCone : V.cycles i
  secondCone : V.cycles i
  rationallyEquivalent : V.quotientMap i firstCone = V.quotientMap i secondCone
  tangentTranslate : V.cycles i →ₗ[ℚ] V.cycles i
  tangent_invariant (z : V.cycles i) :
    V.quotientMap i (tangentTranslate z) = V.quotientMap i z

-/

end

end GromovWitten.AlgebraicGeometry.IntersectionTheory
