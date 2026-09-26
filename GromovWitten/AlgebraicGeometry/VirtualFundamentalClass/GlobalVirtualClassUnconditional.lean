/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalVirtualClassSurjective
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjectiveGlobal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjectiveRelation
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ConeGluingGlobal
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ConeGluingCompatible

/-!
# Global graded cone-class lifts, end to end

This file assembles the three halves of the global cone-class lift construction that were proved
separately in round 18 and states the resulting theorems in the form a user of the theory wants.

## What is now unconditional

* **Existence.**  For a *compact* scheme `X` locally of finite type over a field `F` (a morphism
  `f : X ⟶ Spec F` with `[LocallyOfFiniteType f] [CompactSpace X]`) carrying a global cone datum
  `𝒞 : GlobalCone.GlobalConeData 𝓔 φ` on a vector bundle `𝓔` of finite rank,
  `GlobalVirtualClass.gradedConeClassLiftFT' f 𝒞 i RX RE`
  (`VirtualFundamentalClass/GlobalVirtualClassSurjective.lean`) is a class in the rational Chow
  group `A_i(X)` with pullback equal to the cone class, and it carries **no hypothesis at all**:
  the
  surjectivity half of the homotopy property (Fulton, *Intersection Theory*, Prop. 1.9) is the
  theorem `BundlePullbackGlobal.chowPullbackBundleFiniteType_surjective`.
* **Uniqueness for a globally trivial obstruction bundle.**  If the bundle admits a
  `GlobalTrivialisation` then the global flat pullback is injective
  (`BundlePullbackGlobal.chowPullbackBundleGlobal_injective`, the rank induction of
  `IntersectionTheory/BundleHomotopyInjectiveGlobal.lean` over the rank-one theorem
  `LineBundleInjective.rankOneInjective` of
  `IntersectionTheory/LineBundleInjectiveRelation.lean`), so the generic lift is the *unique* class
  with pullback equal to the cone class.  This too is now a **theorem with no hypothesis** beyond
  `[Infinite F]`: `existsUnique_gradedConeClassLiftFT'_of_globalTrivialisation'` and its primed
  companions.  The unprimed statements keep the rank-one injectivity as an explicit hypothesis
  `hrank1 : BundlePullbackGlobal.RankOneInjective F`, which is what a finite base field would
  need.
* **The global cone datum from local models.**  A `ConeGluing.LocalConeData 𝓔 φ` — affine
  obstruction models on the charts of the bundle whose resolved-cone ideals agree over every
  affine open of every overlap — glues to a `GlobalCone.GlobalConeData`
  (`LocalConeData.toGlobalConeData`, `VirtualFundamentalClass/ConeGluingGlobal.lean`), and the
  overlap hypothesis follows from compatible local embeddings into flat formally étale charts
  (`ConeGluing.CompatibleLocalEmbeddingData.toLocalConeData`,
  `VirtualFundamentalClass/ConeGluingCompatible.lean`).  Composing, this file defines
  `LocalConeData.gradedConeClassLiftFT` and
  `CompatibleLocalEmbeddingData.gradedConeClassLiftFT`: a generic graded cone-class lift for
  a compact scheme locally of finite type over a field, built from compatible local obstruction
  and refinement data.

## What is still missing

* **Uniqueness for a bundle that is only locally trivial.**  This is the injectivity half of
  Fulton, *Intersection Theory*, Thm. 3.3(a).  Its proof needs Chern classes and the projective
  bundle formula, which the repository does not have; the results below are therefore stated for
  bundles equipped with a `GlobalTrivialisation`.  Without a trivialisation the class
  `gradedConeClassLiftFT'` is still defined, but it is only canonical modulo `ker π^*`.
* An **infinite** base field: the rank-one theorem `LineBundleInjective.rankOneInjective` needs
  `[Infinite F]` (a generic translate of the zero section has to exist).  For a finite base field
  the primed statements do not apply and the rank-one input
  `BundlePullbackGlobal.RankOneInjective F` has to be supplied by hand as `hrank1`.
* `CompatibleLocalEmbeddingData.compat` derives ideal compatibility from direct or common-refinement
  comparisons. Constructing these comparisons for arbitrary ambient presentations remains an
  explicit geometric input; the ideal equality itself is no longer supplied.

## Main declarations

* `GlobalVirtualClass.bundlePullbackFT_injective_of_globalTrivialisation`,
  `GlobalVirtualClass.gradedConeClassLiftFT'_unique_of_globalTrivialisation`,
  `GlobalVirtualClass.existsUnique_gradedConeClassLiftFT'_of_globalTrivialisation`.
* `ConeGluing.LocalConeData.gradedConeClassLiftFT`, with
  `ConeGluing.LocalConeData.bundlePullbackFT_gradedConeClassLiftFT`,
  `ConeGluing.LocalConeData.gradedConeClassLiftFT_unique_of_globalTrivialisation` and
  `ConeGluing.LocalConeData.existsUnique_gradedConeClassLiftFT_of_globalTrivialisation`.
* `ConeGluing.CompatibleLocalEmbeddingData.gradedConeClassLiftFT` and the same three statements.
* `ConeGluing.CompatibleLocalEmbeddingData.CompatibleLocalPerfectObstructionTheories` and
  `ConeGluing.CompatibleLocalEmbeddingData.virtualClassFT`: the public global VFC gate
  over one field and its rank-derived constructor.
* The primed versions of all the uniqueness statements
  (`existsUnique_gradedConeClassLiftFT'_of_globalTrivialisation'`, …), which take `[Infinite F]` in
  place of the hypothesis `hrank1`.
-/

universe u

-- Inherited from `GlobalVirtualClass.lean`: the coordinate ring of the affine product
-- `C ×_X E₀` is a tensor product whose left factor is a quotient of a Rees algebra.
set_option maxSynthPendingDepth 5

-- Inherited from `GlobalVirtualClass.lean`: the index type of Mathlib's directed affine cover is
-- definitionally, but not reducibly, the type of affine opens.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace RelativeSpec
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualFundamentalClass

noncomputable section

namespace VirtualClass.GlobalVirtualClass

/-! ## Uniqueness for a globally trivial obstruction bundle -/

section Trivial

open FiniteTypeDimension

variable {F : Type u} [Field F] {k : Type u} [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] {ι : Type u}
  [Finite ι] {𝓔 : BundleData X ι} {R : 𝓔.J → Type u} [∀ j, CommRing (R j)]
  [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalCone.GlobalConeData 𝓔 φ) [IsLocallyNoetherian 𝒞.coneScheme] (i : ℤ)
  (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **Injectivity of the global flat pullback for a globally trivial bundle.**  This is
`IntersectionTheory.BundlePullbackGlobal.chowPullbackBundleGlobal_injective` stated for the map
`bundlePullbackFT` used by the construction of the generic lift, to which it is definitionally
equal.  The hypothesis `hrank1` is the rank-one case
`BundlePullbackGlobal.RankOneInjective F`. -/
theorem bundlePullbackFT_injective_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔) :
    Function.Injective (bundlePullbackFT f i RX RE) :=
  BundlePullbackGlobal.chowPullbackBundleGlobal_injective hrank1 f t i RX RE

/-- **Uniqueness of the generic lift of a compact scheme locally of finite type over a field,
for a globally trivial obstruction bundle.**  Here the injectivity hypothesis `hinj` of
`gradedConeClassLiftFT'_unique` is discharged; what is left is the rank-one hypothesis `hrank1`
and the
global trivialisation `t`. -/
theorem gradedConeClassLiftFT'_unique_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔)
    (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    α = gradedConeClassLiftFT' f 𝒞 i RX RE :=
  gradedConeClassLiftFT'_unique f 𝒞 i RX RE
    (bundlePullbackFT_injective_of_globalTrivialisation f i RX RE hrank1 t) α hα

/-- The symmetric form of `gradedConeClassLiftFT'_unique_of_globalTrivialisation`. -/
theorem eq_gradedConeClassLiftFT'_of_pullback_eq_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔)
    (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    gradedConeClassLiftFT' f 𝒞 i RX RE = α :=
  (gradedConeClassLiftFT'_unique_of_globalTrivialisation f 𝒞 i RX RE hrank1 t α hα).symm

/-- **Existence and uniqueness of the generic lift of a compact scheme locally of
finite type over a field, for a globally trivial obstruction bundle.**  Both halves of the
homotopy property of Chow groups (Fulton, *Intersection Theory*, Prop. 1.9 and Thm. 3.3(a)) are
theorems in this situation; the only hypothesis is the rank-one injectivity `hrank1`. -/
theorem existsUnique_gradedConeClassLiftFT'_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_gradedConeClassLiftFT' f 𝒞 i RX RE
    (bundlePullbackFT_injective_of_globalTrivialisation f i RX RE hrank1 t)

/-! ### The unconditional versions over an infinite field -/

/-- **Injectivity of the global flat pullback for a globally trivial bundle, unconditionally.**
The rank-one hypothesis is discharged by
`IntersectionTheory.LineBundleInjective.rankOneInjective`, which needs `[Infinite F]`. -/
theorem bundlePullbackFT_injective_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) :
    Function.Injective (bundlePullbackFT f i RX RE) :=
  bundlePullbackFT_injective_of_globalTrivialisation f i RX RE
    (LineBundleInjective.rankOneInjective F) t

/-- **Uniqueness of the generic lift of a compact scheme locally of finite type over an
infinite field, for a globally trivial obstruction bundle** — with no hypothesis left. -/
theorem gradedConeClassLiftFT'_unique_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    α = gradedConeClassLiftFT' f 𝒞 i RX RE :=
  gradedConeClassLiftFT'_unique_of_globalTrivialisation f 𝒞 i RX RE
    (LineBundleInjective.rankOneInjective F) t α hα

/-- The symmetric form of `gradedConeClassLiftFT'_unique_of_globalTrivialisation'`. -/
theorem eq_gradedConeClassLiftFT'_of_pullback_eq_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    gradedConeClassLiftFT' f 𝒞 i RX RE = α :=
  (gradedConeClassLiftFT'_unique_of_globalTrivialisation' f 𝒞 i RX RE t α hα).symm

/-- **Existence and uniqueness of the generic lift of a compact scheme locally of
finite type over an infinite field, for a globally trivial obstruction bundle.**  Both halves of
the homotopy property of Chow groups (Fulton, *Intersection Theory*, Prop. 1.9 and Thm. 3.3(a))
are theorems in this situation, so the statement has **no hypothesis at all** beyond the
instances `[Infinite F]`, `[LocallyOfFiniteType f]`, `[CompactSpace X]` and the trivialisation
`t`. -/
theorem existsUnique_gradedConeClassLiftFT'_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_gradedConeClassLiftFT'_of_globalTrivialisation f 𝒞 i RX RE
    (LineBundleInjective.rankOneInjective F) t

end Trivial

end VirtualClass.GlobalVirtualClass

/-! ## The generic lift of a glued cone -/

namespace VirtualClass.ConeGluing

section Glued

open FiniteTypeDimension GlobalVirtualClass

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
  {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)}
  {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}

/-- **The glued cone of a `LocalConeData` is locally Noetherian**, as an instance, whenever the
base is locally Noetherian and the bundle has finite rank.  This is C2c's
`LocalConeData.isLocallyNoetherian_toGlobalConeData_of_totalSpace` combined with
`IntersectionTheory.BundlePullbackGlobal.isLocallyNoetherian_totalSpace`; it discharges the
Noetherianity instance that `GlobalVirtualClass.lean` requires of a global cone datum. -/
instance isLocallyNoetherian_coneScheme_toGlobalConeData [Finite ι] [IsLocallyNoetherian X]
    [Finite 𝓔.J] (𝓛 : LocalConeData 𝓔 φ) :
    IsLocallyNoetherian (𝓛.toGlobalConeData).coneScheme :=
  𝓛.isLocallyNoetherian_toGlobalConeData_of_totalSpace

namespace LocalConeData

variable {F : Type u} [Field F] [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] [Finite ι]
  [Finite 𝓔.J] (𝓛 : LocalConeData 𝓔 φ) (i : ℤ)
  (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **A generic graded cone-class lift of a compact scheme locally of finite type over a field,
built from local obstruction data.**  The local models `φ j` on the charts of the bundle `𝓔`
 glue to a global cone datum by `LocalConeData.toGlobalConeData`, and the generic lift of that
datum is `GlobalVirtualClass.gradedConeClassLiftFT'`, which carries no hypothesis.

The instance hypotheses are exactly: `[Finite ι]` (the bundle has finite rank), `[Finite 𝓔.J]`
(finitely many charts), `[CompactSpace X]`, `[LocallyOfFiniteType f]` and `[IsLocallyNoetherian
X]`.  The last one is not an extra assumption: it follows from the other two by
`IntersectionTheory.BundlePullbackGlobal.isLocallyNoetherian_of_locallyOfFiniteType f 𝓔`, but it
cannot be inferred by instance resolution because `f` does not occur in its statement.  The
quasi-separatedness of `X` required by `toGlobalConeData` is inferred from it. -/
def gradedConeClassLiftFT : RX.ChowGroup :=
  GlobalVirtualClass.gradedConeClassLiftFT' f 𝓛.toGlobalConeData i RX RE

/-- The defining property of the generic lift of a glued cone: its pullback is the cone class. -/
@[simp]
theorem bundlePullbackFT_gradedConeClassLiftFT :
    bundlePullbackFT f i RX RE (𝓛.gradedConeClassLiftFT f i RX RE) =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  bundlePullbackFT_gradedConeClassLiftFT' f 𝓛.toGlobalConeData i RX RE

/-- **Uniqueness of the generic lift of a glued cone**, for a globally trivial obstruction
bundle: the only hypotheses are the rank-one injectivity `hrank1` and the trivialisation `t`. -/
theorem gradedConeClassLiftFT_unique_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE) :
    α = 𝓛.gradedConeClassLiftFT f i RX RE :=
  gradedConeClassLiftFT'_unique_of_globalTrivialisation f 𝓛.toGlobalConeData i RX RE hrank1 t α hα

/-- **Existence and uniqueness of the generic lift of a compact scheme locally of
finite type over a field, from local obstruction data and a global trivialisation of the
obstruction bundle.**  This is the end-to-end statement of the construction. -/
theorem existsUnique_gradedConeClassLiftFT_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_gradedConeClassLiftFT'_of_globalTrivialisation f 𝓛.toGlobalConeData i RX RE hrank1 t

/-- **Existence and uniqueness of the generic lift of a compact scheme locally of
finite type over an infinite field, built from local obstruction data**, for a globally trivial
obstruction bundle.  Nothing is assumed beyond the instances and the trivialisation `t`: the
rank-one injectivity is `IntersectionTheory.LineBundleInjective.rankOneInjective`. -/
theorem existsUnique_gradedConeClassLiftFT_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.existsUnique_gradedConeClassLiftFT_of_globalTrivialisation f i RX RE
    (LineBundleInjective.rankOneInjective F) t

end LocalConeData

/-! ## The generic lift from local embeddings -/

namespace CompatibleLocalEmbeddingData

variable {F : Type u} [Field F] [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] [Finite ι]
  [Finite 𝓔.J] (𝓛 : CompatibleLocalEmbeddingData 𝓔 φ) (i : ℤ)
  (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **The generic lift attached to local embeddings.**  A `CompatibleLocalEmbeddingData`
presents, over every affine open of every chart, the sections of `X` as a quotient of a flat
formally étale algebra and the bundle algebra as the corresponding base change of the local
obstruction model and direct or common-refinement comparisons.
`CompatibleLocalEmbeddingData.toLocalConeData` derives the overlap ideal equality from those
comparisons; ideal equality is not supplied separately. -/
def gradedConeClassLiftFT : RX.ChowGroup :=
  𝓛.toLocalConeData.gradedConeClassLiftFT f i RX RE

/-- The defining property of the generic lift attached to local embeddings. -/
@[simp]
theorem bundlePullbackFT_gradedConeClassLiftFT :
    bundlePullbackFT f i RX RE (𝓛.gradedConeClassLiftFT f i RX RE) =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.toLocalConeData.bundlePullbackFT_gradedConeClassLiftFT f i RX RE

/-- **Uniqueness of the generic lift attached to local embeddings**, for a globally trivial
obstruction bundle. -/
theorem gradedConeClassLiftFT_unique_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE) :
    α = 𝓛.gradedConeClassLiftFT f i RX RE :=
  𝓛.toLocalConeData.gradedConeClassLiftFT_unique_of_globalTrivialisation f i RX RE hrank1 t α hα

/-- **Existence and uniqueness of the generic lift of a compact scheme locally of
finite type over a field, from local embeddings into flat formally étale charts and a global
trivialisation of the obstruction bundle.** -/
theorem existsUnique_gradedConeClassLiftFT_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.toLocalConeData.existsUnique_gradedConeClassLiftFT_of_globalTrivialisation f i RX RE hrank1 t

/-- **The theorem the whole construction aims at**: for a compact scheme `X` locally of finite
type over an infinite field, local embeddings into flat formally étale charts with compatible
obstruction models, and a global trivialisation of the obstruction bundle, there is a *unique*
class in `A_i(X)` whose flat pullback to the total space of the bundle is the class of the
glued cone.  There is no hypothesis beyond the listed instances and the data. -/
theorem existsUnique_gradedConeClassLiftFT_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.toLocalConeData.existsUnique_gradedConeClassLiftFT_of_globalTrivialisation' f i RX RE t

end CompatibleLocalEmbeddingData

/-! ## The VFC from compatible local obstruction theories -/

namespace CompatibleLocalEmbeddingData

section PerfectObstructionTheory

variable {F : Type u} [Field F] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
  [Finite ι] [IsLocallyNoetherian X] [CompactSpace X] [Finite 𝓔.J]
  {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra F (R j)]
  {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex F (R j) (I j))}
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f]
  (𝓛 : CompatibleLocalEmbeddingData (k := F) 𝓔 φ)

/-- Local perfect obstruction theories compatible with a finite affine embedding cover.

The `CompatibleLocalEmbeddingData` argument carries the actual overlap comparisons. The scalar
field ties each chosen affine model to the given morphism `f : X ⟶ Spec F`; this makes the local
cotangent complexes and the global dimension function use the same field. -/
structure CompatibleLocalPerfectObstructionTheories (j₀ : 𝓔.J) : Prop where
  ambientSmooth : ∀ j, Algebra.FormallySmooth F (R j)
  perfect : ∀ j, PicardCriteria.IsPerfectTwoTerm (E j)
  obstruction : ∀ j, PicardCriteria.IsObstructionTheory (φ j)
  virtualRank_eq : ∀ j,
    PicardCriteria.virtualRank (E j) = PicardCriteria.virtualRank (E j₀)
  /-- The local resolution presents the bundle used by the global pullback. -/
  bundleRank_eq : ∀ j, Module.finrank (R j ⧸ I j) (E j).degreeZero = Nat.card ι
  chartScalar : ∀ (j : 𝓔.J) (a : F),
    𝓛.chartBase j
        (((Scheme.ΓSpecIso (.of F)).inv ≫
          f.appLE ⊤ (𝓔.chart j).1 (by simp)) a) =
      algebraMap F (R j ⧸ I j) a

omit [IsLocallyNoetherian X] [CompactSpace X] [Finite ι] [Finite 𝓔.J] [LocallyOfFiniteType f] in
/-- Build the compatible-local gate from chartwise POT witnesses and scalar compatibility. -/
theorem CompatibleLocalPerfectObstructionTheories.ofWitnesses (j₀ : 𝓔.J)
    (ambientSmooth : ∀ j, Algebra.FormallySmooth F (R j))
    (perfect : ∀ j, PicardCriteria.IsPerfectTwoTerm (E j))
    (obstruction : ∀ j, PicardCriteria.IsObstructionTheory (φ j))
    (virtualRank_eq : ∀ j,
      PicardCriteria.virtualRank (E j) = PicardCriteria.virtualRank (E j₀))
    (bundleRank_eq : ∀ j, Module.finrank (R j ⧸ I j) (E j).degreeZero = Nat.card ι)
    (chartScalar : ∀ (j : 𝓔.J) (a : F),
      𝓛.chartBase j
          (((Scheme.ΓSpecIso (.of F)).inv ≫
            f.appLE ⊤ (𝓔.chart j).1 (by simp)) a) =
        algebraMap F (R j ⧸ I j) a) :
    𝓛.CompatibleLocalPerfectObstructionTheories f j₀ :=
  { ambientSmooth := ambientSmooth
    perfect := perfect
    obstruction := obstruction
    virtualRank_eq := virtualRank_eq
    bundleRank_eq := bundleRank_eq
    chartScalar := chartScalar }

variable (j₀ : 𝓔.J)
  (hpot : 𝓛.CompatibleLocalPerfectObstructionTheories f j₀)
  (RX₀ : RationalEquivalenceSystem X (dimensionFunction f)
    (PicardCriteria.virtualRank (E j₀)))
  (RE₀ : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (PicardCriteria.virtualRank (E j₀) + (Nat.card ι : ℤ)))

/-- **The global virtual fundamental class** attached to compatible local perfect obstruction
theories.  Its Chow degree is the virtual rank of the certified local complex on chart `j₀`. -/
noncomputable def virtualClassFT : RX₀.ChowGroup := by
  have _ := hpot
  exact 𝓛.gradedConeClassLiftFT f (PicardCriteria.virtualRank (E j₀)) RX₀ RE₀

/-- The global VFC API rejects an invocation without compatible local POT evidence. -/
noncomputable example : RX₀.ChowGroup := by
  fail_if_success exact 𝓛.virtualClassFT f j₀ RX₀ RE₀
  exact 𝓛.virtualClassFT f j₀ hpot RX₀ RE₀

end PerfectObstructionTheory

end CompatibleLocalEmbeddingData

end Glued

end VirtualClass.ConeGluing

end

end GromovWitten.AlgebraicGeometry
