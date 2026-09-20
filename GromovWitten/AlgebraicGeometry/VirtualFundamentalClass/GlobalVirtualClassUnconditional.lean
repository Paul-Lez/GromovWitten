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
# The global virtual fundamental class, end to end

This file assembles the three halves of the global construction of the virtual fundamental
class that were proved separately in round 18 and states the resulting theorems in the form a
user of the theory wants them.

## What is now unconditional

* **Existence.**  For a *compact* scheme `X` locally of finite type over a field `F` (a morphism
  `f : X ⟶ Spec F` with `[LocallyOfFiniteType f] [CompactSpace X]`) carrying a global cone datum
  `𝒞 : GlobalCone.GlobalConeData 𝓔 φ` on a vector bundle `𝓔` of finite rank,
  `GlobalVirtualClass.virtualClassFT' f 𝒞 i RX RE`
  (`VirtualFundamentalClass/GlobalVirtualClassSurjective.lean`) is a class in the rational Chow
  group `A_i(X)` with `π^*[X]^vir = [C(E)]`, and it carries **no hypothesis at all**: the
  surjectivity half of the homotopy property (Fulton, *Intersection Theory*, Prop. 1.9) is the
  theorem `BundlePullbackGlobal.chowPullbackBundleFiniteType_surjective`.
* **Uniqueness for a globally trivial obstruction bundle.**  If the bundle admits a
  `GlobalTrivialisation` then the global flat pullback is injective
  (`BundlePullbackGlobal.chowPullbackBundleGlobal_injective`, the rank induction of
  `IntersectionTheory/BundleHomotopyInjectiveGlobal.lean` over the rank-one theorem
  `LineBundleInjective.rankOneInjective` of
  `IntersectionTheory/LineBundleInjectiveRelation.lean`), so `[X]^vir` is the *unique* class
  with `π^*[X]^vir = [C(E)]`.  This too is now a **theorem with no hypothesis** beyond
  `[Infinite F]`: `existsUnique_virtualClassFT'_of_globalTrivialisation'` and its primed
  companions.  The unprimed statements keep the rank-one injectivity as an explicit hypothesis
  `hrank1 : BundlePullbackGlobal.RankOneInjective F`, which is what a finite base field would
  need.
* **The global cone datum from local models.**  A `ConeGluing.LocalConeData 𝓔 φ` — affine
  obstruction models on the charts of the bundle whose resolved-cone ideals agree over every
  affine open of every overlap — glues to a `GlobalCone.GlobalConeData`
  (`LocalConeData.toGlobalConeData`, `VirtualFundamentalClass/ConeGluingGlobal.lean`), and the
  overlap hypothesis itself is a consequence of local embeddings into flat formally étale charts
  (`ConeGluing.LocalEmbeddingData.toLocalConeData`,
  `VirtualFundamentalClass/ConeGluingCompatible.lean`).  Composing, this file defines
  `LocalConeData.virtualClassFT` and `LocalEmbeddingData.virtualClassFT`: **the virtual class of
  a compact scheme locally of finite type over a field, built from local obstruction data
  alone.**

## What is still missing

* **Uniqueness for a bundle that is only locally trivial.**  This is the injectivity half of
  Fulton, *Intersection Theory*, Thm. 3.3(a).  Its proof needs Chern classes and the projective
  bundle formula, which the repository does not have; the results below are therefore stated for
  bundles equipped with a `GlobalTrivialisation`.  Without a trivialisation the class
  `virtualClassFT'` is still defined, but it is only canonical modulo `ker π^*`.
* An **infinite** base field: the rank-one theorem `LineBundleInjective.rankOneInjective` needs
  `[Infinite F]` (a generic translate of the zero section has to exist).  For a finite base field
  the primed statements do not apply and the rank-one input
  `BundlePullbackGlobal.RankOneInjective F` has to be supplied by hand as `hrank1`.
* The overlap comparison `LocalEmbeddingData.transition_ideal` is a field of
  `LocalEmbeddingData`, not a theorem (it needs a transport of `LinearTwoTermComplex` and of
  `ResolvedCone.ideal` along a ring isomorphism of the base).

## Main declarations

* `GlobalVirtualClass.bundlePullbackFT_injective_of_globalTrivialisation`,
  `GlobalVirtualClass.virtualClassFT'_unique_of_globalTrivialisation`,
  `GlobalVirtualClass.existsUnique_virtualClassFT'_of_globalTrivialisation`.
* `ConeGluing.LocalConeData.virtualClassFT`, with
  `ConeGluing.LocalConeData.bundlePullbackFT_virtualClassFT`,
  `ConeGluing.LocalConeData.virtualClassFT_unique_of_globalTrivialisation` and
  `ConeGluing.LocalConeData.existsUnique_virtualClassFT_of_globalTrivialisation`.
* `ConeGluing.LocalEmbeddingData.virtualClassFT` and the same three statements.
* The primed versions of all the uniqueness statements
  (`existsUnique_virtualClassFT'_of_globalTrivialisation'`, …), which take `[Infinite F]` in
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
`bundlePullbackFT` used by the construction of the virtual class, to which it is definitionally
equal.  The hypothesis `hrank1` is the rank-one case
`BundlePullbackGlobal.RankOneInjective F`. -/
theorem bundlePullbackFT_injective_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔) :
    Function.Injective (bundlePullbackFT f i RX RE) :=
  BundlePullbackGlobal.chowPullbackBundleGlobal_injective hrank1 f t i RX RE

/-- **Uniqueness of the virtual class of a compact scheme locally of finite type over a field,
for a globally trivial obstruction bundle.**  Here the injectivity hypothesis `hinj` of
`virtualClassFT'_unique` is discharged; what is left is the rank-one hypothesis `hrank1` and the
global trivialisation `t`. -/
theorem virtualClassFT'_unique_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔)
    (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    α = virtualClassFT' f 𝒞 i RX RE :=
  virtualClassFT'_unique f 𝒞 i RX RE
    (bundlePullbackFT_injective_of_globalTrivialisation f i RX RE hrank1 t) α hα

/-- The symmetric form of `virtualClassFT'_unique_of_globalTrivialisation`. -/
theorem eq_virtualClassFT'_of_pullback_eq_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔)
    (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    virtualClassFT' f 𝒞 i RX RE = α :=
  (virtualClassFT'_unique_of_globalTrivialisation f 𝒞 i RX RE hrank1 t α hα).symm

/-- **Existence and uniqueness of the virtual fundamental class of a compact scheme locally of
finite type over a field, for a globally trivial obstruction bundle.**  Both halves of the
homotopy property of Chow groups (Fulton, *Intersection Theory*, Prop. 1.9 and Thm. 3.3(a)) are
theorems in this situation; the only hypothesis is the rank-one injectivity `hrank1`. -/
theorem existsUnique_virtualClassFT'_of_globalTrivialisation
    (hrank1 : BundlePullbackGlobal.RankOneInjective F) (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT' f 𝒞 i RX RE
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

/-- **Uniqueness of the virtual class of a compact scheme locally of finite type over an
infinite field, for a globally trivial obstruction bundle** — with no hypothesis left. -/
theorem virtualClassFT'_unique_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    α = virtualClassFT' f 𝒞 i RX RE :=
  virtualClassFT'_unique_of_globalTrivialisation f 𝒞 i RX RE
    (LineBundleInjective.rankOneInjective F) t α hα

/-- The symmetric form of `virtualClassFT'_unique_of_globalTrivialisation'`. -/
theorem eq_virtualClassFT'_of_pullback_eq_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    virtualClassFT' f 𝒞 i RX RE = α :=
  (virtualClassFT'_unique_of_globalTrivialisation' f 𝒞 i RX RE t α hα).symm

/-- **Existence and uniqueness of the virtual fundamental class of a compact scheme locally of
finite type over an infinite field, for a globally trivial obstruction bundle.**  Both halves of
the homotopy property of Chow groups (Fulton, *Intersection Theory*, Prop. 1.9 and Thm. 3.3(a))
are theorems in this situation, so the statement has **no hypothesis at all** beyond the
instances `[Infinite F]`, `[LocallyOfFiniteType f]`, `[CompactSpace X]` and the trivialisation
`t`. -/
theorem existsUnique_virtualClassFT'_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT'_of_globalTrivialisation f 𝒞 i RX RE
    (LineBundleInjective.rankOneInjective F) t

end Trivial

end VirtualClass.GlobalVirtualClass

/-! ## The virtual class of a glued cone -/

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

/-- **The virtual fundamental class of a compact scheme locally of finite type over a field,
built from local obstruction data.**  The local models `φ j` on the charts of the bundle `𝓔`
glue to a global cone datum by `LocalConeData.toGlobalConeData`, and the virtual class of that
datum is `GlobalVirtualClass.virtualClassFT'`, which carries no hypothesis.

The instance hypotheses are exactly: `[Finite ι]` (the bundle has finite rank), `[Finite 𝓔.J]`
(finitely many charts), `[CompactSpace X]`, `[LocallyOfFiniteType f]` and `[IsLocallyNoetherian
X]`.  The last one is not an extra assumption: it follows from the other two by
`IntersectionTheory.BundlePullbackGlobal.isLocallyNoetherian_of_locallyOfFiniteType f 𝓔`, but it
cannot be inferred by instance resolution because `f` does not occur in its statement.  The
quasi-separatedness of `X` required by `toGlobalConeData` is inferred from it. -/
def virtualClassFT : RX.ChowGroup :=
  GlobalVirtualClass.virtualClassFT' f 𝓛.toGlobalConeData i RX RE

/-- The defining property of the virtual class of a glued cone: `π^*[X]^vir = [C(E)]`. -/
@[simp]
theorem bundlePullbackFT_virtualClassFT :
    bundlePullbackFT f i RX RE (𝓛.virtualClassFT f i RX RE) =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  bundlePullbackFT_virtualClassFT' f 𝓛.toGlobalConeData i RX RE

/-- **Uniqueness of the virtual class of a glued cone**, for a globally trivial obstruction
bundle: the only hypotheses are the rank-one injectivity `hrank1` and the trivialisation `t`. -/
theorem virtualClassFT_unique_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE) :
    α = 𝓛.virtualClassFT f i RX RE :=
  virtualClassFT'_unique_of_globalTrivialisation f 𝓛.toGlobalConeData i RX RE hrank1 t α hα

/-- **Existence and uniqueness of the virtual fundamental class of a compact scheme locally of
finite type over a field, from local obstruction data and a global trivialisation of the
obstruction bundle.**  This is the end-to-end statement of the construction. -/
theorem existsUnique_virtualClassFT_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT'_of_globalTrivialisation f 𝓛.toGlobalConeData i RX RE hrank1 t

/-- **Existence and uniqueness of the virtual fundamental class of a compact scheme locally of
finite type over an infinite field, built from local obstruction data**, for a globally trivial
obstruction bundle.  Nothing is assumed beyond the instances and the trivialisation `t`: the
rank-one injectivity is `IntersectionTheory.LineBundleInjective.rankOneInjective`. -/
theorem existsUnique_virtualClassFT_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.existsUnique_virtualClassFT_of_globalTrivialisation f i RX RE
    (LineBundleInjective.rankOneInjective F) t

end LocalConeData

/-! ## The virtual class from local embeddings -/

namespace LocalEmbeddingData

variable {F : Type u} [Field F] [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] [Finite ι]
  [Finite 𝓔.J] (𝓛 : LocalEmbeddingData 𝓔 φ) (i : ℤ)
  (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **The virtual fundamental class attached to local embeddings.**  A `LocalEmbeddingData`
presents, over every affine open of every chart, the sections of `X` as a quotient of a flat
formally étale algebra and the bundle algebra as the corresponding base change of the local
obstruction model; `LocalEmbeddingData.toLocalConeData` then *proves* the overlap compatibility
of the resolved-cone ideals, so no ad-hoc gluing hypothesis is left. -/
def virtualClassFT : RX.ChowGroup :=
  𝓛.toLocalConeData.virtualClassFT f i RX RE

/-- The defining property of the virtual class attached to local embeddings. -/
@[simp]
theorem bundlePullbackFT_virtualClassFT :
    bundlePullbackFT f i RX RE (𝓛.virtualClassFT f i RX RE) =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.toLocalConeData.bundlePullbackFT_virtualClassFT f i RX RE

/-- **Uniqueness of the virtual class attached to local embeddings**, for a globally trivial
obstruction bundle. -/
theorem virtualClassFT_unique_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE) :
    α = 𝓛.virtualClassFT f i RX RE :=
  𝓛.toLocalConeData.virtualClassFT_unique_of_globalTrivialisation f i RX RE hrank1 t α hα

/-- **Existence and uniqueness of the virtual fundamental class of a compact scheme locally of
finite type over a field, from local embeddings into flat formally étale charts and a global
trivialisation of the obstruction bundle.** -/
theorem existsUnique_virtualClassFT_of_globalTrivialisation
    (hrank1 : IntersectionTheory.BundlePullbackGlobal.RankOneInjective F)
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.toLocalConeData.existsUnique_virtualClassFT_of_globalTrivialisation f i RX RE hrank1 t

/-- **The theorem the whole construction aims at**: for a compact scheme `X` locally of finite
type over an infinite field, local embeddings into flat formally étale charts with compatible
obstruction models, and a global trivialisation of the obstruction bundle, there is a *unique*
class in `A_i(X)` whose flat pullback to the total space of the bundle is the class of the
glued cone.  There is no hypothesis beyond the listed instances and the data. -/
theorem existsUnique_virtualClassFT_of_globalTrivialisation' [Infinite F]
    (t : GlobalTrivialisation 𝓔) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      (𝓛.toLocalConeData.toGlobalConeData).coneClassAt (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) RE :=
  𝓛.toLocalConeData.existsUnique_virtualClassFT_of_globalTrivialisation' f i RX RE t

end LocalEmbeddingData

end Glued

end VirtualClass.ConeGluing

end

end GromovWitten.AlgebraicGeometry
