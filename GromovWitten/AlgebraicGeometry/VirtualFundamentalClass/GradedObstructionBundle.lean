/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackInjective
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalVirtualClassSurjective

/-!
# The virtual fundamental class for a graded obstruction bundle

Let `X` be a compact scheme locally of finite type over an infinite field `F` and let
`𝓖 : GradedBundleData X ι` be a graded vector bundle of finite rank on `X` (a locally trivial
bundle whose transition functions are graded; no global trivialisation is assumed).  By
`IntersectionTheory/BundlePullbackInjective.lean` (Fulton, *Intersection Theory*, Thm. 3.3(a))
the flat pullback `p^* : A_i(X) → A_{i+r}(E)` along the total space `E` of `𝓖.bundle` is
injective, provided intersections of affine opens of `X` are affine (`hX`), which holds when `X`
is separated.  This file feeds that injectivity into the construction of the virtual
fundamental class of `VirtualFundamentalClass/GlobalVirtualClassSurjective.lean`: for every
global cone datum `𝒞` on `𝓖.bundle`, `virtualClassFT' f 𝒞 i RX RE` is the **unique** class
`α ∈ A_i(X)` with `p^* α = [C(E)]`.

## Main results

* `isAffineOpen_inf_of_isSeparated`, `isAffineOpen_inf_of_isSeparated_hom`: the hypothesis `hX`
  (intersections of affine opens are affine) holds for a separated scheme, resp. for `X`
  separated over `Spec F` (Mathlib's `IsAffineOpen.inf`).
* `chowPullbackBundleGlobal_injective_finiteType_graded`: injectivity of the flat pullback along
  `𝓖.bundle` over a compact scheme locally of finite type over an infinite field.
* `bundlePullbackFT_injective_graded`, `virtualClassFT'_unique_graded`,
  `eq_virtualClassFT'_of_pullback_eq_graded`, `existsUnique_virtualClassFT'_graded`: the
  virtual class of a graded obstruction bundle is the unique class with `p^* [X]^vir = [C(E)]`,
  under `hX`.
* `bundlePullbackFT_injective_graded_of_isSeparated`,
  `existsUnique_virtualClassFT'_graded_of_isSeparated`,
  `existsUnique_virtualClassFT'_graded_of_isSeparated_hom`: the same with `hX` discharged by
  separatedness of `X` (resp. of `f`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualFundamentalClass

/-! ## Intersections of affine opens of a separated scheme -/

section Separated

variable {X : Scheme.{u}}

/-- On a separated scheme, the intersection of two affine opens is affine (Mathlib's
`IsAffineOpen.inf`): the hypothesis `hX` of the projective bundle formula. -/
theorem isAffineOpen_inf_of_isSeparated [X.IsSeparated] (U V : X.affineOpens) :
    IsAffineOpen (U.1 ⊓ V.1) :=
  U.2.inf V.2

/-- A scheme separated over an affine scheme is separated. -/
theorem Scheme.isSeparated_of_hom {S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsSeparated f] :
    X.IsSeparated := by
  refine ⟨?_⟩
  rw [← terminal.comp_from f]
  infer_instance

/-- If `X` is separated over `Spec F`, the intersection of two affine opens of `X` is affine. -/
theorem isAffineOpen_inf_of_isSeparated_hom {F : Type u} [Field F]
    (f : X ⟶ Spec (CommRingCat.of F)) [IsSeparated f] (U V : X.affineOpens) :
    IsAffineOpen (U.1 ⊓ V.1) :=
  have := Scheme.isSeparated_of_hom f
  isAffineOpen_inf_of_isSeparated U V

end Separated

namespace VirtualClass.GlobalVirtualClass

/-! ## Compact schemes locally of finite type over an infinite field -/

section FiniteType

open FiniteTypeDimension

variable {F : Type u} [Field F] [Infinite F] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] {ι : Type u}
  [Finite ι] (𝓖 : GradedBundleData X ι) (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
  (i : ℤ) (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓖.bundle.totalSpace (dimensionFunction (𝓖.bundle.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

include hX in
/-- **Injectivity of the flat pullback along a graded vector bundle over a compact scheme locally
of finite type over an infinite field** (Fulton, *Intersection Theory*, Thm. 3.3(a)), at the
canonical dimension functions: `X` has Noetherian underlying space since it is compact and
locally Noetherian, and the remaining hypothesis is `hX` (intersections of affine opens of `X`
are affine). -/
theorem chowPullbackBundleGlobal_injective_finiteType_graded :
    Function.Injective (BundleOverSubscheme.chowPullbackBundleGlobal 𝓖.bundle
      (dimensionFunction f) (dimensionFunction (𝓖.bundle.proj ≫ f))
      (dimensionFunction_bundlePoint f 𝓖.bundle) i RX RE) :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  chowPullbackBundleGlobal_injective_graded' f 𝓖 hX i RX RE

variable {k : Type u} [CommRing k] {R : 𝓖.bundle.J → Type u} [∀ j, CommRing (R j)]
  [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalCone.GlobalConeData 𝓖.bundle φ) [IsLocallyNoetherian 𝒞.coneScheme]

include hX in
/-- **The injectivity hypothesis `hinj` of `virtualClassFT'_unique` holds for every graded
obstruction bundle** over a compact scheme locally of finite type over an infinite field whose
affine opens have affine intersections. -/
theorem bundlePullbackFT_injective_graded :
    Function.Injective (bundlePullbackFT (𝓔 := 𝓖.bundle) f i RX RE) :=
  chowPullbackBundleGlobal_injective_finiteType_graded f 𝓖 hX i RX RE

include hX in
/-- **Uniqueness of the virtual class for a graded obstruction bundle**: over an infinite field,
for `X` compact and locally of finite type with `hX`, every class `α ∈ A_i(X)` with
`p^* α = [C(E)]` is `virtualClassFT'`.  No global trivialisation of the bundle is assumed. -/
theorem virtualClassFT'_unique_graded (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓖.bundle.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    α = virtualClassFT' f 𝒞 i RX RE :=
  virtualClassFT'_unique f 𝒞 i RX RE (bundlePullbackFT_injective_graded f 𝓖 hX i RX RE) α hα

include hX in
/-- The symmetric form of `virtualClassFT'_unique_graded`. -/
theorem eq_virtualClassFT'_of_pullback_eq_graded (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓖.bundle.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    virtualClassFT' f 𝒞 i RX RE = α :=
  (virtualClassFT'_unique_graded f 𝓖 hX i RX RE 𝒞 α hα).symm

include hX in
/-- **Existence and uniqueness of the virtual fundamental class for a graded obstruction
bundle** over a compact scheme locally of finite type over an infinite field whose affine opens
have affine intersections: there is exactly one class `α ∈ A_i(X)` with `p^* α = [C(E)]`.  Both
halves of the homotopy property of Chow groups (Fulton, Prop. 1.9 and Thm. 3.3(a)) are theorems
here; no global trivialisation of the bundle is assumed.  The remaining hypotheses are the
instances `[Infinite F]`, `[LocallyOfFiniteType f]`, `[CompactSpace X]`, `[Finite ι]`,
`[IsLocallyNoetherian 𝒞.coneScheme]` and `hX`. -/
theorem existsUnique_virtualClassFT'_graded :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓖.bundle.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT' f 𝒞 i RX RE (bundlePullbackFT_injective_graded f 𝓖 hX i RX RE)

/-! ### Separated schemes -/

/-- `bundlePullbackFT_injective_graded` for a separated scheme `X`: the hypothesis `hX` is
discharged by `isAffineOpen_inf_of_isSeparated`. -/
theorem bundlePullbackFT_injective_graded_of_isSeparated [X.IsSeparated] :
    Function.Injective (bundlePullbackFT (𝓔 := 𝓖.bundle) f i RX RE) :=
  bundlePullbackFT_injective_graded f 𝓖 isAffineOpen_inf_of_isSeparated i RX RE

/-- **Existence and uniqueness of the virtual fundamental class for a graded obstruction bundle
over a separated compact scheme locally of finite type over an infinite field**: no hypothesis
is left beyond the instances. -/
theorem existsUnique_virtualClassFT'_graded_of_isSeparated [X.IsSeparated] :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓖.bundle.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT'_graded f 𝓖 isAffineOpen_inf_of_isSeparated i RX RE 𝒞

/-- `existsUnique_virtualClassFT'_graded` for `X` separated over `Spec F`
(`[IsSeparated f]`). -/
theorem existsUnique_virtualClassFT'_graded_of_isSeparated_hom [IsSeparated f] :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓖.bundle.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT'_graded f 𝓖 (isAffineOpen_inf_of_isSeparated_hom f) i RX RE 𝒞

end FiniteType

end VirtualClass.GlobalVirtualClass

end GromovWitten.AlgebraicGeometry
