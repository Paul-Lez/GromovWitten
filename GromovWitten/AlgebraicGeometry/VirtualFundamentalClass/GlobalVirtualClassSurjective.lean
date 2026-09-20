/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalVirtualClass
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyGlobal

/-!
# The global virtual class without the surjectivity hypothesis

`VirtualFundamentalClass/GlobalVirtualClass.lean` constructs the virtual fundamental class
`virtualClass 𝒞 dimX dimE hshift i RX RE hmem` of a scheme carrying a global cone datum as the
preimage of the global cone class under the global flat pullback
`bundlePullback 𝓔 dimX dimE hshift i RX RE : A_i(X) →ₗ[ℚ] A_{i+r}(E₁)`.  It takes as a
hypothesis `hmem` the membership of the cone class in the range of that pullback, i.e. *one half*
of the homotopy property of Chow groups (Fulton, *Intersection Theory*, Prop. 1.9 and
Thm. 3.3(a)).

That half is now a theorem: `IntersectionTheory/BundleHomotopyGlobal.lean` proves by Noetherian
induction that `BundleOverSubscheme.chowPullbackBundleGlobal` is **surjective** for a vector
bundle of finite rank over a compact, locally Noetherian scheme.  This file feeds that theorem
into the construction, giving primed versions of the virtual class and of its characterisations
in which `hmem` no longer appears.

## Main results

* `coneClass_mem_range`: the global cone class lies in the range of `bundlePullback`, for a
  bundle over a compact locally Noetherian scheme (with the chart dimension functions and the
  homogeneity of principal divisors as hypotheses, exactly as in
  `BundlePullbackGlobal.chowPullbackBundleGlobal_surjective`).
* `virtualClass'`: **the global virtual fundamental class with `hmem` discharged**, together with
  `bundlePullback_virtualClass'`, `virtualClass'_unique`, `eq_virtualClass'_of_pullback_eq` and
  `existsUnique_virtualClass'`.
* `coneClassFT_mem_range`, `virtualClassFT'`, `bundlePullbackFT_virtualClassFT'`,
  `virtualClassFT'_unique`, `existsUnique_virtualClassFT'`: the same for a **compact** scheme
  locally of finite type over a field, where no hypothesis at all is left beyond `[CompactSpace
  X]` (and, for the uniqueness statements, the injectivity `hinj`).
* `virtualClass'_eq_overFieldVirtualClass`: the consistency statement with the affine virtual
  class `OverField.virtualClass`, restated for `virtualClass'`.

## What is still hypothetical

Only the **injectivity** `hinj` of the global bundle pullback — the other half of Fulton
3.3(a) — remains an explicit hypothesis, and it is needed only for the *uniqueness* statements,
never to define the class.  (The repository proves injectivity for globally trivial bundles; the
general statement is not available here.)  The general theorems of this file also carry the
chart dimension data `dimChart`, `dimChartE`, `hdimChart`, `hdimChartE`, the universal dimension
formula `hdim` of the chart rings and the homogeneity `hhom` of principal divisors on the total
space, since a `DimensionFunction` does not restrict to an open subscheme in general; in the
finite-type case over a field all of these are discharged.
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
open GlobalBlowup (isAffineOpen)
open RationalEquivalenceSystem.DescendingMap (openImmersionPullback)

namespace VirtualClass.GlobalVirtualClass

noncomputable section

/-! ## The cone class is a pullback -/

section MemRange

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} [Finite ι]
  {𝓔 : BundleData X ι} {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
  {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalCone.GlobalConeData 𝓔 φ) [IsLocallyNoetherian 𝒞.coneScheme]
  [IsLocallyNoetherian X] [CompactSpace X]
  (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
  (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
  (i : ℤ) (RX : RationalEquivalenceSystem X dimX i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)))

/-- **The global cone class is a flat pullback.**  For a vector bundle of finite rank over a
compact, locally Noetherian scheme the global flat pullback `π^*` is surjective
(`BundlePullbackGlobal.chowPullbackBundleGlobal_surjective`, the global form of Fulton's
Proposition 1.9), so the hypothesis `hmem` of `virtualClass` holds.

The remaining hypotheses are those of the surjectivity theorem: certified dimension functions
`dimChart`, `dimChartE` on the affine models of the trivialising charts, compatible with `dimX`
and `dimE`, the universal dimension formula for the rings of sections of the charts, and
homogeneity of the principal divisors on the total space.  All of them are discharged for a
compact scheme locally of finite type over a field; see `coneClassFT_mem_range`. -/
theorem coneClass_mem_range
    (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimChartE : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((BundlePullbackGlobal.chartε 𝓔 j).base y))
    (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
    (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
    (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE) :
    𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE) :=
  LinearMap.mem_range.2 (BundlePullbackGlobal.chowPullbackBundleGlobal_surjective 𝓔 dimX dimE
    hshift dimChart dimChartE hdimChart hdimChartE hdim hhom i RX RE
    (𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE))

/-- **The global virtual fundamental class of a compact locally Noetherian scheme.**  This is
`virtualClass` with the membership hypothesis `hmem` discharged by `coneClass_mem_range`: no
surjectivity assumption on the global flat pullback is made.

The only property of the global bundle pullback that is still hypothetical in this file is its
**injectivity** (the second half of Fulton, *Intersection Theory*, Thm. 3.3(a)); it appears as
the hypothesis `hinj` of `virtualClass'_unique` and `existsUnique_virtualClass'` and is proved in
this repository for globally trivial bundles.  It is not needed to *define* the class. -/
def virtualClass'
    (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimChartE : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((BundlePullbackGlobal.chartε 𝓔 j).base y))
    (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
    (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
    (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE) : RX.ChowGroup :=
  virtualClass 𝒞 dimX dimE hshift i RX RE
    (coneClass_mem_range 𝒞 dimX dimE hshift i RX RE dimChart dimChartE hdimChart hdimChartE
      hdim hhom)

/-- **The defining property of the global virtual class**: `π^*[X]^vir = [C(E)]`, now without any
surjectivity hypothesis. -/
@[simp]
theorem bundlePullback_virtualClass'
    (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimChartE : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((BundlePullbackGlobal.chartε 𝓔 j).base y))
    (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
    (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
    (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE) :
    bundlePullback 𝓔 dimX dimE hshift i RX RE
        (virtualClass' 𝒞 dimX dimE hshift i RX RE dimChart dimChartE hdimChart hdimChartE
          hdim hhom) =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE :=
  bundlePullback_virtualClass 𝒞 dimX dimE hshift i RX RE _

/-- **Uniqueness of the global virtual class.**  Any class pulling back to the cone class is the
virtual class, provided the global bundle pullback is injective.  Injectivity is the only
remaining hypothesis: it is the half of Fulton, *Intersection Theory*, Thm. 3.3(a) which this
file does not discharge (it is proved in this repository for globally trivial bundles). -/
theorem virtualClass'_unique
    (hinj : Function.Injective (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimChartE : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((BundlePullbackGlobal.chartε 𝓔 j).base y))
    (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
    (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
    (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE)
    (α : RX.ChowGroup)
    (hα : bundlePullback 𝓔 dimX dimE hshift i RX RE α =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE) :
    α = virtualClass' 𝒞 dimX dimE hshift i RX RE dimChart dimChartE hdimChart hdimChartE
      hdim hhom :=
  virtualClass_unique 𝒞 dimX dimE hshift i RX RE hinj _ α hα

/-- The symmetric form of `virtualClass'_unique`, convenient for rewriting. -/
theorem eq_virtualClass'_of_pullback_eq
    (hinj : Function.Injective (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimChartE : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((BundlePullbackGlobal.chartε 𝓔 j).base y))
    (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
    (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
    (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE)
    (α : RX.ChowGroup)
    (hα : bundlePullback 𝓔 dimX dimE hshift i RX RE α =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE) :
    virtualClass' 𝒞 dimX dimE hshift i RX RE dimChart dimChartE hdimChart hdimChartE
        hdim hhom = α :=
  (virtualClass'_unique 𝒞 dimX dimE hshift i RX RE hinj dimChart dimChartE hdimChart hdimChartE
    hdim hhom α hα).symm

/-- **Existence and uniqueness of the global virtual class** for a compact locally Noetherian
scheme: existence is unconditional here, and uniqueness needs only the injectivity `hinj` of the
global flat pullback. -/
theorem existsUnique_virtualClass'
    (hinj : Function.Injective (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (dimChart : ∀ j : 𝓔.J, DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimChartE : ∀ j : 𝓔.J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hdimChart : ∀ (j : 𝓔.J) (y), dimChart j y = dimX ((BundlePullbackGlobal.chartε 𝓔 j).base y))
    (hdimChartE : ∀ (j : 𝓔.J) (q), dimChartE j q = dimE ((𝓔.chartι j).base q))
    (hdim : ∀ j : 𝓔.J, VectorBundle.HasUniversalDimensionFormula Γ(X, (𝓔.chart j).1))
    (hhom : PrincipalDivisorsHomogeneous 𝓔.totalSpace dimE) :
    ∃! α : RX.ChowGroup, bundlePullback 𝓔 dimX dimE hshift i RX RE α =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClass 𝒞 dimX dimE hshift i RX RE hinj
    (coneClass_mem_range 𝒞 dimX dimE hshift i RX RE dimChart dimChartE hdimChart hdimChartE
      hdim hhom)

end MemRange

/-! ## Compact schemes locally of finite type over a field -/

section FiniteType

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

/-- **The global cone class is a flat pullback**, for a bundle over a compact scheme locally of
finite type over a field.  This discharges the hypothesis `hmem` of `virtualClassFT` with no
extra assumption beyond compactness of `X`: it is
`BundlePullbackGlobal.mem_range_chowPullbackBundleFiniteType`, whose map is by definition
`bundlePullbackFT`. -/
theorem coneClassFT_mem_range :
    𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullbackFT f i RX RE) :=
  BundlePullbackGlobal.mem_range_chowPullbackBundleFiniteType f 𝓔 i RX RE
    (𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE)

/-- **The virtual fundamental class of a compact scheme locally of finite type over a field.**
Compared with `virtualClassFT`, the membership hypothesis `hmem` is discharged by
`coneClassFT_mem_range`, and compared with `virtualClass'` no dimension data is left: the
gradings are the canonical ones of `IntersectionTheory/FiniteTypeDimension.lean`.

Hence this definition has **no hypotheses at all** besides the instance `[CompactSpace X]`.  The
only statement about the global flat pullback that is still hypothetical is its injectivity
(Fulton, *Intersection Theory*, Thm. 3.3(a)), which enters the characterisations
`virtualClassFT'_unique` and `existsUnique_virtualClassFT'` as `hinj` and is proved in this
repository for globally trivial bundles. -/
def virtualClassFT' : RX.ChowGroup :=
  virtualClassFT f 𝒞 i RX RE (coneClassFT_mem_range f 𝒞 i RX RE)

/-- The defining property of the finite-type virtual class: `π^*[X]^vir = [C(E)]`. -/
@[simp]
theorem bundlePullbackFT_virtualClassFT' :
    bundlePullbackFT f i RX RE (virtualClassFT' f 𝒞 i RX RE) =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  bundlePullbackFT_virtualClassFT f 𝒞 i RX RE (coneClassFT_mem_range f 𝒞 i RX RE)

/-- **Uniqueness of the finite-type virtual class**, under the injectivity `hinj` of the global
flat pullback — the only hypothesis left. -/
theorem virtualClassFT'_unique (hinj : Function.Injective (bundlePullbackFT f i RX RE))
    (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    α = virtualClassFT' f 𝒞 i RX RE :=
  virtualClass_unique 𝒞 (dimensionFunction f) (dimensionFunction (𝓔.proj ≫ f))
    (dimensionFunction_bundlePoint f 𝓔) i RX RE hinj (coneClassFT_mem_range f 𝒞 i RX RE) α hα

/-- The symmetric form of `virtualClassFT'_unique`. -/
theorem eq_virtualClassFT'_of_pullback_eq
    (hinj : Function.Injective (bundlePullbackFT f i RX RE)) (α : RX.ChowGroup)
    (hα : bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE) :
    virtualClassFT' f 𝒞 i RX RE = α :=
  (virtualClassFT'_unique f 𝒞 i RX RE hinj α hα).symm

/-- **Existence and uniqueness of the virtual class of a compact scheme locally of finite type
over a field**: existence is unconditional, uniqueness needs only the injectivity `hinj` of the
global flat pullback. -/
theorem existsUnique_virtualClassFT' (hinj : Function.Injective (bundlePullbackFT f i RX RE)) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClassFT f 𝒞 i RX RE hinj (coneClassFT_mem_range f 𝒞 i RX RE)

end FiniteType

/-! ## Consistency with the affine virtual class -/

section AffineConsistency

open GlobalConeAffine

variable {k R : Type u} [Field k] [Infinite k] [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R] [IsNoetherianRing R] {I : Ideal R} [Nontrivial (R ⧸ I)]
  {E : LinearTwoTermComplex (R ⧸ I)} [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero]
  (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
  (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (bundleData φ).totalSpace)
  (dimC : DimensionFunction (ResolvedCone.bundleSpace φ))
  (hdimC : ∀ y, dimC y = dimE (((globalConeData φ).bundleChartι (chartPoint φ)).base y))
  (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint (bundleData φ) x) =
    dimX x + (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero) : ℤ))
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
    (VirtualClass.virtualDimension φ))
  (RE : RationalEquivalenceSystem (bundleData φ).totalSpace dimE (VirtualClass.coneDegree φ))
  (RC : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimC (VirtualClass.coneDegree φ))

/-- **Consistency with the affine virtual class**, for the virtual class with `hmem` discharged.
For the single-chart global cone datum `GlobalConeAffine.globalConeData φ` attached to an affine
obstruction datum over a field, `virtualClass'` is the affine virtual class
`OverField.virtualClass φ`, as soon as the genuine global bundle pullback agrees with the
transported affine pullback `GlobalConeAffine.chowPullback` of the acceptance test (the
hypothesis `hmatch`, which is not proved in this repository).

This is `virtualClass_eq_overFieldVirtualClass` with its hypothesis `hmem` replaced by
`coneClass_mem_range`; the base `Spec (R ⧸ I)` is compact and locally Noetherian, so the only
hypotheses left are the chart dimension data and `hmatch`. -/
theorem virtualClass'_eq_overFieldVirtualClass
    (dimChart : ∀ j : (bundleData φ).J,
      DimensionFunction (Spec (CommRingCat.of Γ(Spec (CommRingCat.of (R ⧸ I)),
        ((bundleData φ).chart j).1))))
    (dimChartE : ∀ j : (bundleData φ).J,
      DimensionFunction (Spec (CommRingCat.of (MvPolynomial
        (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero)
        Γ(Spec (CommRingCat.of (R ⧸ I)), ((bundleData φ).chart j).1)))))
    (hdimChart : ∀ (j : (bundleData φ).J) (y),
      dimChart j y = dimX ((BundlePullbackGlobal.chartε (bundleData φ) j).base y))
    (hdimChartE : ∀ (j : (bundleData φ).J) (q),
      dimChartE j q = dimE (((bundleData φ).chartι j).base q))
    (hdim : ∀ j : (bundleData φ).J, VectorBundle.HasUniversalDimensionFormula
      Γ(Spec (CommRingCat.of (R ⧸ I)), ((bundleData φ).chart j).1))
    (hhom : PrincipalDivisorsHomogeneous (bundleData φ).totalSpace dimE)
    (hmatch : bundlePullback (bundleData φ) dimX dimE hshift
      (VirtualClass.virtualDimension φ) RX RE = chowPullback φ dimX dimE dimC hdimC RX RE RC) :
    virtualClass' (globalConeData φ) dimX dimE hshift (VirtualClass.virtualDimension φ) RX RE
        dimChart dimChartE hdimChart hdimChartE hdim hhom =
      OverField.virtualClass φ dimX dimC RX RC :=
  virtualClass_eq_overFieldVirtualClass φ dimX dimE dimC hdimC hshift RX RE RC hmatch _

end AffineConsistency

end

end VirtualClass.GlobalVirtualClass

end GromovWitten.AlgebraicGeometry
