/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalCone
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobalChow
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalConeAffine
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension

/-!
# The virtual fundamental class of a general scheme

This file defines the virtual fundamental class of a scheme `X` carrying a global cone datum
`𝒞 : GlobalCone.GlobalConeData 𝓔 φ` (a global vector bundle `𝓔` with a closed subcone `C ⊆ E₁`
which over every trivialising chart is the affine resolved cone of an obstruction datum `φ j`),
using the *genuine* global flat pullback

`bundlePullback 𝓔 dimX dimE hshift i RX RE = BundleOverSubscheme.chowPullbackBundleGlobal …
  : A_i(X) →ₗ[ℚ] A_{i+r}(E₁)`

of `IntersectionTheory/BundlePullbackGlobalChow.lean`, rather than an abstract hypothesis.

## Main definitions and results

* `bundlePullback 𝓔 dimX dimE hshift i RX RE`: the flat pullback along the bundle projection on
  dimension-graded rational Chow groups.  It is `BundleOverSubscheme.chowPullbackBundleGlobal`,
  named here for readability.
* `virtualClass 𝒞 dimX dimE hshift i RX RE hmem`: **the global virtual fundamental class**
  `[X]^vir ∈ A_i(X)`, the preimage of the global cone class under the bundle pullback.
* `bundlePullback_virtualClass`: `π^*[X]^vir = [C(E)]`, the defining property.
* `virtualClass_unique`, `eq_virtualClass_of_pullback_eq`, `existsUnique_virtualClass`: the class
  is the unique such preimage when `π^*` is injective.
* `bundleChartι_eq`: the affine chart of the total space used by `GlobalConeData`
  (`bundleChartι`, built from `GlobalConeData.chartBundle`) and the one used by `BundleData`
  (`BundleData.chartι`, built from the polynomial trivialisation `BundleData.triv`) differ by the
  isomorphism of affine schemes induced by the ring isomorphism
  `chartRingEquiv 𝒞 j : MvPolynomial ι Γ(X, U_j) ≃+* ResolvedCone.bundleRing (φ j)`.  This closes
  open item 1 of the report on `GlobalCone.lean`.
* `chartPullback`: the affine bundle pullback of a chart, read on the affine model
  `ResolvedCone.bundleSpace (φ j)` of the chart.
* `chartPullback_chartRestrict_virtualClass`: **the chart comparison.**  On every chart, the
  restriction of the global virtual class satisfies exactly the equation that defines the affine
  virtual class `VirtualClass.virtualClassAt (φ j)`, namely `π_j^* (α|_{U_j}) = [C(E)|_{U_j}]`,
  where the right-hand side is the affine resolved-cone class
  `VirtualClass.resolvedConeClassAt (φ j)`.
* `chartRestrict_virtualClass_unique`: consequently, if the chart pullback is injective, the
  restriction of the global virtual class to a chart is the unique class with that property, i.e.
  it is the affine virtual class of the chart model.
* `bundlePullbackFT`, `virtualClassFT`, `bundlePullbackFT_virtualClassFT`,
  `existsUnique_virtualClassFT`: the same for a scheme locally of finite type over a field, at the
  canonical dimension functions of `IntersectionTheory/FiniteTypeDimension.lean`.  There the
  dimension-shift hypothesis `hshift` disappears (it is
  `FiniteTypeDimension.dimensionFunction_bundlePoint`), so `hmem` is the only hypothesis left.
* `virtualClass_eq_of_pullback_eq`: if the global bundle pullback agrees with another injective
  pullback (for instance the transported affine pullback `GlobalConeAffine.chowPullback` of the
  acceptance test), the two virtual classes agree.  Its specialisation
  `virtualClass_eq_overFieldVirtualClass` is the consistency statement with
  `OverField.virtualClass` for the single-chart datum `GlobalConeAffine.globalConeData φ`; it is
  conditional on the agreement `hmatch` of the two pullbacks, which is not proved here.

## What is still hypothetical

Two facts about the global bundle pullback `π^* : A_i(X) → A_{i+r}(E₁)` remain **hypotheses**
of `virtualClass` and its characterisation:

* `hmem`: the global cone class lies in the range of `π^*`;
* `hinj` (only for the uniqueness statements): `π^*` is injective.

Both are consequences of the global homotopy property of Chow groups, `π^* : A_i(X) ≅ A_{i+r}(E)`
(Fulton, *Intersection Theory*, Prop. 1.9 and Thm. 3.3(a)).  This repository proves that
isomorphism only over an affine base and for a trivialised bundle
(`VectorBundle.chowPullbackBundle`); gluing the affine statements needs a Mayer–Vietoris sequence
for Chow groups which is not available here.  In addition the dimension-shift hypothesis
`hshift` of `chowPullbackBundleGlobal` and the chart dimension hypotheses `hU`, `hP`, `hC` are
carried along, as everywhere in this repository, because a `DimensionFunction` is not
automatically compatible with an open immersion.
-/

universe u

-- The coordinate ring of the affine product `C ×_X E₀` is a tensor product whose left factor is
-- a quotient of a Rees algebra; synthesising its ring instances needs one more level of pending
-- instance problems than the default, exactly as in `GlobalCone.lean`.
set_option maxSynthPendingDepth 5

-- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
-- type of affine opens; as in `RelativeSpec.lean` the unifier is told not to respect
-- transparency in this file.
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

/-! ## The global flat pullback along the bundle projection -/

section Pullback

variable {X : Scheme.{u}} {ι : Type u} [Finite ι] (𝓔 : BundleData X ι)
  (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
  (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
  (i : ℤ) (RX : RationalEquivalenceSystem X dimX i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)))

/-- **The flat pullback along the projection of the total space of a global vector bundle**, on
dimension-graded rational Chow groups: `π^* : A_i(X) →ₗ[ℚ] A_{i+r}(E₁)`.  This is
`BundleOverSubscheme.chowPullbackBundleGlobal`, given a short name for use in the construction of
the virtual class. -/
def bundlePullback : RX.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE

theorem bundlePullback_def :
    bundlePullback 𝓔 dimX dimE hshift i RX RE =
      BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE :=
  rfl

/-- The global bundle pullback is induced by the flat pullback of dimension-graded cycles. -/
@[simp]
theorem bundlePullback_quotientMap (z : cyclesOfDimension X dimX i) :
    bundlePullback 𝓔 dimX dimE hshift i RX RE (RX.quotientMap z) =
      RE.quotientMap (BundlePullbackGlobal.flatPullbackBundleGlobal 𝓔 dimX dimE hshift i z) :=
  rfl

end Pullback

/-! ## The global virtual fundamental class -/

section VirtualClass

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} [Finite ι]
  {𝓔 : BundleData X ι} {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
  {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalCone.GlobalConeData 𝓔 φ) [IsLocallyNoetherian 𝒞.coneScheme]
  (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
  (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
  (i : ℤ) (RX : RationalEquivalenceSystem X dimX i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)))

/-- **The global virtual fundamental class** `[X]^vir ∈ A_i(X)` of a scheme carrying a global
cone datum: the preimage of the global cone class `[C(E)] ∈ A_{i+r}(E₁)` under the global flat
pullback `π^*` along the bundle projection.

The hypothesis `hmem` — that the cone class is in the image of `π^*` — is **not** proved in this
repository for a general base; it is one half of the global homotopy property of Chow groups
`π^* : A_i(X) ≅ A_{i+r}(E₁)` (Fulton, Prop. 1.9 and Thm. 3.3(a)), which is available here only
over an affine base with a trivialised bundle.  The other half, injectivity of `π^*`, is the
hypothesis `hinj` of `virtualClass_unique`; it is needed only to characterise the class, not to
define it.  The dimension-shift hypothesis `hshift` is inherited from the construction of the
pullback. -/
def virtualClass
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE)) : RX.ChowGroup :=
  𝒞.virtualClassOf dimE dimX i (i + (Nat.card ι : ℤ)) RX RE
    (bundlePullback 𝓔 dimX dimE hshift i RX RE) hmem

/-- **The defining property of the global virtual class**: `π^*[X]^vir = [C(E)]`. -/
@[simp]
theorem bundlePullback_virtualClass
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE)) :
    bundlePullback 𝓔 dimX dimE hshift i RX RE
        (virtualClass 𝒞 dimX dimE hshift i RX RE hmem) =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE :=
  𝒞.pull_virtualClassOf dimE dimX i (i + (Nat.card ι : ℤ)) RX RE _ hmem

/-- **Uniqueness of the global virtual class**: any class pulling back to the cone class is the
virtual class, provided the global bundle pullback is injective (the second half of the global
homotopy property of Chow groups, an explicit hypothesis). -/
theorem virtualClass_unique
    (hinj : Function.Injective (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (α : RX.ChowGroup)
    (hα : bundlePullback 𝓔 dimX dimE hshift i RX RE α =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE) :
    α = virtualClass 𝒞 dimX dimE hshift i RX RE hmem :=
  𝒞.virtualClassOf_unique dimE dimX i (i + (Nat.card ι : ℤ)) RX RE _ hinj hmem α hα

/-- The symmetric form of `virtualClass_unique`, convenient for rewriting. -/
theorem eq_virtualClass_of_pullback_eq
    (hinj : Function.Injective (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (α : RX.ChowGroup)
    (hα : bundlePullback 𝓔 dimX dimE hshift i RX RE α =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE) :
    virtualClass 𝒞 dimX dimE hshift i RX RE hmem = α :=
  (virtualClass_unique 𝒞 dimX dimE hshift i RX RE hinj hmem α hα).symm

/-- If the global bundle pullback coincides with another (injective) pullback `pull`, the global
virtual class is the preimage of the cone class under `pull`.  This is the form in which the
global class is compared with a class built from a different presentation of the same pullback,
for instance the transported affine pullback `GlobalConeAffine.chowPullback`. -/
theorem virtualClass_eq_of_pullback_eq
    (pull : RX.ChowGroup →ₗ[ℚ] RE.ChowGroup)
    (hpull : bundlePullback 𝓔 dimX dimE hshift i RX RE = pull)
    (hinj : Function.Injective pull)
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (α : RX.ChowGroup)
    (hα : pull α = 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE) :
    virtualClass 𝒞 dimX dimE hshift i RX RE hmem = α := by
  subst hpull
  exact eq_virtualClass_of_pullback_eq 𝒞 dimX dimE hshift i RX RE hinj hmem α hα

/-- **Existence and uniqueness of the global virtual class**, under the global homotopy property
of Chow groups (the hypotheses `hinj` and `hmem`). -/
theorem existsUnique_virtualClass
    (hinj : Function.Injective (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE)) :
    ∃! α : RX.ChowGroup, bundlePullback 𝓔 dimX dimE hshift i RX RE α =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE :=
  𝒞.existsUnique_virtualClass dimE dimX i (i + (Nat.card ι : ℤ)) RX RE _ hinj hmem

end VirtualClass

/-! ## Comparison of the two affine charts of the total space -/

section ChartIso

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
  {𝓔 : BundleData X ι} {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
  {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalCone.GlobalConeData 𝓔 φ)

/-- The comparison between the two presentations of the coordinate ring of a trivialising chart
of the total space: the polynomial trivialisation `BundleData.triv j` and the affine model
`ResolvedCone.bundleRing (φ j)` of `GlobalConeData.chartBundle j`. -/
def chartRingEquiv (j : 𝓔.J) :
    MvPolynomial ι Γ(X, (𝓔.chart j).1) ≃+* ResolvedCone.bundleRing (φ j) :=
  (𝓔.triv j).symm.toRingEquiv.trans (𝒞.chartBundle j)

instance isIso_specMap_chartRingEquiv (j : 𝓔.J) :
    IsIso (Spec.map (CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom)) :=
  GlobalCone.isIso_specMap_ringEquiv _

/-- The chart identification of `GlobalConeData` factors through the polynomial trivialisation of
`BundleData`. -/
theorem ofHom_chartBundle (j : 𝓔.J) :
    CommRingCat.ofHom (𝒞.chartBundle j).toRingHom =
      CommRingCat.ofHom (𝓔.triv j).toRingHom ≫
        CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom := by
  ext a
  change (𝒞.chartBundle j) a = (chartRingEquiv 𝒞 j) ((𝓔.triv j) a)
  simp [chartRingEquiv]

/-- **The two affine charts of the total space agree up to the isomorphism `chartRingEquiv`.**
`GlobalConeData.bundleChartι j` is built from the ring isomorphism `chartBundle j`, while
`BundleData.chartι j` is built from the polynomial trivialisation `triv j`; the two open
immersions of the chart into the total space differ exactly by `Spec` of `chartRingEquiv`.  This
is the compatibility that `GlobalConeData` deliberately does not impose as a field, and it is
what allows the cone comparison of `GlobalCone.lean` and the flat-pullback comparison of
`BundlePullbackGlobalChow.lean` to be combined. -/
theorem bundleChartι_eq (j : 𝓔.J) :
    𝒞.bundleChartι j =
      Spec.map (CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom) ≫ 𝓔.chartι j := by
  change Spec.map (CommRingCat.ofHom (𝒞.chartBundle j).toRingHom) ≫
    affineι X 𝓔.algebra (𝓔.chart j) = _
  rw [ofHom_chartBundle 𝒞 j, Spec.map_comp, BundleData.chartι, 𝓔.chartIso_inv,
    Category.assoc]

end ChartIso

/-! ## General functoriality lemmas for the Chow pullback along an open immersion -/

section Congr

variable {U V : Scheme.{u}} {dV : DimensionFunction V} {dU : DimensionFunction U} {i : ℤ}

/-- The Chow pullback along an open immersion depends only on the morphism. -/
theorem openImmersionPullback_congr (RV : RationalEquivalenceSystem V dV i)
    (RU : RationalEquivalenceSystem U dU i) (f g : U ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] (hfg : f = g)
    (hf : ∀ u, dU u = dV (f.base u)) (hg : ∀ u, dU u = dV (g.base u)) :
    openImmersionPullback RV f hf RU = openImmersionPullback RV g hg RU := by
  subst hfg
  rfl

end Congr

/-! ## The chart comparison of the global virtual class -/

section ChartComparison

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} [Finite ι]
  {𝓔 : BundleData X ι} {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
  [∀ j, IsNoetherianRing (R j)] {I : ∀ j, Ideal (R j)}
  {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
  [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero]
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalCone.GlobalConeData 𝓔 φ) [IsLocallyNoetherian 𝒞.coneScheme]
  (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
  (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
  (i : ℤ) (RX : RationalEquivalenceSystem X dimX i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)))
  (j : 𝓔.J) [IsNoetherianRing Γ(X, (𝓔.chart j).1)]
  (dimU : DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
  (dimP : DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
  (dimC : DimensionFunction (ResolvedCone.bundleSpace (φ j)))
  (hU : ∀ y, dimU y =
    dimX (((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι).base y))
  (hP : ∀ q, dimP q = dimE ((𝓔.chartι j).base q))
  (hC : ∀ v, dimC v =
    dimP ((Spec.map (CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom)).base v))
  (RU : RationalEquivalenceSystem (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) dimU i)
  (RP : RationalEquivalenceSystem
    (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))) dimP (i + (Nat.card ι : ℤ)))
  (RC : RationalEquivalenceSystem (ResolvedCone.bundleSpace (φ j)) dimC (i + (Nat.card ι : ℤ)))

omit [Finite ι] [∀ j, IsNoetherianRing (R j)] [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
  [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero] [IsLocallyNoetherian 𝒞.coneScheme]
  [IsNoetherianRing Γ(X, (𝓔.chart j).1)] in
include hP hC in
/-- The dimension grading of the affine model of a chart is the restriction of the grading of the
total space along `GlobalConeData.bundleChartι`. -/
theorem dim_bundleChartι (v : ResolvedCone.bundleSpace (φ j)) :
    dimC v = dimE ((𝒞.bundleChartι j).base v) := by
  rw [hC v, hP, bundleChartι_eq 𝒞 j, GlobalCone.comp_base_apply]

/-- **The flat pullback of the chart `j`, read in the affine model of the chart**: the affine
bundle pullback `A_i(Spec Γ(X, U_j)) → A_{i+r}(𝔸^ι_{U_j})` of `VectorBundle.chowPullbackBundle`,
followed by the transport along the chart identification `chartRingEquiv` to the affine model
`ResolvedCone.bundleSpace (φ j)` of the obstruction datum `φ j`. -/
def chartPullback : RU.ChowGroup →ₗ[ℚ] RC.ChowGroup :=
  (openImmersionPullback RP
      (Spec.map (CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom)) hC RC).comp
    (VectorBundle.chowPullbackBundle (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
      dimU dimP i RU RP)

omit [∀ j, IsNoetherianRing (R j)] [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
  [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero] [IsLocallyNoetherian 𝒞.coneScheme] in
/-- The restriction of a rational Chow class on `X` to the chart `j`, read on
`Spec Γ(X, U_j)`. -/
def chartRestrictBase : RX.ChowGroup →ₗ[ℚ] RU.ChowGroup :=
  openImmersionPullback RX
    ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι) hU RU

omit [Finite ι] [IsNoetherianRing Γ(X, (𝓔.chart j).1)] in
/-- **The restriction of the global cone class to a chart is the affine resolved-cone class.**
This is the graded chart comparison of `GlobalCone.lean`, read on rational Chow groups. -/
theorem openImmersionPullback_bundleChartι_coneClassAt :
    openImmersionPullback RE (𝒞.bundleChartι j)
        (dim_bundleChartι 𝒞 dimE j dimP dimC hP hC) RC
        (𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE) =
      VirtualClass.resolvedConeClassAt (φ j) dimC i RC := by
  change RC.quotientMap (cyclesOfDimension.flatPullbackOpen _
    (dim_bundleChartι 𝒞 dimE j dimP dimC hP hC)
    (cyclesOfDimension.project (𝒞.coneCycle dimE))) = _
  rw [cyclesOfDimension.flatPullbackOpen_project,
    𝒞.coneCycleAt_eq_resolvedConeCycleAt dimE j (i + (Nat.card ι : ℤ)) dimC]
  rfl

omit [Finite ι] [∀ j, IsNoetherianRing (R j)] [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
  [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero] [IsLocallyNoetherian 𝒞.coneScheme]
  [IsNoetherianRing Γ(X, (𝓔.chart j).1)] in
/-- Restricting to a chart and then transporting to the affine model of the chart is the
restriction along `GlobalConeData.bundleChartι`. -/
theorem openImmersionPullback_comp_chartι :
    (openImmersionPullback RP
          (Spec.map (CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom)) hC RC).comp
        (openImmersionPullback RE (𝓔.chartι j) hP RP) =
      openImmersionPullback RE (𝒞.bundleChartι j)
        (dim_bundleChartι 𝒞 dimE j dimP dimC hP hC) RC := by
  rw [openImmersionPullback_congr RE RC (𝒞.bundleChartι j)
      (Spec.map (CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom) ≫ 𝓔.chartι j)
      (bundleChartι_eq 𝒞 j) _
      (fun v ↦ (hC v).trans (hP _)),
    RationalEquivalenceSystem.DescendingMap.openImmersionPullback_comp RE RP RC _ _ hC hP]

include hP in
/-- **The chart comparison of the global virtual class.**  On every trivialising chart `j`, the
restriction of the global virtual class to the chart satisfies exactly the equation that defines
the affine virtual class of the obstruction datum `φ j`: its affine bundle pullback is the affine
resolved-cone class `VirtualClass.resolvedConeClassAt (φ j)` (compare
`VirtualClass.chowPullbackBundle_virtualClassAt`). -/
theorem chartPullback_chartRestrict_virtualClass
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE)) :
    chartPullback 𝒞 i j dimU dimP dimC hC RU RP RC
        (chartRestrictBase dimX i RX j dimU hU RU
          (virtualClass 𝒞 dimX dimE hshift i RX RE hmem)) =
      VirtualClass.resolvedConeClassAt (φ j) dimC i RC := by
  have hchart := BundleOverSubscheme.openImmersionPullback_chowPullbackBundleGlobal
    𝓔 dimX dimE hshift i j dimU dimP hU hP RX RE RU RP
  have hpull : BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE
      (virtualClass 𝒞 dimX dimE hshift i RX RE hmem) =
      𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE :=
    bundlePullback_virtualClass 𝒞 dimX dimE hshift i RX RE hmem
  have key : (VectorBundle.chowPullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) dimU dimP i RU RP).comp
        (openImmersionPullback RX
          ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι) hU RU)
        (virtualClass 𝒞 dimX dimE hshift i RX RE hmem) =
      openImmersionPullback RE (𝓔.chartι j) hP RP
        (𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE) := by
    rw [← hpull]
    exact (LinearMap.congr_fun hchart _).symm
  refine Eq.trans ?_ (openImmersionPullback_bundleChartι_coneClassAt 𝒞 dimE i RE j dimP dimC
    hP hC RC)
  rw [← openImmersionPullback_comp_chartι 𝒞 dimE i RE j dimP dimC hP hC RP RC,
    LinearMap.comp_apply]
  exact congrArg (⇑(openImmersionPullback RP
    (Spec.map (CommRingCat.ofHom (chartRingEquiv 𝒞 j).toRingHom)) hC RC)) key

include hP in
/-- **Uniqueness of the chart restriction.**  If the affine bundle pullback of the chart is
injective — which over a field with an infinite residue field is
`VirtualClass.hinj`/`OverField.hinjOf` — the restriction of the global virtual class to the chart
is the unique class whose affine bundle pullback is the affine resolved-cone class, that is, it
is the affine virtual class of `φ j`. -/
theorem chartRestrict_virtualClass_unique
    (hinjC : Function.Injective (chartPullback 𝒞 i j dimU dimP dimC hC RU RP RC))
    (hmem : 𝒞.coneClassAt dimE (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullback 𝓔 dimX dimE hshift i RX RE))
    (β : RU.ChowGroup)
    (hβ : chartPullback 𝒞 i j dimU dimP dimC hC RU RP RC β =
      VirtualClass.resolvedConeClassAt (φ j) dimC i RC) :
    β = chartRestrictBase dimX i RX j dimU hU RU
      (virtualClass 𝒞 dimX dimE hshift i RX RE hmem) :=
  hinjC (hβ.trans
    (chartPullback_chartRestrict_virtualClass 𝒞 dimX dimE hshift i RX RE j dimU dimP dimC hU hP
      hC RU RP RC hmem).symm)

end ChartComparison

/-! ## Schemes locally of finite type over a field -/

section FiniteType

open FiniteTypeDimension

variable {F : Type u} [Field F] {k : Type u} [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] {ι : Type u} [Finite ι]
  {𝓔 : BundleData X ι} {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
  {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalCone.GlobalConeData 𝓔 φ) [IsLocallyNoetherian 𝒞.coneScheme] (i : ℤ)
  (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **The global flat pullback for a scheme locally of finite type over a field**, at the
canonical dimension functions of `IntersectionTheory/FiniteTypeDimension.lean`: no dimension
hypothesis is needed, since the shift `dim_E = dim_X + r` is proved there
(`FiniteTypeDimension.dimensionFunction_bundlePoint`). -/
def bundlePullbackFT : RX.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  bundlePullback 𝓔 (dimensionFunction f) (dimensionFunction (𝓔.proj ≫ f))
    (dimensionFunction_bundlePoint f 𝓔) i RX RE

/-- **The virtual fundamental class of a scheme locally of finite type over a field.**  Compared
with `virtualClass`, no dimension hypothesis is left: the certified dimension gradings of `X` and
of the total space are `FiniteTypeDimension.dimensionFunction f` and
`FiniteTypeDimension.dimensionFunction (𝓔.proj ≫ f)`, and the shift `hshift` is
`FiniteTypeDimension.dimensionFunction_bundlePoint`.  The only remaining hypothesis is `hmem`,
the membership of the cone class in the range of the bundle pullback (half of the global homotopy
property of Chow groups).

For the missing half — injectivity of the bundle pullback — the ingredients that a Noetherian
induction would need are available at these dimension functions as well:
`FiniteTypeDimension.principalDivisorsHomogeneous` on `X`,
`FiniteTypeDimension.principalDivisorsHomogeneous_totalSpace` on `𝓔.totalSpace` and
`FiniteTypeDimension.flatPullbackBundleFiniteType_injective` on cycles. -/
def virtualClassFT
    (hmem : 𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullbackFT f i RX RE)) : RX.ChowGroup :=
  virtualClass 𝒞 (dimensionFunction f) (dimensionFunction (𝓔.proj ≫ f))
    (dimensionFunction_bundlePoint f 𝓔) i RX RE hmem

/-- The defining property of the finite-type virtual class: `π^*[X]^vir = [C(E)]`. -/
@[simp]
theorem bundlePullbackFT_virtualClassFT
    (hmem : 𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullbackFT f i RX RE)) :
    bundlePullbackFT f i RX RE (virtualClassFT f 𝒞 i RX RE hmem) =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  bundlePullback_virtualClass 𝒞 (dimensionFunction f) (dimensionFunction (𝓔.proj ≫ f))
    (dimensionFunction_bundlePoint f 𝓔) i RX RE hmem

/-- Existence and uniqueness of the finite-type virtual class, given injectivity of the bundle
pullback. -/
theorem existsUnique_virtualClassFT
    (hinj : Function.Injective (bundlePullbackFT f i RX RE))
    (hmem : 𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE ∈
      LinearMap.range (bundlePullbackFT f i RX RE)) :
    ∃! α : RX.ChowGroup, bundlePullbackFT f i RX RE α =
      𝒞.coneClassAt (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE :=
  existsUnique_virtualClass 𝒞 (dimensionFunction f) (dimensionFunction (𝓔.proj ≫ f))
    (dimensionFunction_bundlePoint f 𝓔) i RX RE hinj hmem

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
  (hdim : ∀ y, dimC y = dimE (((globalConeData φ).bundleChartι (chartPoint φ)).base y))
  (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint (bundleData φ) x) =
    dimX x + (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero) : ℤ))
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
    (VirtualClass.virtualDimension φ))
  (RE : RationalEquivalenceSystem (bundleData φ).totalSpace dimE (VirtualClass.coneDegree φ))
  (RC : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimC (VirtualClass.coneDegree φ))

/-- **Consistency with the affine virtual class.**  For the single-chart global cone datum
`GlobalConeAffine.globalConeData φ` attached to an affine obstruction datum over a field, the
global virtual class of this file is the affine virtual class `OverField.virtualClass φ`, as soon
as the genuine global bundle pullback `bundlePullback` agrees with the transported affine
pullback `GlobalConeAffine.chowPullback` of the acceptance test.

That agreement `hmatch` is an explicit hypothesis: `GlobalConeAffine.chowPullback` is *defined*
as the affine `VirtualClass.bundlePullback φ` transported along the chart isomorphism, and
identifying it with the geometric global pullback needs the transport of the affine bundle
pullback along the base isomorphism `Spec Γ(Spec (R ⧸ I), ⊤) ≅ Spec (R ⧸ I)`, which the
repository does not provide.  Everything else — injectivity of the pullback and membership of
the cone class in its range — is discharged from report J
(`GlobalConeAffine.chowPullback_injective`, `GlobalConeAffine.chowPullback_virtualClass`). -/
theorem virtualClass_eq_overFieldVirtualClass
    (hmatch : bundlePullback (bundleData φ) dimX dimE hshift
        (VirtualClass.virtualDimension φ) RX RE = chowPullback φ dimX dimE dimC hdim RX RE RC)
    (hmem : (globalConeData φ).coneClassAt dimE (VirtualClass.coneDegree φ) RE ∈
      LinearMap.range (bundlePullback (bundleData φ) dimX dimE hshift
        (VirtualClass.virtualDimension φ) RX RE)) :
    virtualClass (globalConeData φ) dimX dimE hshift (VirtualClass.virtualDimension φ)
        RX RE hmem =
      OverField.virtualClass φ dimX dimC RX RC :=
  virtualClass_eq_of_pullback_eq (globalConeData φ) dimX dimE hshift
    (VirtualClass.virtualDimension φ) RX RE _ hmatch
    (chowPullback_injective φ dimX dimE dimC hdim RX RE RC) hmem _
    (chowPullback_virtualClass φ dimX dimE dimC hdim RX RE RC)

end AffineConsistency

end

end VirtualClass.GlobalVirtualClass

end GromovWitten.AlgebraicGeometry
