/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.CycleGluing
import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

/-!
# Flat pullback of cycles along the total space of a global vector bundle

Let `𝓔 : BundleData X ι` be a vector bundle over a scheme `X` in the sense of
`GromovWitten/AlgebraicGeometry/VectorBundleTotalSpace.lean`: a quasi-coherent algebra with an
augmentation and trivialisations `triv j` over affine opens `chart j` covering `X`.  This file
constructs the flat pullback of rational algebraic cycles

`BundlePullbackGlobal.pullbackBundle 𝓔 : AlgebraicCycle X ℚ → AlgebraicCycle 𝓔.totalSpace ℚ`

and proves that it agrees over every chart with the affine flat pullback
`AlgebraicCycle.pullbackBundle` of `IntersectionTheory/ChernClasses.lean`.

## The generic point of a fibre, and its independence of the chart

The pullback is supported on the generic points of the fibres, so the whole construction rests on
the fact that the point `BundleData.chartBundlePoint j x` of the total space attached to a point
`x` of a chart does not depend on the chart.  This is proved here without any localisation
theory, from a purely order-theoretic affine lemma:
`VectorBundle.bundlePoint_specializes_iff` says that for a trivialised affine bundle
`e : A ≃ₐ[R] MvPolynomial ι R` the generic point `p · A` of the fibre over `p` specialises exactly
to the points of `π⁻¹(closure p)`, which is the adjunction `Ideal.map_le_iff_le_comap` read
through `PrimeSpectrum.le_iff_specializes`.  Transporting it along the cartesian square
`BundleData.isPullback_chart` gives `chartBundlePoint_specializes_iff`: for every point `q` of the
total space lying over the chart, `chartBundlePoint j x ⤳ q` iff `x ⤳ π(q)`.  Testing two chart
points against each other makes them inseparable, and the underlying space of a scheme is `T0`, so
they are equal (`chartBundlePoint_congr`).  Hence `bundlePoint 𝓔 : X → 𝓔.totalSpace` is
well defined, lies over the given point (`proj_bundlePoint`), is injective
(`bundlePoint_injective`) and is computed in every chart (`bundlePoint_chart`,
`bundlePoint_proj_chartι`).

## The pullback

`pullbackBundle 𝓔 c` puts the coefficient `c x` at `bundlePoint 𝓔 x` and zero elsewhere; local
finiteness holds because the projection is injective on its support with image inside the support
of `c`.  It is additive (`pullbackBundle_add`), rational linear (`pullbackBundleLinear`) and
injective (`pullbackBundle_injective`), and `pullbackOpen_chartι_pullbackBundle` identifies its
restriction to the chart `Spec (MvPolynomial ι Γ(X, U))` with the affine pullback of the
restriction of `c` to `Spec Γ(X, U)`.  Together with `ext_of_chartι` (a cycle on the total space
is determined by its restrictions to the charts) this characterises it
(`pullbackBundle_unique`).

## The graded pullback

`dimension_bundlePoint_chart` proves the dimension shift `dim_E (bundlePoint 𝓔 x) = dim_X x + r`
over a chart, from `VectorBundle.dimension_bundlePoint` and the two compatibility hypotheses of
the chart dimension functions with the global ones (the analogue of the hypothesis `hdim` of
`cyclesOfDimension.flatPullbackOpen`; a `DimensionFunction` is not automatically compatible with
open immersions).  `flatPullbackBundleGlobal` then takes the global shift as an explicit
hypothesis `hshift` and produces
`cyclesOfDimension X dimX i →ₗ[ℚ] cyclesOfDimension 𝓔.totalSpace dimE (i + Nat.card ι)`,
proved injective.

## What is not here

No descent to Chow groups: as in the affine case, whether the flat pullback respects rational
equivalence is not proved.  The compatibility of the affine bundle pullback with a localisation
of the base is not proved either; it is not needed for the chart independence above, which is why
it is absent.  The identification `pullbackBundle 𝓔 X.fundamentalCycle =
𝓔.totalSpace.fundamentalCycle` is also not proved.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

namespace VectorBundle

/-! ## Specialisations of the generic point of a fibre (affine case) -/

section Affine

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)

/-- The extended prime `p · A` is contained in a prime `q` of `A` exactly when `p` is contained
in the contraction of `q`.  This is the adjunction `Ideal.map_le_iff_le_comap`. -/
theorem bundlePrime_le_iff (y : PrimeSpectrum R) (q : PrimeSpectrum A) :
    bundlePrime e y ≤ q ↔ y ≤ PrimeSpectrum.comap (algebraMap R A) q :=
  Ideal.map_le_iff_le_comap

/-- The key affine lemma: the generic point of the fibre over `y` specialises exactly to the
points of the preimage of the closure of `y`.  This characterises `bundlePoint e y` inside
`Spec A` without reference to the trivialisation, and is what makes the global generic fibre
point independent of the chosen chart. -/
theorem bundlePoint_specializes_iff (y : ↥(Spec (CommRingCat.of R)))
    (q : ↥(Spec (CommRingCat.of A))) :
    bundlePoint e y ⤳ q ↔ y ⤳ (GradedCone.projection R A).base q :=
  ((PrimeSpectrum.le_iff_specializes (bundlePrime e y) q).symm.trans
    (bundlePrime_le_iff e y q)).trans
      (PrimeSpectrum.le_iff_specializes y (PrimeSpectrum.comap (algebraMap R A) q))

end Affine

end VectorBundle

namespace BundlePullbackGlobal

/-! ## The generic point of a fibre of a global vector bundle -/

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-- The base map of the chart immersion followed by the projection, computed through the
cartesian square `BundleData.isPullback_chart`. -/
theorem proj_chartι_base (j : 𝓔.J)
    (q : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))))) :
    𝓔.proj.base ((𝓔.chartι j).base q) =
      (𝓔.chart j).1.ι.base ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q)) := by
  have h : 𝓔.proj.base ((𝓔.chartι j).base q) = (𝓔.chartι j ≫ 𝓔.proj).base q := rfl
  rw [h, ← (𝓔.isPullback_chart j).w]
  rfl

/-- Specialisation from the generic point of the fibre over a point of a chart, tested against a
point of the same chart of the total space: it holds exactly when the base points specialise.
This is the global form of `VectorBundle.bundlePoint_specializes_iff`. -/
theorem chartBundlePoint_specializes_chartι_iff (j : 𝓔.J) (x : (𝓔.chart j).1.toScheme)
    (q : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))))) :
    𝓔.chartBundlePoint j x ⤳ (𝓔.chartι j).base q ↔
      (𝓔.chart j).1.ι.base x ⤳ 𝓔.proj.base ((𝓔.chartι j).base q) := by
  rw [proj_chartι_base, BundleData.chartBundlePoint,
    (𝓔.chartι j).isOpenEmbedding.isInducing.specializes_iff,
    VectorBundle.bundlePoint_specializes_iff,
    (𝓔.chart j).1.ι.isOpenEmbedding.isInducing.specializes_iff,
    ← ((isAffineOpen X (𝓔.chart j)).isoSpec.hom.isOpenEmbedding.isInducing.specializes_iff
      (x := x)
      (y := (isAffineOpen X (𝓔.chart j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q)))]
  have hinv : (isAffineOpen X (𝓔.chart j)).isoSpec.hom.base
      ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q)) =
      (GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q := by
    change ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫
      (isAffineOpen X (𝓔.chart j)).isoSpec.hom).base _ = _
    rw [Iso.inv_hom_id]
    rfl
  rw [hinv]
  rfl

/-- Specialisation from the generic point of the fibre over a point of a chart, tested against an
arbitrary point of the total space lying over that chart. -/
theorem chartBundlePoint_specializes_iff (j : 𝓔.J) (x : (𝓔.chart j).1.toScheme)
    (q : 𝓔.totalSpace) (hq : 𝓔.proj.base q ∈ (𝓔.chart j).1) :
    𝓔.chartBundlePoint j x ⤳ q ↔ (𝓔.chart j).1.ι.base x ⤳ 𝓔.proj.base q := by
  have hmem : q ∈ (𝓔.chartι j).opensRange := by
    rw [BundleData.opensRange_chartι]
    exact hq
  obtain ⟨q₀, rfl⟩ := hmem
  exact chartBundlePoint_specializes_chartι_iff 𝓔 j x q₀

/-- **Independence of the chart.**  The generic point of the fibre over a point of the base does
not depend on the chart used to compute it: two such points specialise to one another by
`chartBundlePoint_specializes_iff`, and the underlying space of a scheme is `T0`. -/
theorem chartBundlePoint_congr (j j' : 𝓔.J) (x : (𝓔.chart j).1.toScheme)
    (x' : (𝓔.chart j').1.toScheme)
    (hx : (𝓔.chart j).1.ι.base x = (𝓔.chart j').1.ι.base x') :
    𝓔.chartBundlePoint j x = 𝓔.chartBundlePoint j' x' := by
  have ha : 𝓔.proj.base (𝓔.chartBundlePoint j x) = (𝓔.chart j).1.ι.base x :=
    𝓔.proj_chartBundlePoint j x
  have hb : 𝓔.proj.base (𝓔.chartBundlePoint j' x') = (𝓔.chart j').1.ι.base x' :=
    𝓔.proj_chartBundlePoint j' x'
  have hmem : 𝓔.proj.base (𝓔.chartBundlePoint j' x') ∈ (𝓔.chart j).1 := by
    rw [hb, ← hx]
    exact x.2
  have hmem' : 𝓔.proj.base (𝓔.chartBundlePoint j x) ∈ (𝓔.chart j').1 := by
    rw [ha, hx]
    exact x'.2
  have h₁ : 𝓔.chartBundlePoint j x ⤳ 𝓔.chartBundlePoint j' x' := by
    rw [chartBundlePoint_specializes_iff 𝓔 j x _ hmem, hb, ← hx]
  have h₂ : 𝓔.chartBundlePoint j' x' ⤳ 𝓔.chartBundlePoint j x := by
    rw [chartBundlePoint_specializes_iff 𝓔 j' x' _ hmem', ha, hx]
  exact (h₁.antisymm h₂).eq

/-- A chart containing a given point of the base. -/
noncomputable def chartIndex (x : X) : 𝓔.J :=
  (CycleGluing.exists_mem_of_iSup_eq_top 𝓔.iSup_chart x).choose

/-- The chart chosen by `chartIndex` does contain the point. -/
theorem mem_chart_chartIndex (x : X) : x ∈ (𝓔.chart (chartIndex 𝓔 x)).1 :=
  (CycleGluing.exists_mem_of_iSup_eq_top 𝓔.iSup_chart x).choose_spec

/-- The generic point of the fibre of the bundle over a point of the base, computed in any chart
containing the point (`chartBundlePoint_congr` shows the choice is immaterial). -/
noncomputable def bundlePoint (x : X) : 𝓔.totalSpace :=
  𝓔.chartBundlePoint (chartIndex 𝓔 x) ⟨x, mem_chart_chartIndex 𝓔 x⟩

/-- The generic fibre point is computed by any chart containing the base point. -/
theorem bundlePoint_chart (j : 𝓔.J) (x : (𝓔.chart j).1.toScheme) :
    bundlePoint 𝓔 ((𝓔.chart j).1.ι.base x) = 𝓔.chartBundlePoint j x :=
  chartBundlePoint_congr 𝓔 _ j _ x rfl

/-- The generic point of the fibre over `x` lies over `x`. -/
@[simp]
theorem proj_bundlePoint (x : X) : 𝓔.proj.base (bundlePoint 𝓔 x) = x :=
  𝓔.proj_chartBundlePoint _ _

/-- Distinct points of the base have distinct generic fibre points. -/
theorem bundlePoint_injective : Function.Injective (bundlePoint 𝓔) := fun a b h => by
  have h' := congrArg 𝓔.proj.base h
  rwa [proj_bundlePoint, proj_bundlePoint] at h'

/-- Over a chart, the global generic fibre point is the affine generic fibre point of the
trivialised affine space `𝔸^ι_U`. -/
theorem bundlePoint_proj_chartι (j : 𝓔.J)
    (q : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))))) :
    bundlePoint 𝓔 (𝓔.proj.base ((𝓔.chartι j).base q)) =
      (𝓔.chartι j).base (VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        ((GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q)) := by
  have hinv : (isAffineOpen X (𝓔.chart j)).isoSpec.hom.base
      ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q)) =
      (GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q := by
    change ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫
      (isAffineOpen X (𝓔.chart j)).isoSpec.hom).base _ = _
    rw [Iso.inv_hom_id]
    rfl
  rw [proj_chartι_base, bundlePoint_chart, BundleData.chartBundlePoint,
    BundleData.chartBasePoint, hinv]

/-! ## Flat pullback of cycles along the total space -/

open scoped Classical in
/-- The coefficient function of the flat pullback of a cycle along the total space of a global
vector bundle: the coefficient of `c` at `x` sits at the generic point of the fibre over `x`, and
all other coefficients vanish. -/
noncomputable def pullbackBundleFun (c : AlgebraicCycle X ℚ) : 𝓔.totalSpace → ℚ :=
  fun q => if q = bundlePoint 𝓔 (𝓔.proj.base q) then c (𝓔.proj.base q) else 0

@[simp]
theorem pullbackBundleFun_apply_bundlePoint (c : AlgebraicCycle X ℚ) (x : X) :
    pullbackBundleFun 𝓔 c (bundlePoint 𝓔 x) = c x := by
  have h : 𝓔.proj.base (bundlePoint 𝓔 x) = x := proj_bundlePoint 𝓔 x
  simp only [pullbackBundleFun, h, if_pos]

theorem pullbackBundleFun_eq_zero_of_notMem (c : AlgebraicCycle X ℚ) {q : 𝓔.totalSpace}
    (hq : q ∉ Set.range (bundlePoint 𝓔)) : pullbackBundleFun 𝓔 c q = 0 := by
  rw [pullbackBundleFun]
  exact if_neg fun h => hq ⟨𝓔.proj.base q, h.symm⟩

theorem support_pullbackBundleFun_subset (c : AlgebraicCycle X ℚ) :
    Function.support (pullbackBundleFun 𝓔 c) ⊆ Set.range (bundlePoint 𝓔) := by
  intro q hq
  by_contra hmem
  exact hq (pullbackBundleFun_eq_zero_of_notMem 𝓔 c hmem)

/-- Flat pullback of a rational algebraic cycle along the total space of a global vector bundle.
Local finiteness holds because the projection is injective on the support of the pullback, with
image inside the support of the original cycle. -/
noncomputable def pullbackBundle (c : AlgebraicCycle X ℚ) :
    AlgebraicCycle 𝓔.totalSpace ℚ where
  toFun := pullbackBundleFun 𝓔 c
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' q _ := by
    obtain ⟨t, ht, hfinite⟩ := c.supportLocallyFiniteWithinDomain (𝓔.proj.base q) (by trivial)
    refine ⟨𝓔.proj.base ⁻¹' t, 𝓔.proj.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    have hsub : 𝓔.proj.base '' (𝓔.proj.base ⁻¹' t ∩ Function.support (pullbackBundleFun 𝓔 c)) ⊆
        t ∩ Function.support (c : X → ℚ) := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨w, rfl⟩ := support_pullbackBundleFun_subset 𝓔 c hz.2
      have hval := hz.2
      rw [Function.mem_support, pullbackBundleFun_apply_bundlePoint] at hval
      have h1 : 𝓔.proj.base (bundlePoint 𝓔 w) = w := proj_bundlePoint 𝓔 w
      have ht' : w ∈ t := by
        rw [← h1]
        exact hz.1
      rw [h1]
      exact ⟨ht', hval⟩
    have hinj : Set.InjOn 𝓔.proj.base
        (𝓔.proj.base ⁻¹' t ∩ Function.support (pullbackBundleFun 𝓔 c)) := by
      rintro a ha b hb hab
      obtain ⟨a', rfl⟩ := support_pullbackBundleFun_subset 𝓔 c ha.2
      obtain ⟨b', rfl⟩ := support_pullbackBundleFun_subset 𝓔 c hb.2
      rw [proj_bundlePoint, proj_bundlePoint] at hab
      rw [hab]
    exact Set.Finite.of_finite_image (hfinite.subset hsub) hinj

@[simp]
theorem pullbackBundle_apply (c : AlgebraicCycle X ℚ) (q : 𝓔.totalSpace) :
    pullbackBundle 𝓔 c q = pullbackBundleFun 𝓔 c q :=
  rfl

/-- The pullback of a cycle has the original coefficient at the generic point of the fibre. -/
theorem pullbackBundle_apply_bundlePoint (c : AlgebraicCycle X ℚ) (x : X) :
    pullbackBundle 𝓔 c (bundlePoint 𝓔 x) = c x :=
  pullbackBundleFun_apply_bundlePoint 𝓔 c x

/-- The pullback of a cycle vanishes away from the generic points of the fibres. -/
theorem pullbackBundle_eq_zero_of_notMem (c : AlgebraicCycle X ℚ) {q : 𝓔.totalSpace}
    (hq : q ∉ Set.range (bundlePoint 𝓔)) : pullbackBundle 𝓔 c q = 0 :=
  pullbackBundleFun_eq_zero_of_notMem 𝓔 c hq

/-- Flat pullback along the total space of a global vector bundle is additive. -/
theorem pullbackBundle_add (c d : AlgebraicCycle X ℚ) :
    pullbackBundle 𝓔 (c + d) = pullbackBundle 𝓔 c + pullbackBundle 𝓔 d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  by_cases h : q ∈ Set.range (bundlePoint 𝓔)
  · obtain ⟨x, rfl⟩ := h
    simp
  · have h0 : ∀ z : AlgebraicCycle X ℚ, pullbackBundleFun 𝓔 z q = 0 := fun z =>
      pullbackBundleFun_eq_zero_of_notMem 𝓔 z h
    simp [h0]

/-- Flat pullback along the total space of a global vector bundle commutes with rational
scalars. -/
theorem pullbackBundle_smul (a : ℚ) (c : AlgebraicCycle X ℚ) :
    pullbackBundle 𝓔 (a • c) = a • pullbackBundle 𝓔 c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  by_cases h : q ∈ Set.range (bundlePoint 𝓔)
  · obtain ⟨x, rfl⟩ := h
    simp
  · have h0 : ∀ z : AlgebraicCycle X ℚ, pullbackBundleFun 𝓔 z q = 0 := fun z =>
      pullbackBundleFun_eq_zero_of_notMem 𝓔 z h
    simp [h0]

/-- Flat pullback along the total space of a global vector bundle, with its proved rational
linearity. -/
noncomputable def pullbackBundleLinear :
    AlgebraicCycle X ℚ →ₗ[ℚ] AlgebraicCycle 𝓔.totalSpace ℚ where
  toFun := pullbackBundle 𝓔
  map_add' := pullbackBundle_add 𝓔
  map_smul' := pullbackBundle_smul 𝓔

@[simp]
theorem pullbackBundleLinear_apply (c : AlgebraicCycle X ℚ) :
    pullbackBundleLinear 𝓔 c = pullbackBundle 𝓔 c :=
  rfl

/-- Flat pullback along the total space of a global vector bundle is injective. -/
theorem pullbackBundle_injective : Function.Injective (pullbackBundle 𝓔) := by
  intro c d h
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  have hx := congrArg (fun z : AlgebraicCycle 𝓔.totalSpace ℚ => z (bundlePoint 𝓔 x)) h
  simpa using hx

/-- The global flat pullback restricted to a chart of the total space is the affine flat pullback
of the restriction of the cycle to the corresponding chart of the base.  The chart of the base is
read through `IsAffineOpen.isoSpec`, so the cycle on `Spec Γ(X, U)` is
`AlgebraicCycle.pullbackOpen (isoSpec.inv ≫ U.ι) c`. -/
theorem pullbackOpen_chartι_pullbackBundle (j : 𝓔.J) (c : AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen (𝓔.chartι j) (pullbackBundle 𝓔 c) =
      AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        (AlgebraicCycle.pullbackOpen
          ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι) c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  dsimp only
  by_cases h : q ∈ Set.range (VectorBundle.bundlePoint
      (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))))
  · obtain ⟨y, rfl⟩ := h
    have hproj : (GradedCone.projection Γ(X, (𝓔.chart j).1)
        (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base
          (VectorBundle.bundlePoint
            (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) y) = y :=
      VectorBundle.projection_base_bundlePoint _ y
    have hpt := bundlePoint_proj_chartι 𝓔 j
      (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) y)
    have hbase := proj_chartι_base 𝓔 j
      (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) y)
    rw [hproj] at hpt hbase
    rw [AlgebraicCycle.pullbackOpen_apply, ← hpt, pullbackBundle_apply_bundlePoint, hbase,
      AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    rfl
  · have hnot : (𝓔.chartι j).base q ∉ Set.range (bundlePoint 𝓔) := by
      rintro ⟨z, hz⟩
      refine h ⟨(GradedCone.projection Γ(X, (𝓔.chart j).1)
        (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q, ?_⟩
      have hz' : 𝓔.proj.base ((𝓔.chartι j).base q) = z := by
        rw [← hz, proj_bundlePoint]
      have hq : (𝓔.chartι j).base q =
          (𝓔.chartι j).base (VectorBundle.bundlePoint
            (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
            ((GradedCone.projection Γ(X, (𝓔.chart j).1)
              (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base q)) := by
        rw [← bundlePoint_proj_chartι, hz', ← hz]
      exact ((𝓔.chartι j).isOpenEmbedding.injective hq).symm
    have hR : AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        (AlgebraicCycle.pullbackOpen
          ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι) c) q = 0 :=
      AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ _ h
    have hLz : AlgebraicCycle.pullbackOpen (𝓔.chartι j) (pullbackBundle 𝓔 c) q = 0 :=
      pullbackBundle_eq_zero_of_notMem 𝓔 c hnot
    rw [hLz, hR]

/-- A cycle on the total space is determined by its restrictions to the trivialising charts. -/
theorem ext_of_chartι (c d : AlgebraicCycle 𝓔.totalSpace ℚ)
    (h : ∀ j, AlgebraicCycle.pullbackOpen (𝓔.chartι j) c =
      AlgebraicCycle.pullbackOpen (𝓔.chartι j) d) : c = d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  have hq : q ∈ (⨆ j, (𝓔.chartι j).opensRange : 𝓔.totalSpace.Opens) := by
    rw [BundleData.iSup_opensRange_chartι]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hq
  obtain ⟨q₀, rfl⟩ := hj
  exact congrArg (fun z : AlgebraicCycle
    (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))) ℚ => z q₀) (h j)

/-- The global flat pullback is the unique cycle on the total space whose restriction to every
trivialising chart is the affine flat pullback of the restricted cycle. -/
theorem pullbackBundle_unique (c : AlgebraicCycle X ℚ) (d : AlgebraicCycle 𝓔.totalSpace ℚ)
    (hd : ∀ j, AlgebraicCycle.pullbackOpen (𝓔.chartι j) d =
      AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        (AlgebraicCycle.pullbackOpen
          ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι) c)) :
    d = pullbackBundle 𝓔 c :=
  ext_of_chartι 𝓔 d _ fun j => (hd j).trans (pullbackOpen_chartι_pullbackBundle 𝓔 j c).symm

/-! ## The dimension shift and the graded pullback -/

/-- The dimension shift of the global flat pullback over a chart.  The two hypotheses `hU` and
`hP` say that the certified dimension gradings of the chart of the base and of the chart of the
total space are the restrictions of the global ones (the analogue of the hypothesis `hdim` of
`cyclesOfDimension.flatPullbackOpen`); the shift itself is the proved polynomial Krull-dimension
formula `VectorBundle.dimension_bundlePoint`. -/
theorem dimension_bundlePoint_chart [Finite ι] (j : 𝓔.J)
    [IsNoetherianRing Γ(X, (𝓔.chart j).1)]
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (dimU : DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimP : DimensionFunction
      (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hU : ∀ y, dimU y =
      dimX (((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι).base y))
    (hP : ∀ q, dimP q = dimE ((𝓔.chartι j).base q))
    (x : (𝓔.chart j).1.toScheme) :
    dimE (bundlePoint 𝓔 ((𝓔.chart j).1.ι.base x)) =
      dimX ((𝓔.chart j).1.ι.base x) + (Nat.card ι : ℤ) := by
  have hx : (isAffineOpen X (𝓔.chart j)).isoSpec.inv.base
      ((isAffineOpen X (𝓔.chart j)).isoSpec.hom.base x) = x := by
    change ((isAffineOpen X (𝓔.chart j)).isoSpec.hom ≫
      (isAffineOpen X (𝓔.chart j)).isoSpec.inv).base _ = _
    rw [Iso.hom_inv_id]
    rfl
  rw [bundlePoint_chart, BundleData.chartBundlePoint, ← hP,
    VectorBundle.dimension_bundlePoint _ dimU dimP, hU, BundleData.chartBasePoint]
  change dimX ((𝓔.chart j).1.ι.base ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base
    ((isAffineOpen X (𝓔.chart j)).isoSpec.hom.base x))) + _ = _
  rw [hx]

/-- Flat pullback of dimension-graded rational cycles along the total space of a global vector
bundle.  The dimension shift is supplied as the hypothesis `hshift`, which
`dimension_bundlePoint_chart` establishes chart by chart. -/
noncomputable def flatPullbackBundleGlobal [Finite ι]
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ) :
    cyclesOfDimension X dimX i →ₗ[ℚ]
      cyclesOfDimension 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)) where
  toFun c := ⟨pullbackBundle 𝓔 c.1, by
    intro q hq
    by_contra hne
    have hsupp : q ∈ Function.support (pullbackBundleFun 𝓔 c.1) := hne
    obtain ⟨x, rfl⟩ := support_pullbackBundleFun_subset 𝓔 c.1 hsupp
    have hval : (c : AlgebraicCycle X ℚ) x ≠ 0 := by
      rw [← pullbackBundle_apply_bundlePoint 𝓔 c.1 x]
      exact hne
    have hdx : dimX x = i := by
      by_contra hcon
      exact hval (c.2 x hcon)
    exact hq (by rw [hshift x, hdx])⟩
  map_add' c d := Subtype.ext (pullbackBundle_add 𝓔 c.1 d.1)
  map_smul' a c := Subtype.ext (pullbackBundle_smul 𝓔 a c.1)

@[simp]
theorem flatPullbackBundleGlobal_apply [Finite ι]
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ)
    (c : cyclesOfDimension X dimX i) (q : 𝓔.totalSpace) :
    ((flatPullbackBundleGlobal 𝓔 dimX dimE hshift i c :
        cyclesOfDimension 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ))) :
          AlgebraicCycle 𝓔.totalSpace ℚ) q =
      pullbackBundle 𝓔 (c : AlgebraicCycle X ℚ) q :=
  rfl

/-- The graded global flat pullback is injective. -/
theorem flatPullbackBundleGlobal_injective [Finite ι]
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (hshift : ∀ x, dimE (bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ) :
    Function.Injective (flatPullbackBundleGlobal 𝓔 dimX dimE hshift i) := fun _ _ h =>
  Subtype.ext (pullbackBundle_injective 𝓔 (congrArg Subtype.val h))

end BundlePullbackGlobal

end GromovWitten.AlgebraicGeometry.IntersectionTheory
