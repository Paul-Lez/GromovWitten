/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobal

/-!
# Flat pullback of cycles along a morphism with affine charts

`BundlePullbackGlobal.lean` constructs the flat pullback of rational algebraic cycles along the
total space of a global vector bundle `𝓔 : BundleData X ι`, using only the following features of
its trivialising charts `chartι j : 𝔸^ι_{Γ(X,U_j)} ⟶ E`: they are open immersions over the
affine opens `U_j` covering `X`, every point of `E` over `U_j` lies in `chartι j`, and the affine
specialisation lemma `VectorBundle.bundlePoint_specializes_iff`. The projective completion
`P(E ⊕ 1)` of a graded vector bundle has charts of the same shape (the `D₊(x_i)`), but a chart no
longer contains the whole fibre over its base open: instead, any two charts over a common base
point simply *meet* somewhere in the fibre. This file introduces the structure `AffineCharts q ι`
recording exactly this weaker hypothesis, and redevelops `BundlePullbackGlobal.lean` for it.

## Chart independence of the generic fibre point

For `𝒞 : AffineCharts q ι`, `chartPoint 𝒞 j x` is the generic point of the fibre over a point `x`
of the chart `base j`, computed through the chart `chartι j` exactly as in the bundle case
(`chartPoint_specializes_chartι_iff`, `chartPoint_specializes_iff`, ported verbatim from
`BundlePullbackGlobal.lean`, using `𝒞.chartι_comp` in place of the cartesian square `.w`). What
replaces the bundle argument is `chartPoint_mem_range`: if the base point of `chartPoint 𝒞 j x`
also lies in another chart `base j'`, then `chartPoint 𝒞 j x` itself lies in the *range* of
`chartι j'` — not because `chartι j'` contains the whole fibre, but because `𝒞.meets` supplies a
point `p` lying in both chart ranges over that base point, `chartPoint 𝒞 j x` specialises to `p`
(trivially, since they lie over the same base point), and a specialisation of a point of an open
set lies in that open set (`Specializes.mem_open`). Testing the chart points attached to two
charts against each other this way, in both directions, makes them inseparable, and the
underlying space of a scheme is `T0`, so they are equal (`chartPoint_congr`). Hence
`fibrePoint 𝒞 : X → P` is well defined (`fibrePoint_chart`), lies over the given point
(`q_fibrePoint`), is injective (`fibrePoint_injective`), is computed in every chart
(`fibrePoint_chartι`), and lies in the range of every chart containing its base point
(`fibrePoint_mem_range`). It is genuinely *the* generic point of the fibre, chart-independently:
`fibrePoint_specializes_iff` shows `fibrePoint 𝒞 x ⤳ p ↔ x ⤳ q.base p` for every `p : P`.

## The pullback

`pullbackCharted 𝒞 c` puts the coefficient `c x` at `fibrePoint 𝒞 x` and zero elsewhere, exactly
as `BundlePullbackGlobal.pullbackBundle`; all the chart-free lemmas (additivity, scalar
linearity, injectivity) are ported verbatim, since they never use the chart data at all.
`pullbackOpen_chartι_pullbackCharted` identifies its restriction to a chart with the affine
pullback of the restriction of `c`, `ext_of_chartι` shows a cycle on `P` is determined by its
restrictions to the charts (using only `𝒞.exists_mem_range`), and together these give
`pullbackCharted_unique`. `isAffineOpen_range_chartι` records that the range of a chart is an
affine open of `P` (the image of an affine scheme under an open immersion).

## The graded pullback, and the bundle case

`dimension_fibrePoint_chart` and `flatPullbackCharted` port the dimension-graded pullback
verbatim. Finally `BundleData.affineCharts` (accessible as `𝓔.affineCharts`) exhibits the
bundle's own trivialising charts as an instance of `AffineCharts 𝓔.proj ι` (`meets` is immediate:
the generic fibre point computed in one chart lies in the other, since a bundle chart contains
its *whole* fibre over its base open, by `BundleData.opensRange_chartι`), and
`pullbackCharted_affineCharts`/`fibrePoint_affineCharts` identify the resulting construction with
`BundlePullbackGlobal.pullbackBundle`/`bundlePoint`.

## What is not here

No descent to Chow groups (`IntersectionTheory/ChartedPullbackChow.lean`), no restriction of the
charts to an open of the base or to a subscheme of `P`, no `AffineCharts.restrictOpen`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

open GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

/-- Affine charts on a morphism `q : P ⟶ X`: affine opens `base j` of `X` covering `X`, and open
immersions `chartι j : 𝔸^ι_{Γ(base j)} ⟶ P` over `base j`, covering `P`, any two of which meet
in every fibre over a common base point. -/
structure AffineCharts {P X : Scheme.{u}} (q : P ⟶ X) (ι : Type u) where
  /-- The index type of the charts. -/
  J : Type u
  /-- The affine open of the base underlying a chart. -/
  base : J → X.affineOpens
  /-- The charts cover the base. -/
  iSup_base : ⨆ j, (base j).1 = ⊤
  /-- The chart: an affine space over `Γ(X, base j)` mapping into `P`. -/
  chartι : ∀ j, Spec (CommRingCat.of (MvPolynomial ι Γ(X, (base j).1))) ⟶ P
  /-- The chart is an open immersion. -/
  [isOpenImmersion_chartι : ∀ j, IsOpenImmersion (chartι j)]
  /-- The chart lies over `base j`. -/
  chartι_comp : ∀ j, chartι j ≫ q =
    Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, (base j).1) (MvPolynomial ι Γ(X, (base j).1)))) ≫
      (isAffineOpen X (base j)).isoSpec.inv ≫ (base j).1.ι
  /-- The charts cover `P`. -/
  exists_mem_range : ∀ p : P, ∃ j, p ∈ Set.range (chartι j).base
  /-- Any two charts meet in every fibre over a point of both their base opens. -/
  meets : ∀ (j j' : J) (x : X), x ∈ (base j).1 → x ∈ (base j').1 →
    ∃ p : P, q.base p = x ∧ p ∈ Set.range (chartι j).base ∧ p ∈ Set.range (chartι j').base

attribute [instance] AffineCharts.isOpenImmersion_chartι

namespace AffineCharts

/-! ## The generic point of a fibre -/

variable {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} (𝒞 : AffineCharts q ι)

/-- A point of a chart of the base, read as a point of the spectrum of its section ring. -/
noncomputable def chartBasePoint (j : 𝒞.J) (x : (𝒞.base j).1.toScheme) :
    ↥(Spec (CommRingCat.of Γ(X, (𝒞.base j).1))) :=
  (isAffineOpen X (𝒞.base j)).isoSpec.hom.base x

/-- The generic point of the fibre of `q` over a point of a chart, pushed into `P` along the
chart. Independence of the chart is `chartPoint_congr`. -/
noncomputable def chartPoint (j : 𝒞.J) (x : (𝒞.base j).1.toScheme) : P :=
  (𝒞.chartι j).base (VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1))) (chartBasePoint 𝒞 j x))

/-- The base map of the chart immersion followed by `q`, computed through `chartι_comp`. -/
theorem q_chartι_base (j : 𝒞.J)
    (p : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1))))) :
    q.base ((𝒞.chartι j).base p) =
      (𝒞.base j).1.ι.base ((isAffineOpen X (𝒞.base j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p)) := by
  have h : q.base ((𝒞.chartι j).base p) = (𝒞.chartι j ≫ q).base p := rfl
  rw [h, 𝒞.chartι_comp j]
  rfl

/-- The generic point of a fibre, tested against a point of the same chart of `P`: it specialises
to that point exactly when the base points specialise. The global form of
`VectorBundle.bundlePoint_specializes_iff`. -/
theorem chartPoint_specializes_chartι_iff (j : 𝒞.J) (x : (𝒞.base j).1.toScheme)
    (p : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1))))) :
    chartPoint 𝒞 j x ⤳ (𝒞.chartι j).base p ↔
      (𝒞.base j).1.ι.base x ⤳ q.base ((𝒞.chartι j).base p) := by
  rw [q_chartι_base, chartPoint, (𝒞.chartι j).isOpenEmbedding.isInducing.specializes_iff,
    VectorBundle.bundlePoint_specializes_iff,
    (𝒞.base j).1.ι.isOpenEmbedding.isInducing.specializes_iff,
    ← ((isAffineOpen X (𝒞.base j)).isoSpec.hom.isOpenEmbedding.isInducing.specializes_iff
      (x := x)
      (y := (isAffineOpen X (𝒞.base j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p)))]
  have hinv : (isAffineOpen X (𝒞.base j)).isoSpec.hom.base
      ((isAffineOpen X (𝒞.base j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p)) =
      (GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p := by
    change ((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫
      (isAffineOpen X (𝒞.base j)).isoSpec.hom).base _ = _
    rw [Iso.inv_hom_id]
    rfl
  rw [hinv]
  rfl

/-- The generic point of a fibre, tested against an arbitrary point of `P` lying in the range of
the same chart. The hypothesis replaces the whole-fibre membership used in the bundle case. -/
theorem chartPoint_specializes_iff (j : 𝒞.J) (x : (𝒞.base j).1.toScheme) (p : P)
    (hp : p ∈ Set.range (𝒞.chartι j).base) :
    chartPoint 𝒞 j x ⤳ p ↔ (𝒞.base j).1.ι.base x ⤳ q.base p := by
  obtain ⟨p₀, rfl⟩ := hp
  exact chartPoint_specializes_chartι_iff 𝒞 j x p₀

/-- The chart point lies over the given base point. -/
theorem q_chartPoint (j : 𝒞.J) (x : (𝒞.base j).1.toScheme) :
    q.base (chartPoint 𝒞 j x) = (𝒞.base j).1.ι.base x := by
  change q.base ((𝒞.chartι j).base (VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1))) (chartBasePoint 𝒞 j x))) = _
  rw [q_chartι_base 𝒞 j, chartBasePoint, VectorBundle.projection_base_bundlePoint]
  change (𝒞.base j).1.ι.base (((isAffineOpen X (𝒞.base j)).isoSpec.hom ≫
    (isAffineOpen X (𝒞.base j)).isoSpec.inv).base x) = _
  rw [Iso.hom_inv_id]
  rfl

/-- **The key independence lemma.** If the base point of a chart point also lies in another
chart's base open, the chart point itself lies in the range of that other chart: pick, by
`𝒞.meets`, a point `p` lying over the common base point in both chart ranges; the chart point
specialises to `p` (since they lie over the same base point, by `chartPoint_specializes_iff`),
and a specialisation of a point of an open set lies in that open set. -/
theorem chartPoint_mem_range (j j' : 𝒞.J) (x : (𝒞.base j).1.toScheme)
    (hx : (𝒞.base j).1.ι.base x ∈ (𝒞.base j').1) :
    chartPoint 𝒞 j x ∈ Set.range (𝒞.chartι j').base := by
  obtain ⟨p, hp, hpj, hpj'⟩ := 𝒞.meets j j' ((𝒞.base j).1.ι.base x) x.2 hx
  have hspec : chartPoint 𝒞 j x ⤳ p := by
    rw [chartPoint_specializes_iff 𝒞 j x p hpj, hp]
  exact hspec.mem_open (𝒞.chartι j').isOpenEmbedding.isOpen_range hpj'

/-- **Independence of the chart.** The generic point of the fibre over a point of the base does
not depend on the chart used to compute it: two such points specialise to one another by
`chartPoint_mem_range` and `chartPoint_specializes_iff`, and the underlying space of a scheme is
`T0`. -/
theorem chartPoint_congr (j j' : 𝒞.J) (x : (𝒞.base j).1.toScheme)
    (x' : (𝒞.base j').1.toScheme)
    (hx : (𝒞.base j).1.ι.base x = (𝒞.base j').1.ι.base x') :
    chartPoint 𝒞 j x = chartPoint 𝒞 j' x' := by
  have ha : q.base (chartPoint 𝒞 j x) = (𝒞.base j).1.ι.base x := q_chartPoint 𝒞 j x
  have hb : q.base (chartPoint 𝒞 j' x') = (𝒞.base j').1.ι.base x' := q_chartPoint 𝒞 j' x'
  have hmemj' : (𝒞.base j).1.ι.base x ∈ (𝒞.base j').1 := by rw [hx]; exact x'.2
  have hmemj : (𝒞.base j').1.ι.base x' ∈ (𝒞.base j).1 := by rw [← hx]; exact x.2
  have hrange1 : chartPoint 𝒞 j x ∈ Set.range (𝒞.chartι j').base :=
    chartPoint_mem_range 𝒞 j j' x hmemj'
  have hrange2 : chartPoint 𝒞 j' x' ∈ Set.range (𝒞.chartι j).base :=
    chartPoint_mem_range 𝒞 j' j x' hmemj
  have h₁ : chartPoint 𝒞 j x ⤳ chartPoint 𝒞 j' x' := by
    rw [chartPoint_specializes_iff 𝒞 j x _ hrange2, hb, ← hx]
  have h₂ : chartPoint 𝒞 j' x' ⤳ chartPoint 𝒞 j x := by
    rw [chartPoint_specializes_iff 𝒞 j' x' _ hrange1, ha, hx]
  exact (h₁.antisymm h₂).eq

/-- A chart containing a given point of the base. -/
noncomputable def chartIndex (x : X) : 𝒞.J :=
  (CycleGluing.exists_mem_of_iSup_eq_top 𝒞.iSup_base x).choose

/-- The chart chosen by `chartIndex` does contain the point. -/
theorem mem_base_chartIndex (x : X) : x ∈ (𝒞.base (chartIndex 𝒞 x)).1 :=
  (CycleGluing.exists_mem_of_iSup_eq_top 𝒞.iSup_base x).choose_spec

/-- The generic point of the fibre of `q` over a point of the base, computed in any chart
containing the point (`chartPoint_congr` shows the choice is immaterial). -/
noncomputable def fibrePoint (x : X) : P :=
  chartPoint 𝒞 (chartIndex 𝒞 x) ⟨x, mem_base_chartIndex 𝒞 x⟩

/-- The generic fibre point is computed by any chart containing the base point. -/
theorem fibrePoint_chart (j : 𝒞.J) (x : (𝒞.base j).1.toScheme) :
    fibrePoint 𝒞 ((𝒞.base j).1.ι.base x) = chartPoint 𝒞 j x :=
  chartPoint_congr 𝒞 _ j _ x rfl

/-- The generic point of the fibre over `x` lies over `x`. -/
@[simp]
theorem q_fibrePoint (x : X) : q.base (fibrePoint 𝒞 x) = x :=
  q_chartPoint 𝒞 _ _

/-- Distinct points of the base have distinct generic fibre points. -/
theorem fibrePoint_injective : Function.Injective (fibrePoint 𝒞) := fun a b h => by
  have h' := congrArg q.base h
  rwa [q_fibrePoint, q_fibrePoint] at h'

/-- Over a chart, the global generic fibre point is the affine generic fibre point of the
trivialised affine space `𝔸^ι_{base j}`. -/
theorem fibrePoint_chartι (j : 𝒞.J)
    (p : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1))))) :
    fibrePoint 𝒞 (q.base ((𝒞.chartι j).base p)) =
      (𝒞.chartι j).base (VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
        ((GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p)) := by
  have hinv : (isAffineOpen X (𝒞.base j)).isoSpec.hom.base
      ((isAffineOpen X (𝒞.base j)).isoSpec.inv.base
        ((GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p)) =
      (GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p := by
    change ((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫
      (isAffineOpen X (𝒞.base j)).isoSpec.hom).base _ = _
    rw [Iso.inv_hom_id]
    rfl
  rw [q_chartι_base 𝒞 j p, fibrePoint_chart, chartPoint, chartBasePoint, hinv]

/-- The generic fibre point over a point of a chart's base open lies in that chart's range. -/
theorem fibrePoint_mem_range (j : 𝒞.J) (x : X) (hx : x ∈ (𝒞.base j).1) :
    fibrePoint 𝒞 x ∈ Set.range (𝒞.chartι j).base := by
  have hx' : (𝒞.base (chartIndex 𝒞 x)).1.ι.base ⟨x, mem_base_chartIndex 𝒞 x⟩ ∈ (𝒞.base j).1 := hx
  exact chartPoint_mem_range 𝒞 (chartIndex 𝒞 x) j ⟨x, mem_base_chartIndex 𝒞 x⟩ hx'

/-- A point of the `j`-th chart of `P` lies over the `j`-th base open. -/
theorem q_mem_base_of_mem_range (j : 𝒞.J) {p : P} (hp : p ∈ Set.range (𝒞.chartι j).base) :
    q.base p ∈ (𝒞.base j).1 := by
  obtain ⟨z, rfl⟩ := hp
  rw [q_chartι_base 𝒞 j]
  exact Subtype.property _

/-- The generic point of the fibre over `x` specialises to every point `p` of `P` with
`x ⤳ q.base p`. This is the chart-independent form of `chartPoint_specializes_iff`. -/
theorem fibrePoint_specializes {x : X} {p : P} (h : x ⤳ q.base p) : fibrePoint 𝒞 x ⤳ p := by
  obtain ⟨j, hj⟩ := 𝒞.exists_mem_range p
  have hx : x ∈ (𝒞.base j).1 := h.mem_open (𝒞.base j).1.isOpen (q_mem_base_of_mem_range 𝒞 j hj)
  have h1 : fibrePoint 𝒞 x = chartPoint 𝒞 j (⟨x, hx⟩ : (𝒞.base j).1.toScheme) :=
    fibrePoint_chart 𝒞 j ⟨x, hx⟩
  rw [h1]
  exact (chartPoint_specializes_iff 𝒞 j _ p hj).2 h

/-- **`fibrePoint` computes the generic point of the fibre, chart-independently.** The generic
point of the fibre over `x` specialises to a point `p` of `P` exactly when `x` specialises to
`q.base p`. The forward direction is `Specializes.map` along `q.base` followed by
`q_fibrePoint`; the converse is `fibrePoint_specializes`. -/
theorem fibrePoint_specializes_iff {x : X} {p : P} :
    fibrePoint 𝒞 x ⤳ p ↔ x ⤳ q.base p := by
  refine ⟨fun h => ?_, fibrePoint_specializes 𝒞⟩
  have h' := h.map q.continuous
  rwa [q_fibrePoint] at h'

/-! ## Flat pullback of cycles along `P` -/

open scoped Classical in
/-- The coefficient function of the flat pullback of a cycle along `P`: the coefficient of `c`
at `x` sits at the generic point of the fibre over `x`, and all other coefficients vanish. -/
noncomputable def pullbackChartedFun (c : AlgebraicCycle X ℚ) : P → ℚ :=
  fun p => if p = fibrePoint 𝒞 (q.base p) then c (q.base p) else 0

@[simp]
theorem pullbackChartedFun_apply_fibrePoint (c : AlgebraicCycle X ℚ) (x : X) :
    pullbackChartedFun 𝒞 c (fibrePoint 𝒞 x) = c x := by
  have h : q.base (fibrePoint 𝒞 x) = x := q_fibrePoint 𝒞 x
  simp only [pullbackChartedFun, h, if_pos]

theorem pullbackChartedFun_eq_zero_of_notMem (c : AlgebraicCycle X ℚ) {p : P}
    (hp : p ∉ Set.range (fibrePoint 𝒞)) : pullbackChartedFun 𝒞 c p = 0 := by
  rw [pullbackChartedFun]
  exact if_neg fun h => hp ⟨q.base p, h.symm⟩

theorem support_pullbackChartedFun_subset (c : AlgebraicCycle X ℚ) :
    Function.support (pullbackChartedFun 𝒞 c) ⊆ Set.range (fibrePoint 𝒞) := by
  intro p hp
  by_contra hmem
  exact hp (pullbackChartedFun_eq_zero_of_notMem 𝒞 c hmem)

/-- Flat pullback of a rational algebraic cycle along a morphism with affine charts. Local
finiteness holds because `q` is injective on the support of the pullback, with image inside the
support of the original cycle. -/
noncomputable def pullbackCharted (c : AlgebraicCycle X ℚ) : AlgebraicCycle P ℚ where
  toFun := pullbackChartedFun 𝒞 c
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' p _ := by
    obtain ⟨t, ht, hfinite⟩ := c.supportLocallyFiniteWithinDomain (q.base p) (by trivial)
    refine ⟨q.base ⁻¹' t, q.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
    have hsub : q.base '' (q.base ⁻¹' t ∩ Function.support (pullbackChartedFun 𝒞 c)) ⊆
        t ∩ Function.support (c : X → ℚ) := by
      rintro y ⟨z, hz, rfl⟩
      obtain ⟨w, rfl⟩ := support_pullbackChartedFun_subset 𝒞 c hz.2
      have hval := hz.2
      rw [Function.mem_support, pullbackChartedFun_apply_fibrePoint] at hval
      have h1 : q.base (fibrePoint 𝒞 w) = w := q_fibrePoint 𝒞 w
      have ht' : w ∈ t := by
        rw [← h1]
        exact hz.1
      rw [h1]
      exact ⟨ht', hval⟩
    have hinj : Set.InjOn q.base
        (q.base ⁻¹' t ∩ Function.support (pullbackChartedFun 𝒞 c)) := by
      rintro a ha b hb hab
      obtain ⟨a', rfl⟩ := support_pullbackChartedFun_subset 𝒞 c ha.2
      obtain ⟨b', rfl⟩ := support_pullbackChartedFun_subset 𝒞 c hb.2
      rw [q_fibrePoint, q_fibrePoint] at hab
      rw [hab]
    exact Set.Finite.of_finite_image (hfinite.subset hsub) hinj

@[simp]
theorem pullbackCharted_apply (c : AlgebraicCycle X ℚ) (p : P) :
    pullbackCharted 𝒞 c p = pullbackChartedFun 𝒞 c p :=
  rfl

/-- The pullback of a cycle has the original coefficient at the generic point of the fibre. -/
theorem pullbackCharted_apply_fibrePoint (c : AlgebraicCycle X ℚ) (x : X) :
    pullbackCharted 𝒞 c (fibrePoint 𝒞 x) = c x :=
  pullbackChartedFun_apply_fibrePoint 𝒞 c x

/-- The pullback of a cycle vanishes away from the generic points of the fibres. -/
theorem pullbackCharted_eq_zero_of_notMem (c : AlgebraicCycle X ℚ) {p : P}
    (hp : p ∉ Set.range (fibrePoint 𝒞)) : pullbackCharted 𝒞 c p = 0 :=
  pullbackChartedFun_eq_zero_of_notMem 𝒞 c hp

/-- Flat pullback along a morphism with affine charts is additive. -/
theorem pullbackCharted_add (c d : AlgebraicCycle X ℚ) :
    pullbackCharted 𝒞 (c + d) = pullbackCharted 𝒞 c + pullbackCharted 𝒞 d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  by_cases h : p ∈ Set.range (fibrePoint 𝒞)
  · obtain ⟨x, rfl⟩ := h
    simp
  · have h0 : ∀ z : AlgebraicCycle X ℚ, pullbackChartedFun 𝒞 z p = 0 := fun z =>
      pullbackChartedFun_eq_zero_of_notMem 𝒞 z h
    simp [h0]

/-- Flat pullback along a morphism with affine charts commutes with rational scalars. -/
theorem pullbackCharted_smul (a : ℚ) (c : AlgebraicCycle X ℚ) :
    pullbackCharted 𝒞 (a • c) = a • pullbackCharted 𝒞 c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  by_cases h : p ∈ Set.range (fibrePoint 𝒞)
  · obtain ⟨x, rfl⟩ := h
    simp
  · have h0 : ∀ z : AlgebraicCycle X ℚ, pullbackChartedFun 𝒞 z p = 0 := fun z =>
      pullbackChartedFun_eq_zero_of_notMem 𝒞 z h
    simp [h0]

/-- Flat pullback along a morphism with affine charts, with its proved rational linearity. -/
noncomputable def pullbackChartedLinear : AlgebraicCycle X ℚ →ₗ[ℚ] AlgebraicCycle P ℚ where
  toFun := pullbackCharted 𝒞
  map_add' := pullbackCharted_add 𝒞
  map_smul' := pullbackCharted_smul 𝒞

@[simp]
theorem pullbackChartedLinear_apply (c : AlgebraicCycle X ℚ) :
    pullbackChartedLinear 𝒞 c = pullbackCharted 𝒞 c :=
  rfl

/-- Flat pullback along a morphism with affine charts is injective. -/
theorem pullbackCharted_injective : Function.Injective (pullbackCharted 𝒞) := by
  intro c d h
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  have hx := congrArg (fun z : AlgebraicCycle P ℚ => z (fibrePoint 𝒞 x)) h
  simpa using hx

/-- The global flat pullback restricted to a chart of `P` is the affine flat pullback of the
restriction of the cycle to the corresponding chart of `X`. -/
theorem pullbackOpen_chartι_pullbackCharted (j : 𝒞.J) (c : AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen (𝒞.chartι j) (pullbackCharted 𝒞 c) =
      AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
        (AlgebraicCycle.pullbackOpen
          ((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫ (𝒞.base j).1.ι) c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  dsimp only
  by_cases h : p ∈ Set.range (VectorBundle.bundlePoint
      (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1))))
  · obtain ⟨y, rfl⟩ := h
    have hproj : (GradedCone.projection Γ(X, (𝒞.base j).1)
        (MvPolynomial ι Γ(X, (𝒞.base j).1))).base
          (VectorBundle.bundlePoint
            (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1))) y) = y :=
      VectorBundle.projection_base_bundlePoint _ y
    have hpt := fibrePoint_chartι 𝒞 j
      (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1))) y)
    have hbase := q_chartι_base 𝒞 j
      (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1))) y)
    rw [hproj] at hpt hbase
    rw [AlgebraicCycle.pullbackOpen_apply, ← hpt, pullbackCharted_apply_fibrePoint, hbase,
      AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    rfl
  · have hnot : (𝒞.chartι j).base p ∉ Set.range (fibrePoint 𝒞) := by
      rintro ⟨z, hz⟩
      refine h ⟨(GradedCone.projection Γ(X, (𝒞.base j).1)
        (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p, ?_⟩
      have hz' : q.base ((𝒞.chartι j).base p) = z := by
        rw [← hz, q_fibrePoint]
      have hq : (𝒞.chartι j).base p =
          (𝒞.chartι j).base (VectorBundle.bundlePoint
            (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
            ((GradedCone.projection Γ(X, (𝒞.base j).1)
              (MvPolynomial ι Γ(X, (𝒞.base j).1))).base p)) := by
        rw [← fibrePoint_chartι, hz', ← hz]
      exact ((𝒞.chartι j).isOpenEmbedding.injective hq).symm
    have hR : AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
        (AlgebraicCycle.pullbackOpen
          ((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫ (𝒞.base j).1.ι) c) p = 0 :=
      AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ _ h
    have hLz : AlgebraicCycle.pullbackOpen (𝒞.chartι j) (pullbackCharted 𝒞 c) p = 0 :=
      pullbackCharted_eq_zero_of_notMem 𝒞 c hnot
    rw [hLz, hR]

/-- A cycle on `P` is determined by its restrictions to the charts. Uses only
`𝒞.exists_mem_range`. -/
theorem ext_of_chartι (c d : AlgebraicCycle P ℚ)
    (h : ∀ j, AlgebraicCycle.pullbackOpen (𝒞.chartι j) c =
      AlgebraicCycle.pullbackOpen (𝒞.chartι j) d) : c = d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  obtain ⟨j, p₀, hp₀⟩ := 𝒞.exists_mem_range p
  subst hp₀
  exact congrArg (fun z : AlgebraicCycle
    (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1)))) ℚ => z p₀) (h j)

/-- The global flat pullback is the unique cycle on `P` whose restriction to every chart is the
affine flat pullback of the restricted cycle. -/
theorem pullbackCharted_unique (c : AlgebraicCycle X ℚ) (d : AlgebraicCycle P ℚ)
    (hd : ∀ j, AlgebraicCycle.pullbackOpen (𝒞.chartι j) d =
      AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
        (AlgebraicCycle.pullbackOpen
          ((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫ (𝒞.base j).1.ι) c)) :
    d = pullbackCharted 𝒞 c :=
  ext_of_chartι 𝒞 d _ fun j => (hd j).trans (pullbackOpen_chartι_pullbackCharted 𝒞 j c).symm

/-- The range of a chart is an affine open of `P`: the image of an affine scheme under an open
immersion. -/
theorem isAffineOpen_range_chartι (j : 𝒞.J) : IsAffineOpen (𝒞.chartι j).opensRange :=
  isAffineOpen_opensRange (𝒞.chartι j)

/-! ## The dimension shift and the graded pullback -/

/-- The dimension shift of the global flat pullback over a chart. -/
theorem dimension_fibrePoint_chart [Finite ι] (j : 𝒞.J)
    [IsNoetherianRing Γ(X, (𝒞.base j).1)]
    (dimX : DimensionFunction X) (dimP : DimensionFunction P)
    (dimU : DimensionFunction (Spec (CommRingCat.of Γ(X, (𝒞.base j).1))))
    (dimW : DimensionFunction
      (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1)))))
    (hU : ∀ y, dimU y =
      dimX (((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫ (𝒞.base j).1.ι).base y))
    (hW : ∀ p, dimW p = dimP ((𝒞.chartι j).base p))
    (x : (𝒞.base j).1.toScheme) :
    dimP (fibrePoint 𝒞 ((𝒞.base j).1.ι.base x)) =
      dimX ((𝒞.base j).1.ι.base x) + (Nat.card ι : ℤ) := by
  have hx : (isAffineOpen X (𝒞.base j)).isoSpec.inv.base
      ((isAffineOpen X (𝒞.base j)).isoSpec.hom.base x) = x := by
    change ((isAffineOpen X (𝒞.base j)).isoSpec.hom ≫
      (isAffineOpen X (𝒞.base j)).isoSpec.inv).base _ = _
    rw [Iso.hom_inv_id]
    rfl
  rw [fibrePoint_chart, chartPoint, ← hW,
    VectorBundle.dimension_bundlePoint _ dimU dimW, hU, chartBasePoint]
  change dimX ((𝒞.base j).1.ι.base ((isAffineOpen X (𝒞.base j)).isoSpec.inv.base
    ((isAffineOpen X (𝒞.base j)).isoSpec.hom.base x))) + _ = _
  rw [hx]

/-- Flat pullback of dimension-graded rational cycles along a morphism with affine charts. The
dimension shift is supplied as the hypothesis `hshift`, which `dimension_fibrePoint_chart`
establishes chart by chart. -/
noncomputable def flatPullbackCharted [Finite ι]
    (dimX : DimensionFunction X) (dimP : DimensionFunction P)
    (hshift : ∀ x, dimP (fibrePoint 𝒞 x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ) :
    cyclesOfDimension X dimX i →ₗ[ℚ]
      cyclesOfDimension P dimP (i + (Nat.card ι : ℤ)) where
  toFun c := ⟨pullbackCharted 𝒞 c.1, by
    intro p hp
    by_contra hne
    have hsupp : p ∈ Function.support (pullbackChartedFun 𝒞 c.1) := hne
    obtain ⟨x, rfl⟩ := support_pullbackChartedFun_subset 𝒞 c.1 hsupp
    have hval : (c : AlgebraicCycle X ℚ) x ≠ 0 := by
      rw [← pullbackCharted_apply_fibrePoint 𝒞 c.1 x]
      exact hne
    have hdx : dimX x = i := by
      by_contra hcon
      exact hval (c.2 x hcon)
    exact hp (by rw [hshift x, hdx])⟩
  map_add' c d := Subtype.ext (pullbackCharted_add 𝒞 c.1 d.1)
  map_smul' a c := Subtype.ext (pullbackCharted_smul 𝒞 a c.1)

@[simp]
theorem flatPullbackCharted_apply [Finite ι]
    (dimX : DimensionFunction X) (dimP : DimensionFunction P)
    (hshift : ∀ x, dimP (fibrePoint 𝒞 x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ)
    (c : cyclesOfDimension X dimX i) (p : P) :
    ((flatPullbackCharted 𝒞 dimX dimP hshift i c :
        cyclesOfDimension P dimP (i + (Nat.card ι : ℤ))) : AlgebraicCycle P ℚ) p =
      pullbackCharted 𝒞 (c : AlgebraicCycle X ℚ) p :=
  rfl

/-- The graded global flat pullback is injective. -/
theorem flatPullbackCharted_injective [Finite ι]
    (dimX : DimensionFunction X) (dimP : DimensionFunction P)
    (hshift : ∀ x, dimP (fibrePoint 𝒞 x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ) :
    Function.Injective (flatPullbackCharted 𝒞 dimX dimP hshift i) := fun _ _ h =>
  Subtype.ext (pullbackCharted_injective 𝒞 (congrArg Subtype.val h))

end AffineCharts

end GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## The bundle case -/

namespace GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace.BundleData

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-- A vector bundle's own trivialising charts form affine charts for its projection in the sense
of this file: `chartι_comp` is `.w.symm` of the cartesian square `isPullback_chart`, `meets` is
immediate because a bundle chart contains its *whole* fibre over its base open
(`BundleData.opensRange_chartι`), so the generic fibre point computed in one chart already lies
in every other chart over a common base point. -/
noncomputable def affineCharts : AffineCharts 𝓔.proj ι where
  J := 𝓔.J
  base := 𝓔.chart
  iSup_base := 𝓔.iSup_chart
  chartι := 𝓔.chartι
  isOpenImmersion_chartι := 𝓔.isOpenImmersion_chartι
  chartι_comp j := (𝓔.isPullback_chart j).w.symm
  exists_mem_range p := by
    have hp : p ∈ (⨆ j, (𝓔.chartι j).opensRange : 𝓔.totalSpace.Opens) := by
      rw [𝓔.iSup_opensRange_chartι]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hp
    exact ⟨j, hj⟩
  meets j j' x hxj hxj' := by
    set y : (𝓔.chart j).1.toScheme := ⟨x, hxj⟩ with hy
    refine ⟨𝓔.chartBundlePoint j y, 𝓔.proj_chartBundlePoint j y,
      ⟨VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        (𝓔.chartBasePoint j y), rfl⟩, ?_⟩
    have hmem : 𝓔.chartBundlePoint j y ∈ 𝓔.proj ⁻¹ᵁ (𝓔.chart j').1 := by
      change 𝓔.proj.base (𝓔.chartBundlePoint j y) ∈ (𝓔.chart j').1
      rw [𝓔.proj_chartBundlePoint, hy]
      exact hxj'
    rw [← BundleData.opensRange_chartι] at hmem
    exact hmem

/-- The charted pullback along the bundle's own affine charts agrees with the bundle flat
pullback `BundlePullbackGlobal.pullbackBundle`. -/
theorem pullbackCharted_affineCharts :
    AffineCharts.pullbackCharted 𝓔.affineCharts = BundlePullbackGlobal.pullbackBundle 𝓔 := by
  funext c
  exact (AffineCharts.pullbackCharted_unique 𝓔.affineCharts c
    (BundlePullbackGlobal.pullbackBundle 𝓔 c)
    fun j => BundlePullbackGlobal.pullbackOpen_chartι_pullbackBundle 𝓔 j c).symm

/-- The generic fibre point computed along the bundle's own affine charts agrees with
`BundlePullbackGlobal.bundlePoint`. -/
theorem fibrePoint_affineCharts :
    AffineCharts.fibrePoint 𝓔.affineCharts = BundlePullbackGlobal.bundlePoint 𝓔 := by
  funext x
  rfl

end GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace.BundleData
