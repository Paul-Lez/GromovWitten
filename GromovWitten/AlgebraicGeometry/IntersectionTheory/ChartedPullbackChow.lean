/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChartedOverSubscheme

/-!
# Descent of the charted flat pullback to rational Chow groups

Let `q : P ⟶ X` be a morphism with affine charts `𝒞 : AffineCharts q ι` (`ChartedPullback.lean`)
with `ι` finite.  This file proves the comparison `q^* (ι_V)_* div(f) = (ι_{P_V})_* div(q_V^* f)`
of cycles for every integral closed subscheme `V` of `X` and rational function `f` on `V`, where
`P_V = P ×_X V` is the integral closed subscheme `ChartedOverSubscheme.restrictSubscheme 𝒞 V`, and
deduces that the charted flat pullback `AffineCharts.flatPullbackCharted` descends to rational
Chow groups.  It is the port of `BundlePullbackGlobalChow.lean` from vector bundles to morphisms
with affine charts; the general lemmas of that file (`dominantFunctionFieldMap_comp`,
`VectorBundle.bundlePoint_specMap`, …) are reused.

## Main results

* `ChartedOverSubscheme.pullbackFunctionField_chart`: the chart compatibility of the
  function-field map `q_V^*` with the affine one of `GradedCone.projection`.
* `ChartedOverSubscheme.pullbackCharted_pushforward_principalCycle`: the cycle identity.
* `ChartedOverSubscheme.totalRationalRelations_pullbackCharted`,
  `ChartedOverSubscheme.chowPullbackCharted` (with `chowPullbackCharted_quotientMap`): the
  descent `A_i(X) →ₗ[ℚ] A_{i+|ι|}(P)`, given the dimension shift `hshift` at the generic fibre
  points (as for `BundleOverSubscheme.chowPullbackBundleGlobal`).
* `ChartedOverSubscheme.openImmersionPullback_chowPullbackCharted`: on the `j`-th chart the
  Chow-group pullback is the affine `VectorBundle.chowPullbackBundle`.

## Method

As in the bundle case, the cycle identity is a pointwise statement on `P_V` (both sides vanish off
the range of `restrictι`), checked in a chart of `P_V`, where the affine comparison
`VectorBundle.pullbackBundle_principalCycle` applies.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)
open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

namespace ChartedOverSubscheme

variable {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} (𝒞 : AffineCharts q ι)
  (V : IntegralClosedSubscheme X)

/-! ## Instances on a chart meeting the closed subscheme -/

section Chart

variable (j : 𝒞.J)

/-- If `Spec Γ(V, chartOpen 𝒞 V j)` has a point, then the trace of `V` on the `j`-th base open
is nonempty. -/
theorem nonempty_chartOpen
    (y : ↥(Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝒞 V j)))) :
    Nonempty (chartOpen 𝒞 V j) := by
  refine ⟨⟨(isAffineOpen_chartOpen 𝒞 V j).fromSpec.base y, ?_⟩⟩
  have hmem : (isAffineOpen_chartOpen 𝒞 V j).fromSpec.base y ∈
      Set.range (isAffineOpen_chartOpen 𝒞 V j).fromSpec.base := ⟨y, rfl⟩
  rw [(isAffineOpen_chartOpen 𝒞 V j).range_fromSpec] at hmem
  exact hmem

variable [Nonempty (chartOpen 𝒞 V j)]

/-- The spectrum of the coordinate ring of a nonempty trace is nonempty. -/
instance nonempty_specChartOpen :
    Nonempty ↥(Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝒞 V j))) :=
  PrimeSpectrum.nonempty_iff_nontrivial.2 inferInstance

/-- The `j`-th chart of the restriction is nonempty when the trace of `V` is. -/
instance nonempty_chartRestrict :
    Nonempty ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))) :=
  ⟨VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))
    (Nonempty.some inferInstance)⟩

/-- The affine chart of the restriction is locally Noetherian. -/
instance isLocallyNoetherian_chartRestrict [Finite ι] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian
      (Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))) := by
  have hB : IsNoetherianRing Γ(V.scheme, chartOpen 𝒞 V j) := isNoetherianRing_chartOpen 𝒞 V j
  have h : IsNoetherianRing (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)) :=
    MvPolynomial.isNoetherianRing
  exact _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.2 h

/-- The spectrum of the coordinate ring of the trace is locally Noetherian. -/
instance isLocallyNoetherian_specChartOpen :
    _root_.AlgebraicGeometry.IsLocallyNoetherian
      (Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝒞 V j))) :=
  _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.2 (isNoetherianRing_chartOpen 𝒞 V j)

/-- The affine open immersion of a nonempty trace of `V` is dominant, because `V` is
irreducible. -/
instance isDominant_fromSpec_chartOpen :
    _root_.AlgebraicGeometry.IsDominant (isAffineOpen_chartOpen 𝒞 V j).fromSpec :=
  _root_.AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _

/-- The projection of the `j`-th chart of the restriction onto the trace of `V` is dominant. -/
instance isDominant_chartQuotProj :
    _root_.AlgebraicGeometry.IsDominant (chartQuotProj 𝒞 V j) := by
  rw [chartQuotProj_eq_projection]
  exact VectorBundle.isDominant_projection
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))

/-- The open immersion of the `j`-th chart of the restriction is dominant, because the
restriction is irreducible. -/
instance isDominant_chartιRestrict :
    _root_.AlgebraicGeometry.IsDominant (chartιRestrict 𝒞 V j) :=
  _root_.AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _

/-! ### The function field of the restriction, read in a chart -/

/-- Over a chart meeting `V`, the function-field pullback `pullbackFunctionField` of the
restriction is the function-field pullback of the affine projection `GradedCone.projection`
applied to the restriction of the rational function to the trace of `V`. -/
theorem pullbackFunctionField_chart (f : V.scheme.functionField) :
    _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (chartιRestrict 𝒞 V j)
        (pullbackFunctionField 𝒞 V f) =
      _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (chartQuotProj 𝒞 V j)
        (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
          (isAffineOpen_chartOpen 𝒞 V j).fromSpec f) := by
  have e1 := dominantFunctionFieldMap_comp (chartιRestrict 𝒞 V j) (restrictProj 𝒞 V)
  have e2 := dominantFunctionFieldMap_comp (chartQuotProj 𝒞 V j)
    (isAffineOpen_chartOpen 𝒞 V j).fromSpec
  have e3 := dominantFunctionFieldMap_congr (chartιRestrict_restrictProj 𝒞 V j)
  exact RingHom.congr_fun (e1.symm.trans (e3.trans e2)) f

/-- The principal divisor of the pulled-back rational function, restricted to the `j`-th chart of
the restriction, is the affine bundle pullback of the principal divisor of the restriction of the
rational function to the trace of `V` on the `j`-th base open. -/
theorem principalCycle_pullbackFunctionField_chart [Finite ι] (f : V.scheme.functionField)
    (z : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))))) :
    (restrictScheme 𝒞 V).principalCycle (pullbackFunctionField 𝒞 V f)
        ((chartιRestrict 𝒞 V j).base z) =
      AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))
        ((Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝒞 V j))).principalCycle
          (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
            (isAffineOpen_chartOpen 𝒞 V j).fromSpec f)) z := by
  have hnoethB : IsNoetherianRing Γ(V.scheme, chartOpen 𝒞 V j) :=
    isNoetherianRing_chartOpen 𝒞 V j
  have hnoethA : IsNoetherianRing (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)) :=
    MvPolynomial.isNoetherianRing
  have hdom : _root_.AlgebraicGeometry.IsDominant
      (GradedCone.projection Γ(V.scheme, chartOpen 𝒞 V j)
        (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) :=
    VectorBundle.isDominant_projection
      (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))
  have hd := VectorBundle.pullbackBundle_principalCycle
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))
    (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
      (isAffineOpen_chartOpen 𝒞 V j).fromSpec f)
  have hb := _root_.AlgebraicGeometry.Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion
    (chartιRestrict 𝒞 V j) z (pullbackFunctionField 𝒞 V f)
  have he : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (chartQuotProj 𝒞 V j) =
      _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        (GradedCone.projection Γ(V.scheme, chartOpen 𝒞 V j)
          (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) :=
    dominantFunctionFieldMap_congr (chartQuotProj_eq_projection 𝒞 V j)
  rw [hd, _root_.AlgebraicGeometry.Scheme.principalCycle_apply,
    _root_.AlgebraicGeometry.Scheme.principalCycle_apply, ← hb,
    pullbackFunctionField_chart 𝒞 V j f, he]

end Chart

/-! ## The cycle identity -/

omit V in
/-- The charted flat pullback of a cycle vanishes at a point of `P` which is not the generic point
of the fibre over its own image. -/
theorem pullbackCharted_eq_zero_of_ne (c : AlgebraicCycle X ℚ) {p : P}
    (hp : p ≠ 𝒞.fibrePoint (q.base p)) : 𝒞.pullbackCharted c p = 0 := by
  refine 𝒞.pullbackCharted_eq_zero_of_notMem c ?_
  rintro ⟨x, rfl⟩
  exact hp (by rw [AffineCharts.q_fibrePoint])

/-- The value, at a point of the restriction, of the charted flat pullback of a principal
divisor pushed forward from the integral closed subscheme `V`: it is the order of vanishing of the
pulled-back rational function. -/
theorem pullbackCharted_pushforward_principalCycle_apply [Finite ι]
    (dimX : DimensionFunction X) (f : V.scheme.functionField) (w : restrictScheme 𝒞 V) :
    𝒞.pullbackCharted (V.pushforward dimX (V.scheme.principalCycle f)) ((restrictι 𝒞 V).base w) =
      (restrictScheme 𝒞 V).principalCycle (pullbackFunctionField 𝒞 V f) w := by
  obtain ⟨j, v, rfl⟩ := exists_chartιRestrict 𝒞 V w
  have hne : Nonempty (chartOpen 𝒞 V j) :=
    nonempty_chartOpen 𝒞 V j ((chartQuotProj 𝒞 V j).base v)
  rw [principalCycle_pullbackFunctionField_chart 𝒞 V j f v]
  by_cases hv : v = VectorBundle.bundlePoint
      (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))
      ((GradedCone.projection Γ(V.scheme, chartOpen 𝒞 V j)
        (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))).base v)
  · obtain ⟨y, rfl⟩ : ∃ y, v = VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) y := ⟨_, hv⟩
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint,
      restrictι_chartιRestrict_bundlePoint,
      AffineCharts.pullbackCharted_apply_fibrePoint]
    have hpush : V.pushforward dimX (V.scheme.principalCycle f)
        (V.inclusion.base ((isAffineOpen_chartOpen 𝒞 V j).fromSpec.base y)) =
        V.scheme.principalCycle f ((isAffineOpen_chartOpen 𝒞 V j).fromSpec.base y) :=
      AlgebraicCycle.map_closedImmersion_apply_image V.inclusion (dimX : X → ℤ) _ _
    rw [hpush, _root_.AlgebraicGeometry.Scheme.principalCycle_apply,
      _root_.AlgebraicGeometry.Scheme.principalCycle_apply,
      _root_.AlgebraicGeometry.Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion]
  · rw [pullbackBundleAffine_eq_zero_of_ne _ _ hv]
    refine pullbackCharted_eq_zero_of_ne 𝒞 _ ?_
    intro hcon
    refine hv ?_
    rw [q_restrictι_chartιRestrict 𝒞 V j v,
      ← restrictι_chartιRestrict_bundlePoint 𝒞 V j ((chartQuotProj 𝒞 V j).base v)] at hcon
    have h2 := (chartιRestrict 𝒞 V j).isOpenEmbedding.injective
      ((restrictι 𝒞 V).isClosedEmbedding.injective hcon)
    have h3 : (chartQuotProj 𝒞 V j).base v =
        (GradedCone.projection Γ(V.scheme, chartOpen 𝒞 V j)
          (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))).base v :=
      base_congr_apply (chartQuotProj_eq_projection 𝒞 V j) v
    rw [← h3]
    exact h2

/-- The comparison `q^* (ι_V)_* div(f) = (ι_{P_V})_* div(q_V^* f)` of cycles on `P`: the charted
flat pullback of a principal divisor supported on an integral closed subscheme `V` of `X` is the
principal divisor of the pulled-back rational function, supported on the restriction
`P_V = P ×_X V`. -/
theorem pullbackCharted_pushforward_principalCycle [Finite ι]
    (dimX : DimensionFunction X) (dimP : DimensionFunction P)
    (f : V.scheme.functionField) :
    𝒞.pullbackCharted (V.pushforward dimX (V.scheme.principalCycle f)) =
      (restrictSubscheme 𝒞 V).pushforward dimP
        ((restrictScheme 𝒞 V).principalCycle (pullbackFunctionField 𝒞 V f)) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  dsimp only
  by_cases hp : p ∈ Set.range (restrictι 𝒞 V).base
  · obtain ⟨w, rfl⟩ := hp
    have hR : (restrictSubscheme 𝒞 V).pushforward dimP
        ((restrictScheme 𝒞 V).principalCycle (pullbackFunctionField 𝒞 V f))
        ((restrictι 𝒞 V).base w) =
        (restrictScheme 𝒞 V).principalCycle (pullbackFunctionField 𝒞 V f) w :=
      AlgebraicCycle.map_closedImmersion_apply_image (restrictι 𝒞 V) (dimP : _ → ℤ) _ w
    rw [hR]
    exact pullbackCharted_pushforward_principalCycle_apply 𝒞 V dimX f w
  · have hnot : q.base p ∉ Set.range V.inclusion.base := fun hmem ↦
      hp ((mem_range_restrictι_iff 𝒞 V p).2 hmem)
    have hRzero : (restrictSubscheme 𝒞 V).pushforward dimP
        ((restrictScheme 𝒞 V).principalCycle (pullbackFunctionField 𝒞 V f)) p = 0 :=
      AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range (restrictι 𝒞 V)
        (dimP : _ → ℤ) _ p hp
    rw [hRzero]
    by_cases hb : p = 𝒞.fibrePoint (q.base p)
    · have hval := 𝒞.pullbackCharted_apply_fibrePoint
        (V.pushforward dimX (V.scheme.principalCycle f)) (q.base p)
      rw [← hb] at hval
      rw [hval]
      exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range V.inclusion
        (dimX : X → ℤ) _ _ hnot
    · exact pullbackCharted_eq_zero_of_ne 𝒞 _ hb

/-! ## Descent of the charted flat pullback to rational Chow groups -/

section Descent

variable [Finite ι] (dimX : DimensionFunction X) (dimP : DimensionFunction P)

omit V in
/-- The charted flat pullback of the principal divisor of a rational function on an arbitrary
integral closed subscheme of `X` is a rational-equivalence relation on `P`: it is the principal
divisor of the pulled-back rational function on the restriction. -/
theorem pullbackCharted_divisor_mem_totalRationalRelations (g : RationalFunctionGenerator X) :
    𝒞.pullbackCharted (g.divisor dimX) ∈ totalRationalRelations P dimP := by
  refine Submodule.subset_span ⟨⟨restrictSubscheme 𝒞 g.subspace,
    Units.map (pullbackFunctionField 𝒞 g.subspace).toMonoidHom g.function⟩, ?_⟩
  exact (pullbackCharted_pushforward_principalCycle 𝒞 g.subspace dimX dimP
    (g.function : g.subspace.scheme.functionField)).symm

omit V in
/-- The charted flat pullback carries the canonical span of principal divisors on `X` into the
canonical span on `P`. -/
theorem totalRationalRelations_pullbackCharted :
    Submodule.map 𝒞.pullbackChartedLinear (totalRationalRelations X dimX) ≤
      totalRationalRelations P dimP := by
  rw [totalRationalRelations, Submodule.map_span, Submodule.span_le]
  rintro z ⟨c, ⟨g, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, AffineCharts.pullbackChartedLinear_apply]
  exact pullbackCharted_divisor_mem_totalRationalRelations 𝒞 dimX dimP g

variable (hshift : ∀ x, dimP (𝒞.fibrePoint x) = dimX x + (Nat.card ι : ℤ)) (i : ℤ)

omit V in
/-- The dimension-graded charted flat pullback, together with its proved preservation of the
canonical rational-equivalence subspaces. -/
noncomputable def ofCharted
    (RX : RationalEquivalenceSystem X dimX i)
    (RP : RationalEquivalenceSystem P dimP (i + (Nat.card ι : ℤ))) :
    RX.DescendingMap RP where
  onCycles := 𝒞.flatPullbackCharted dimX dimP hshift i
  maps_relations := by
    cases RX
    cases RP
    intro z hz
    have h := totalRationalRelations_pullbackCharted 𝒞 dimX dimP ⟨z.1, hz, rfl⟩
    rw [AffineCharts.pullbackChartedLinear_apply] at h
    change ((𝒞.flatPullbackCharted dimX dimP hshift i z :
      cyclesOfDimension P dimP (i + (Nat.card ι : ℤ))) : AlgebraicCycle P ℚ) ∈
        totalRationalRelations P dimP
    convert h using 1
    apply Function.locallyFinsuppWithin.coe_injective
    funext p
    exact AffineCharts.flatPullbackCharted_apply 𝒞 dimX dimP hshift i z p

omit V in
/-- Flat pullback along a morphism `q : P ⟶ X` with affine charts in `ι` coordinates on
dimension-graded rational Chow groups, `A_i(X) →ₗ[ℚ] A_{i+|ι|}(P)`. -/
noncomputable def chowPullbackCharted
    (RX : RationalEquivalenceSystem X dimX i)
    (RP : RationalEquivalenceSystem P dimP (i + (Nat.card ι : ℤ))) :
    RX.ChowGroup →ₗ[ℚ] RP.ChowGroup :=
  RationalEquivalenceSystem.DescendingMap.inducedMap RX
    (ofCharted 𝒞 dimX dimP hshift i RX RP)

omit V in
/-- The Chow-group charted flat pullback is induced by the flat pullback of dimension-graded
cycles. -/
@[simp]
theorem chowPullbackCharted_quotientMap
    (RX : RationalEquivalenceSystem X dimX i)
    (RP : RationalEquivalenceSystem P dimP (i + (Nat.card ι : ℤ)))
    (z : cyclesOfDimension X dimX i) :
    chowPullbackCharted 𝒞 dimX dimP hshift i RX RP (RX.quotientMap z) =
      RP.quotientMap (𝒞.flatPullbackCharted dimX dimP hshift i z) :=
  rfl

omit V in
/-- Chart comparison on rational Chow groups: restricting the charted flat pullback to the `j`-th
chart of `P` is the affine flat pullback of the restriction of the class to the `j`-th base open.
The dimension gradings of the two charts are assumed to be the restrictions of the global ones
(`hU`, `hC`). -/
theorem openImmersionPullback_chowPullbackCharted (j : 𝒞.J)
    [IsNoetherianRing Γ(X, (𝒞.base j).1)]
    (dimU : DimensionFunction (Spec (CommRingCat.of Γ(X, (𝒞.base j).1))))
    (dimC : DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1)))))
    (hU : ∀ y, dimU y =
      dimX (((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫ (𝒞.base j).1.ι).base y))
    (hC : ∀ z, dimC z = dimP ((𝒞.chartι j).base z))
    (RX : RationalEquivalenceSystem X dimX i)
    (RP : RationalEquivalenceSystem P dimP (i + (Nat.card ι : ℤ)))
    (RU : RationalEquivalenceSystem (Spec (CommRingCat.of Γ(X, (𝒞.base j).1))) dimU i)
    (RC : RationalEquivalenceSystem
      (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1)))) dimC
      (i + (Nat.card ι : ℤ))) :
    (RationalEquivalenceSystem.DescendingMap.openImmersionPullback RP (𝒞.chartι j) hC RC).comp
        (chowPullbackCharted 𝒞 dimX dimP hshift i RX RP) =
      (VectorBundle.chowPullbackBundle
          (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1))) dimU dimC i RU RC).comp
        (RationalEquivalenceSystem.DescendingMap.openImmersionPullback RX
          ((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫ (𝒞.base j).1.ι) hU RU) := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z⟩ := c
  refine congrArg RC.quotientMap (Subtype.ext ?_)
  have h := 𝒞.pullbackOpen_chartι_pullbackCharted j (z : AlgebraicCycle X ℚ)
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  have hy := DFunLike.congr_fun h y
  change ((𝒞.flatPullbackCharted dimX dimP hshift i z :
      cyclesOfDimension P dimP (i + (Nat.card ι : ℤ))) : AlgebraicCycle P ℚ)
      ((𝒞.chartι j).base y) =
    AlgebraicCycle.pullbackBundle (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
      (AlgebraicCycle.pullbackOpen
        ((isAffineOpen X (𝒞.base j)).isoSpec.inv ≫ (𝒞.base j).1.ι)
        (z : AlgebraicCycle X ℚ)) y
  rw [← hy, AlgebraicCycle.pullbackOpen_apply]
  exact AffineCharts.flatPullbackCharted_apply 𝒞 dimX dimP hshift i z _

omit V in
/-- For the affine charts `BundleData.affineCharts 𝓔` of a vector bundle, the charted Chow-group
pullback is the global bundle pullback `BundleOverSubscheme.chowPullbackBundleGlobal`. -/
theorem chowPullbackCharted_affineCharts {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (𝓔 : VectorBundleTotalSpace.BundleData X ι)
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
    (i : ℤ) (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ))) :
    chowPullbackCharted (BundleData.affineCharts 𝓔) dimX dimE hshift i RX RE =
      BundleOverSubscheme.chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z⟩ := c
  refine congrArg RE.quotientMap (Subtype.ext ?_)
  change AffineCharts.pullbackCharted (BundleData.affineCharts 𝓔) z.1 = _
  rw [BundleData.pullbackCharted_affineCharts]
  rfl

end Descent

end ChartedOverSubscheme

end GromovWitten.AlgebraicGeometry.IntersectionTheory
