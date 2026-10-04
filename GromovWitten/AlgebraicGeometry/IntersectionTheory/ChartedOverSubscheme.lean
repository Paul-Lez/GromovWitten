/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobalChow
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChartedPullback

/-!
# Restricting a morphism with affine charts to an integral closed subscheme

Let `q : P ⟶ X` be a morphism with affine charts `𝒞 : AffineCharts q ι` (see
`ChartedPullback.lean`): affine opens `U_j` covering `X` and open immersions
`𝒞.chartι j : 𝔸^ι_{Γ(X, U_j)} ⟶ P` over `U_j`, covering `P`, any two of which meet in every fibre
over a common base point.  For an integral locally Noetherian closed subscheme `V` of `X`, this
file constructs the restriction `P_V = P ×_X V` as an integral closed subscheme of `P`, shows that
the charts of `q` restrict to affine charts of `P_V ⟶ V`, and identifies the generic points of the
fibres of `P_V ⟶ V` with those of `q`.  It is the port of `BundleOverSubscheme.lean` from vector
bundles to morphisms with affine charts; only the commutativity `AffineCharts.chartι_comp` of the
chart squares is used, never a cartesian property of them.

## Main results

* `ChartedOverSubscheme.restrictScheme`, `restrictι` (a closed immersion), `restrictProj`: the
  fibre product `P ×_X V`.
* `ChartedOverSubscheme.chartιRestrict`, `isPullback_chartιRestrict`: the `j`-th chart of `P_V`,
  the affine space over the coordinate ring `Γ(V, V ∩ U_j)`, is the part of `P_V` lying over the
  `j`-th chart of `P` (cartesian square); hence it is an open immersion.
* `ChartedOverSubscheme.restrictCharts 𝒞 V : AffineCharts (restrictProj 𝒞 V) ι`.
* `ChartedOverSubscheme.restrictι_fibrePoint`: the generic point of the fibre of `P_V ⟶ V` over
  `v` maps to the generic point of the fibre of `q` over the image of `v`.
* `ChartedOverSubscheme.surjective_restrictProj_base`, `isDominant_restrictProj`,
  `isReduced_restrictScheme`, `isLocallyNoetherian_restrictScheme` (for `Finite ι`),
  `irreducibleSpace_restrictScheme` (the generic point of `P_V` is the generic point of the fibre
  over the generic point of `V`, `restrictι_genericPoint`), `isIntegral_restrictScheme`.
* `ChartedOverSubscheme.restrictSubscheme 𝒞 V : IntegralClosedSubscheme P` (for `Finite ι`) and
  `pullbackFunctionField : V.functionField →+* P_V.functionField`.

## Implementation note

`restrictScheme 𝒞 V` is a `def` with the charts `𝒞` as an (otherwise unused) argument: the
integrality and Noetherianity instances of `P_V` are proved with the help of the charts, and
recording them in the scheme lets instance search find these instances.
-/

open CategoryTheory AlgebraicGeometry Limits

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u


namespace ChartedOverSubscheme

/-! ## The restriction as a fibre product -/

section FibreProduct

variable {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} (𝒞 : AffineCharts q ι)
  (V : IntegralClosedSubscheme X)

/-- The restriction `P ×_X V` of `q : P ⟶ X` to the integral closed subscheme `V`, defined as a
fibre product of schemes.  It does not depend on the charts `𝒞`; they are recorded in the
notation so that the instances proved with their help (integrality, Noetherianity) are found by
instance search. -/
noncomputable def restrictScheme (_𝒞 : AffineCharts q ι) (V : IntegralClosedSubscheme X) :
    Scheme.{u} :=
  pullback q V.inclusion

/-- The inclusion of the restriction `P ×_X V` into `P`. -/
noncomputable abbrev restrictι : restrictScheme 𝒞 V ⟶ P := pullback.fst q V.inclusion

/-- The projection of the restriction `P ×_X V` onto `V`. -/
noncomputable abbrev restrictProj : restrictScheme 𝒞 V ⟶ V.scheme := pullback.snd q V.inclusion

/-- The defining fibre-product square of the restriction. -/
theorem isPullback_restrict :
    IsPullback (restrictι 𝒞 V) (restrictProj 𝒞 V) q V.inclusion :=
  IsPullback.of_hasPullback _ _

/-- The restriction is a closed subscheme of `P`: closed immersions are stable under base
change. -/
instance isClosedImmersion_restrictι :
    _root_.AlgebraicGeometry.IsClosedImmersion (restrictι 𝒞 V) :=
  MorphismProperty.of_isPullback (isPullback_restrict 𝒞 V).flip inferInstance

/-- A point of `P` lies in the restriction exactly when its image in `X` lies in `V`. -/
theorem mem_range_restrictι_iff (p : P) :
    p ∈ Set.range (restrictι 𝒞 V).base ↔ q.base p ∈ Set.range V.inclusion.base := by
  change p ∈ Set.range (pullback.fst q V.inclusion).base ↔ _
  rw [AlgebraicGeometry.Scheme.Pullback.range_fst q V.inclusion]
  exact Iff.rfl

end FibreProduct

/-! ## The trace of the subscheme on a chart -/

section Charts

variable {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} (𝒞 : AffineCharts q ι)
  (V : IntegralClosedSubscheme X)

/-- The trace of the closed subscheme `V` on the `j`-th base open of the charts `𝒞`, an affine
open of `V.scheme`. -/
abbrev chartOpen (j : 𝒞.J) : V.scheme.Opens := V.inclusion ⁻¹ᵁ (𝒞.base j).1

/-- The trace of `V` on a base open of the charts is an affine open, since a closed immersion is
an affine morphism. -/
theorem isAffineOpen_chartOpen (j : 𝒞.J) : IsAffineOpen (chartOpen 𝒞 V j) :=
  (isAffineOpen X (𝒞.base j)).preimage V.inclusion

/-- The trace of `V` on the `j`-th base open, as an affine open of `V.scheme`. -/
abbrev chartBase (j : 𝒞.J) : V.scheme.affineOpens :=
  ⟨chartOpen 𝒞 V j, isAffineOpen_chartOpen 𝒞 V j⟩

/-- The restriction map of coordinate rings from the `j`-th base open of `X` to its trace on
`V`. -/
noncomputable abbrev chartHom (j : 𝒞.J) :
    Γ(X, (𝒞.base j).1) →+* Γ(V.scheme, chartOpen 𝒞 V j) :=
  (V.inclusion.app (𝒞.base j).1).hom

/-- Restricting `V` to a base open of `X` is `Spec` of the restriction map of coordinate
rings. -/
theorem specMap_chartHom_fromSpec (j : 𝒞.J) :
    Spec.map (CommRingCat.ofHom (chartHom 𝒞 V j)) ≫ (isAffineOpen X (𝒞.base j)).fromSpec =
      (isAffineOpen_chartOpen 𝒞 V j).fromSpec ≫ V.inclusion := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec V.inclusion (isAffineOpen X (𝒞.base j))
    (isAffineOpen_chartOpen 𝒞 V j) (le_refl (V.inclusion ⁻¹ᵁ (𝒞.base j).1))
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

/-- The trace of `V` on the `j`-th base open is the fibre product of that open with `V`
over `X`. -/
theorem isPullback_chartHom (j : 𝒞.J) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartHom 𝒞 V j)))
      (isAffineOpen_chartOpen 𝒞 V j).fromSpec (isAffineOpen X (𝒞.base j)).fromSpec
      V.inclusion := by
  refine (isPullback_morphismRestrict V.inclusion (𝒞.base j).1).of_iso
    (isAffineOpen_chartOpen 𝒞 V j).isoSpec (isAffineOpen X (𝒞.base j)).isoSpec
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (isAffineOpen X (𝒞.base j)).fromSpec, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec, specMap_chartHom_fromSpec,
      IsAffineOpen.isoSpec_hom_fromSpec_assoc, morphismRestrict_ι]
  · simp
  · simp
  · simp

/-- The restriction map of coordinate rings of a base open is surjective, because `V` is a
closed subscheme. -/
theorem surjective_chartHom (j : 𝒞.J) : Function.Surjective (chartHom 𝒞 V j) :=
  Scheme.Hom.app_surjective V.inclusion (𝒞.base j).1 (isAffineOpen X (𝒞.base j))

/-- The projection of the `j`-th chart of the restriction onto the trace of `V`. -/
noncomputable abbrev chartQuotProj (j : 𝒞.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) ⟶
      Spec Γ(V.scheme, chartOpen 𝒞 V j) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C :
    Γ(V.scheme, chartOpen 𝒞 V j) →+* MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))

/-- The closed immersion of the `j`-th chart of the restriction into the `j`-th chart of `P`,
given by restricting the coefficients of a polynomial to `V`. -/
noncomputable abbrev chartQuotι (j : 𝒞.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) ⟶
      Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝒞.base j).1))) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := ι) (chartHom 𝒞 V j)))

omit V in
/-- The structural map of the `j`-th chart of `P`, written through `fromSpec`; this only uses
the commutativity `AffineCharts.chartι_comp`. -/
theorem specMap_C_fromSpec_chart (j : 𝒞.J) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.C :
        Γ(X, (𝒞.base j).1) →+* MvPolynomial ι Γ(X, (𝒞.base j).1))) ≫
        (isAffineOpen X (𝒞.base j)).fromSpec = 𝒞.chartι j ≫ q := by
  rw [𝒞.chartι_comp j, IsAffineOpen.isoSpec_inv_ι, MvPolynomial.algebraMap_eq]

/-- The `j`-th chart of the restriction is the fibre product of the `j`-th chart of `P` with `V`
over `X`. -/
theorem isPullback_chartQuot (j : 𝒞.J) :
    IsPullback (chartQuotι 𝒞 V j)
      (chartQuotProj 𝒞 V j ≫ (isAffineOpen_chartOpen 𝒞 V j).fromSpec)
      (𝒞.chartι j ≫ q) V.inclusion := by
  rw [← specMap_C_fromSpec_chart 𝒞 j]
  exact (BundleOverSubscheme.isPullback_specMap_mvPolynomialMap ι (chartHom 𝒞 V j)).paste_vert
    (isPullback_chartHom 𝒞 V j)

/-- The `j`-th chart of the restriction `P ×_X V`, an affine space over the coordinate ring of
the trace of `V` on the `j`-th base open. -/
noncomputable def chartιRestrict (j : 𝒞.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) ⟶
      restrictScheme 𝒞 V :=
  pullback.lift (chartQuotι 𝒞 V j ≫ 𝒞.chartι j)
    (chartQuotProj 𝒞 V j ≫ (isAffineOpen_chartOpen 𝒞 V j).fromSpec)
    (by rw [Category.assoc]; exact (isPullback_chartQuot 𝒞 V j).w)

/-- The `j`-th chart of the restriction, followed by the inclusion into `P`. -/
@[reassoc (attr := simp)]
theorem chartιRestrict_restrictι (j : 𝒞.J) :
    chartιRestrict 𝒞 V j ≫ restrictι 𝒞 V = chartQuotι 𝒞 V j ≫ 𝒞.chartι j :=
  pullback.lift_fst _ _ _

/-- The `j`-th chart of the restriction, followed by the projection onto `V`. -/
@[reassoc (attr := simp)]
theorem chartιRestrict_restrictProj (j : 𝒞.J) :
    chartιRestrict 𝒞 V j ≫ restrictProj 𝒞 V =
      chartQuotProj 𝒞 V j ≫ (isAffineOpen_chartOpen 𝒞 V j).fromSpec :=
  pullback.lift_snd _ _ _

/-- The `j`-th chart of the restriction is the part of `P ×_X V` lying over the `j`-th chart
of `P`.  No cartesian property of the chart `𝒞.chartι j` itself is needed. -/
theorem isPullback_chartιRestrict (j : 𝒞.J) :
    IsPullback (chartιRestrict 𝒞 V j) (chartQuotι 𝒞 V j) (restrictι 𝒞 V) (𝒞.chartι j) := by
  refine IsPullback.of_right ?_ (chartιRestrict_restrictι 𝒞 V j) (isPullback_restrict 𝒞 V).flip
  rw [chartιRestrict_restrictProj]
  exact (isPullback_chartQuot 𝒞 V j).flip

/-- The charts of the restriction are open immersions. -/
instance isOpenImmersion_chartιRestrict (j : 𝒞.J) :
    _root_.AlgebraicGeometry.IsOpenImmersion (chartιRestrict 𝒞 V j) :=
  MorphismProperty.of_isPullback (isPullback_chartιRestrict 𝒞 V j).flip inferInstance

/-- The `j`-th chart of the restriction is exactly the part of `P ×_X V` lying over the `j`-th
chart of `P`. -/
theorem opensRange_chartιRestrict (j : 𝒞.J) :
    (chartιRestrict 𝒞 V j).opensRange = restrictι 𝒞 V ⁻¹ᵁ (𝒞.chartι j).opensRange := by
  refine TopologicalSpace.Opens.ext ?_
  have he : (isPullback_chartιRestrict 𝒞 V j).isoPullback.hom ≫
      pullback.fst (restrictι 𝒞 V) (𝒞.chartι j) = chartιRestrict 𝒞 V j :=
    IsPullback.isoPullback_hom_fst _
  have hrange : Set.range (chartιRestrict 𝒞 V j).base =
      Set.range (pullback.fst (restrictι 𝒞 V) (𝒞.chartι j)).base := by
    rw [← he]
    exact (BundleOverSubscheme.surjective_base_of_iso _).range_comp _
  rw [Scheme.Hom.coe_opensRange, hrange,
    AlgebraicGeometry.Scheme.Pullback.range_fst (restrictι 𝒞 V) (𝒞.chartι j)]
  rfl

/-- A point of the restriction lies in its `j`-th chart exactly when its image in `P` lies in
the `j`-th chart of `P`. -/
theorem mem_range_chartιRestrict_iff (j : 𝒞.J) (w : restrictScheme 𝒞 V) :
    w ∈ Set.range (chartιRestrict 𝒞 V j).base ↔
      (restrictι 𝒞 V).base w ∈ Set.range (𝒞.chartι j).base := by
  have h := congrArg (fun U : (restrictScheme 𝒞 V).Opens => w ∈ U) (opensRange_chartιRestrict 𝒞 V j)
  exact h.to_iff

/-- The structural map of the `j`-th chart of the restriction, in the shape required by
`AffineCharts.chartι_comp`. -/
theorem chartιRestrict_comp (j : 𝒞.J) :
    chartιRestrict 𝒞 V j ≫ restrictProj 𝒞 V =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(V.scheme, (chartBase 𝒞 V j).1)
        (MvPolynomial ι Γ(V.scheme, (chartBase 𝒞 V j).1)))) ≫
        (isAffineOpen V.scheme (chartBase 𝒞 V j)).isoSpec.inv ≫ (chartBase 𝒞 V j).1.ι := by
  rw [chartιRestrict_restrictProj, IsAffineOpen.isoSpec_inv_ι, MvPolynomial.algebraMap_eq]

/-- The traces of the base opens of `𝒞` cover `V`. -/
theorem iSup_chartOpen : ⨆ j, (chartBase 𝒞 V j).1 = ⊤ := by
  refine top_le_iff.1 fun v _ => ?_
  have hv : V.inclusion.base v ∈ (⊤ : X.Opens) := trivial
  rw [← 𝒞.iSup_base] at hv
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hv
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩

/-- **The restricted charts.**  The affine charts `𝒞` of `q : P ⟶ X` restrict to affine charts
of the projection `P ×_X V ⟶ V`: the `j`-th chart is the affine space over the coordinate ring
of the trace of `V` on the `j`-th base open. -/
noncomputable def restrictCharts : AffineCharts (restrictProj 𝒞 V) ι where
  J := 𝒞.J
  base := chartBase 𝒞 V
  iSup_base := iSup_chartOpen 𝒞 V
  chartι := chartιRestrict 𝒞 V
  isOpenImmersion_chartι := isOpenImmersion_chartιRestrict 𝒞 V
  chartι_comp := chartιRestrict_comp 𝒞 V
  exists_mem_range w := by
    obtain ⟨j, hj⟩ := 𝒞.exists_mem_range ((restrictι 𝒞 V).base w)
    exact ⟨j, (mem_range_chartιRestrict_iff 𝒞 V j w).2 hj⟩
  meets j j' v hj hj' := by
    obtain ⟨p, hp, hpj, hpj'⟩ := 𝒞.meets j j' (V.inclusion.base v) hj hj'
    obtain ⟨w, hw₁, hw₂⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := q) (g := V.inclusion) p v hp
    let w' : restrictScheme 𝒞 V := w
    have hw₁' : (restrictι 𝒞 V).base w' = p := hw₁
    refine ⟨w', hw₂, (mem_range_chartιRestrict_iff 𝒞 V j w').2 (hw₁' ▸ hpj),
      (mem_range_chartιRestrict_iff 𝒞 V j' w').2 (hw₁' ▸ hpj')⟩

/-- Every point of the restriction lies in one of its charts. -/
theorem exists_chartιRestrict (w : restrictScheme 𝒞 V) :
    ∃ (j : 𝒞.J) (z : Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))),
      (chartιRestrict 𝒞 V j).base z = w := by
  obtain ⟨j, hj⟩ := 𝒞.exists_mem_range ((restrictι 𝒞 V).base w)
  obtain ⟨z, hz⟩ := (mem_range_chartιRestrict_iff 𝒞 V j w).2 hj
  exact ⟨j, z, hz⟩

/-- The projection of the `j`-th chart of the restriction is the projection of the trivial
affine bundle over the coordinate ring of the trace of `V` on the `j`-th base open. -/
theorem chartQuotProj_eq_projection (j : 𝒞.J) :
    chartQuotProj 𝒞 V j =
      GradedCone.projection Γ(V.scheme, chartOpen 𝒞 V j)
        (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)) := by
  simp [GradedCone.projection, MvPolynomial.algebraMap_eq]

/-! ## Local structure: Noetherian and reduced; surjectivity of the projection -/

/-- The cover of the restriction by its charts. -/
noncomputable abbrev restrictCover : (restrictScheme 𝒞 V).OpenCover :=
  Scheme.Cover.mkOfCovers 𝒞.J
    (fun j => Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))))
    (fun j => chartιRestrict 𝒞 V j) (exists_chartιRestrict 𝒞 V)

/-- The coordinate ring of the trace of `V` on a base open is Noetherian. -/
theorem isNoetherianRing_chartOpen (j : 𝒞.J) :
    IsNoetherianRing Γ(V.scheme, chartOpen 𝒞 V j) :=
  _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian
    ⟨chartOpen 𝒞 V j, isAffineOpen_chartOpen 𝒞 V j⟩

/-- The restriction `P ×_X V` is locally Noetherian when `q` has affine charts with finitely
many coordinates: every chart is a polynomial algebra over a Noetherian ring. -/
instance isLocallyNoetherian_restrictScheme [Finite ι] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian (restrictScheme 𝒞 V) := by
  rw [_root_.AlgebraicGeometry.isLocallyNoetherian_iff_openCover (restrictCover 𝒞 V)]
  intro j
  have hB : IsNoetherianRing Γ(V.scheme, chartOpen 𝒞 V j) := isNoetherianRing_chartOpen 𝒞 V j
  have h : IsNoetherianRing (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)) :=
    MvPolynomial.isNoetherianRing
  exact _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.2 h

/-- The restriction `P ×_X V` is reduced when `q` has affine charts: every chart is a polynomial
algebra over the reduced coordinate ring of a trace of `V`. -/
instance isReduced_restrictScheme :
    _root_.AlgebraicGeometry.IsReduced (restrictScheme 𝒞 V) := by
  apply +allowSynthFailures _root_.AlgebraicGeometry.isReduced_of_isReduced_stalk
  intro x
  obtain ⟨j, z, rfl⟩ := exists_chartιRestrict 𝒞 V x
  have hred : _root_.IsReduced
      ((Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))).presheaf.stalk z) :=
    _root_.AlgebraicGeometry.isReduced_stalk_of_isReduced _ z
  exact isReduced_of_injective ((chartιRestrict 𝒞 V j).stalkMap z).hom
    ((ConcreteCategory.bijective_of_isIso ((chartιRestrict 𝒞 V j).stalkMap z)).injective)

/-- The projection to `V` of a point of the `j`-th chart of the restriction. -/
theorem restrictProj_chartιRestrict (j : 𝒞.J)
    (z : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))))) :
    (restrictProj 𝒞 V).base ((chartιRestrict 𝒞 V j).base z) =
      (isAffineOpen_chartOpen 𝒞 V j).fromSpec.base ((chartQuotProj 𝒞 V j).base z) :=
  base_congr_apply (chartιRestrict_restrictProj 𝒞 V j) z

/-- The image in `P` of a point of the `j`-th chart of the restriction. -/
theorem restrictι_chartιRestrict (j : 𝒞.J)
    (z : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))))) :
    (restrictι 𝒞 V).base ((chartιRestrict 𝒞 V j).base z) =
      (𝒞.chartι j).base ((chartQuotι 𝒞 V j).base z) :=
  base_congr_apply (chartιRestrict_restrictι 𝒞 V j) z

/-- The projection `P ×_X V ⟶ V` is surjective when `q` has affine charts: over a point `v` of
the trace of `V` on a base open, the chart contains the generic point of the fibre. -/
theorem surjective_restrictProj_base :
    Function.Surjective (restrictProj 𝒞 V).base := by
  intro v
  have hv : v ∈ (⊤ : V.scheme.Opens) := trivial
  rw [← iSup_chartOpen 𝒞 V] at hv
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hv
  have hr : v ∈ Set.range (isAffineOpen_chartOpen 𝒞 V j).fromSpec.base := by
    rw [(isAffineOpen_chartOpen 𝒞 V j).range_fromSpec]
    exact hj
  obtain ⟨y, rfl⟩ := hr
  refine ⟨(chartιRestrict 𝒞 V j).base (VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) y), ?_⟩
  rw [restrictProj_chartιRestrict]
  congr 1
  rw [base_congr_apply (chartQuotProj_eq_projection 𝒞 V j)]
  exact VectorBundle.projection_base_bundlePoint _ y

/-- The projection `P ×_X V ⟶ V` is dominant when `q` has affine charts. -/
instance isDominant_restrictProj :
    _root_.AlgebraicGeometry.IsDominant (restrictProj 𝒞 V) :=
  ⟨(surjective_restrictProj_base 𝒞 V).denseRange⟩

end Charts

/-! ## Generic points of the fibres of the restriction -/

section FibrePoint

variable {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} (𝒞 : AffineCharts q ι)
  (V : IntegralClosedSubscheme X)

/-- The image in `X` of a point of the `j`-th chart of the restriction. -/
theorem q_restrictι_chartιRestrict (j : 𝒞.J)
    (z : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))))) :
    q.base ((restrictι 𝒞 V).base ((chartιRestrict 𝒞 V j).base z)) =
      V.inclusion.base ((isAffineOpen_chartOpen 𝒞 V j).fromSpec.base
        ((chartQuotProj 𝒞 V j).base z)) := by
  have hcomm : q.base ((restrictι 𝒞 V).base ((chartιRestrict 𝒞 V j).base z)) =
      V.inclusion.base ((restrictProj 𝒞 V).base ((chartιRestrict 𝒞 V j).base z)) :=
    base_congr_apply (isPullback_restrict 𝒞 V).w ((chartιRestrict 𝒞 V j).base z)
  rw [hcomm, restrictProj_chartιRestrict]

/-- The generic point of the fibre of the restriction over a point of the trace of `V` on the
`j`-th base open, computed in the `j`-th chart, is the generic point of the fibre of `q` over the
image of that point in `X`. -/
theorem restrictι_chartιRestrict_bundlePoint (j : 𝒞.J)
    (y : ↥(Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝒞 V j)))) :
    (restrictι 𝒞 V).base ((chartιRestrict 𝒞 V j).base
        (VectorBundle.bundlePoint
          (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) y)) =
      𝒞.fibrePoint (V.inclusion.base ((isAffineOpen_chartOpen 𝒞 V j).fromSpec.base y)) := by
  set bp := VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) y with hbp
  have h1 : (restrictι 𝒞 V).base ((chartιRestrict 𝒞 V j).base bp) =
      (𝒞.chartι j).base ((chartQuotι 𝒞 V j).base bp) :=
    restrictι_chartιRestrict 𝒞 V j bp
  have h3 : (chartQuotProj 𝒞 V j).base bp = y := by
    rw [base_congr_apply (chartQuotProj_eq_projection 𝒞 V j), hbp]
    exact VectorBundle.projection_base_bundlePoint _ y
  have h4 : q.base ((restrictι 𝒞 V).base ((chartιRestrict 𝒞 V j).base bp)) =
      V.inclusion.base ((isAffineOpen_chartOpen 𝒞 V j).fromSpec.base y) := by
    rw [q_restrictι_chartιRestrict, h3]
  have h5 : (chartQuotι 𝒞 V j).base bp =
      VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
        ((Spec.map (CommRingCat.ofHom (chartHom 𝒞 V j))).base y) :=
    VectorBundle.bundlePoint_specMap (chartHom 𝒞 V j) (surjective_chartHom 𝒞 V j) y
  have h7 : VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝒞.base j).1)))
        ((GradedCone.projection Γ(X, (𝒞.base j).1)
          (MvPolynomial ι Γ(X, (𝒞.base j).1))).base ((chartQuotι 𝒞 V j).base bp)) =
      (chartQuotι 𝒞 V j).base bp := by
    rw [h5, VectorBundle.projection_base_bundlePoint]
  have h6 := 𝒞.fibrePoint_chartι j ((chartQuotι 𝒞 V j).base bp)
  rw [← h1, h4] at h6
  rw [h1, h6, h7]

/-- **The generic fibre points of the restriction.**  The generic point of the fibre of
`P ×_X V ⟶ V` over `v` (for the restricted charts `restrictCharts 𝒞 V`) is, in `P`, the generic
point of the fibre of `q` over the image of `v` in `X`. -/
theorem restrictι_fibrePoint (v : V.scheme) :
    (restrictι 𝒞 V).base ((restrictCharts 𝒞 V).fibrePoint v) =
      𝒞.fibrePoint (V.inclusion.base v) := by
  have hv : v ∈ (⊤ : V.scheme.Opens) := trivial
  rw [← iSup_chartOpen 𝒞 V] at hv
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hv
  have hr : v ∈ Set.range (isAffineOpen_chartOpen 𝒞 V j).fromSpec.base := by
    rw [(isAffineOpen_chartOpen 𝒞 V j).range_fromSpec]
    exact hj
  obtain ⟨y, rfl⟩ := hr
  set z := VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))) y with hz
  have hy : (chartQuotProj 𝒞 V j).base z = y := by
    rw [base_congr_apply (chartQuotProj_eq_projection 𝒞 V j), hz]
    exact VectorBundle.projection_base_bundlePoint _ y
  have hp : (restrictProj 𝒞 V).base ((chartιRestrict 𝒞 V j).base z) =
      (isAffineOpen_chartOpen 𝒞 V j).fromSpec.base y := by
    rw [restrictProj_chartιRestrict, hy]
  have hy' : (GradedCone.projection Γ(V.scheme, chartOpen 𝒞 V j)
      (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))).base z = y := by
    rw [hz]
    exact VectorBundle.projection_base_bundlePoint _ y
  have h := (restrictCharts 𝒞 V).fibrePoint_chartι j z
  change (restrictCharts 𝒞 V).fibrePoint ((restrictProj 𝒞 V).base
      ((chartιRestrict 𝒞 V j).base z)) = (chartιRestrict 𝒞 V j).base
      (VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j)))
        ((GradedCone.projection Γ(V.scheme, chartOpen 𝒞 V j)
          (MvPolynomial ι Γ(V.scheme, chartOpen 𝒞 V j))).base z)) at h
  rw [hp, hy'] at h
  rw [h]
  exact restrictι_chartιRestrict_bundlePoint 𝒞 V j y

end FibrePoint

/-! ## Irreducibility and integrality -/

section Integral

variable {P X : Scheme.{u}} {q : P ⟶ X} {ι : Type u} (𝒞 : AffineCharts q ι)
  (V : IntegralClosedSubscheme X)

/-- The generic point of the fibre of `q` over the generic point of `V`. -/
noncomputable def genericFibrePoint : P :=
  𝒞.fibrePoint (BundleOverSubscheme.genericBasePoint V)

/-- The generic point of the fibre over the generic point of `V` specialises to every point of
`P` lying over `V`. -/
theorem specializes_genericFibrePoint (p : P) (hp : q.base p ∈ Set.range V.inclusion.base) :
    genericFibrePoint 𝒞 V ⤳ p := by
  obtain ⟨v, hv⟩ := hp
  exact AffineCharts.fibrePoint_specializes 𝒞
    (hv ▸ BundleOverSubscheme.specializes_genericBasePoint V v)

/-- The generic point of the fibre over the generic point of `V` lies in the restriction. -/
theorem mem_range_genericFibrePoint :
    genericFibrePoint 𝒞 V ∈ Set.range (restrictι 𝒞 V).base := by
  rw [mem_range_restrictι_iff, genericFibrePoint, AffineCharts.q_fibrePoint]
  exact ⟨genericPoint V.scheme, rfl⟩

/-- The generic point of the restriction `P ×_X V`. -/
noncomputable def genericRestrictPoint : restrictScheme 𝒞 V :=
  (mem_range_genericFibrePoint 𝒞 V).choose

/-- The distinguished point of the restriction maps to the generic point of the fibre over the
generic point of `V`. -/
@[simp]
theorem restrictι_genericRestrictPoint :
    (restrictι 𝒞 V).base (genericRestrictPoint 𝒞 V) = genericFibrePoint 𝒞 V :=
  (mem_range_genericFibrePoint 𝒞 V).choose_spec

/-- The distinguished point of the restriction specialises to every point of it. -/
theorem genericRestrictPoint_specializes (w : restrictScheme 𝒞 V) :
    genericRestrictPoint 𝒞 V ⤳ w := by
  have hind : Topology.IsInducing (restrictι 𝒞 V).base :=
    (restrictι 𝒞 V).isClosedEmbedding.isInducing
  rw [← hind.specializes_iff, restrictι_genericRestrictPoint]
  refine specializes_genericFibrePoint 𝒞 V _ ?_
  have hmem : (restrictι 𝒞 V).base w ∈ Set.range (restrictι 𝒞 V).base := ⟨w, rfl⟩
  rw [mem_range_restrictι_iff] at hmem
  exact hmem

/-- The closure of the distinguished point is the whole restriction. -/
theorem closure_genericRestrictPoint :
    closure ({genericRestrictPoint 𝒞 V} : Set (restrictScheme 𝒞 V)) = Set.univ :=
  Set.eq_univ_of_forall fun w => (genericRestrictPoint_specializes 𝒞 V w).mem_closure

/-- The restriction `P ×_X V` is irreducible. -/
instance irreducibleSpace_restrictScheme : IrreducibleSpace (restrictScheme 𝒞 V) := by
  rw [irreducibleSpace_def, Set.top_eq_univ, ← closure_genericRestrictPoint 𝒞 V]
  exact isIrreducible_singleton.closure

/-- The restriction `P ×_X V` is integral. -/
instance isIntegral_restrictScheme :
    _root_.AlgebraicGeometry.IsIntegral (restrictScheme 𝒞 V) :=
  _root_.AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- The restriction `P ×_X V`, packaged as an integral locally Noetherian closed subscheme of
`P` (for finitely many coordinates). -/
noncomputable def restrictSubscheme [Finite ι] : IntegralClosedSubscheme P where
  scheme := restrictScheme 𝒞 V
  inclusion := restrictι 𝒞 V

/-- The scheme of `restrictSubscheme` is the restriction. -/
@[simp]
theorem restrictSubscheme_scheme [Finite ι] :
    (restrictSubscheme 𝒞 V).scheme = restrictScheme 𝒞 V := rfl

/-- The inclusion of `restrictSubscheme` is `restrictι`. -/
@[simp]
theorem restrictSubscheme_inclusion [Finite ι] :
    (restrictSubscheme 𝒞 V).inclusion = restrictι 𝒞 V := rfl

/-- The generic point of the restriction is the distinguished point constructed above. -/
theorem genericPoint_restrictScheme :
    genericPoint (restrictScheme 𝒞 V) = genericRestrictPoint 𝒞 V :=
  IsGenericPoint.eq (genericPoint_spec _) (closure_genericRestrictPoint 𝒞 V)

/-- The generic point of the restriction is the generic point of the fibre of `q` over the
generic point of `V`. -/
theorem restrictι_genericPoint :
    (restrictι 𝒞 V).base (genericPoint (restrictScheme 𝒞 V)) =
      𝒞.fibrePoint (V.inclusion.base (genericPoint V.scheme)) := by
  rw [genericPoint_restrictScheme, restrictι_genericRestrictPoint]
  rfl

/-- The function-field map of the dominant projection `P ×_X V ⟶ V`. -/
noncomputable def pullbackFunctionField :
    V.scheme.functionField →+* (restrictScheme 𝒞 V).functionField :=
  _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (restrictProj 𝒞 V)

end Integral

end ChartedOverSubscheme

end GromovWitten.AlgebraicGeometry.IntersectionTheory
