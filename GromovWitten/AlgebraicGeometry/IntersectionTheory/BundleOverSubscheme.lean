/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackChow

/-!
# The restriction of a global vector bundle to an integral closed subscheme

Let `𝓔 : BundleData X ι` be a vector bundle over a scheme `X` (see
`GromovWitten/AlgebraicGeometry/VectorBundleTotalSpace.lean`) and let `V` be an integral locally
Noetherian closed subscheme of `X` (`IntegralClosedSubscheme X`).  This file constructs the
restricted bundle `E_V = E ×_X V` as an *integral* closed subscheme of the total space
`E = 𝓔.totalSpace`, with a dominant projection to `V`, and identifies it over every trivialising
chart with an affine space over the coordinate ring of the trace of `V` on that chart.

## The fibre product

`restrictScheme 𝓔 V` is the categorical fibre product `pullback 𝓔.proj V.inclusion`, with
`restrictι` (a closed immersion, `isClosedImmersion_restrictι`) into the total space and
`restrictProj` (an affine morphism) onto `V`.  The zero section of `𝓔` restricts to a section
`restrictZero` of `restrictProj`, so `restrictProj` is surjective and in particular dominant
(`isDominant_restrictProj`).

## The charts

The trace of `V` on the `j`-th chart of `𝓔` is the affine open `chartOpen 𝓔 V j` of `V.scheme`,
and `chartHom 𝓔 V j : Γ(X, U_j) →+* Γ(V, W_j)` is the (surjective, `surjective_chartHom`)
restriction map of coordinate rings; `chartQuotEquiv` presents its target as the quotient
`Γ(X, U_j) ⧸ p_j` by `chartIdeal 𝓔 V j := RingHom.ker (chartHom 𝓔 V j)`.  The key affine input is
`isPullback_specMap_mvPolynomialMap`, the statement that affine space is stable under base change
of the base ring.  Pasting it with `isPullback_chartHom` and `BundleData.isPullback_chart` gives
`isPullback_chartιRestrict`: the chart `Spec (MvPolynomial ι Γ(V, W_j))` is the part of `E_V`
lying over the `j`-th chart of `E`.  The charts are open immersions
(`isOpenImmersion_chartιRestrict`), their images are the preimages of the charts of `E`
(`opensRange_chartιRestrict`), and they cover `E_V` (`iSup_opensRange_chartιRestrict`).
`chartQuotSpecIso_hom_quotBundleImmersion` matches the chart inclusion with the affine closed
immersion `VectorBundle.quotBundleImmersion` of `BundlePullbackChow.lean`.

## Integrality

`E_V` is reduced and locally Noetherian because its charts are polynomial algebras over the
reduced Noetherian rings `Γ(V, W_j)`.  It is irreducible because the point
`genericBundlePoint 𝓔 V`, the generic point of the fibre of `E` over the generic point of `V`,
lies in `E_V` and specialises to every point of it; this uses
`BundlePullbackGlobal.chartBundlePoint_specializes_iff`.  Hence
`isIntegral_restrictScheme`, and `restrictSubscheme 𝓔 V : IntegralClosedSubscheme 𝓔.totalSpace`,
with `pullbackFunctionField` the function-field map of the dominant projection.

## What is not here

The cycle identity `pullbackBundle 𝓔 (V.pushforward (principalCycle f)) =
(restrictSubscheme 𝓔 V).pushforward (principalCycle (pullbackFunctionField f))` and the resulting
descent of the global bundle pullback to Chow groups are not proved; they need the compatibility
of `pullbackFunctionField` with the affine function-field maps of the charts, which is not
established here.
-/

open CategoryTheory AlgebraicGeometry Limits

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

namespace BundleOverSubscheme

/-! ## Affine space is stable under base change of the base ring -/

/-- Base change of affine space: for a ring map `f : Γ →+* B` the square of polynomial algebras
`Γ → Γ[ι]`, `Γ → B`, `Γ[ι] → B[ι]`, `B → B[ι]` is a pushout, hence its spectrum is a pullback
square of schemes.  In other words `𝔸^ι_B = 𝔸^ι_Γ ×_{Spec Γ} Spec B`. -/
theorem isPullback_specMap_mvPolynomialMap (ι : Type u) {Γ B : Type u} [CommRing Γ] [CommRing B]
    (f : Γ →+* B) :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := ι) f)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : B →+* MvPolynomial ι B)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ →+* MvPolynomial ι Γ)))
      (Spec.map (CommRingCat.ofHom f)) := by
  let _ : Algebra Γ B := f.toAlgebra
  have hpush :
      IsPushout (CommRingCat.ofHom (algebraMap Γ (MvPolynomial ι Γ)))
        (CommRingCat.ofHom (algebraMap Γ B))
        (CommRingCat.ofHom (MvPolynomial.map (σ := ι) f))
        (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))) := by
    refine GromovWitten.AlgebraicGeometry.isPushout_of_algEquiv _
      (MvPolynomial.algebraTensorAlgEquiv Γ B) ?_
    intro s
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  exact isPullback_SpecMap_of_isPushout _ _ _ _ hpush

/-! ## The restricted bundle as a fibre product -/

section Global

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι) (V : IntegralClosedSubscheme X)

/-- The total space of the restriction `E ×_X V` of the bundle `𝓔` to the integral closed
subscheme `V`, defined as a fibre product of schemes. -/
noncomputable abbrev restrictScheme : Scheme.{u} := pullback 𝓔.proj V.inclusion

/-- The inclusion of the restricted bundle into the total space of `𝓔`. -/
noncomputable abbrev restrictι : restrictScheme 𝓔 V ⟶ 𝓔.totalSpace := pullback.fst _ _

/-- The projection of the restricted bundle onto the integral closed subscheme `V`. -/
noncomputable abbrev restrictProj : restrictScheme 𝓔 V ⟶ V.scheme := pullback.snd _ _

/-- The defining fibre-product square of the restricted bundle. -/
theorem isPullback_restrict :
    IsPullback (restrictι 𝓔 V) (restrictProj 𝓔 V) 𝓔.proj V.inclusion :=
  IsPullback.of_hasPullback _ _

/-- The restricted bundle is a closed subscheme of the total space: closed immersions are stable
under base change. -/
instance isClosedImmersion_restrictι :
    _root_.AlgebraicGeometry.IsClosedImmersion (restrictι 𝓔 V) :=
  MorphismProperty.of_isPullback (isPullback_restrict 𝓔 V).flip inferInstance

/-- The projection of the restricted bundle is an affine morphism. -/
instance isAffineHom_restrictProj :
    _root_.AlgebraicGeometry.IsAffineHom (restrictProj 𝓔 V) :=
  MorphismProperty.of_isPullback (isPullback_restrict 𝓔 V) inferInstance

/-- The zero section of the restricted bundle, obtained from the zero section of `𝓔`. -/
noncomputable def restrictZero : V.scheme ⟶ restrictScheme 𝓔 V :=
  pullback.lift (V.inclusion ≫ 𝓔.zeroSection) (𝟙 _) (by
    rw [Category.assoc, 𝓔.zeroSection_proj, Category.comp_id, Category.id_comp])

/-- The zero section is a section of the projection of the restricted bundle. -/
@[simp]
theorem restrictZero_proj : restrictZero 𝓔 V ≫ restrictProj 𝓔 V = 𝟙 V.scheme :=
  pullback.lift_snd _ _ _

/-- The projection of the restricted bundle is surjective, because it has a section. -/
theorem surjective_restrictProj_base : Function.Surjective (restrictProj 𝓔 V).base := by
  intro y
  refine ⟨(restrictZero 𝓔 V).base y, ?_⟩
  have h : (restrictZero 𝓔 V ≫ restrictProj 𝓔 V).base y = y := by
    rw [restrictZero_proj]
    rfl
  exact h

/-- The projection of the restricted bundle is dominant. -/
instance isDominant_restrictProj :
    _root_.AlgebraicGeometry.IsDominant (restrictProj 𝓔 V) :=
  ⟨(surjective_restrictProj_base 𝓔 V).denseRange⟩

/-! ## The trace of the subscheme on a chart -/

/-- The trace of the closed subscheme `V` on the `j`-th trivialising chart of `𝓔`, an affine
open of `V.scheme`. -/
abbrev chartOpen (j : 𝓔.J) : V.scheme.Opens := V.inclusion ⁻¹ᵁ (𝓔.chart j).1

/-- The trace of `V` on a chart is an affine open, since a closed immersion is an affine
morphism. -/
theorem isAffineOpen_chartOpen (j : 𝓔.J) : IsAffineOpen (chartOpen 𝓔 V j) :=
  (isAffineOpen X (𝓔.chart j)).preimage V.inclusion

/-- The restriction map of coordinate rings from the `j`-th chart of `X` to its trace on `V`. -/
noncomputable abbrev chartHom (j : 𝓔.J) :
    Γ(X, (𝓔.chart j).1) →+* Γ(V.scheme, chartOpen 𝓔 V j) :=
  (V.inclusion.app (𝓔.chart j).1).hom

/-- The comparison square of affine opens: restricting `V` to a chart of `X` is `Spec` of the
restriction map of coordinate rings. -/
theorem specMap_chartHom_fromSpec (j : 𝓔.J) :
    Spec.map (CommRingCat.ofHom (chartHom 𝓔 V j)) ≫ (isAffineOpen X (𝓔.chart j)).fromSpec =
      (isAffineOpen_chartOpen 𝓔 V j).fromSpec ≫ V.inclusion := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec V.inclusion (isAffineOpen X (𝓔.chart j))
    (isAffineOpen_chartOpen 𝓔 V j) (le_refl (V.inclusion ⁻¹ᵁ (𝓔.chart j).1))
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h

/-- The trace of `V` on the `j`-th chart is the fibre product of that chart with `V` over `X`. -/
theorem isPullback_chartHom (j : 𝓔.J) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartHom 𝓔 V j)))
      (isAffineOpen_chartOpen 𝓔 V j).fromSpec (isAffineOpen X (𝓔.chart j)).fromSpec
      V.inclusion := by
  refine (isPullback_morphismRestrict V.inclusion (𝓔.chart j).1).of_iso
    (isAffineOpen_chartOpen 𝓔 V j).isoSpec (isAffineOpen X (𝓔.chart j)).isoSpec
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (isAffineOpen X (𝓔.chart j)).fromSpec, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec, specMap_chartHom_fromSpec,
      IsAffineOpen.isoSpec_hom_fromSpec_assoc, morphismRestrict_ι]
  · simp
  · simp
  · simp

/-! ## The charts of the restricted bundle -/

/-- The projection of the `j`-th chart of the restricted bundle onto the trace of `V` on the
chart. -/
noncomputable abbrev chartQuotProj (j : 𝓔.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) ⟶
      Spec Γ(V.scheme, chartOpen 𝓔 V j) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C :
    Γ(V.scheme, chartOpen 𝓔 V j) →+* MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))

/-- The closed immersion of the `j`-th chart of the restricted bundle into the `j`-th chart of
the total space, given by restricting the coefficients of a polynomial to `V`. -/
noncomputable abbrev chartQuotι (j : 𝓔.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) ⟶
      Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := ι) (chartHom 𝓔 V j)))

/-- The structural map of the `j`-th chart of the total space, written through `fromSpec`. -/
theorem specMap_C_fromSpec_chart (j : 𝓔.J) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.C :
        Γ(X, (𝓔.chart j).1) →+* MvPolynomial ι Γ(X, (𝓔.chart j).1))) ≫
        (isAffineOpen X (𝓔.chart j)).fromSpec = 𝓔.chartι j ≫ 𝓔.proj := by
  rw [← (𝓔.isPullback_chart j).w, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    MvPolynomial.algebraMap_eq]

/-- The `j`-th chart of the restricted bundle is the fibre product of the `j`-th chart of the
total space with `V` over `X`. -/
theorem isPullback_chartQuot (j : 𝓔.J) :
    IsPullback (chartQuotι 𝓔 V j)
      (chartQuotProj 𝓔 V j ≫ (isAffineOpen_chartOpen 𝓔 V j).fromSpec)
      (𝓔.chartι j ≫ 𝓔.proj) V.inclusion := by
  rw [← specMap_C_fromSpec_chart 𝓔 j]
  exact (isPullback_specMap_mvPolynomialMap ι (chartHom 𝓔 V j)).paste_vert
    (isPullback_chartHom 𝓔 V j)

/-- The restriction of `V` to the `j`-th chart is a closed subscheme of the `j`-th chart. -/
instance isClosedImmersion_chartQuotι (j : 𝓔.J) :
    _root_.AlgebraicGeometry.IsClosedImmersion (chartQuotι 𝓔 V j) :=
  MorphismProperty.of_isPullback (isPullback_chartQuot 𝓔 V j).flip inferInstance

/-- The `j`-th chart of the restricted bundle, an affine space over the coordinate ring of the
trace of `V` on the chart. -/
noncomputable def chartιRestrict (j : 𝓔.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) ⟶
      restrictScheme 𝓔 V :=
  pullback.lift (chartQuotι 𝓔 V j ≫ 𝓔.chartι j)
    (chartQuotProj 𝓔 V j ≫ (isAffineOpen_chartOpen 𝓔 V j).fromSpec)
    (by rw [Category.assoc]; exact (isPullback_chartQuot 𝓔 V j).w)

@[reassoc (attr := simp)]
theorem chartιRestrict_restrictι (j : 𝓔.J) :
    chartιRestrict 𝓔 V j ≫ restrictι 𝓔 V = chartQuotι 𝓔 V j ≫ 𝓔.chartι j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem chartιRestrict_restrictProj (j : 𝓔.J) :
    chartιRestrict 𝓔 V j ≫ restrictProj 𝓔 V =
      chartQuotProj 𝓔 V j ≫ (isAffineOpen_chartOpen 𝓔 V j).fromSpec :=
  pullback.lift_snd _ _ _

/-- The `j`-th chart of the restricted bundle is the part of `E_V` lying over the `j`-th chart
of the total space. -/
theorem isPullback_chartιRestrict (j : 𝓔.J) :
    IsPullback (chartιRestrict 𝓔 V j) (chartQuotι 𝓔 V j) (restrictι 𝓔 V) (𝓔.chartι j) := by
  refine IsPullback.of_right ?_ (chartιRestrict_restrictι 𝓔 V j) (isPullback_restrict 𝓔 V).flip
  rw [chartιRestrict_restrictProj]
  exact (isPullback_chartQuot 𝓔 V j).flip

/-- The charts of the restricted bundle are open immersions. -/
instance isOpenImmersion_chartιRestrict (j : 𝓔.J) :
    _root_.AlgebraicGeometry.IsOpenImmersion (chartιRestrict 𝓔 V j) :=
  MorphismProperty.of_isPullback (isPullback_chartιRestrict 𝓔 V j).flip inferInstance

/-! ## The charts cover the restricted bundle -/

/-- An isomorphism of schemes is surjective on points. -/
theorem surjective_base_of_iso {A B : Scheme.{u}} (e : A ≅ B) :
    Function.Surjective e.hom.base := fun b =>
  ⟨e.inv.base b, by
    have h : (e.inv ≫ e.hom).base b = b := by rw [e.inv_hom_id]; rfl
    exact h⟩

/-- The `j`-th chart of the restricted bundle is exactly the part of `E_V` lying over the `j`-th
chart of the total space. -/
theorem opensRange_chartιRestrict (j : 𝓔.J) :
    (chartιRestrict 𝓔 V j).opensRange = restrictι 𝓔 V ⁻¹ᵁ (𝓔.chartι j).opensRange := by
  refine TopologicalSpace.Opens.ext ?_
  have he : (isPullback_chartιRestrict 𝓔 V j).isoPullback.hom ≫
      pullback.fst (restrictι 𝓔 V) (𝓔.chartι j) = chartιRestrict 𝓔 V j :=
    IsPullback.isoPullback_hom_fst _
  have hrange : Set.range (chartιRestrict 𝓔 V j).base =
      Set.range (pullback.fst (restrictι 𝓔 V) (𝓔.chartι j)).base := by
    rw [← he]
    exact (surjective_base_of_iso _).range_comp _
  rw [Scheme.Hom.coe_opensRange, hrange,
    AlgebraicGeometry.Scheme.Pullback.range_fst (restrictι 𝓔 V) (𝓔.chartι j)]
  rfl

/-- The charts of the restricted bundle cover it. -/
theorem iSup_opensRange_chartιRestrict :
    ⨆ j, (chartιRestrict 𝓔 V j).opensRange = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have hx : (restrictι 𝓔 V).base x ∈ (⊤ : 𝓔.totalSpace.Opens) := trivial
  rw [← 𝓔.iSup_opensRange_chartι] at hx
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  rw [opensRange_chartιRestrict]
  exact hj

/-- Every point of the restricted bundle lies in one of its charts. -/
theorem exists_chartιRestrict (x : restrictScheme 𝓔 V) :
    ∃ (j : 𝓔.J) (q : Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))),
      (chartιRestrict 𝓔 V j).base q = x := by
  have hx : x ∈ (⊤ : (restrictScheme 𝓔 V).Opens) := trivial
  rw [← iSup_opensRange_chartιRestrict 𝓔 V] at hx
  obtain ⟨j, q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨j, q, hq⟩

/-! ## Local structure: Noetherian and reduced -/

/-- The cover of the restricted bundle by its charts. -/
noncomputable abbrev restrictCover : (restrictScheme 𝓔 V).OpenCover :=
  Scheme.Cover.mkOfCovers 𝓔.J
    (fun j => Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))))
    (fun j => chartιRestrict 𝓔 V j) (exists_chartιRestrict 𝓔 V)

/-- The coordinate ring of the trace of `V` on a chart is Noetherian. -/
theorem isNoetherianRing_chartOpen (j : 𝓔.J) :
    IsNoetherianRing Γ(V.scheme, chartOpen 𝓔 V j) :=
  _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian
    ⟨chartOpen 𝓔 V j, isAffineOpen_chartOpen 𝓔 V j⟩

/-- The restricted bundle is locally Noetherian: every chart is an affine space over a
Noetherian ring. -/
instance isLocallyNoetherian_restrictScheme [Finite ι] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian (restrictScheme 𝓔 V) := by
  rw [_root_.AlgebraicGeometry.isLocallyNoetherian_iff_openCover (restrictCover 𝓔 V)]
  intro j
  have hB : IsNoetherianRing Γ(V.scheme, chartOpen 𝓔 V j) := isNoetherianRing_chartOpen 𝓔 V j
  have h : IsNoetherianRing (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)) :=
    MvPolynomial.isNoetherianRing
  exact _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.2 h

/-- The restricted bundle is reduced: every chart is a polynomial algebra over the reduced
coordinate ring of the trace of `V`. -/
instance isReduced_restrictScheme :
    _root_.AlgebraicGeometry.IsReduced (restrictScheme 𝓔 V) := by
  apply +allowSynthFailures _root_.AlgebraicGeometry.isReduced_of_isReduced_stalk
  intro x
  obtain ⟨j, q, rfl⟩ := exists_chartιRestrict 𝓔 V x
  have hred : _root_.IsReduced
      ((Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))).presheaf.stalk q) :=
    _root_.AlgebraicGeometry.isReduced_stalk_of_isReduced _ q
  exact isReduced_of_injective ((chartιRestrict 𝓔 V j).stalkMap q).hom
    ((ConcreteCategory.bijective_of_isIso ((chartιRestrict 𝓔 V j).stalkMap q)).injective)

/-! ## Irreducibility and integrality -/

/-- The generic point of the integral closed subscheme `V`, viewed as a point of `X`. -/
noncomputable def genericBasePoint : X := V.inclusion.base (genericPoint V.scheme)

/-- Every point of `V` is a specialisation of its generic point, seen in `X`. -/
theorem specializes_genericBasePoint (v : V.scheme) :
    genericBasePoint V ⤳ V.inclusion.base v :=
  (genericPoint_specializes v).map V.inclusion.continuous

/-- The generic point of the fibre of the bundle over the generic point of `V`. -/
noncomputable def genericBundlePoint : 𝓔.totalSpace :=
  BundlePullbackGlobal.bundlePoint 𝓔 (genericBasePoint V)

/-- A point of the total space lies in the restricted bundle exactly when its image in `X` lies
in `V`. -/
theorem mem_range_restrictι_iff (q : 𝓔.totalSpace) :
    q ∈ Set.range (restrictι 𝓔 V).base ↔
      𝓔.proj.base q ∈ Set.range V.inclusion.base := by
  rw [show (restrictι 𝓔 V) = pullback.fst 𝓔.proj V.inclusion from rfl,
    AlgebraicGeometry.Scheme.Pullback.range_fst 𝓔.proj V.inclusion]
  exact Iff.rfl

/-- The generic point of the fibre over the generic point of `V` specialises to every point of
the total space lying over `V`. -/
theorem specializes_genericBundlePoint (q : 𝓔.totalSpace)
    (hq : 𝓔.proj.base q ∈ Set.range V.inclusion.base) :
    genericBundlePoint 𝓔 V ⤳ q := by
  obtain ⟨v, hv⟩ := hq
  have hmemtop : 𝓔.proj.base q ∈ (⊤ : X.Opens) := trivial
  rw [← 𝓔.iSup_chart] at hmemtop
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmemtop
  have hspec : genericBasePoint V ⤳ 𝓔.proj.base q := hv ▸ specializes_genericBasePoint V v
  have hmem : genericBasePoint V ∈ (𝓔.chart j).1 :=
    hspec.mem_open (𝓔.chart j).1.isOpen hj
  have hx : (𝓔.chart j).1.ι.base (⟨genericBasePoint V, hmem⟩ : (𝓔.chart j).1.toScheme) =
      genericBasePoint V := rfl
  have h := (BundlePullbackGlobal.chartBundlePoint_specializes_iff 𝓔 j
    ⟨genericBasePoint V, hmem⟩ q hj).2 (by rw [hx]; exact hspec)
  rw [← BundlePullbackGlobal.bundlePoint_chart 𝓔 j ⟨genericBasePoint V, hmem⟩, hx] at h
  exact h

/-- The generic point of the fibre over the generic point of `V` lies in the restricted
bundle. -/
theorem mem_range_genericBundlePoint :
    genericBundlePoint 𝓔 V ∈ Set.range (restrictι 𝓔 V).base := by
  rw [mem_range_restrictι_iff, genericBundlePoint, BundlePullbackGlobal.proj_bundlePoint]
  exact ⟨genericPoint V.scheme, rfl⟩

/-- The generic point of the restricted bundle. -/
noncomputable def genericRestrictPoint : restrictScheme 𝓔 V :=
  (mem_range_genericBundlePoint 𝓔 V).choose

@[simp]
theorem restrictι_genericRestrictPoint :
    (restrictι 𝓔 V).base (genericRestrictPoint 𝓔 V) = genericBundlePoint 𝓔 V :=
  (mem_range_genericBundlePoint 𝓔 V).choose_spec

/-- The distinguished point of the restricted bundle specialises to every point of it. -/
theorem genericRestrictPoint_specializes (x : restrictScheme 𝓔 V) :
    genericRestrictPoint 𝓔 V ⤳ x := by
  have hind : Topology.IsInducing (restrictι 𝓔 V).base :=
    (restrictι 𝓔 V).isClosedEmbedding.isInducing
  rw [← hind.specializes_iff, restrictι_genericRestrictPoint]
  refine specializes_genericBundlePoint 𝓔 V _ ?_
  have hmem : (restrictι 𝓔 V).base x ∈ Set.range (restrictι 𝓔 V).base := ⟨x, rfl⟩
  rw [mem_range_restrictι_iff] at hmem
  exact hmem

/-- The closure of the distinguished point is the whole restricted bundle. -/
theorem closure_genericRestrictPoint :
    closure ({genericRestrictPoint 𝓔 V} : Set (restrictScheme 𝓔 V)) = Set.univ :=
  Set.eq_univ_of_forall fun x => (genericRestrictPoint_specializes 𝓔 V x).mem_closure

/-- The restricted bundle is irreducible. -/
instance irreducibleSpace_restrictScheme : IrreducibleSpace (restrictScheme 𝓔 V) := by
  rw [irreducibleSpace_def, Set.top_eq_univ, ← closure_genericRestrictPoint 𝓔 V]
  exact isIrreducible_singleton.closure

/-- The restricted bundle is integral. -/
instance isIntegral_restrictScheme :
    _root_.AlgebraicGeometry.IsIntegral (restrictScheme 𝓔 V) :=
  _root_.AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-! ## The restricted bundle as an integral closed subscheme -/

/-- The restricted bundle `E_V = E ×_X V`, packaged as an integral locally Noetherian closed
subscheme of the total space of `𝓔`. -/
noncomputable def restrictSubscheme [Finite ι] : IntegralClosedSubscheme 𝓔.totalSpace where
  scheme := restrictScheme 𝓔 V
  inclusion := restrictι 𝓔 V

@[simp]
theorem restrictSubscheme_scheme [Finite ι] :
    (restrictSubscheme 𝓔 V).scheme = restrictScheme 𝓔 V := rfl

@[simp]
theorem restrictSubscheme_inclusion [Finite ι] :
    (restrictSubscheme 𝓔 V).inclusion = restrictι 𝓔 V := rfl

/-- The generic point of the restricted bundle is the distinguished point constructed above. -/
theorem genericPoint_restrictScheme :
    genericPoint (restrictScheme 𝓔 V) = genericRestrictPoint 𝓔 V :=
  IsGenericPoint.eq (genericPoint_spec _) (closure_genericRestrictPoint 𝓔 V)

/-- The generic point of the restricted bundle is the generic point of the fibre of `E` over the
generic point of `V`. -/
theorem restrictι_genericPoint :
    (restrictι 𝓔 V).base (genericPoint (restrictScheme 𝓔 V)) =
      BundlePullbackGlobal.bundlePoint 𝓔 (V.inclusion.base (genericPoint V.scheme)) := by
  rw [genericPoint_restrictScheme, restrictι_genericRestrictPoint]
  rfl

/-- The function-field map of the dominant projection `E_V → V`. -/
noncomputable def pullbackFunctionField :
    V.scheme.functionField →+* (restrictScheme 𝓔 V).functionField :=
  _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (restrictProj 𝓔 V)

/-! ## The quotient presentation of a chart -/

/-- The restriction map of coordinate rings of a chart is surjective, because `V` is a closed
subscheme. -/
theorem surjective_chartHom (j : 𝓔.J) : Function.Surjective (chartHom 𝓔 V j) :=
  Scheme.Hom.app_surjective V.inclusion (𝓔.chart j).1 (isAffineOpen X (𝓔.chart j))

/-- The ideal of the trace of `V` on the `j`-th chart. -/
noncomputable abbrev chartIdeal (j : 𝓔.J) : Ideal Γ(X, (𝓔.chart j).1) :=
  RingHom.ker (chartHom 𝓔 V j)

/-- The coordinate ring of the trace of `V` on the `j`-th chart is the quotient of the chart
coordinate ring by the ideal of `V`. -/
noncomputable def chartQuotEquiv (j : 𝓔.J) :
    Γ(X, (𝓔.chart j).1) ⧸ chartIdeal 𝓔 V j ≃+* Γ(V.scheme, chartOpen 𝓔 V j) :=
  RingHom.quotientKerEquivOfSurjective (surjective_chartHom 𝓔 V j)

@[simp]
theorem chartQuotEquiv_mk (j : 𝓔.J) (a : Γ(X, (𝓔.chart j).1)) :
    chartQuotEquiv 𝓔 V j (Ideal.Quotient.mk (chartIdeal 𝓔 V j) a) = chartHom 𝓔 V j a := rfl

/-- The `j`-th chart of the restricted bundle, identified with the affine space over the
quotient ring `Γ(X, U_j) ⧸ p_j` used by the affine theory of `BundlePullbackChow.lean`. -/
noncomputable def chartQuotSpecIso (j : 𝓔.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) ≅
      Spec (CommRingCat.of (MvPolynomial ι (Γ(X, (𝓔.chart j).1) ⧸ chartIdeal 𝓔 V j))) :=
  Scheme.Spec.mapIso
    (RingEquiv.toCommRingCatIso (MvPolynomial.mapEquiv ι (chartQuotEquiv 𝓔 V j))).op

/-- `chartQuotSpecIso` is the spectrum of the polynomial extension of the quotient
presentation. -/
theorem chartQuotSpecIso_hom (j : 𝓔.J) :
    (chartQuotSpecIso 𝓔 V j).hom =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.mapEquiv ι (chartQuotEquiv 𝓔 V j)).toRingHom) := rfl

/-- Through the identification `chartQuotSpecIso`, the inclusion of the `j`-th chart of the
restricted bundle into the `j`-th chart of the total space is the closed immersion
`VectorBundle.quotBundleImmersion` of the affine theory. -/
theorem chartQuotSpecIso_hom_quotBundleImmersion (j : 𝓔.J) :
    (chartQuotSpecIso 𝓔 V j).hom ≫
        VectorBundle.quotBundleImmersion
          (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) (chartIdeal 𝓔 V j) =
      chartQuotι 𝓔 V j := by
  rw [chartQuotSpecIso_hom, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change MvPolynomial.map (chartQuotEquiv 𝓔 V j).toRingHom
      (MvPolynomial.map (Ideal.Quotient.mk (chartIdeal 𝓔 V j)) a) =
    MvPolynomial.map (chartHom 𝓔 V j) a
  rw [MvPolynomial.map_map]
  rfl

end Global

end BundleOverSubscheme

end GromovWitten.AlgebraicGeometry.IntersectionTheory
