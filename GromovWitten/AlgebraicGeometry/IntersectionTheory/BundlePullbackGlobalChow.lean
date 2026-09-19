/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleOverSubscheme
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackChow

/-!
# Descent of the global bundle pullback to rational Chow groups

This file finishes the construction of the flat pullback along the total space of a global vector
bundle `𝓔 : BundleData X ι` begun in `BundlePullbackGlobal.lean` and continued in
`BundleOverSubscheme.lean`: it proves the comparison `π^* (ι_V)_* div(f) = (ι_{E_V})_* div(π_V^* f)`
of cycles and deduces that the global flat pullback descends to rational Chow groups.

## Contents

* `dominantFunctionFieldMap_comp`: the function-field pullback of a composite of dominant
  morphisms of integral schemes is the composite of the function-field pullbacks.  This is a
  general fact missing from the repository and from Mathlib.
* `VectorBundle.comap_mvPolynomialMap_map_C`: for a surjective ring map `φ`, the contraction along
  `MvPolynomial.map φ` of an extended ideal is the extension of the contracted ideal, and
  `VectorBundle.bundlePoint_specMap`: consequently `Spec (MvPolynomial.map φ)` carries the generic
  point of a fibre to the generic point of the fibre over the image point.
* `BundleOverSubscheme.restrictι_chartιRestrict_bundlePoint`: the chart description of the generic
  points of the fibres of the restricted bundle `E_V = E ×_X V`.
* `BundleOverSubscheme.pullbackFunctionField_chart`: the chart compatibility of the function-field
  map `π_V^*` of `BundleOverSubscheme.pullbackFunctionField` with the affine one of
  `GradedCone.projection`.
* `BundleOverSubscheme.pullbackBundle_pushforward_principalCycle`: the cycle identity
  `π^* (ι_V)_* div(f) = (ι_{E_V})_* div(π_V^* f)`.
* `BundleOverSubscheme.totalRationalRelations_pullbackBundleGlobal`,
  `BundleOverSubscheme.ofBundleGlobal`, `BundleOverSubscheme.chowPullbackBundleGlobal`: the
  descent of the global flat pullback to rational Chow groups.
* `BundleOverSubscheme.openImmersionPullback_chowPullbackBundleGlobal`: the resulting map of Chow
  groups restricts on every trivialising chart to the affine `VectorBundle.chowPullbackBundle`.

## Method

Unlike the affine theory, the cycle identity is *not* proved by restricting both sides to the
trivialising charts of `E`.  Both sides are pushforwards along the closed immersion
`restrictι 𝓔 V : E_V ⟶ E` with the pulled-back weight, so they vanish off the range of
`restrictι` and are determined by their values at the points `restrictι w`; the identity is
therefore a pointwise statement on `E_V`, which is checked in a chart of `E_V` (the charts of
`E_V` are affine spaces over the coordinate rings of the traces of `V`, by
`BundleOverSubscheme.isPullback_chartιRestrict`).  Only there is the affine comparison
`VectorBundle.pullbackBundle_principalCycle` used.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
open GromovWitten.AlgebraicGeometry.GlobalBlowup (isAffineOpen)

/-! ## Functoriality of the function-field pullback -/

/-- The stalk map of a composite, transported along the images of a point under the two factors.
This is the `eqToHom`-decorated form of `AlgebraicGeometry.Scheme.stalkMap_comp` needed to
compare the function-field pullbacks of `f`, `g` and `f ≫ g` at the generic points. -/
theorem stalkMap_comp_eqToHom {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (a : A) (b : B) (c : C) (hb : f.base a = b) (hc : g.base b = c)
    (h1 : C.presheaf.stalk c = C.presheaf.stalk (g.base (f.base a)))
    (h2 : C.presheaf.stalk c = C.presheaf.stalk (g.base b))
    (h3 : B.presheaf.stalk b = B.presheaf.stalk (f.base a)) :
    eqToHom h1 ≫ (f ≫ g).stalkMap a =
      (eqToHom h2 ≫ g.stalkMap b) ≫ eqToHom h3 ≫ f.stalkMap a := by
  subst hb
  subst hc
  simp [_root_.AlgebraicGeometry.Scheme.Hom.stalkMap_comp]

/-- The canonical function-field pullback of a composite of dominant morphisms of integral
schemes is the composite of the canonical function-field pullbacks. -/
theorem dominantFunctionFieldMap_comp {A B C : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral A] [_root_.AlgebraicGeometry.IsIntegral B]
    [_root_.AlgebraicGeometry.IsIntegral C] (f : A ⟶ B) (g : B ⟶ C)
    [_root_.AlgebraicGeometry.IsDominant f] [_root_.AlgebraicGeometry.IsDominant g] :
    _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (f ≫ g) =
      (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).comp
        (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap g) := by
  have key := stalkMap_comp_eqToHom f g (genericPoint A) (genericPoint B) (genericPoint C)
    (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant f)
    (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant g)
    (congrArg (fun z ↦ C.presheaf.stalk z)
      (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant (f ≫ g)).symm)
    (congrArg (fun z ↦ C.presheaf.stalk z)
      (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant g).symm)
    (congrArg (fun z ↦ B.presheaf.stalk z)
      (_root_.AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant f).symm)
  exact congrArg CommRingCat.Hom.hom key

/-- The canonical function-field pullback depends only on the underlying morphism: the
`IsDominant` instance is a proposition. -/
theorem dominantFunctionFieldMap_congr {A B : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral A] [_root_.AlgebraicGeometry.IsIntegral B]
    {p q : A ⟶ B} [_root_.AlgebraicGeometry.IsDominant p]
    [_root_.AlgebraicGeometry.IsDominant q] (h : p = q) :
    _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap p =
      _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap q := by
  subst h
  rfl

/-! ## Extended primes along a surjection of base rings -/

namespace VectorBundle

/-- The contraction along `MvPolynomial.map φ` of the extension of an ideal `P` is the extension
of the contraction of `P` along `φ`, for a surjective ring map `φ`.  Geometrically: the affine
space over a closed subscheme of the base is exactly the preimage of that closed subscheme, on the
points which carry the flat pullback of a cycle. -/
theorem comap_mvPolynomialMap_map_C {σ R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (P : Ideal S) :
    Ideal.comap (MvPolynomial.map (σ := σ) φ)
        (Ideal.map (MvPolynomial.C : S →+* MvPolynomial σ S) P) =
      Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) (Ideal.comap φ P) := by
  have hPQ : Ideal.map φ (Ideal.comap φ P) = P := Ideal.map_comap_of_surjective _ hφ P
  have hcomp : (MvPolynomial.map (σ := σ) φ).comp
      (MvPolynomial.C : R →+* MvPolynomial σ R) =
      (MvPolynomial.C : S →+* MvPolynomial σ S).comp φ := by
    refine RingHom.ext fun r ↦ ?_
    simp
  have hmapK : Ideal.map (MvPolynomial.map (σ := σ) φ)
      (Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) (Ideal.comap φ P)) =
      Ideal.map (MvPolynomial.C : S →+* MvPolynomial σ S) P := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hPQ]
  have hker : RingHom.ker φ ≤ Ideal.comap φ P := by
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker.1 hx]
    exact P.zero_mem
  rw [← hmapK, Ideal.comap_map_of_surjective _ (MvPolynomial.map_surjective φ hφ),
    ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, sup_eq_left]
  exact Ideal.map_mono hker

/-- `Spec` of the coefficient-wise extension of a surjection of base rings carries the generic
point of the fibre of a trivial affine bundle over `y` to the generic point of the fibre over the
image of `y`. -/
theorem bundlePoint_specMap {σ R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (y : ↥(Spec (CommRingCat.of S))) :
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := σ) φ))).base
        (bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial σ S)) y) =
      bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial σ R))
        ((Spec.map (CommRingCat.ofHom φ)).base y) := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (MvPolynomial.map (σ := σ) φ)
      (Ideal.map (algebraMap S (MvPolynomial σ S)) (y : PrimeSpectrum S).asIdeal) =
    Ideal.map (algebraMap R (MvPolynomial σ R)) (Ideal.comap φ (y : PrimeSpectrum S).asIdeal)
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq]
  exact comap_mvPolynomialMap_map_C φ hφ _

end VectorBundle

/-! ## The charts of the restricted bundle -/

/-- Two equal morphisms of schemes act in the same way on points. -/
theorem base_congr_apply {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (a : A) :
    f.base a = g.base a := by
  rw [h]

/-- The global flat pullback of a cycle vanishes at a point of the total space which is not the
generic point of the fibre over its own image. -/
theorem pullbackBundle_eq_zero_of_ne {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)
    (c : AlgebraicCycle X ℚ) {q : 𝓔.totalSpace}
    (hq : q ≠ BundlePullbackGlobal.bundlePoint 𝓔 (𝓔.proj.base q)) :
    BundlePullbackGlobal.pullbackBundle 𝓔 c q = 0 := by
  refine BundlePullbackGlobal.pullbackBundle_eq_zero_of_notMem 𝓔 c ?_
  rintro ⟨x, rfl⟩
  exact hq (by rw [BundlePullbackGlobal.proj_bundlePoint])

/-- The affine flat pullback of a cycle vanishes at a point of the total space which is not the
generic point of the fibre over its own image. -/
theorem pullbackBundleAffine_eq_zero_of_ne {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {σ : Type u} (e : A ≃ₐ[R] MvPolynomial σ R)
    (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) {v : ↥(Spec (CommRingCat.of A))}
    (hv : v ≠ VectorBundle.bundlePoint e ((GradedCone.projection R A).base v)) :
    AlgebraicCycle.pullbackBundle e c v = 0 := by
  refine AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e c ?_
  rintro ⟨x, rfl⟩
  exact hv (by rw [VectorBundle.projection_base_bundlePoint])

namespace BundleOverSubscheme

section Global

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι) (V : IntegralClosedSubscheme X)

/-- The projection of the `j`-th chart of the restricted bundle `E_V = E ×_X V` is the projection
of the trivial affine bundle over the coordinate ring of the trace of `V` on that chart. -/
theorem chartQuotProj_eq_projection (j : 𝓔.J) :
    chartQuotProj 𝓔 V j =
      GradedCone.projection Γ(V.scheme, chartOpen 𝓔 V j)
        (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)) := by
  simp [GradedCone.projection, MvPolynomial.algebraMap_eq]

/-- The `j`-th chart of the restricted bundle sits inside the `j`-th chart of the total space. -/
theorem restrictι_chartιRestrict (j : 𝓔.J)
    (v : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))))) :
    (restrictι 𝓔 V).base ((chartιRestrict 𝓔 V j).base v) =
      (𝓔.chartι j).base ((chartQuotι 𝓔 V j).base v) :=
  base_congr_apply (chartιRestrict_restrictι 𝓔 V j) v

/-- The projection to `V` of a point of the `j`-th chart of the restricted bundle. -/
theorem restrictProj_chartιRestrict (j : 𝓔.J)
    (v : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))))) :
    (restrictProj 𝓔 V).base ((chartιRestrict 𝓔 V j).base v) =
      (isAffineOpen_chartOpen 𝓔 V j).fromSpec.base ((chartQuotProj 𝓔 V j).base v) :=
  base_congr_apply (chartιRestrict_restrictProj 𝓔 V j) v

/-- The image in `X` of a point of the `j`-th chart of the restricted bundle. -/
theorem proj_restrictι_chartιRestrict (j : 𝓔.J)
    (v : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))))) :
    𝓔.proj.base ((restrictι 𝓔 V).base ((chartιRestrict 𝓔 V j).base v)) =
      V.inclusion.base ((isAffineOpen_chartOpen 𝓔 V j).fromSpec.base
        ((chartQuotProj 𝓔 V j).base v)) := by
  have hcomm : 𝓔.proj.base ((restrictι 𝓔 V).base ((chartιRestrict 𝓔 V j).base v)) =
      V.inclusion.base ((restrictProj 𝓔 V).base ((chartιRestrict 𝓔 V j).base v)) :=
    base_congr_apply (isPullback_restrict 𝓔 V).w ((chartιRestrict 𝓔 V j).base v)
  rw [hcomm, restrictProj_chartιRestrict]

/-- The generic point of the fibre of the restricted bundle over a point of the `j`-th chart,
computed in that chart, is the generic point of the fibre of the whole bundle over the image of
that point in `X`. -/
theorem restrictι_chartιRestrict_bundlePoint (j : 𝓔.J)
    (y : ↥(Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝓔 V j)))) :
    (restrictι 𝓔 V).base ((chartιRestrict 𝓔 V j).base
        (VectorBundle.bundlePoint
          (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) y)) =
      BundlePullbackGlobal.bundlePoint 𝓔
        (V.inclusion.base ((isAffineOpen_chartOpen 𝓔 V j).fromSpec.base y)) := by
  set bp := VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) y with hbp
  have h1 : (restrictι 𝓔 V).base ((chartιRestrict 𝓔 V j).base bp) =
      (𝓔.chartι j).base ((chartQuotι 𝓔 V j).base bp) :=
    base_congr_apply (chartιRestrict_restrictι 𝓔 V j) bp
  have h2 : (restrictProj 𝓔 V).base ((chartιRestrict 𝓔 V j).base bp) =
      (isAffineOpen_chartOpen 𝓔 V j).fromSpec.base ((chartQuotProj 𝓔 V j).base bp) :=
    base_congr_apply (chartιRestrict_restrictProj 𝓔 V j) bp
  have h3 : (chartQuotProj 𝓔 V j).base bp = y := by
    rw [chartQuotProj_eq_projection, hbp]
    exact VectorBundle.projection_base_bundlePoint _ y
  have h4 : 𝓔.proj.base ((restrictι 𝓔 V).base ((chartιRestrict 𝓔 V j).base bp)) =
      V.inclusion.base ((isAffineOpen_chartOpen 𝓔 V j).fromSpec.base y) := by
    have hcomm : 𝓔.proj.base ((restrictι 𝓔 V).base ((chartιRestrict 𝓔 V j).base bp)) =
        V.inclusion.base ((restrictProj 𝓔 V).base ((chartιRestrict 𝓔 V j).base bp)) :=
      base_congr_apply (isPullback_restrict 𝓔 V).w ((chartιRestrict 𝓔 V j).base bp)
    rw [hcomm, h2, h3]
  have h5 : (chartQuotι 𝓔 V j).base bp =
      VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        ((Spec.map (CommRingCat.ofHom (chartHom 𝓔 V j))).base y) :=
    VectorBundle.bundlePoint_specMap (chartHom 𝓔 V j) (surjective_chartHom 𝓔 V j) y
  have h7 : VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        ((GradedCone.projection Γ(X, (𝓔.chart j).1)
          (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base ((chartQuotι 𝓔 V j).base bp)) =
      (chartQuotι 𝓔 V j).base bp := by
    rw [h5, VectorBundle.projection_base_bundlePoint]
  have h6 := BundlePullbackGlobal.bundlePoint_proj_chartι 𝓔 j ((chartQuotι 𝓔 V j).base bp)
  rw [← h1, h4] at h6
  rw [h1, h6, h7]

/-! ## Instances on a chart meeting the closed subscheme -/

section Chart

variable (j : 𝓔.J)

/-- If the `j`-th chart of the restricted bundle has a point over the base, then the trace of `V`
on the `j`-th chart of `X` is nonempty. -/
theorem nonempty_chartOpen
    (y : ↥(Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝓔 V j)))) :
    Nonempty (chartOpen 𝓔 V j) := by
  refine ⟨⟨(isAffineOpen_chartOpen 𝓔 V j).fromSpec.base y, ?_⟩⟩
  have hmem : (isAffineOpen_chartOpen 𝓔 V j).fromSpec.base y ∈
      Set.range (isAffineOpen_chartOpen 𝓔 V j).fromSpec.base := ⟨y, rfl⟩
  rw [(isAffineOpen_chartOpen 𝓔 V j).range_fromSpec] at hmem
  exact hmem

variable [Nonempty (chartOpen 𝓔 V j)]

/-- The coordinate ring of a nonempty trace of an integral scheme is nontrivial. -/
instance nontrivial_chartOpen : Nontrivial Γ(V.scheme, chartOpen 𝓔 V j) :=
  inferInstance

/-- The spectrum of the coordinate ring of a nonempty trace is nonempty. -/
instance nonempty_specChartOpen :
    Nonempty ↥(Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝓔 V j))) :=
  PrimeSpectrum.nonempty_iff_nontrivial.2 inferInstance

/-- The `j`-th chart of the restricted bundle is nonempty when the trace of `V` is. -/
instance nonempty_chartBundle :
    Nonempty ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))) :=
  ⟨VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))
    (Nonempty.some inferInstance)⟩

/-- The coordinate ring of a nonempty trace of the integral scheme `V` is a domain. -/
instance isDomain_chartOpen : IsDomain Γ(V.scheme, chartOpen 𝓔 V j) :=
  _root_.AlgebraicGeometry.IsIntegral.component_integral (chartOpen 𝓔 V j)

/-- The affine chart of the restricted bundle is an integral scheme. -/
instance isIntegral_chartBundle :
    _root_.AlgebraicGeometry.IsIntegral
      (Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))) :=
  inferInstance

/-- The spectrum of the coordinate ring of a nonempty trace is integral. -/
instance isIntegral_specChartOpen :
    _root_.AlgebraicGeometry.IsIntegral
      (Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝓔 V j))) :=
  inferInstance

/-- The affine chart of the restricted bundle is locally Noetherian. -/
instance isLocallyNoetherian_chartBundle [Finite ι] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian
      (Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))) := by
  have hB : IsNoetherianRing Γ(V.scheme, chartOpen 𝓔 V j) := isNoetherianRing_chartOpen 𝓔 V j
  have h : IsNoetherianRing (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)) :=
    MvPolynomial.isNoetherianRing
  exact _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.2 h

/-- The spectrum of the coordinate ring of the trace is locally Noetherian. -/
instance isLocallyNoetherian_specChartOpen :
    _root_.AlgebraicGeometry.IsLocallyNoetherian
      (Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝓔 V j))) :=
  _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.2 (isNoetherianRing_chartOpen 𝓔 V j)

/-- The affine open immersion of a nonempty trace of `V` is dominant, because `V` is
irreducible. -/
instance isDominant_fromSpec_chartOpen :
    _root_.AlgebraicGeometry.IsDominant (isAffineOpen_chartOpen 𝓔 V j).fromSpec :=
  _root_.AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _

/-- The projection of the `j`-th chart of the restricted bundle onto the trace of `V` is
dominant. -/
instance isDominant_chartQuotProj :
    _root_.AlgebraicGeometry.IsDominant (chartQuotProj 𝓔 V j) := by
  rw [chartQuotProj_eq_projection]
  exact VectorBundle.isDominant_projection
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))

/-- The open immersion of the `j`-th chart of the restricted bundle is dominant, because the
restricted bundle is irreducible. -/
instance isDominant_chartιRestrict :
    _root_.AlgebraicGeometry.IsDominant (chartιRestrict 𝓔 V j) :=
  _root_.AlgebraicGeometry.Scheme.isDominant_of_isOpenImmersion _

/-! ### The function field of the restricted bundle, read in a chart -/

/-- Over a chart meeting `V`, the function-field pullback `pullbackFunctionField` of the
restricted bundle is the function-field pullback of the affine projection
`GradedCone.projection` applied to the restriction of the rational function to the trace of `V`.
This is the chart compatibility of `BundleOverSubscheme.pullbackFunctionField`. -/
theorem pullbackFunctionField_chart (f : V.scheme.functionField) :
    _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (chartιRestrict 𝓔 V j)
        (pullbackFunctionField 𝓔 V f) =
      _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (chartQuotProj 𝓔 V j)
        (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
          (isAffineOpen_chartOpen 𝓔 V j).fromSpec f) := by
  have e1 := dominantFunctionFieldMap_comp (chartιRestrict 𝓔 V j) (restrictProj 𝓔 V)
  have e2 := dominantFunctionFieldMap_comp (chartQuotProj 𝓔 V j)
    (isAffineOpen_chartOpen 𝓔 V j).fromSpec
  have e3 := dominantFunctionFieldMap_congr (chartιRestrict_restrictProj 𝓔 V j)
  exact RingHom.congr_fun (e1.symm.trans (e3.trans e2)) f

/-- The principal divisor of the pulled-back rational function, restricted to the `j`-th chart of
the restricted bundle, is the affine bundle pullback of the principal divisor of the restriction
of the rational function to the trace of `V` on the `j`-th chart. -/
theorem principalCycle_pullbackFunctionField_chart [Finite ι] (f : V.scheme.functionField)
    (v : ↥(Spec (CommRingCat.of (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))))) :
    (restrictScheme 𝓔 V).principalCycle (pullbackFunctionField 𝓔 V f)
        ((chartιRestrict 𝓔 V j).base v) =
      AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))
        ((Spec (CommRingCat.of Γ(V.scheme, chartOpen 𝓔 V j))).principalCycle
          (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
            (isAffineOpen_chartOpen 𝓔 V j).fromSpec f)) v := by
  have hnoethB : IsNoetherianRing Γ(V.scheme, chartOpen 𝓔 V j) :=
    isNoetherianRing_chartOpen 𝓔 V j
  have hnoethA : IsNoetherianRing (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)) :=
    MvPolynomial.isNoetherianRing
  have hdom : _root_.AlgebraicGeometry.IsDominant
      (GradedCone.projection Γ(V.scheme, chartOpen 𝓔 V j)
        (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) :=
    VectorBundle.isDominant_projection
      (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))
  have hd := VectorBundle.pullbackBundle_principalCycle
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))
    (_root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
      (isAffineOpen_chartOpen 𝓔 V j).fromSpec f)
  have hb := _root_.AlgebraicGeometry.Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion
    (chartιRestrict 𝓔 V j) v (pullbackFunctionField 𝓔 V f)
  have he : _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap (chartQuotProj 𝓔 V j) =
      _root_.AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        (GradedCone.projection Γ(V.scheme, chartOpen 𝓔 V j)
          (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) :=
    dominantFunctionFieldMap_congr (chartQuotProj_eq_projection 𝓔 V j)
  rw [hd, _root_.AlgebraicGeometry.Scheme.principalCycle_apply,
    _root_.AlgebraicGeometry.Scheme.principalCycle_apply, ← hb,
    pullbackFunctionField_chart 𝓔 V j f, he]


end Chart

/-! ## The cycle identity -/

/-- The value, at a point of the restricted bundle, of the global flat pullback of a principal
divisor pushed forward from the integral closed subscheme `V`: it is the order of vanishing of
the pulled-back rational function.  This is the pointwise form of
`pullbackBundle_pushforward_principalCycle`. -/
theorem pullbackBundle_pushforward_principalCycle_apply [Finite ι]
    (dimX : DimensionFunction X) (f : V.scheme.functionField) (w : restrictScheme 𝓔 V) :
    BundlePullbackGlobal.pullbackBundle 𝓔
        (V.pushforward dimX (V.scheme.principalCycle f)) ((restrictι 𝓔 V).base w) =
      (restrictScheme 𝓔 V).principalCycle (pullbackFunctionField 𝓔 V f) w := by
  obtain ⟨j, v, rfl⟩ := exists_chartιRestrict 𝓔 V w
  have hne : Nonempty (chartOpen 𝓔 V j) :=
    nonempty_chartOpen 𝓔 V j ((chartQuotProj 𝓔 V j).base v)
  rw [principalCycle_pullbackFunctionField_chart 𝓔 V j f v]
  by_cases hv : v = VectorBundle.bundlePoint
      (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j)))
      ((GradedCone.projection Γ(V.scheme, chartOpen 𝓔 V j)
        (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))).base v)
  · obtain ⟨y, rfl⟩ : ∃ y, v = VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))) y := ⟨_, hv⟩
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint,
      restrictι_chartιRestrict_bundlePoint,
      BundlePullbackGlobal.pullbackBundle_apply_bundlePoint]
    have hpush : V.pushforward dimX (V.scheme.principalCycle f)
        (V.inclusion.base ((isAffineOpen_chartOpen 𝓔 V j).fromSpec.base y)) =
        V.scheme.principalCycle f ((isAffineOpen_chartOpen 𝓔 V j).fromSpec.base y) :=
      AlgebraicCycle.map_closedImmersion_apply_image V.inclusion (dimX : X → ℤ) _ _
    rw [hpush, _root_.AlgebraicGeometry.Scheme.principalCycle_apply,
      _root_.AlgebraicGeometry.Scheme.principalCycle_apply,
      _root_.AlgebraicGeometry.Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion]
  · rw [pullbackBundleAffine_eq_zero_of_ne _ _ hv]
    refine pullbackBundle_eq_zero_of_ne 𝓔 _ ?_
    intro hcon
    refine hv ?_
    rw [proj_restrictι_chartιRestrict 𝓔 V j v,
      ← restrictι_chartιRestrict_bundlePoint 𝓔 V j ((chartQuotProj 𝓔 V j).base v)] at hcon
    have h2 := (chartιRestrict 𝓔 V j).isOpenEmbedding.injective
      ((restrictι 𝓔 V).isClosedEmbedding.injective hcon)
    have h3 : (chartQuotProj 𝓔 V j).base v =
        (GradedCone.projection Γ(V.scheme, chartOpen 𝓔 V j)
          (MvPolynomial ι Γ(V.scheme, chartOpen 𝓔 V j))).base v :=
      base_congr_apply (chartQuotProj_eq_projection 𝓔 V j) v
    rw [← h3]
    exact h2


/-- The comparison `π^* (ι_V)_* div(f) = (ι_{E_V})_* div(π_V^* f)` of cycles on the total space of
a global vector bundle: the flat pullback of a principal divisor supported on an integral closed
subscheme `V` of the base is the principal divisor of the pulled-back rational function, supported
on the restricted bundle `E_V = E ×_X V`. -/
theorem pullbackBundle_pushforward_principalCycle [Finite ι]
    (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)
    (f : V.scheme.functionField) :
    BundlePullbackGlobal.pullbackBundle 𝓔 (V.pushforward dimX (V.scheme.principalCycle f)) =
      (restrictSubscheme 𝓔 V).pushforward dimE
        ((restrictScheme 𝓔 V).principalCycle (pullbackFunctionField 𝓔 V f)) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  dsimp only
  by_cases hq : q ∈ Set.range (restrictι 𝓔 V).base
  · obtain ⟨w, rfl⟩ := hq
    have hR : (restrictSubscheme 𝓔 V).pushforward dimE
        ((restrictScheme 𝓔 V).principalCycle (pullbackFunctionField 𝓔 V f))
        ((restrictι 𝓔 V).base w) =
        (restrictScheme 𝓔 V).principalCycle (pullbackFunctionField 𝓔 V f) w :=
      AlgebraicCycle.map_closedImmersion_apply_image (restrictι 𝓔 V) (dimE : _ → ℤ) _ w
    rw [hR]
    exact pullbackBundle_pushforward_principalCycle_apply 𝓔 V dimX f w
  · have hnot : 𝓔.proj.base q ∉ Set.range V.inclusion.base := fun hmem ↦
      hq ((mem_range_restrictι_iff 𝓔 V q).2 hmem)
    have hRzero : (restrictSubscheme 𝓔 V).pushforward dimE
        ((restrictScheme 𝓔 V).principalCycle (pullbackFunctionField 𝓔 V f)) q = 0 :=
      AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range (restrictι 𝓔 V)
        (dimE : _ → ℤ) _ q hq
    rw [hRzero]
    by_cases hb : q = BundlePullbackGlobal.bundlePoint 𝓔 (𝓔.proj.base q)
    · have hval := BundlePullbackGlobal.pullbackBundle_apply_bundlePoint 𝓔
        (V.pushforward dimX (V.scheme.principalCycle f)) (𝓔.proj.base q)
      rw [← hb] at hval
      rw [hval]
      exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range V.inclusion
        (dimX : X → ℤ) _ _ hnot
    · exact pullbackBundle_eq_zero_of_ne 𝓔 _ hb

end Global

/-! ## Descent of the global flat pullback to rational Chow groups -/

section Descent

variable {X : Scheme.{u}} {ι : Type u} [Finite ι] (𝓔 : BundleData X ι)
  (dimX : DimensionFunction X) (dimE : DimensionFunction 𝓔.totalSpace)

/-- The flat pullback along the total space of a global vector bundle of the principal divisor of
a rational function on an arbitrary integral closed subscheme of the base is a
rational-equivalence relation on the total space: it is the principal divisor of the pulled-back
rational function on the restricted bundle. -/
theorem pullbackBundle_divisor_mem_totalRationalRelations (g : RationalFunctionGenerator X) :
    BundlePullbackGlobal.pullbackBundle 𝓔 (g.divisor dimX) ∈
      totalRationalRelations 𝓔.totalSpace dimE := by
  refine Submodule.subset_span ⟨⟨restrictSubscheme 𝓔 g.subspace,
    Units.map (pullbackFunctionField 𝓔 g.subspace).toMonoidHom g.function⟩, ?_⟩
  exact (pullbackBundle_pushforward_principalCycle 𝓔 g.subspace dimX dimE
    (g.function : g.subspace.scheme.functionField)).symm

/-- The global flat pullback carries the canonical span of principal divisors on the base into the
canonical span on the total space. -/
theorem totalRationalRelations_pullbackBundleGlobal :
    Submodule.map (BundlePullbackGlobal.pullbackBundleLinear 𝓔)
        (totalRationalRelations X dimX) ≤ totalRationalRelations 𝓔.totalSpace dimE := by
  rw [totalRationalRelations, Submodule.map_span, Submodule.span_le]
  rintro z ⟨c, ⟨g, rfl⟩, rfl⟩
  exact pullbackBundle_divisor_mem_totalRationalRelations 𝓔 dimX dimE g

variable (hshift : ∀ x, dimE (BundlePullbackGlobal.bundlePoint 𝓔 x) = dimX x + (Nat.card ι : ℤ))
  (i : ℤ)

/-- The dimension-graded global flat pullback along a rank-`r` vector bundle, together with its
proved preservation of the canonical rational-equivalence subspaces. -/
noncomputable def ofBundleGlobal
    (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ))) :
    RX.DescendingMap RE where
  onCycles := BundlePullbackGlobal.flatPullbackBundleGlobal 𝓔 dimX dimE hshift i
  maps_relations := by
    cases RX
    cases RE
    intro z hz
    change BundlePullbackGlobal.pullbackBundle 𝓔 z.1 ∈
      totalRationalRelations 𝓔.totalSpace dimE
    exact totalRationalRelations_pullbackBundleGlobal 𝓔 dimX dimE ⟨z.1, hz, rfl⟩

/-- Flat pullback along the total space of a global vector bundle of rank `r` on
dimension-graded rational Chow groups, `A_i(X) →ₗ[ℚ] A_{i+r}(E)`. -/
noncomputable def chowPullbackBundleGlobal
    (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ))) :
    RX.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  RationalEquivalenceSystem.DescendingMap.inducedMap RX
    (ofBundleGlobal 𝓔 dimX dimE hshift i RX RE)

/-- The Chow-group global flat pullback is induced by the flat pullback of dimension-graded
cycles. -/
@[simp]
theorem chowPullbackBundleGlobal_quotientMap
    (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)))
    (z : cyclesOfDimension X dimX i) :
    chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE (RX.quotientMap z) =
      RE.quotientMap (BundlePullbackGlobal.flatPullbackBundleGlobal 𝓔 dimX dimE hshift i z) :=
  rfl

/-- Chart comparison on rational Chow groups: restricting the global flat pullback to the `j`-th
trivialising chart of the total space is the affine flat pullback of the restriction of the class
on the base.  The dimension gradings of the two charts are assumed to be the restrictions of the
global ones (`hU`, `hP`), exactly as for `cyclesOfDimension.flatPullbackOpen`. -/
theorem openImmersionPullback_chowPullbackBundleGlobal (j : 𝓔.J)
    [IsNoetherianRing Γ(X, (𝓔.chart j).1)]
    (dimU : DimensionFunction (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))))
    (dimP : DimensionFunction (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))))
    (hU : ∀ y, dimU y =
      dimX (((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι).base y))
    (hP : ∀ q, dimP q = dimE ((𝓔.chartι j).base q))
    (RX : RationalEquivalenceSystem X dimX i)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE (i + (Nat.card ι : ℤ)))
    (RU : RationalEquivalenceSystem (Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) dimU i)
    (RP : RationalEquivalenceSystem
      (Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1)))) dimP
      (i + (Nat.card ι : ℤ))) :
    (RationalEquivalenceSystem.DescendingMap.openImmersionPullback RE (𝓔.chartι j) hP RP).comp
        (chowPullbackBundleGlobal 𝓔 dimX dimE hshift i RX RE) =
      (VectorBundle.chowPullbackBundle
          (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) dimU dimP i RU RP).comp
        (RationalEquivalenceSystem.DescendingMap.openImmersionPullback RX
          ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι) hU RU) := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z⟩ := c
  exact congrArg RP.quotientMap (Subtype.ext
    (BundlePullbackGlobal.pullbackOpen_chartι_pullbackBundle 𝓔 j (z : AlgebraicCycle X ℚ)))

end Descent

end BundleOverSubscheme

end GromovWitten.AlgebraicGeometry.IntersectionTheory
