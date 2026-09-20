/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalConeAffine

/-!
# Gluing the global cone from local obstruction models

`VirtualFundamentalClass/GlobalCone.lean` defines `GlobalConeData 𝓔 φ`, the datum of a global
cone `C ⊆ E = 𝓔.totalSpace` together with identifications of its sections over every chart
`𝓔.chart j` with the affine resolved cone `ResolvedCone.ring (φ j)`.  Round 17 constructed such a
datum only for an affine base with a single chart (`GlobalConeAffine.globalConeData`).

This file starts from *local* data instead: affine obstruction models `φ j` on the charts of a
bundle `𝓔 : BundleData X ι`, identifications `chartBundle j` of the bundle algebra over the chart
with `Sym(E⁻¹)`, and the single geometric hypothesis that the resolved-cone ideals of two charts
agree over every affine open of their overlap.  This is packaged as `LocalConeData 𝓔 φ`.

## Main definitions

* `LocalConeData` — the local data, with the overlap hypothesis `LocalConeData.compat`.
* `LocalConeData.chartIdeal j : Ideal (𝓔.algebra.ring (𝓔.chart j))` — the resolved-cone ideal of
  the chart `j` pulled back to the bundle algebra along `chartBundle j`.
* `LocalConeData.coneChart j`, `LocalConeData.coneChartι j` — the affine cone of the chart `j` and
  its (affine) morphism to the total space; it is the composite of a closed immersion into the
  affine chart of `E` with the open immersion `affineι`.
* `LocalConeData.kerIdeal` — the ideal sheaf of the glued cone, defined as the kernel of the
  morphism `∐ j, coneChart j ⟶ E` assembled from the charts, and
  `LocalConeData.coneScheme`, `LocalConeData.coneι` — the associated closed subscheme of `E`.
* `bundleOpen 𝓔 W`, `gammaEquiv 𝓔 W : 𝓔.algebra.ring W ≃+* Γ(𝓔.totalSpace, bundleOpen 𝓔 W)` —
  the affine open of the total space over an affine open `W` of the base, and the identification
  of its sections with the bundle algebra; `chartOpen 𝓔 j` and `chartGammaEquiv 𝓔 j` are the
  chart case `W = 𝓔.chart j`.

## Main results

* `LocalConeData.quasiCompact_sigmaDesc` — the assembled morphism is quasi-compact when `𝓔.J` is
  finite and `X` is quasi-separated, so `Scheme.Hom.ker_apply` applies to it.
* `LocalConeData.ker_coneChartι_appLE` — the kernel of the restriction of a section of the bundle
  algebra to the affine cone of *its own* chart is exactly `chartIdeal j`.
* `LocalConeData.coneChartι_app_chartOpen_eq_zero` — the heart of the gluing: a section of
  `chartIdeal j` restricts to zero on the affine cone of *every* chart `i`.  It is checked on the
  affine opens `W` of the overlap `𝓔.chart i ⊓ 𝓔.chart j`, which cover the relevant part of the
  cone of `i`, and over such a `W` the two chart ideals agree by `LocalConeData.compat`.
* `LocalConeData.kerIdeal_chart` — the chart computation of the glued ideal: for finite `𝓔.J`
  and quasi-separated `X`, over the chart `j` the ideal of the glued cone is exactly the
  transport of `chartIdeal j` along `chartGammaEquiv 𝓔 j`.
* `LocalConeData.chartConeEquiv'` and `LocalConeData.chartConeEquiv'_symm_mk` — the sections of
  the glued cone over the chart `j` are the affine resolved-cone ring `ResolvedCone.ring (φ j)`,
  compatibly with `Ideal.Quotient.mk`.  This is the field `chartCone` of a
  `GlobalCone.GlobalConeData`.  (`chartConeEquiv` is the version taking the chart computation as
  a hypothesis `hker`; `chartConeEquiv'` discharges it with `kerIdeal_chart`.)
* `LocalConeData.ofAffine` — the round-17 affine datum is a `LocalConeData` with a single chart,
  for which `compat` is trivial.  No separate comparison of cycles is required: the chart
  comparison `GlobalCone.GlobalConeData.coneCycleAt_eq_resolvedConeCycleAt` holds for every
  `GlobalConeData`.

## What is not proved here

The assembly of a full `GlobalCone.GlobalConeData 𝓔 φ` out of `coneScheme` and `coneι`.  It
needs the quasi-coherent algebra `AlgebraData.ofAffineHom (coneι ≫ 𝓔.proj)` and the morphism of
algebra data `RelativeSpec.Hom.ofOverRelativeSpec`, which are not yet available.
-/

universe u

-- As in `ResolvedCone.lean` and `GlobalCone.lean`: the ring instances of the tensor products
-- occurring in `ResolvedCone.ideal` need one more level of pending instance problems.
set_option maxSynthPendingDepth 5

-- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
-- type of affine opens; as in `RelativeSpec.lean` the unifier is told not to respect
-- transparency in this file.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace RelativeSpec
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualFundamentalClass

namespace VirtualClass.ConeGluing

noncomputable section

/-- Local data for a global cone: affine obstruction models on the charts of a vector bundle,
together with the identifications of the bundle algebra with the affine models and the
compatibility of the resolved-cone ideals on overlaps.

The last field `compat` is the only geometric hypothesis: it says that for two charts `i`, `j`
and an affine open `W` of `X` contained in both charts, the two resolved-cone ideals extend to
the *same* ideal of `𝓔.algebra.ring W`.  In applications it is derived from the invariance
results for `ResolvedCone.ideal` (`Independence.ideal_map_bundleEquiv`,
`HomotopyInvariance.ideal_congr`, `LocalisationCone.ideal_map_bundleRingEquiv`). -/
structure LocalConeData {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
    (𝓔 : BundleData X ι) {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
    {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
    (φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))) where
  /-- The identification of the sections over a chart with the affine model of the base. -/
  chartBase : ∀ j, Γ(X, (𝓔.chart j).1) ≃+* (R j ⧸ I j)
  /-- The identification of the bundle algebra over a chart with `Sym(E⁻¹)`. -/
  chartBundle : ∀ j, 𝓔.algebra.ring (𝓔.chart j) ≃+* ResolvedCone.bundleRing (φ j)
  /-- `chartBundle` is a map of algebras over the base, via `chartBase`. -/
  chartBundle_algebraMap : ∀ (j : 𝓔.J) (r : Γ(X, (𝓔.chart j).1)),
    chartBundle j (algebraMap Γ(X, (𝓔.chart j).1) (𝓔.algebra.ring (𝓔.chart j)) r) =
      algebraMap (R j ⧸ I j) (ResolvedCone.bundleRing (φ j)) (chartBase j r)
  /-- **The gluing hypothesis**: over every affine open of the overlap of two charts the two
  resolved-cone ideals extend to the same ideal of the bundle algebra. -/
  compat : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i) (hj : W ≤ 𝓔.chart j),
    ((ResolvedCone.ideal (φ i)).comap (chartBundle i).toRingHom).map (𝓔.algebra.map hi) =
      ((ResolvedCone.ideal (φ j)).comap (chartBundle j).toRingHom).map (𝓔.algebra.map hj)

/-- The `appLE` of a morphism from `⊤` to `⊤` is the map on global sections. -/
theorem appLE_top_eq_appTop {Y Z : Scheme.{u}} (f : Y ⟶ Z) (e : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE, Scheme.Hom.appTop, Subsingleton.elim (homOfLE e) (𝟙 _)]
  simp

/-- The `appLE` from an open to the whole of an affine source, computed along a factorisation
`f ≫ g = k` of the morphism through an intermediate scheme. -/
theorem appLE_top_comp {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (hk : f ≫ g = k) (U : W.Opens) (e : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ U)
    (e' : (⊤ : Y.Opens) ≤ k ⁻¹ᵁ U) :
    k.appLE U ⊤ e' = g.appLE U ⊤ e ≫ f.appTop := by
  subst hk
  rw [← appLE_top_eq_appTop f le_top, Scheme.Hom.appLE_comp_appLE]

section TotalSpace

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-- The affine pieces of a relative `Spec` are compatible with the transition maps. -/
theorem specMap_map_affineι (𝒜 : AlgebraData X) {W V : X.affineOpens} (h : W ≤ V) :
    Spec.map (CommRingCat.ofHom (𝒜.map h)) ≫ affineι X 𝒜 V = affineι X 𝒜 W :=
  Limits.colimit.w (gluingData X 𝒜).functor (homOfLE h)

/-- The total space of a bundle over a quasi-separated base is quasi-separated: the projection
is an affine, hence separated, morphism. -/
instance quasiSeparatedSpace_totalSpace [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace 𝓔.totalSpace :=
  have : IsSeparated 𝓔.proj := IsSeparated.of_isAffineHom 𝓔.proj
  quasiSeparatedSpace_of_quasiSeparated 𝓔.proj

/-- The affine open of the total space lying over an affine open of the base. -/
def bundleOpen (W : X.affineOpens) : 𝓔.totalSpace.affineOpens :=
  ⟨𝓔.proj ⁻¹ᵁ W.1, W.2.preimage 𝓔.proj⟩

@[simp]
theorem bundleOpen_coe (W : X.affineOpens) : (bundleOpen 𝓔 W).1 = 𝓔.proj ⁻¹ᵁ W.1 := rfl

/-- The affine pieces of the total space are monotone in the affine open of the base. -/
theorem bundleOpen_mono {W V : X.affineOpens} (h : W ≤ V) :
    (bundleOpen 𝓔 W).1 ≤ (bundleOpen 𝓔 V).1 := fun _ hx ↦ h hx

/-- The affine piece of the total space over an affine open is the range of `affineι`. -/
theorem opensRange_affineι_bundleOpen (W : X.affineOpens) :
    (affineι X 𝓔.algebra W).opensRange = (bundleOpen 𝓔 W).1 :=
  opensRange_affineι X 𝓔.algebra W

/-- The affine open of the total space lying over the chart `j`. -/
abbrev chartOpen (j : 𝓔.J) : 𝓔.totalSpace.affineOpens := bundleOpen 𝓔 (𝓔.chart j)

/-- The chart open of the total space is the affine open over the chart. -/
theorem chartOpen_eq_bundleOpen (j : 𝓔.J) : chartOpen 𝓔 j = bundleOpen 𝓔 (𝓔.chart j) := rfl

@[simp]
theorem chartOpen_coe (j : 𝓔.J) : (chartOpen 𝓔 j).1 = 𝓔.proj ⁻¹ᵁ (𝓔.chart j).1 := rfl

/-- The affine chart of the total space is the range of the affine piece of the relative `Spec`. -/
theorem opensRange_affineι_chart (j : 𝓔.J) :
    (affineι X 𝓔.algebra (𝓔.chart j)).opensRange = 𝓔.proj ⁻¹ᵁ (𝓔.chart j).1 :=
  opensRange_affineι X 𝓔.algebra (𝓔.chart j)

/-- The affine piece over an affine open is the whole preimage of that open. -/
theorem affineι_preimage_bundleOpen (W : X.affineOpens) :
    affineι X 𝓔.algebra W ⁻¹ᵁ (bundleOpen 𝓔 W).1 = ⊤ := by
  rw [← opensRange_affineι_bundleOpen]
  exact Scheme.Hom.preimage_opensRange _

/-- The affine chart of the total space is the whole preimage of the chart of `X`. -/
theorem affineι_preimage_chartOpen (j : 𝓔.J) :
    affineι X 𝓔.algebra (𝓔.chart j) ⁻¹ᵁ (chartOpen 𝓔 j).1 = ⊤ :=
  affineι_preimage_bundleOpen 𝓔 (𝓔.chart j)

/-- The comparison map from the sections of the total space over an affine open of the base to
the bundle algebra of that open. -/
def gammaHom (W : X.affineOpens) :
    Γ(𝓔.totalSpace, (bundleOpen 𝓔 W).1) ⟶ CommRingCat.of (𝓔.algebra.ring W) :=
  (affineι X 𝓔.algebra W).appLE (bundleOpen 𝓔 W).1 ⊤ (affineι_preimage_bundleOpen 𝓔 W).ge ≫
    (Scheme.ΓSpecIso (CommRingCat.of (𝓔.algebra.ring W))).hom

/-- The comparison map over an affine open is an isomorphism. -/
instance isIso_gammaHom (W : X.affineOpens) : IsIso (gammaHom 𝓔 W) := by
  have h₁ : IsIso ((affineι X 𝓔.algebra W).app (bundleOpen 𝓔 W).1) :=
    Scheme.Hom.isIso_app _ _ (opensRange_affineι_bundleOpen 𝓔 W).ge
  have h₂ : IsIso ((Spec (CommRingCat.of (𝓔.algebra.ring W))).presheaf.map
      (homOfLE (affineι_preimage_bundleOpen 𝓔 W).ge).op) := by
    rw [Subsingleton.elim (homOfLE (affineι_preimage_bundleOpen 𝓔 W).ge)
      (eqToHom (affineι_preimage_bundleOpen 𝓔 W).symm)]
    infer_instance
  rw [gammaHom, Scheme.Hom.appLE]
  infer_instance

/-- The sections of the total space over an affine open of the base are the bundle algebra of
that open.  This is the identification of the sections of a relative `Spec` over the preimage of
an affine open (`RelativeSpec.ringEquivGamma`). -/
def gammaEquiv (W : X.affineOpens) :
    𝓔.algebra.ring W ≃+* Γ(𝓔.totalSpace, (bundleOpen 𝓔 W).1) :=
  (asIso (gammaHom 𝓔 W)).symm.commRingCatIsoToRingEquiv

/-- `gammaHom` is the inverse of `gammaEquiv`. -/
@[simp]
theorem gammaHom_gammaEquiv (W : X.affineOpens) (a : 𝓔.algebra.ring W) :
    gammaHom 𝓔 W (gammaEquiv 𝓔 W a) = a :=
  (gammaEquiv 𝓔 W).symm_apply_apply a

/-- `gammaEquiv` is the inverse of `gammaHom`. -/
@[simp]
theorem gammaEquiv_gammaHom (W : X.affineOpens) (a : Γ(𝓔.totalSpace, (bundleOpen 𝓔 W).1)) :
    gammaEquiv 𝓔 W (gammaHom 𝓔 W a) = a :=
  (gammaEquiv 𝓔 W).apply_symm_apply a

/-- The comparison maps are compatible with the restriction maps of the total space and the
transition maps of the bundle algebra. -/
theorem gammaHom_res {W V : X.affineOpens} (h : W ≤ V) :
    𝓔.totalSpace.presheaf.map (homOfLE (bundleOpen_mono 𝓔 h)).op ≫ gammaHom 𝓔 W =
      gammaHom 𝓔 V ≫ CommRingCat.ofHom (𝓔.algebra.map h) := by
  rw [gammaHom, gammaHom, ← Category.assoc, Scheme.Hom.map_appLE,
    appLE_top_comp (Spec.map (CommRingCat.ofHom (𝓔.algebra.map h)))
      (affineι X 𝓔.algebra V) (affineι X 𝓔.algebra W) (specMap_map_affineι 𝓔.algebra h)
      (bundleOpen 𝓔 V).1 (affineι_preimage_bundleOpen 𝓔 V).ge,
    Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]

/-- Elementwise form of `gammaHom_res`: the transition maps of the bundle algebra are the
restriction maps of the total space. -/
theorem gammaEquiv_map {W V : X.affineOpens} (h : W ≤ V) (a : 𝓔.algebra.ring V) :
    gammaEquiv 𝓔 W (𝓔.algebra.map h a) =
      𝓔.totalSpace.presheaf.map (homOfLE (bundleOpen_mono 𝓔 h)).op (gammaEquiv 𝓔 V a) := by
  have key : gammaHom 𝓔 W (𝓔.totalSpace.presheaf.map (homOfLE (bundleOpen_mono 𝓔 h)).op
      (gammaEquiv 𝓔 V a)) = 𝓔.algebra.map h a := by
    rw [← CommRingCat.comp_apply, gammaHom_res, CommRingCat.comp_apply, gammaHom_gammaEquiv]
    rfl
  rw [← key, gammaEquiv_gammaHom]

/-- The comparison map from the sections of the total space over the chart `j` to the bundle
algebra of that chart. -/
abbrev chartGammaHom (j : 𝓔.J) :
    Γ(𝓔.totalSpace, (chartOpen 𝓔 j).1) ⟶ CommRingCat.of (𝓔.algebra.ring (𝓔.chart j)) :=
  gammaHom 𝓔 (𝓔.chart j)

/-- The comparison map of the chart `j` is an isomorphism. -/
instance isIso_chartGammaHom (j : 𝓔.J) : IsIso (chartGammaHom 𝓔 j) :=
  isIso_gammaHom 𝓔 (𝓔.chart j)

/-- The sections of the total space over the chart `j` are the bundle algebra of the chart.
This is the chart case of the identification of the sections of a relative `Spec` over the
preimage of an affine open (`RelativeSpec.ringEquivGamma`). -/
abbrev chartGammaEquiv (j : 𝓔.J) :
    𝓔.algebra.ring (𝓔.chart j) ≃+* Γ(𝓔.totalSpace, (chartOpen 𝓔 j).1) :=
  gammaEquiv 𝓔 (𝓔.chart j)

/-- `chartGammaHom` is the inverse of `chartGammaEquiv`. -/
@[simp]
theorem chartGammaHom_chartGammaEquiv (j : 𝓔.J) (a : 𝓔.algebra.ring (𝓔.chart j)) :
    chartGammaHom 𝓔 j (chartGammaEquiv 𝓔 j a) = a :=
  (chartGammaEquiv 𝓔 j).symm_apply_apply a

/-- `chartGammaEquiv` is the inverse of `chartGammaHom`. -/
@[simp]
theorem chartGammaEquiv_chartGammaHom (j : 𝓔.J) (a : Γ(𝓔.totalSpace, (chartOpen 𝓔 j).1)) :
    chartGammaEquiv 𝓔 j (chartGammaHom 𝓔 j a) = a :=
  (chartGammaEquiv 𝓔 j).apply_symm_apply a

end TotalSpace

namespace LocalConeData

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
  {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)}
  {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝓛 : LocalConeData 𝓔 φ)

/-- The resolved-cone ideal of the chart `j`, read inside the bundle algebra of that chart. -/
def chartIdeal (j : 𝓔.J) : Ideal (𝓔.algebra.ring (𝓔.chart j)) :=
  (ResolvedCone.ideal (φ j)).comap (𝓛.chartBundle j).toRingHom

/-- The gluing hypothesis, restated in terms of `chartIdeal`. -/
theorem map_chartIdeal (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i)
    (hj : W ≤ 𝓔.chart j) :
    (𝓛.chartIdeal i).map (𝓔.algebra.map hi) = (𝓛.chartIdeal j).map (𝓔.algebra.map hj) :=
  𝓛.compat i j W hi hj

/-- The image of `chartIdeal j` under the identification `chartBundle j` is the resolved-cone
ideal of the chart. -/
theorem map_chartIdeal_chartBundle (j : 𝓔.J) :
    (𝓛.chartIdeal j).map (𝓛.chartBundle j).toRingHom = ResolvedCone.ideal (φ j) :=
  Ideal.map_comap_of_surjective (𝓛.chartBundle j).toRingHom (𝓛.chartBundle j).surjective _

/-- The affine cone of the chart `j`: the spectrum of the bundle algebra of the chart modulo the
resolved-cone ideal. -/
abbrev coneChart (j : 𝓔.J) : Scheme.{u} :=
  Spec (CommRingCat.of (𝓔.algebra.ring (𝓔.chart j) ⧸ 𝓛.chartIdeal j))

/-- The closed immersion of the affine cone of the chart `j` into the affine chart of the total
space. -/
abbrev coneChartToAffine (j : 𝓔.J) :
    𝓛.coneChart j ⟶ Spec (CommRingCat.of (𝓔.algebra.ring (𝓔.chart j))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝓛.chartIdeal j)))

instance isClosedImmersion_coneChartToAffine (j : 𝓔.J) :
    IsClosedImmersion (𝓛.coneChartToAffine j) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The morphism from the affine cone of the chart `j` to the total space: the closed immersion
into the affine chart followed by the open immersion `affineι`. -/
def coneChartι (j : 𝓔.J) : 𝓛.coneChart j ⟶ 𝓔.totalSpace :=
  𝓛.coneChartToAffine j ≫ affineι X 𝓔.algebra (𝓔.chart j)

/-- The affine cone of a chart lies over that chart. -/
theorem coneChartι_proj (j : 𝓔.J) :
    𝓛.coneChartι j ≫ 𝓔.proj =
      𝓛.coneChartToAffine j ≫ projection X 𝓔.algebra (𝓔.chart j) ≫ (𝓔.chart j).1.ι := by
  rw [coneChartι, Category.assoc, BundleData.proj, affineι_toBase]

/-- The ideal sheaf of the glued cone: the kernel of the morphism from the disjoint union of the
affine cones of the charts. -/
def kerIdeal : 𝓔.totalSpace.IdealSheafData :=
  (Limits.Sigma.desc 𝓛.coneChartι).ker

/-- The glued cone, as a closed subscheme of the total space. -/
abbrev coneScheme : Scheme.{u} := 𝓛.kerIdeal.subscheme

/-- The closed immersion of the glued cone into the total space. -/
def coneι : 𝓛.coneScheme ⟶ 𝓔.totalSpace := 𝓛.kerIdeal.subschemeι

instance isClosedImmersion_coneι : IsClosedImmersion 𝓛.coneι := by
  rw [coneι]; infer_instance

/-- The disjoint union of the affine cones of finitely many charts is affine. -/
instance isAffine_sigmaConeChart [Finite 𝓔.J] : IsAffine (Limits.sigmaObj 𝓛.coneChart) :=
  inferInstanceAs (IsAffine (∐ 𝓛.coneChart))

/-- For a finite chart index and a quasi-separated base the morphism assembling the affine cones
of the charts is quasi-compact; this is what makes `Scheme.Hom.ker_apply` available for
`kerIdeal`. -/
instance quasiCompact_sigmaDesc [Finite 𝓔.J] [QuasiSeparatedSpace X] :
    QuasiCompact (Limits.Sigma.desc 𝓛.coneChartι) :=
  quasiCompact_of_compactSpace _

/-- The glued ideal sheaf is contained in the kernel of every chart cone. -/
theorem kerIdeal_le_ker_coneChartι (j : 𝓔.J) : 𝓛.kerIdeal ≤ (𝓛.coneChartι j).ker := by
  have h : Limits.Sigma.ι 𝓛.coneChart j ≫ Limits.Sigma.desc 𝓛.coneChartι = 𝓛.coneChartι j := by
    simp
  rw [kerIdeal, ← h]
  exact Scheme.Hom.le_ker_comp _ _

/-- The affine cone of the chart `j` lies entirely over the chart `j`. -/
theorem coneChartι_preimage_chartOpen (j : 𝓔.J) :
    𝓛.coneChartι j ⁻¹ᵁ (chartOpen 𝓔 j).1 = ⊤ := by
  have h : 𝓛.coneChartToAffine j ⁻¹ᵁ
      (affineι X 𝓔.algebra (𝓔.chart j) ⁻¹ᵁ (chartOpen 𝓔 j).1) = ⊤ := by
    rw [affineι_preimage_chartOpen]
    simp
  exact h

/-- Over its own chart, the affine cone of the chart `j` is the quotient of the bundle algebra
by the chart ideal. -/
theorem coneChartι_appLE (j : 𝓔.J) :
    (𝓛.coneChartι j).appLE (chartOpen 𝓔 j).1 ⊤ (𝓛.coneChartι_preimage_chartOpen j).ge =
      chartGammaHom 𝓔 j ≫ CommRingCat.ofHom (Ideal.Quotient.mk (𝓛.chartIdeal j)) ≫
        (Scheme.ΓSpecIso
          (CommRingCat.of (𝓔.algebra.ring (𝓔.chart j) ⧸ 𝓛.chartIdeal j))).inv := by
  have he : (⊤ : (𝓛.coneChart j).Opens) ≤ 𝓛.coneChartToAffine j ⁻¹ᵁ ⊤ := by simp
  rw [chartGammaHom, gammaHom, Category.assoc, Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc,
    ← appLE_top_eq_appTop (𝓛.coneChartToAffine j) he, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Transporting an ideal of the bundle algebra of a chart to the sections of the total space
over that chart. -/
theorem comap_chartGammaHom (j : 𝓔.J) (J : Ideal (𝓔.algebra.ring (𝓔.chart j))) :
    J.comap (chartGammaHom 𝓔 j).hom = J.map (chartGammaEquiv 𝓔 j).toRingHom := by
  refine le_antisymm (fun a ha ↦ ?_) (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_)
  · rw [← chartGammaEquiv_chartGammaHom 𝓔 j a]
    exact Ideal.mem_map_of_mem _ ha
  · change chartGammaHom 𝓔 j (chartGammaEquiv 𝓔 j x) ∈ J
    rw [chartGammaHom_chartGammaEquiv]
    exact hx

/-- The kernel of the restriction of a section of the bundle algebra to the affine cone of its
own chart is exactly the chart ideal. -/
theorem ker_coneChartι_appLE (j : 𝓔.J) :
    RingHom.ker ((𝓛.coneChartι j).appLE (chartOpen 𝓔 j).1 ⊤
        (𝓛.coneChartι_preimage_chartOpen j).ge).hom =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom := by
  have hinj : Function.Injective (Scheme.ΓSpecIso
      (CommRingCat.of (𝓔.algebra.ring (𝓔.chart j) ⧸ 𝓛.chartIdeal j))).inv.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  rw [𝓛.coneChartι_appLE j, ← Category.assoc, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hinj, CommRingCat.hom_comp, ← RingHom.comap_ker,
    ← comap_chartGammaHom]
  congr 1
  exact Ideal.mk_ker

/-- Sections in the glued ideal vanish on every affine cone chart. -/
theorem kerIdeal_ideal_le_ker_app (j : 𝓔.J) (U : 𝓔.totalSpace.affineOpens) :
    𝓛.kerIdeal.ideal U ≤ RingHom.ker ((𝓛.coneChartι j).app U.1).hom :=
  (𝓛.kerIdeal_le_ker_coneChartι j U).trans ((𝓛.coneChartι j).ideal_ker_le U)

/-- **One half of the chart computation of the glued ideal**: over the chart `j` the glued ideal
sheaf is contained in the transport of the chart ideal.  The reverse inclusion is the content of
the hypothesis `hker` of `toGlobalConeData`. -/
theorem kerIdeal_chart_le (j : 𝓔.J) :
    𝓛.kerIdeal.ideal (chartOpen 𝓔 j) ≤
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom := by
  rw [← 𝓛.ker_coneChartι_appLE j]
  intro a ha
  have h := 𝓛.kerIdeal_ideal_le_ker_app j (chartOpen 𝓔 j) ha
  rw [Scheme.Hom.appLE]
  simp only [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h ⊢
  rw [h, map_zero]

/-- Restricting a section along `coneChartι i` commutes with restricting it in the total
space. -/
theorem coneChartι_app_res (i : 𝓔.J) {U V : 𝓔.totalSpace.Opens} (h : V ≤ U)
    (h' : 𝓛.coneChartι i ⁻¹ᵁ V ≤ 𝓛.coneChartι i ⁻¹ᵁ U) (t : Γ(𝓔.totalSpace, U)) :
    (𝓛.coneChartι i).app V (𝓔.totalSpace.presheaf.map (homOfLE h).op t) =
      (𝓛.coneChart i).presheaf.map (homOfLE h').op ((𝓛.coneChartι i).app U t) := by
  rw [Subsingleton.elim (homOfLE h')
    ((TopologicalSpace.Opens.map (𝓛.coneChartι i).base).map (homOfLE h))]
  exact congrArg
    (fun g : Γ(𝓔.totalSpace, U) ⟶ Γ(𝓛.coneChart i, 𝓛.coneChartι i ⁻¹ᵁ V) ↦ g t)
    ((𝓛.coneChartι i).naturality (homOfLE h).op)

/-- A section of the chart ideal of the chart `i` restricts to zero on the affine cone of that
same chart. -/
theorem coneChartι_app_chartOpen_self (i : 𝓔.J) (z : 𝓔.algebra.ring (𝓔.chart i))
    (hz : z ∈ 𝓛.chartIdeal i) :
    (𝓛.coneChartι i).app (chartOpen 𝓔 i).1 (chartGammaEquiv 𝓔 i z) = 0 := by
  have hiso : IsIso ((𝓛.coneChart i).presheaf.map
      (homOfLE (𝓛.coneChartι_preimage_chartOpen i).ge).op) := by
    rw [Subsingleton.elim (homOfLE (𝓛.coneChartι_preimage_chartOpen i).ge)
      (eqToHom (𝓛.coneChartι_preimage_chartOpen i).symm)]
    infer_instance
  have h0 : ((𝓛.coneChartι i).appLE (chartOpen 𝓔 i).1 ⊤
      (𝓛.coneChartι_preimage_chartOpen i).ge).hom (chartGammaEquiv 𝓔 i z) = 0 := by
    rw [← RingHom.mem_ker, 𝓛.ker_coneChartι_appLE i]
    exact Ideal.mem_map_of_mem _ hz
  refine (ConcreteCategory.bijective_of_isIso ((𝓛.coneChart i).presheaf.map
    (homOfLE (𝓛.coneChartι_preimage_chartOpen i).ge).op)).1 ?_
  rw [map_zero, ← h0, Scheme.Hom.appLE, CommRingCat.comp_apply]

/-- Sections of the bundle algebra over an affine open `W` of the base contained in the chart `i`
which lie in the extension of `chartIdeal i` restrict to zero on the affine cone of that chart. -/
theorem coneChartι_app_bundleOpen_eq_zero (i : 𝓔.J) {W : X.affineOpens} (hi : W ≤ 𝓔.chart i)
    (y : 𝓔.algebra.ring W) (hy : y ∈ (𝓛.chartIdeal i).map (𝓔.algebra.map hi)) :
    (𝓛.coneChartι i).app (bundleOpen 𝓔 W).1 (gammaEquiv 𝓔 W y) = 0 := by
  have hker : (𝓛.chartIdeal i).map (𝓔.algebra.map hi) ≤
      RingHom.ker (((𝓛.coneChartι i).app (bundleOpen 𝓔 W).1).hom.comp
        (gammaEquiv 𝓔 W).toRingHom) := by
    refine Ideal.map_le_iff_le_comap.mpr fun z hz ↦ ?_
    change (𝓛.coneChartι i).app (bundleOpen 𝓔 W).1
      (gammaEquiv 𝓔 W (𝓔.algebra.map hi z)) = 0
    rw [gammaEquiv_map 𝓔 hi z,
      𝓛.coneChartι_app_res i (bundleOpen_mono 𝓔 hi) (fun _ hw ↦ bundleOpen_mono 𝓔 hi hw),
      𝓛.coneChartι_app_chartOpen_self i z hz, map_zero]
  exact RingHom.mem_ker.mp (hker hy)

/-- **The heart of the gluing.**  A section of the chart ideal of the chart `j` restricts to zero
on the affine cone of *every* chart `i`: the affine opens `W` of the overlap of the two charts
cover the part of the cone of `i` lying over the chart `j`, and over such a `W` the two chart
ideals agree by `LocalConeData.compat`. -/
theorem coneChartι_app_chartOpen_eq_zero (i j : 𝓔.J) (x : 𝓔.algebra.ring (𝓔.chart j))
    (hx : x ∈ 𝓛.chartIdeal j) :
    (𝓛.coneChartι i).app (chartOpen 𝓔 j).1 (chartGammaEquiv 𝓔 j x) = 0 := by
  refine (𝓛.coneChart i).IsSheaf.section_ext fun y hy ↦ ?_
  have hyj : 𝓔.proj.base ((𝓛.coneChartι i).base y) ∈ (𝓔.chart j).1 := hy
  have hyi : 𝓔.proj.base ((𝓛.coneChartι i).base y) ∈ (𝓔.chart i).1 := by
    have hmem : (𝓛.coneChartι i).base y ∈ (affineι X 𝓔.algebra (𝓔.chart i)).opensRange :=
      ⟨(𝓛.coneChartToAffine i).base y, rfl⟩
    rw [opensRange_affineι_chart] at hmem
    exact hmem
  obtain ⟨W, hWaff, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.isBasis_affineOpens
    (U := (𝓔.chart i).1 ⊓ (𝓔.chart j).1) ⟨hyi, hyj⟩
  have hi : (⟨W, hWaff⟩ : X.affineOpens) ≤ 𝓔.chart i := hWle.trans inf_le_left
  have hj : (⟨W, hWaff⟩ : X.affineOpens) ≤ 𝓔.chart j := hWle.trans inf_le_right
  refine ⟨𝓛.coneChartι i ⁻¹ᵁ (bundleOpen 𝓔 ⟨W, hWaff⟩).1, fun _ hz ↦ hj hz, hyW, ?_⟩
  rw [map_zero, ← 𝓛.coneChartι_app_res i (bundleOpen_mono 𝓔 hj)
    (fun _ hz ↦ bundleOpen_mono 𝓔 hj hz) (chartGammaEquiv 𝓔 j x), ← gammaEquiv_map 𝓔 hj x]
  refine 𝓛.coneChartι_app_bundleOpen_eq_zero i hi _ ?_
  rw [𝓛.map_chartIdeal i j ⟨W, hWaff⟩ hi hj]
  exact Ideal.mem_map_of_mem _ hx

/-- The affine cone of a chart is quasi-compact over the total space: it is affine, hence its
underlying space is compact. -/
instance quasiCompact_coneChartι [QuasiSeparatedSpace X] (i : 𝓔.J) :
    QuasiCompact (𝓛.coneChartι i) :=
  quasiCompact_of_compactSpace _

/-- The glued ideal sheaf is the intersection of the kernels of the affine cone charts: the
`coneChart i` form an open cover of their disjoint union. -/
theorem kerIdeal_ideal_eq_iInf [Finite 𝓔.J] [QuasiSeparatedSpace X]
    (U : 𝓔.totalSpace.affineOpens) :
    𝓛.kerIdeal.ideal U = ⨅ i, (𝓛.coneChartι i).ker.ideal U := by
  have h : ∀ i, (sigmaOpenCover 𝓛.coneChart).f i ≫ Limits.Sigma.desc 𝓛.coneChartι =
      𝓛.coneChartι i := by
    intro i
    simp
  rw [kerIdeal, ← Scheme.Hom.iInf_ker_openCover_map_comp_apply (Limits.Sigma.desc 𝓛.coneChartι)
    (sigmaOpenCover 𝓛.coneChart) U]
  exact iInf_congr fun i ↦ by rw [h i]

/-- **The chart computation of the glued ideal.**  Over the chart `j` the ideal of the glued cone
is exactly the transport of the chart ideal: the inclusion `≤` is `kerIdeal_chart_le`, and the
reverse inclusion is `coneChartι_app_chartOpen_eq_zero`, i.e. the overlap hypothesis `compat`. -/
theorem kerIdeal_chart [Finite 𝓔.J] [QuasiSeparatedSpace X] (j : 𝓔.J) :
    𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom := by
  refine le_antisymm (𝓛.kerIdeal_chart_le j) ?_
  rw [𝓛.kerIdeal_ideal_eq_iInf (chartOpen 𝓔 j), le_iInf_iff]
  intro i
  rw [Scheme.Hom.ker_apply]
  refine Ideal.map_le_iff_le_comap.mpr fun z hz ↦ ?_
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  exact 𝓛.coneChartι_app_chartOpen_eq_zero i j z hz

/-- **The chart identification of the glued cone.**  Given the chart computation `hker` of the
glued ideal (the reverse inclusion of `kerIdeal_chart_le`), the sections of the glued cone over
the chart `j` are the affine resolved-cone ring of that chart.  This is the ring isomorphism
`chartCone j` required by `GlobalCone.GlobalConeData`. -/
def chartConeEquiv (j : 𝓔.J)
    (hker : 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom) :
    Γ(𝓛.coneScheme, 𝓛.coneι ⁻¹ᵁ (chartOpen 𝓔 j).1) ≃+* ResolvedCone.ring (φ j) :=
  (𝓛.kerIdeal.subschemeObjIso (chartOpen 𝓔 j)).commRingCatIsoToRingEquiv.trans
    ((Ideal.quotEquivOfEq hker).trans
      (((Ideal.quotientEquiv (𝓛.chartIdeal j) _ (chartGammaEquiv 𝓔 j) rfl).symm).trans
        (Ideal.quotientEquiv (𝓛.chartIdeal j) (ResolvedCone.ideal (φ j)) (𝓛.chartBundle j)
          (𝓛.map_chartIdeal_chartBundle j).symm)))

/-- `chartConeEquiv` intertwines the quotient map by the resolved-cone ideal with the restriction
of sections along `coneι`. -/
theorem chartConeEquiv_symm_mk (j : 𝓔.J)
    (hker : 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom)
    (a : 𝓔.algebra.ring (𝓔.chart j)) :
    (𝓛.chartConeEquiv j hker).symm
        (Ideal.Quotient.mk (ResolvedCone.ideal (φ j)) (𝓛.chartBundle j a)) =
      (𝓛.coneι.app (chartOpen 𝓔 j).1) (chartGammaEquiv 𝓔 j a) := by
  rw [chartConeEquiv, RingEquiv.symm_trans_apply, RingEquiv.symm_trans_apply,
    RingEquiv.symm_trans_apply, Ideal.quotientEquiv_symm_mk, RingEquiv.symm_apply_apply,
    RingEquiv.symm_symm]
  change (𝓛.kerIdeal.subschemeObjIso (chartOpen 𝓔 j)).commRingCatIsoToRingEquiv.symm
      (Ideal.Quotient.mk (𝓛.kerIdeal.ideal (chartOpen 𝓔 j)) (chartGammaEquiv 𝓔 j a)) =
    ((𝓛.kerIdeal.subschemeι.app (chartOpen 𝓔 j).1)) (chartGammaEquiv 𝓔 j a)
  rw [Scheme.IdealSheafData.subschemeι_app]
  rfl

/-- **The chart identification of the glued cone**, unconditionally: the hypothesis `hker` of
`chartConeEquiv` is the theorem `kerIdeal_chart`.  This is the ring isomorphism `chartCone j`
required by `GlobalCone.GlobalConeData`. -/
def chartConeEquiv' [Finite 𝓔.J] [QuasiSeparatedSpace X] (j : 𝓔.J) :
    Γ(𝓛.coneScheme, 𝓛.coneι ⁻¹ᵁ (chartOpen 𝓔 j).1) ≃+* ResolvedCone.ring (φ j) :=
  𝓛.chartConeEquiv j (𝓛.kerIdeal_chart j)

/-- `chartConeEquiv'` intertwines the quotient map by the resolved-cone ideal with the
restriction of sections along `coneι`. -/
theorem chartConeEquiv'_symm_mk [Finite 𝓔.J] [QuasiSeparatedSpace X] (j : 𝓔.J)
    (a : 𝓔.algebra.ring (𝓔.chart j)) :
    (𝓛.chartConeEquiv' j).symm
        (Ideal.Quotient.mk (ResolvedCone.ideal (φ j)) (𝓛.chartBundle j a)) =
      (𝓛.coneι.app (chartOpen 𝓔 j).1) (chartGammaEquiv 𝓔 j a) :=
  𝓛.chartConeEquiv_symm_mk j (𝓛.kerIdeal_chart j) a

end LocalConeData

/-! ## Consistency with the affine case

For an affine base with the single chart `⊤` the overlap hypothesis is vacuous, so the round-17
datum `GlobalConeAffine.bundleData` carries a `LocalConeData`.  Note that no separate comparison
of cycles is needed: `GlobalCone.GlobalConeData.coneCycleAt_eq_resolvedConeCycleAt` holds for
*every* `GlobalConeData`, hence in particular for the one glued from local data. -/

section Affine

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
  {E : LinearTwoTermComplex (R ⧸ I)} [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero]
  (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The affine obstruction datum of round 17, viewed as local cone data with the single chart
`⊤ ⊆ Spec (R ⧸ I)`.  The overlap hypothesis `compat` is trivial because the chart index type is
`PUnit`. -/
def ofAffine : LocalConeData (k := k) (GlobalConeAffine.bundleData φ)
    (R := fun _ ↦ R) (I := fun _ ↦ I) (E := fun _ ↦ E) (fun _ ↦ φ) where
  chartBase _ := (GlobalConeAffine.topAlgEquiv (R ⧸ I)).toRingEquiv
  chartBundle _ :=
    (GlobalConeAffine.constTopEquiv (R ⧸ I) (ResolvedCone.bundleRing φ)).toRingEquiv
  chartBundle_algebraMap _ r := by
    change GlobalConeAffine.constTopEquiv (R ⧸ I) (ResolvedCone.bundleRing φ)
      (r ⊗ₜ[R ⧸ I] 1) = _
    rw [GlobalConeAffine.constTopEquiv_tmul, Algebra.smul_def, mul_one]
    rfl
  compat i j W hi hj := by
    obtain rfl : i = j := @Subsingleton.elim PUnit.{u + 1} _ i j
    rfl

end Affine

end

end VirtualClass.ConeGluing

end GromovWitten.AlgebraicGeometry
