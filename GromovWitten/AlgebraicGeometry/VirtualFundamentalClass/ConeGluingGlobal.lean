/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ConeGluing
import GromovWitten.AlgebraicGeometry.RelativeSpecAffineHom

/-!
# The global cone datum glued from local obstruction models

`VirtualFundamentalClass/ConeGluing.lean` builds, from local data `𝓛 : LocalConeData 𝓔 φ`, the
glued cone `𝓛.coneScheme` as the closed subscheme of the total space `𝓔.totalSpace` cut out by
the kernel `𝓛.kerIdeal` of the morphism assembled from the affine cones of the charts, and it
identifies its sections over a chart with the affine resolved-cone ring
(`LocalConeData.chartConeEquiv`, and `LocalConeData.chartConeEquiv'` using the chart computation
`LocalConeData.kerIdeal_chart` of the glued ideal).

This file assembles these pieces into a genuine `GlobalCone.GlobalConeData 𝓔 φ`, using
`GromovWitten/AlgebraicGeometry/RelativeSpecAffineHom.lean`: the closed immersion `𝓛.coneι`
composed with the bundle projection is an affine morphism, hence is the relative `Spec` of the
quasi-coherent algebra `RelativeSpec.AlgebraData.ofAffineHom`, and the factorisation of `𝓛.coneι`
through `𝓔.totalSpace = relativeSpec X 𝓔.algebra` gives the surjective morphism of algebra data
required by `GlobalConeData`.

## Main definitions

* `LocalConeData.coneProj` — the structure morphism `𝓛.coneScheme ⟶ X` of the glued cone; it is
  affine (`LocalConeData.isAffineHom_coneProj`).
* `LocalConeData.coneAlgebra` — the quasi-coherent algebra of functions on the glued cone.
* `LocalConeData.inclusion` — the presentation of `coneAlgebra` as a quotient of `𝓔.algebra`.
* `LocalConeData.toGlobalConeDataOfKer` — the global cone datum, under the hypothesis `hker`
  (the chart computation of the glued ideal sheaf).
* `LocalConeData.toGlobalConeData` — the same datum without any hypothesis, for a finite chart
  index over a quasi-separated base: there `hker` is the theorem `LocalConeData.kerIdeal_chart`.
* `LocalConeData.ofAffineGlobalConeData` — the specialisation to the single-chart affine datum
  of round 17.

## Main results

* `LocalConeData.surjective_inclusion_app` — `inclusion` is surjective on every affine open.
* `LocalConeData.inclusion_app_chart` — over a chart, `inclusion` is the restriction of sections
  along `coneι`, transported along `chartGammaEquiv`.
* `LocalConeData.isNoetherianRing_coneAlgebra_ring` and the instance
  `LocalConeData.isLocallyNoetherian_toGlobalConeData` — the glued cone is locally Noetherian as
  soon as all the bundle algebras `𝓔.algebra.ring W` are Noetherian rings, which holds for
  instance when `𝓔.totalSpace` is locally Noetherian (`isNoetherianRing_bundleRing`).
* `LocalConeData.coneCycleAt_toGlobalConeData_eq_resolvedConeCycleAt` — the chart comparison of
  the glued cone cycle with the affine resolved-cone cycle of the local model.
* `LocalConeData.coneSchemeIso` — the cone scheme of the global datum (a relative `Spec`) is
  isomorphic over `X` to the glued closed subscheme `𝓛.coneScheme` of the total space.

## Hypotheses

Nothing here is axiomatic: `toGlobalConeData` needs only `[Finite 𝓔.J]` and
`[QuasiSeparatedSpace X]` (the hypotheses of `LocalConeData.kerIdeal_chart`), and the
Noetherianity statements need Noetherian bundle algebras.  The single geometric hypothesis of
the whole construction is the overlap compatibility `LocalConeData.compat`, a field of
`LocalConeData`.

## Consistency with the affine case

For the single-chart datum `LocalConeData.ofAffine φ` of round 17 no separate comparison of
cycles is needed: `GlobalCone.GlobalConeData.coneCycleAt_eq_resolvedConeCycleAt` holds for
*every* `GlobalConeData`, hence for `ofAffineGlobalConeData φ` and for
`GlobalConeAffine.globalConeData φ` alike, so both restrict on the chart to the affine
resolved-cone cycle `VirtualClass.resolvedConeCycleAt φ`.
-/

universe u

-- As in `ResolvedCone.lean`, `GlobalCone.lean` and `ConeGluing.lean`: the ring instances of the
-- tensor products occurring in `ResolvedCone.ideal` need one more level of pending instances.
set_option maxSynthPendingDepth 5

-- As in `RelativeSpec.lean` and `ConeGluing.lean`: the index type of Mathlib's directed affine
-- cover is definitionally, but not reducibly, the type of affine opens.
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

section TotalSpace

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : BundleData X ι)

/-- The local comparison map of `ConeGluing.lean` is the one of `RelativeSpecAffineHom.lean`. -/
theorem ringEquivGamma_eq_gammaEquiv (W : X.affineOpens) :
    ringEquivGamma X 𝓔.algebra W = gammaEquiv 𝓔 W := rfl

/-- The chart case of `ringEquivGamma_eq_gammaEquiv`. -/
theorem ringEquivGamma_chart_eq_chartGammaEquiv (j : 𝓔.J) :
    ringEquivGamma X 𝓔.algebra (𝓔.chart j) = chartGammaEquiv 𝓔 j := rfl

/-- If the total space of the bundle is locally Noetherian then all the bundle algebras are
Noetherian rings. -/
theorem isNoetherianRing_bundleRing [IsLocallyNoetherian 𝓔.totalSpace] (W : X.affineOpens) :
    IsNoetherianRing (𝓔.algebra.ring W) :=
  have : IsNoetherianRing Γ(𝓔.totalSpace, (bundleOpen 𝓔 W).1) :=
    IsLocallyNoetherian.component_noetherian (bundleOpen 𝓔 W)
  isNoetherianRing_of_ringEquiv _ (gammaEquiv 𝓔 W).symm

end TotalSpace

namespace LocalConeData

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
  {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)}
  {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝓛 : LocalConeData 𝓔 φ)

/-! ## The glued cone as a relative `Spec` -/

/-- The structure morphism of the glued cone: the closed immersion into the total space followed
by the bundle projection. -/
def coneProj : 𝓛.coneScheme ⟶ X := 𝓛.coneι ≫ 𝓔.proj

/-- The structure morphism of the glued cone is affine: it is a closed immersion followed by the
affine morphism `𝓔.proj`. -/
instance isAffineHom_coneProj : IsAffineHom 𝓛.coneProj := by
  rw [coneProj]; infer_instance

/-- The glued cone lies over the base, in terms of the structure morphism of the total space. -/
theorem coneι_toBase : 𝓛.coneι ≫ toBase X 𝓔.algebra = 𝓛.coneProj := rfl

/-- The quasi-coherent algebra of functions on the glued cone: its sections over an affine open
`W` of `X` are the sections of the cone over the part lying above `W`. -/
def coneAlgebra : AlgebraData X := AlgebraData.ofAffineHom 𝓛.coneProj

/-- The sections of `coneAlgebra` are the sections of the glued cone. -/
theorem coneAlgebra_ring (W : X.affineOpens) :
    𝓛.coneAlgebra.ring W = Γ(𝓛.coneScheme, 𝓛.coneProj ⁻¹ᵁ W.1) := rfl

/-- The presentation of the cone algebra as a quotient of the bundle algebra, obtained from the
factorisation of the closed immersion `coneι` through the total space. -/
def inclusion : RelativeSpec.Hom X 𝓛.coneAlgebra 𝓔.algebra :=
  RelativeSpec.Hom.ofOverRelativeSpec 𝓔.algebra (g := 𝓛.coneProj) 𝓛.coneι rfl

/-- The presentation of the cone algebra is surjective over every affine open: this is the
surjectivity of the restriction of sections along a closed immersion. -/
theorem surjective_inclusion_app (W : X.affineOpens) :
    Function.Surjective (𝓛.inclusion.app W) :=
  RelativeSpec.Hom.ofOverRelativeSpec_app_surjective 𝓔.algebra 𝓛.coneι rfl W

/-- Over a chart, the presentation of the cone algebra is the restriction of sections along the
closed immersion `coneι`, read through the identification `chartGammaEquiv`.  The part of the
glued cone lying over the chart `j` is the preimage of the affine chart of the total space, so
no restriction map intervenes. -/
theorem inclusion_app_chart (j : 𝓔.J) (a : 𝓔.algebra.ring (𝓔.chart j)) :
    𝓛.inclusion.app (𝓔.chart j) a =
      𝓛.coneι.app (chartOpen 𝓔 j).1 (chartGammaEquiv 𝓔 j a) := by
  change (𝓛.coneι.appLE (chartOpen 𝓔 j).1 (𝓛.coneι ⁻¹ᵁ (chartOpen 𝓔 j).1) le_rfl)
      (chartGammaEquiv 𝓔 j a) = _
  rw [Scheme.Hom.appLE_eq_app]

/-- The chart identification of the glued cone, as an isomorphism of the sections of the cone
algebra over the chart `j` with the affine resolved-cone ring.  This is `chartConeEquiv`, read
through `coneAlgebra`. -/
def chartCone (j : 𝓔.J)
    (hker : 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom) :
    𝓛.coneAlgebra.ring (𝓔.chart j) ≃+* ResolvedCone.ring (φ j) :=
  𝓛.chartConeEquiv j hker

/-- `chartCone` intertwines the quotient map by the resolved-cone ideal with the presentation of
the cone algebra as a quotient of the bundle algebra. -/
theorem chartCone_symm_mk (j : 𝓔.J)
    (hker : 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom)
    (a : 𝓔.algebra.ring (𝓔.chart j)) :
    (𝓛.chartCone j hker).symm
        (Ideal.Quotient.mk (ResolvedCone.ideal (φ j)) (𝓛.chartBundle j a)) =
      𝓛.inclusion.app (𝓔.chart j) a := by
  rw [𝓛.inclusion_app_chart j a]
  exact 𝓛.chartConeEquiv_symm_mk j hker a

/-- The compatibility of `chartCone` with the presentation of the cone algebra: this is the
field `chartCone_inclusion` of `GlobalCone.GlobalConeData`. -/
theorem chartCone_inclusion (j : 𝓔.J)
    (hker : 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom)
    (a : 𝓔.algebra.ring (𝓔.chart j)) :
    𝓛.chartCone j hker (𝓛.inclusion.app (𝓔.chart j) a) =
      Ideal.Quotient.mk (ResolvedCone.ideal (φ j)) (𝓛.chartBundle j a) := by
  rw [← 𝓛.chartCone_symm_mk j hker a, RingEquiv.apply_symm_apply]

/-! ## The global cone datum -/

/-- **The global cone datum glued from local obstruction models.**  Given local cone data `𝓛`
and the chart computation `hker` of the glued ideal sheaf — the reverse inclusion of the
unconditional `LocalConeData.kerIdeal_chart_le` — the glued cone `𝓛.coneScheme ⊆ 𝓔.totalSpace`
is a `GlobalCone.GlobalConeData 𝓔 φ`: its algebra of functions is `coneAlgebra`, its presentation
as a quotient of the bundle algebra is `inclusion`, and over the chart `j` its sections are the
affine resolved-cone ring `ResolvedCone.ring (φ j)` compatibly with `Ideal.Quotient.mk`.

`hker` is the only hypothesis beyond the fields of `LocalConeData`; it is where the overlap
compatibility `LocalConeData.compat` is meant to enter. -/
def toGlobalConeDataOfKer
    (hker : ∀ j : 𝓔.J, 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom) :
    GlobalCone.GlobalConeData 𝓔 φ where
  cone := 𝓛.coneAlgebra
  inclusion := 𝓛.inclusion
  surjective_inclusion := 𝓛.surjective_inclusion_app
  chartBase := 𝓛.chartBase
  chartBundle := 𝓛.chartBundle
  chartBundle_algebraMap := 𝓛.chartBundle_algebraMap
  chartCone j := 𝓛.chartCone j (hker j)
  chartCone_inclusion j a := 𝓛.chartCone_inclusion j (hker j) a

@[simp]
theorem toGlobalConeDataOfKer_cone
    (hker : ∀ j : 𝓔.J, 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom) :
    (𝓛.toGlobalConeDataOfKer hker).cone = 𝓛.coneAlgebra := rfl

/-- **The global cone datum glued from local obstruction models, unconditionally.**  For a
finite chart index and a quasi-separated base the hypothesis `hker` of `toGlobalConeData` is the
theorem `LocalConeData.kerIdeal_chart`, so the local data `𝓛` — whose only geometric hypothesis
is the overlap compatibility `LocalConeData.compat` — determine a `GlobalCone.GlobalConeData`. -/
def toGlobalConeData [Finite 𝓔.J] [QuasiSeparatedSpace X] : GlobalCone.GlobalConeData 𝓔 φ :=
  𝓛.toGlobalConeDataOfKer 𝓛.kerIdeal_chart

@[simp]
theorem toGlobalConeData_cone [Finite 𝓔.J] [QuasiSeparatedSpace X] :
    (𝓛.toGlobalConeData).cone = 𝓛.coneAlgebra := rfl

/-- The cone scheme of the glued global datum is the relative `Spec` of the cone algebra; it is
canonically isomorphic to the glued closed subscheme `𝓛.coneScheme` by
`RelativeSpec.relativeSpecOfAffineHomIso`. -/
def coneSchemeIso : relativeSpec X 𝓛.coneAlgebra ≅ 𝓛.coneScheme :=
  relativeSpecOfAffineHomIso 𝓛.coneProj

/-- The cone scheme of the glued global datum is, by definition, the relative `Spec` of the cone
algebra, so `coneSchemeIso` identifies it with the glued closed subscheme of the total space. -/
theorem toGlobalConeDataOfKer_coneScheme
    (hker : ∀ j : 𝓔.J, 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom) :
    (𝓛.toGlobalConeDataOfKer hker).coneScheme = relativeSpec X 𝓛.coneAlgebra := rfl

/-- The comparison isomorphism identifies the cone scheme of the glued global datum with the
glued closed subscheme of the total space over the base. -/
theorem coneSchemeIso_hom_comp :
    (𝓛.coneSchemeIso).hom ≫ 𝓛.coneProj = toBase X 𝓛.coneAlgebra :=
  relativeSpecOfAffineHomIso_hom_comp 𝓛.coneProj

/-! ## Noetherianity -/

/-- The sections of the glued cone over an affine open of `X` form a Noetherian ring as soon as
the bundle algebra of that open does: they are a quotient of the sections of the total space. -/
theorem isNoetherianRing_coneAlgebra_ring (W : X.affineOpens)
    (hW : IsNoetherianRing (𝓔.algebra.ring W)) :
    IsNoetherianRing (𝓛.coneAlgebra.ring W) :=
  have : IsNoetherianRing Γ(𝓔.totalSpace, (bundleOpen 𝓔 W).1) :=
    isNoetherianRing_of_ringEquiv _ (gammaEquiv 𝓔 W)
  have : IsNoetherianRing (Γ(𝓔.totalSpace, (bundleOpen 𝓔 W).1) ⧸
      𝓛.kerIdeal.ideal (bundleOpen 𝓔 W)) := Ideal.Quotient.isNoetherianRing _
  isNoetherianRing_of_ringEquiv _
    (𝓛.kerIdeal.subschemeObjIso (bundleOpen 𝓔 W)).commRingCatIsoToRingEquiv.symm

/-- **The glued cone is locally Noetherian** as soon as all the bundle algebras are Noetherian
rings.  This is the hypothesis that `GlobalVirtualClass.lean` needs of a `GlobalConeData`. -/
theorem isLocallyNoetherian_toGlobalConeDataOfKer
    (hker : ∀ j : 𝓔.J, 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom)
    (hnoeth : ∀ W : X.affineOpens, IsNoetherianRing (𝓔.algebra.ring W)) :
    IsLocallyNoetherian (𝓛.toGlobalConeDataOfKer hker).coneScheme :=
  GlobalCone.GlobalConeData.isLocallyNoetherian_coneScheme _ fun W ↦
    𝓛.isNoetherianRing_coneAlgebra_ring W (hnoeth W)

/-- The glued cone is locally Noetherian whenever the total space of the bundle is. -/
theorem isLocallyNoetherian_toGlobalConeDataOfKer_of_totalSpace
    [IsLocallyNoetherian 𝓔.totalSpace]
    (hker : ∀ j : 𝓔.J, 𝓛.kerIdeal.ideal (chartOpen 𝓔 j) =
      (𝓛.chartIdeal j).map (chartGammaEquiv 𝓔 j).toRingHom) :
    IsLocallyNoetherian (𝓛.toGlobalConeDataOfKer hker).coneScheme :=
  𝓛.isLocallyNoetherian_toGlobalConeDataOfKer hker (isNoetherianRing_bundleRing 𝓔)

/-- **The glued cone is locally Noetherian**, as an instance: for a finite chart index over a
quasi-separated base, `IsLocallyNoetherian (𝓛.toGlobalConeData).coneScheme` holds as soon as all
the bundle algebras are Noetherian rings.  The hypothesis
`[∀ W : X.affineOpens, IsNoetherianRing (𝓔.algebra.ring W)]` is available for instance when the
total space is locally Noetherian (`isNoetherianRing_bundleRing`). -/
instance isLocallyNoetherian_toGlobalConeData [Finite 𝓔.J] [QuasiSeparatedSpace X]
    [hnoeth : ∀ W : X.affineOpens, IsNoetherianRing (𝓔.algebra.ring W)] :
    IsLocallyNoetherian (𝓛.toGlobalConeData).coneScheme :=
  𝓛.isLocallyNoetherian_toGlobalConeDataOfKer _ hnoeth

/-- The unconditional glued cone is locally Noetherian whenever the total space of the bundle
is. -/
theorem isLocallyNoetherian_toGlobalConeData_of_totalSpace [Finite 𝓔.J] [QuasiSeparatedSpace X]
    [IsLocallyNoetherian 𝓔.totalSpace] :
    IsLocallyNoetherian (𝓛.toGlobalConeData).coneScheme :=
  have := isNoetherianRing_bundleRing 𝓔
  𝓛.isLocallyNoetherian_toGlobalConeDataOfKer _ (isNoetherianRing_bundleRing 𝓔)

/-! ## The chart comparison of the glued cone cycle -/

/-- **The chart comparison for the glued cone.**  Restricting the cone cycle of the glued global
datum to the affine bundle chart of `φ j` and truncating in dimension `d` gives the affine
resolved-cone cycle of the local model.  This is `GlobalCone.GlobalConeData`'s
`coneCycleAt_eq_resolvedConeCycleAt`, whose Noetherianity hypothesis is supplied by
`isLocallyNoetherian_toGlobalConeData`; in particular it applies to the single-chart datum
`LocalConeData.ofAffine`, exactly as it does to `GlobalConeAffine.globalConeData`. -/
theorem coneCycleAt_toGlobalConeData_eq_resolvedConeCycleAt [Finite 𝓔.J] [QuasiSeparatedSpace X]
    [∀ W : X.affineOpens, IsNoetherianRing (𝓔.algebra.ring W)]
    [∀ j, IsNoetherianRing (R j)] [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
    [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero]
    (dimE : DimensionFunction 𝓔.totalSpace) (j : 𝓔.J) (d : ℤ)
    (dimC : DimensionFunction (ResolvedCone.bundleSpace (φ j))) :
    cyclesOfDimension.project (dimension := dimC) (i := d)
        (IntersectionTheory.AlgebraicCycle.pullbackOpen
          ((𝓛.toGlobalConeData).bundleChartι j) ((𝓛.toGlobalConeData).coneCycle dimE)) =
      VirtualFundamentalClass.VirtualClass.resolvedConeCycleAt (φ j) dimC d :=
  (𝓛.toGlobalConeData).coneCycleAt_eq_resolvedConeCycleAt dimE j d dimC

end LocalConeData

/-! ## Consistency with the affine case of round 17

For an affine base with the single chart `⊤` the local data of `LocalConeData.ofAffine` satisfy
all the hypotheses above, so the glued construction applies and produces a second global cone
datum for the affine obstruction model of round 17 (besides
`GlobalConeAffine.globalConeData φ`).  Both are `GlobalCone.GlobalConeData`, hence both satisfy
the chart comparison `GlobalCone.GlobalConeData.coneCycleAt_eq_resolvedConeCycleAt`: their cone
cycles restrict on the single chart to the same affine resolved-cone cycle
`VirtualClass.resolvedConeCycleAt φ`, and therefore their cone classes agree after the chart
restriction of `GlobalConeAffine.chartRestrict_coneClassAt`. -/

section Affine

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
  {E : LinearTwoTermComplex (R ⧸ I)} [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero]
  (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The chart index of the affine bundle datum is `PUnit`, hence finite. -/
instance finite_bundleData_J : Finite (GlobalConeAffine.bundleData φ).J :=
  inferInstanceAs (Finite PUnit.{u + 1})

/-- **The glued global cone datum of an affine obstruction datum.**  The single-chart local data
`LocalConeData.ofAffine φ` glue to a `GlobalCone.GlobalConeData`, so the construction of this
file specialises to the affine situation of round 17. -/
def ofAffineGlobalConeData :
    GlobalCone.GlobalConeData (GlobalConeAffine.bundleData φ) (fun _ ↦ φ) :=
  (ofAffine φ).toGlobalConeData

end Affine

end

end VirtualClass.ConeGluing

end GromovWitten.AlgebraicGeometry
