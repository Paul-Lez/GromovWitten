/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalVirtualClassUnconditional

/-!
# Resolution independence of the global virtual class, for a fixed bundle

`GlobalCone.lean` attaches to a `GlobalConeData 𝓔 φ` a global cone class `coneClassAt` on the
total space of a fixed vector bundle `𝓔`, built chart by chart from the affine obstruction data
`φ j` of `AffineObstructionCone.lean`/`Construction.lean`. `Independence.lean` proves that at a
*single* affine chart, two obstruction theories `φ`, `φ'` over the same conormal complex that are
related by an isomorphism of two-term complexes produce the same resolved-cone cycle and class
(`bundleSpaceIso`, `pullbackOpen_map_fundamentalCycle_toBundle`). This file lifts that comparison
to the global level: chart-wise isomorphic cone data for the same bundle give the same glued cone
class, hence (for a globally trivialised bundle) the same virtual class.

## Main definitions and results

* `ChartIso 𝒞 𝒞'` — the data of a chart-wise isomorphism between two `GlobalConeData 𝓔 φ`,
  `GlobalConeData 𝓔 φ'` for the same bundle `𝓔`: an isomorphism `hom j` of the two-term complexes
  `E j ≅ E' j` at every chart, compatible with `φ j`, `φ' j` (`comp_degreeZero`, matching
  `Independence.lean`'s hypothesis `hcomp`) and with the two embeddings of the affine chart into
  the total space (`bundleChart_comm`).
* `ext_of_isOpenImmersion_cover` — a cycle on a scheme is determined by its restrictions along an
  open cover by arbitrary open immersions (not literally `Opens.ι`), strengthening
  `IntersectionTheory.AlgebraicCycle.ext_of_cover`.
* `coneCycle_eq` — the glued cone cycles of `𝒞` and `𝒞'` agree.
* `coneClassAt_eq` — hence the cone *classes* agree, for any grading `dimE`, `d` and any
  `RationalEquivalenceSystem RE`.
* `virtualClassFT'_eq` — the corollary for the unconditional virtual class of a compact scheme
  locally of finite type over an infinite field with a globally trivialised bundle
  (`existsUnique_virtualClassFT'_of_globalTrivialisation'`): the virtual classes attached to `𝒞`
  and `𝒞'` agree.

## What is not proved here

The quasi-isomorphism variant (chart-wise quasi-isomorphisms rather than isomorphisms of
two-term complexes, using `QuasiIsoInvariance.lean`'s affine result in place of
`Independence.lean`'s) is not proved: it would need a chart-wise "common dominating resolution"
compatible with the gluing data, which is exactly the missing plumbing recorded in the round's
survey and is not a few-hour addition. Comparison of two `GlobalConeData` for genuinely
*different* bundles, and uniqueness for a non-trivialisable bundle, are also out of scope (the
latter needs the Chern-class machinery that `GlobalVirtualClassUnconditional.lean` already
identifies as a Mathlib gap).
-/

universe u

-- As in `GlobalCone.lean`: the coordinate ring of the affine product `C ×_X E₀` is a tensor
-- product whose left factor is a quotient of a Rees algebra, needing one more level of pending
-- instance problems than the default.
set_option maxSynthPendingDepth 5

-- As in `GlobalCone.lean`: the index type of Mathlib's directed affine cover is definitionally,
-- but not reducibly, the type of affine opens.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace RelativeSpec
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualFundamentalClass
open VirtualClass.GlobalCone

noncomputable section

namespace VirtualClass.ConeGluingIndependence

/-! ## A cycle is determined by its restrictions along a cover by open immersions -/

/-- The residue-degree restriction of a cycle along an open immersion `f` factors through the
inclusion of `f.opensRange`, via the isomorphism `f.isoOpensRange` onto the range. Proved
pointwise to avoid rewriting a morphism that occurs in the typeclass argument of `pullbackOpen`.
-/
theorem pullbackOpen_eq_pullbackOpen_isoOpensRange_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (c : AlgebraicCycle Y ℚ) :
    IntersectionTheory.AlgebraicCycle.pullbackOpen f c =
      IntersectionTheory.AlgebraicCycle.pullbackOpen f.isoOpensRange.hom
        (IntersectionTheory.AlgebraicCycle.pullbackOpen f.opensRange.ι c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  change c (f.base u) = c (f.opensRange.ι.base (f.isoOpensRange.hom.base u))
  rw [← comp_base_apply, Scheme.Hom.isoOpensRange_hom_ι]

/-- **Cancelling an isomorphism of schemes under restriction of cycles.** Proved pointwise, for
the same reason as `pullbackOpen_eq_pullbackOpen_isoOpensRange_hom`: rewriting `e.inv ≫ e.hom` to
`𝟙 _` inside the typeclass argument of `IntersectionTheory.AlgebraicCycle.pullbackOpen` fails with
"motive is not type correct". -/
theorem pullbackOpen_inv_pullbackOpen_hom {A B : Scheme.{u}} (e : A ≅ B)
    (c : AlgebraicCycle B ℚ) :
    IntersectionTheory.AlgebraicCycle.pullbackOpen e.inv
      (IntersectionTheory.AlgebraicCycle.pullbackOpen e.hom c) = c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  change c (e.hom.base (e.inv.base u)) = c u
  congr 1
  rw [← comp_base_apply, Iso.inv_hom_id]
  rfl

/-- Cancelling the isomorphism `f.isoOpensRange` under restriction of cycles. -/
theorem pullbackOpen_isoOpensRange_inv_pullbackOpen_isoOpensRange_hom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (e : AlgebraicCycle f.opensRange.toScheme ℚ) :
    IntersectionTheory.AlgebraicCycle.pullbackOpen f.isoOpensRange.inv
      (IntersectionTheory.AlgebraicCycle.pullbackOpen f.isoOpensRange.hom e) = e :=
  pullbackOpen_inv_pullbackOpen_hom f.isoOpensRange e

/-- **A cycle on a scheme is determined by its restrictions along a cover by arbitrary open
immersions.** A strengthening of `IntersectionTheory.AlgebraicCycle.ext_of_cover`, which requires
the cover to be literally given by the inclusions of a family of `Opens`: here the members of the
cover are open immersions from arbitrary schemes, compared through `Scheme.Hom.opensRange`, and
the comparison reduces to `ext_of_cover` by cancelling the isomorphism
`Scheme.Hom.isoOpensRange` onto the range. -/
theorem ext_of_isOpenImmersion_cover {X : Scheme.{u}} {J : Type u} {Y : J → Scheme.{u}}
    (f : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (f j)] (hcov : ⨆ j, (f j).opensRange = ⊤)
    (c d : AlgebraicCycle X ℚ)
    (h : ∀ j, IntersectionTheory.AlgebraicCycle.pullbackOpen (f j) c =
      IntersectionTheory.AlgebraicCycle.pullbackOpen (f j) d) :
    c = d := by
  refine IntersectionTheory.AlgebraicCycle.ext_of_cover (U := fun j ↦ (f j).opensRange) hcov c d
    (fun j ↦ ?_)
  have e3 : IntersectionTheory.AlgebraicCycle.pullbackOpen (f j).isoOpensRange.hom
      (IntersectionTheory.AlgebraicCycle.pullbackOpen (f j).opensRange.ι c) =
      IntersectionTheory.AlgebraicCycle.pullbackOpen (f j).isoOpensRange.hom
        (IntersectionTheory.AlgebraicCycle.pullbackOpen (f j).opensRange.ι d) := by
    rw [← pullbackOpen_eq_pullbackOpen_isoOpensRange_hom,
      ← pullbackOpen_eq_pullbackOpen_isoOpensRange_hom, h j]
  have e4 := congrArg
    (IntersectionTheory.AlgebraicCycle.pullbackOpen (f j).isoOpensRange.inv) e3
  rwa [pullbackOpen_isoOpensRange_inv_pullbackOpen_isoOpensRange_hom,
    pullbackOpen_isoOpensRange_inv_pullbackOpen_isoOpensRange_hom] at e4

/-! ## Chart-wise isomorphisms of cone data for a fixed bundle -/

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
variable {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)}
variable {E E' : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
variable {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
variable {φ' : ∀ j, LinearTwoTermComplex.Hom (E' j) (conormalComplex k (R j) (I j))}

/-- **The chart `bundleChartι j` of the total space of a `GlobalConeData` does not depend on the
cone data**: its range is the preimage of the chart of the base under the bundle projection,
exactly as for the trivialising chart `BundleData.chartι`. This is what lets the same family of
opens serve as a common open cover when comparing the cone cycles of two different
`GlobalConeData` for the same bundle `𝓔`. -/
theorem opensRange_bundleChartι (𝒞 : GlobalConeData 𝓔 φ) (j : 𝓔.J) :
    (𝒞.bundleChartι j).opensRange = 𝓔.proj ⁻¹ᵁ (𝓔.chart j).1 :=
  (Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (CommRingCat.ofHom (𝒞.chartBundle j).toRingHom))
    (affineι X 𝓔.algebra (𝓔.chart j))).trans (opensRange_affineι X 𝓔.algebra (𝓔.chart j))

/-- **The charts `bundleChartι j` cover the total space.** -/
theorem iSup_opensRange_bundleChartι (𝒞 : GlobalConeData 𝓔 φ) :
    ⨆ j, (𝒞.bundleChartι j).opensRange = ⊤ := by
  simp_rw [opensRange_bundleChartι 𝒞]
  exact 𝓔.proj.iSup_preimage_eq_top 𝓔.iSup_chart

/-- **Chart-wise isomorphism data between two cone data `𝒞`, `𝒞'` for the same bundle `𝓔`.**

The data is, at every chart `j`, an isomorphism `hom j` of the two-term complexes `E j` and
`E' j` (`bijective_degreeZero`, `bijective_degreeOne`) compatible with the affine obstruction
data `φ j`, `φ' j` over the *same* conormal complex `conormalComplex k (R j) (I j)`
(`comp_degreeZero`, exactly the hypothesis `hcomp` of
`Independence.lean`'s `bundleSpaceIso`/`coneSchemeIso`), together with the compatibility of the
induced isomorphism of affine bundle charts with the two embeddings of the chart into the total
space of `𝓔` (`bundleChart_comm`). No conclusion is carried by this structure: everything is data
about the two given resolutions `𝒞`, `𝒞'` and the isomorphism `ψ` relating them. -/
structure ChartIso (𝒞 : GlobalConeData 𝓔 φ) (𝒞' : GlobalConeData 𝓔 φ') where
  /-- The chart-wise isomorphism of two-term complexes over `R j ⧸ I j`. -/
  hom : ∀ j, LinearTwoTermComplex.Hom (E j) (E' j)
  /-- `hom j` is bijective in degree zero. -/
  bijective_degreeZero : ∀ j, Function.Bijective (hom j).degreeZero
  /-- `hom j` is bijective in degree one. -/
  bijective_degreeOne : ∀ j, Function.Bijective (hom j).degreeOne
  /-- `hom j` intertwines the two affine obstruction data `φ j`, `φ' j` in degree zero. -/
  comp_degreeZero : ∀ j, (φ' j).degreeZero.comp (hom j).degreeZero = (φ j).degreeZero
  /-- The isomorphism of affine bundle charts induced by `hom j` is compatible with the two
  embeddings of the chart into the total space of `𝓔`. -/
  bundleChart_comm : ∀ j,
    (VirtualClass.bundleSpaceIso (φ j) (φ' j) (hom j) (bijective_degreeZero j)).hom ≫
        𝒞.bundleChartι j = 𝒞'.bundleChartι j

variable {𝒞 : GlobalConeData 𝓔 φ} {𝒞' : GlobalConeData 𝓔 φ'}

/-- **The two embeddings of a chart into the total space, related by a `ChartIso`, are
compatible with the induced isomorphism of affine bundle spaces.** The cycle-level form of
`ChartIso.bundleChart_comm`, proved pointwise for the same reason as the lemmas above. -/
theorem pullbackOpen_bundleChartι_eq_pullbackOpen_inv (H : ChartIso 𝒞 𝒞') (j : 𝓔.J)
    (c : AlgebraicCycle 𝓔.totalSpace ℚ) :
    IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞.bundleChartι j) c =
      IntersectionTheory.AlgebraicCycle.pullbackOpen
        (VirtualClass.bundleSpaceIso (φ j) (φ' j) (H.hom j) (H.bijective_degreeZero j)).inv
        (IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞'.bundleChartι j) c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  set E0 := VirtualClass.bundleSpaceIso (φ j) (φ' j) (H.hom j) (H.bijective_degreeZero j) with hE0
  change c ((𝒞.bundleChartι j).base u) = c ((𝒞'.bundleChartι j).base (E0.inv.base u))
  have hcomp : (E0.hom ≫ 𝒞.bundleChartι j).base (E0.inv.base u) = (𝒞.bundleChartι j).base u := by
    rw [comp_base_apply]
    congr 1
    rw [← comp_base_apply, Iso.inv_hom_id]
    rfl
  have hkey : (𝒞'.bundleChartι j).base (E0.inv.base u) = (𝒞.bundleChartι j).base u := by
    rw [← H.bundleChart_comm j]
    exact hcomp
  rw [hkey]

variable [∀ j, IsNoetherianRing (R j)]
variable [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
variable [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero]
variable [∀ j, Module.Free (R j ⧸ I j) (E' j).degreeZero]
variable [∀ j, Module.Finite (R j ⧸ I j) (E' j).degreeZero]
variable [IsLocallyNoetherian 𝒞.coneScheme] [IsLocallyNoetherian 𝒞'.coneScheme]

/-- **The chart-wise comparison of the two global cone cycles.** For a fixed chart `j`, the
restrictions of `𝒞.coneCycle dimE` and `𝒞'.coneCycle dimE` to the affine bundle chart of `φ j`
agree, given ANY certified dimension function `dimAff` on that chart (its actual values play no
role: both sides are computed by pushing forward with the pulled-back source weight, so the
comparison reduces, via `GlobalConeData.pullbackOpen_bundleChartι_coneCycleOf` on each side and
`VirtualClass.pullbackOpen_map_fundamentalCycle_toBundle` in between, to cancelling the
isomorphism `VirtualClass.bundleSpaceIso`). -/
theorem pullbackOpen_bundleChartι_coneCycle_eq (H : ChartIso 𝒞 𝒞') (j : 𝓔.J)
    (dimAff : DimensionFunction (ResolvedCone.bundleSpace (φ j)))
    (dimE : DimensionFunction 𝓔.totalSpace) :
    IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞.bundleChartι j) (𝒞.coneCycle dimE) =
      IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞.bundleChartι j) (𝒞'.coneCycle dimE) := by
  set E0 := VirtualClass.bundleSpaceIso (φ j) (φ' j) (H.hom j) (H.bijective_degreeZero j)
  set dimAff' := dimAff.comapClosedImmersion E0.hom with hdimAff'
  have hA : IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞.bundleChartι j) (𝒞.coneCycle dimE) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle (φ j))
        (VirtualClass.coneDimension (φ j) dimAff) dimAff
        (ResolvedCone.scheme (φ j)).fundamentalCycle :=
    𝒞.pullbackOpen_bundleChartι_coneCycleOf j (dimE : 𝓔.totalSpace → ℤ) dimAff
  have hB : IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞'.bundleChartι j) (𝒞'.coneCycle dimE) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle (φ' j))
        (VirtualClass.coneDimension (φ' j) dimAff') dimAff'
        (ResolvedCone.scheme (φ' j)).fundamentalCycle :=
    𝒞'.pullbackOpen_bundleChartι_coneCycleOf j (dimE : 𝓔.totalSpace → ℤ) dimAff'
  have hC := VirtualClass.pullbackOpen_map_fundamentalCycle_toBundle (φ j) (φ' j) (H.hom j)
    (H.bijective_degreeZero j) (H.bijective_degreeOne j) (H.comp_degreeZero j) dimAff dimAff'
  rw [hA, pullbackOpen_bundleChartι_eq_pullbackOpen_inv H j, hB, ← hC,
    pullbackOpen_inv_pullbackOpen_hom]

/-- **Chart-wise isomorphic cone data give the same global cone cycle**, for a fixed grading
`dimE`. This is `coneClassAt_eq` below, at the level of the ungraded cycle on the total space
rather than the class in a Chow group. -/
theorem coneCycle_eq (H : ChartIso 𝒞 𝒞')
    (dimAff : ∀ j, DimensionFunction (ResolvedCone.bundleSpace (φ j)))
    (dimE : DimensionFunction 𝓔.totalSpace) :
    𝒞.coneCycle dimE = 𝒞'.coneCycle dimE :=
  ext_of_isOpenImmersion_cover 𝒞.bundleChartι (iSup_opensRange_bundleChartι 𝒞)
    (𝒞.coneCycle dimE) (𝒞'.coneCycle dimE)
    (fun j ↦ pullbackOpen_bundleChartι_coneCycle_eq H j (dimAff j) dimE)

/-- **Chart-wise isomorphic cone data give the same graded global cone cycle.** -/
theorem coneCycleAt_eq (H : ChartIso 𝒞 𝒞')
    (dimAff : ∀ j, DimensionFunction (ResolvedCone.bundleSpace (φ j)))
    (dimE : DimensionFunction 𝓔.totalSpace) (d : ℤ) :
    𝒞.coneCycleAt dimE d = 𝒞'.coneCycleAt dimE d := by
  unfold GlobalConeData.coneCycleAt
  rw [coneCycle_eq H dimAff dimE]

/-- **The main independence theorem: chart-wise isomorphic cone data for the same bundle `𝓔`
give the same global cone class.**

`𝒞 : GlobalConeData 𝓔 φ` and `𝒞' : GlobalConeData 𝓔 φ'` are two resolutions of the (fixed) global
cone of the obstruction bundle `𝓔`, related chart by chart by a `ChartIso H`: at every chart `j`
an isomorphism of two-term complexes intertwining the affine obstruction data `φ j`, `φ' j`
(`ChartIso.comp_degreeZero`, `Independence.lean`'s hypothesis for affine isomorphism invariance),
compatible with the embeddings of the chart into the total space (`ChartIso.bundleChart_comm`).
Given, at each chart, ANY certified dimension function `dimAff j` on the affine model (its actual
values are immaterial to the conclusion, see `pullbackOpen_bundleChartι_coneCycle_eq`), the two
cone classes `𝒞.coneClassAt dimE d RE` and `𝒞'.coneClassAt dimE d RE` agree in EVERY Chow group of
the total space. -/
theorem coneClassAt_eq (H : ChartIso 𝒞 𝒞')
    (dimAff : ∀ j, DimensionFunction (ResolvedCone.bundleSpace (φ j)))
    (dimE : DimensionFunction 𝓔.totalSpace) (d : ℤ)
    (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE d) :
    𝒞.coneClassAt dimE d RE = 𝒞'.coneClassAt dimE d RE := by
  unfold GlobalConeData.coneClassAt
  rw [coneCycleAt_eq H dimAff dimE d]

/-! ## Corollary: the finite-type virtual class of a compact scheme over an infinite field -/

section FiniteType

open FiniteTypeDimension

variable {F : Type u} [Field F] [Infinite F]
  (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] [CompactSpace X] [Finite ι]
  (i : ℤ) (RX : RationalEquivalenceSystem X (dimensionFunction f) i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
    (i + (Nat.card ι : ℤ)))

/-- **Resolution independence of the finite-type virtual class, for a fixed globally trivialised
obstruction bundle.**

For `X` compact and locally of finite type over an infinite field `F`, with a
`GlobalTrivialisation t` of `𝓔`, the unconditional virtual class `virtualClassFT'` of
`GlobalVirtualClassUnconditional.lean` — which exists and is unique with no further hypothesis —
agrees for the two chart-isomorphic cone data `𝒞`, `𝒞'`: the hypothesis is exactly `ChartIso H`,
with no extra assumption beyond those of
`existsUnique_virtualClassFT'_of_globalTrivialisation'`. The per-chart certified dimension
function needed by `coneClassAt_eq` is taken to be the canonical
`FiniteTypeDimension.dimensionFunction` of the composite `𝒞.bundleChartι j ≫ (𝓔.proj ≫ f)`
(locally of finite type since `𝒞.bundleChartι j` is an open immersion and `𝓔.proj ≫ f` is
locally of finite type), so no additional hypothesis is needed for its existence either. -/
theorem virtualClassFT'_eq (H : ChartIso 𝒞 𝒞')
    (t : GlobalTrivialisation 𝓔) :
    VirtualClass.GlobalVirtualClass.virtualClassFT' f 𝒞 i RX RE =
      VirtualClass.GlobalVirtualClass.virtualClassFT' f 𝒞' i RX RE := by
  have hdimAff : ∀ j, DimensionFunction (ResolvedCone.bundleSpace (φ j)) :=
    fun j ↦ dimensionFunction (𝒞.bundleChartι j ≫ (𝓔.proj ≫ f))
  refine (VirtualClass.GlobalVirtualClass.eq_virtualClassFT'_of_pullback_eq_of_globalTrivialisation'
    f 𝒞' i RX RE t (VirtualClass.GlobalVirtualClass.virtualClassFT' f 𝒞 i RX RE) ?_).symm
  rw [VirtualClass.GlobalVirtualClass.bundlePullbackFT_virtualClassFT']
  exact coneClassAt_eq H hdimAff (dimensionFunction (𝓔.proj ≫ f)) (i + (Nat.card ι : ℤ)) RE

end FiniteType

end VirtualClass.ConeGluingIndependence

end

end GromovWitten.AlgebraicGeometry
