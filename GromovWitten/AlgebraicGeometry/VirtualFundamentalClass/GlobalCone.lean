/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
import GromovWitten.AlgebraicGeometry.IntersectionTheory.CycleGluing
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.OverField

/-!
# The global cone of an obstruction theory

The affine model of the virtual fundamental class (`VirtualFundamentalClass/ResolvedCone.lean`,
`Construction.lean`) builds, for a closed subscheme `X = Spec (R ⧸ I) ⊆ Spec R` and a chain map
`φ : E ⟶ conormalComplex k R I`, the resolved cone `C(E) ⊆ E₁ = Spec Sym(E⁻¹)` and the cycle
`[C(E)] ∈ Z_*(E₁)`.  This file carries that picture over to a general scheme `X`.

The global data is a `GlobalConeData`: a vector bundle `𝓔 : BundleData X ι` in the sense of
`AlgebraicGeometry/VectorBundleTotalSpace.lean` (a quasi-coherent algebra with an augmentation
and polynomial trivialisations over affine charts `𝓔.chart j`), together with a second
quasi-coherent algebra `cone` and a surjective morphism of algebra data
`inclusion : Hom X cone 𝓔.algebra`, so that `coneScheme 𝒞 = Spec_X cone` is a closed subscheme
of the total space `𝓔.totalSpace = Spec_X 𝓔.algebra`.  Over every chart the data is identified
with an affine model: ring isomorphisms
`chartBundle j : 𝓔.algebra.ring (𝓔.chart j) ≃+* ResolvedCone.bundleRing (φ j)` and
`chartCone j : cone.ring (𝓔.chart j) ≃+* ResolvedCone.ring (φ j)` intertwining `inclusion.app`
with `Ideal.Quotient.mk (ResolvedCone.ideal (φ j))`.

## Main definitions and results

* `GlobalConeData` — the global cone datum described above.
* `GlobalConeData.coneScheme`, `GlobalConeData.coneι`, `isClosedImmersion_coneι`,
  `GlobalConeData.coneι_toBase` — the cone as a closed subscheme of the total space, lying over
  the base.
* `GlobalConeData.bundleChartι` and `GlobalConeData.coneChartι` — the open immersions of the
  affine models `ResolvedCone.bundleSpace (φ j)` and `ResolvedCone.scheme (φ j)` into the total
  space and into the cone, with the commuting square `coneChartι_coneι` and the chart pullback
  square `isPullback_coneChart`.
* `GlobalConeData.coneCycleOf` — the global cone cycle, the pushforward of the fundamental cycle
  of the cone along the closed immersion into the total space.
* `GlobalConeData.pullbackOpen_bundleChartι_coneCycleOf` — **the chart comparison**: the
  restriction of the global cone cycle to the chart `ResolvedCone.bundleSpace (φ j)` is the
  affine resolved-cone cycle of `φ j`.  `coneCycleAt_eq_resolvedConeCycleAt` is its graded
  form, matching `VirtualClass.resolvedConeCycleAt` when the dimension functions correspond.
* `GlobalConeData.coneCycleAt`, `GlobalConeData.coneClassAt` — the graded cone cycle and its
  class in a Chow group of the total space.
* `GlobalConeData.virtualClassOf`, `pull_virtualClassOf`, `virtualClassOf_unique`,
  `existsUnique_virtualClass` — the global virtual class, **modulo the global homotopy property
  of Chow groups**: the flat pullback `pull : A_i(X) → A_d(E₁)`, its injectivity `hinj` and the
  surjectivity statement `hmem` are explicit hypotheses, not proved here.  For a non-affine base
  they are exactly the content of Fulton, Prop. 1.9/3.3, which the repository proves only for a
  trivialised affine bundle (`VectorBundle.chowPullbackBundle`).

## What is not proved here

Nothing in this file constructs a `GlobalConeData` from geometry: the affine models `φ j` and
the chart identifications are data.  The compatibility of `chartBundle` with the polynomial
trivialisations `𝓔.triv j` and `VirtualClass.trivialization (φ j)` is *not* imposed, because the
chart comparison does not need it; a future wave that compares the global flat pullback with
`VectorBundle.chowPullbackBundle` on charts will have to add it.  The global homotopy property
of Chow groups is an explicit hypothesis of `virtualClassOf`, as described above.
-/

universe u

-- The coordinate ring of the affine product `C ×_X E₀` is a tensor product whose left factor is
-- a quotient of a Rees algebra; synthesising its ring instances needs one more level of pending
-- instance problems than the default, exactly as in `ResolvedCone.lean`.
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

namespace VirtualClass.GlobalCone

noncomputable section

/-! ## Two auxiliary facts -/

/-- The underlying map of a composite of morphisms of schemes. -/
theorem comp_base_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g).base a = g.base (f.base a) :=
  rfl

/-- Equal morphisms of schemes have equal underlying maps. -/
theorem base_apply_congr {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (a : A) :
    f.base a = g.base a := by
  rw [h]

/-- `Spec` of a ring isomorphism is an isomorphism of schemes. -/
theorem isIso_specMap_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  rw [isIso_SpecMap_iff]
  exact e.bijective

/-- A relative `Spec` is locally Noetherian as soon as all its affine coordinate rings are. -/
theorem isLocallyNoetherian_relativeSpec (X : Scheme.{u}) (𝒜 : AlgebraData X)
    (h : ∀ U : X.affineOpens, IsNoetherianRing (𝒜.ring U)) :
    IsLocallyNoetherian (relativeSpec X 𝒜) := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun U : X.affineOpens ↦ ⟨(affineι X 𝒜 U).opensRange, isAffineOpen_opensRange _⟩)
    (iSup_opensRange_affineι X 𝒜) fun U ↦ ?_
  have h₁ : IsNoetherianRing (𝒜.ring U) := h U
  have h₂ : IsNoetherianRing Γ(Spec (CommRingCat.of (𝒜.ring U)), ⊤) :=
    isNoetherianRing_of_ringEquiv (𝒜.ring U)
      (Scheme.ΓSpecIso (CommRingCat.of (𝒜.ring U))).symm.commRingCatIsoToRingEquiv
  have h₃ : IsNoetherianRing Γ(relativeSpec X 𝒜, (affineι X 𝒜 U).opensRange) :=
    isNoetherianRing_of_ringEquiv _
      (IsOpenImmersion.ΓIsoTop (affineι X 𝒜 U)).commRingCatIsoToRingEquiv
  exact h₃

/-! ## Restriction of a closed-immersion pushforward to an open chart

The chart comparison of the cone cycle is an instance of the following purely cycle-theoretic
statement.  No pullback square is required: all that is used is the commuting square together
with the surjectivity `hsurj` of `Z' → Z ×_E E'` on points, which for the relative `Spec` is
supplied by `opensRange_affineι`. -/

/-- Restriction to an open subscheme of the residue-degree pushforward along a closed immersion.
The hypothesis `hsurj` says that `Z'` surjects onto the set-theoretic fibre product of `Z` and
`E'` over `E`; together with `hcomm` it makes the square a pullback on points. -/
theorem pullbackOpen_map_of_isClosedImmersion {Z E Z' E' : Scheme.{u}} (i : Z ⟶ E)
    [IsClosedImmersion i] (f : E' ⟶ E) [IsOpenImmersion f] (g : Z' ⟶ Z) [IsOpenImmersion g]
    (i' : Z' ⟶ E') [IsClosedImmersion i'] (hcomm : g ≫ i = i' ≫ f)
    (hsurj : ∀ (z : Z) (e : E'), f.base e = i.base z →
      ∃ z' : Z', i'.base z' = e ∧ g.base z' = z)
    (wE : E → ℤ) (wE' : E' → ℤ) (c : AlgebraicCycle Z ℚ) :
    IntersectionTheory.AlgebraicCycle.pullbackOpen f
        (AlgebraicCycle.map i (fun z ↦ wE (i.base z)) wE c) =
      AlgebraicCycle.map i' (fun z' ↦ wE' (i'.base z')) wE'
        (IntersectionTheory.AlgebraicCycle.pullbackOpen g c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext e
  change AlgebraicCycle.map i (fun z ↦ wE (i.base z)) wE c (f.base e) =
    AlgebraicCycle.map i' (fun z' ↦ wE' (i'.base z')) wE'
      (IntersectionTheory.AlgebraicCycle.pullbackOpen g c) e
  by_cases hmem : f.base e ∈ Set.range i.base
  · obtain ⟨z, hz⟩ := hmem
    obtain ⟨z', hz'e, hz'z⟩ := hsurj z e hz.symm
    rw [← hz, IntersectionTheory.AlgebraicCycle.map_closedImmersion_apply_image i wE c z,
      ← hz'e, IntersectionTheory.AlgebraicCycle.map_closedImmersion_apply_image i' wE' _ z']
    change c z = c (g.base z')
    rw [hz'z]
  · have hnot : e ∉ Set.range i'.base := by
      rintro ⟨z', rfl⟩
      refine hmem ⟨g.base z', ?_⟩
      have := congrArg (fun m : Z' ⟶ E ↦ m.base z') hcomm
      simpa only [comp_base_apply] using this
    rw [IntersectionTheory.AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range i wE c _ hmem,
      IntersectionTheory.AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range i' wE' _ e hnot]

/-! ## Global cone data -/

/-- **A global cone datum on a scheme `X`.**

`𝓔` is a vector bundle `E₁` on `X` and `φ j` is an affine obstruction datum over the chart
`𝓔.chart j`.  The datum consists of a quasi-coherent algebra `cone` on `X` presented as a
quotient of `𝓔.algebra` (fields `inclusion` and `surjective_inclusion`), so that
`Spec_X cone ⊆ Spec_X 𝓔.algebra` is a closed subscheme, together with identifications of the
chart coordinate rings with the affine resolved-cone rings of `φ j` which intertwine the
quotient presentations (field `chartCone_inclusion`).  The field `chartBase` records that the
chart identification lies over the identification `Γ(X, chart j) ≃+* R j ⧸ I j` of the base. -/
structure GlobalConeData {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
    (𝓔 : BundleData X ι) {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
    {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
    (φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))) where
  /-- The quasi-coherent algebra of functions on the cone. -/
  cone : AlgebraData X
  /-- The presentation of the cone algebra as a quotient of the bundle algebra. -/
  inclusion : RelativeSpec.Hom X cone 𝓔.algebra
  surjective_inclusion : ∀ U : X.affineOpens, Function.Surjective (inclusion.app U)
  /-- The identification of the sections over a chart with the affine model of the base. -/
  chartBase : ∀ j, Γ(X, (𝓔.chart j).1) ≃+* (R j ⧸ I j)
  /-- The identification of the bundle algebra over a chart with `Sym(E⁻¹)`. -/
  chartBundle : ∀ j, 𝓔.algebra.ring (𝓔.chart j) ≃+* ResolvedCone.bundleRing (φ j)
  chartBundle_algebraMap : ∀ (j : 𝓔.J) (r : Γ(X, (𝓔.chart j).1)),
    chartBundle j (algebraMap Γ(X, (𝓔.chart j).1) (𝓔.algebra.ring (𝓔.chart j)) r) =
      algebraMap (R j ⧸ I j) (ResolvedCone.bundleRing (φ j)) (chartBase j r)
  /-- The identification of the cone algebra over a chart with the affine resolved-cone ring. -/
  chartCone : ∀ j, cone.ring (𝓔.chart j) ≃+* ResolvedCone.ring (φ j)
  chartCone_inclusion : ∀ (j : 𝓔.J) (a : 𝓔.algebra.ring (𝓔.chart j)),
    chartCone j (inclusion.app (𝓔.chart j) a) =
      Ideal.Quotient.mk (ResolvedCone.ideal (φ j)) (chartBundle j a)

namespace GlobalConeData

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
  {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)] {I : ∀ j, Ideal (R j)}
  {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
  {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
  (𝒞 : GlobalConeData 𝓔 φ)

/-! ## The cone as a closed subscheme of the total space -/

/-- The cone `C ⊆ E₁` as a scheme: the relative `Spec` of the cone algebra. -/
abbrev coneScheme : Scheme.{u} := relativeSpec X 𝒞.cone

/-- The closed immersion of the cone into the total space of the bundle. -/
def coneι : 𝒞.coneScheme ⟶ 𝓔.totalSpace := 𝒞.inclusion.map

instance isClosedImmersion_coneι : IsClosedImmersion 𝒞.coneι :=
  RelativeSpec.Hom.map_isClosedImmersion _ 𝒞.surjective_inclusion

/-- The cone lies over the base: composing with the bundle projection gives the structure
morphism of the cone. -/
theorem coneι_proj : 𝒞.coneι ≫ 𝓔.proj = toBase X 𝒞.cone :=
  RelativeSpec.Hom.map_toBase _

/-- The cone lies over the base, in terms of the structure morphism of the total space. -/
theorem coneι_toBase : 𝒞.coneι ≫ toBase X 𝓔.algebra = toBase X 𝒞.cone :=
  RelativeSpec.Hom.map_toBase _

/-! ## The affine charts of the cone -/

instance isIso_specMap_chartBundle (j : 𝓔.J) :
    IsIso (Spec.map (CommRingCat.ofHom (𝒞.chartBundle j).toRingHom)) :=
  isIso_specMap_ringEquiv _

instance isIso_specMap_chartCone (j : 𝓔.J) :
    IsIso (Spec.map (CommRingCat.ofHom (𝒞.chartCone j).toRingHom)) :=
  isIso_specMap_ringEquiv _

/-- The chart of the total space attached to `j`, in the affine model `E₁ = Spec Sym(E⁻¹)`
of `φ j`: an open immersion of the affine bundle space into the global total space. -/
def bundleChartι (j : 𝓔.J) : ResolvedCone.bundleSpace (φ j) ⟶ 𝓔.totalSpace :=
  Spec.map (CommRingCat.ofHom (𝒞.chartBundle j).toRingHom) ≫ affineι X 𝓔.algebra (𝓔.chart j)

instance isOpenImmersion_bundleChartι (j : 𝓔.J) : IsOpenImmersion (𝒞.bundleChartι j) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ affineι X 𝓔.algebra (𝓔.chart j)))

/-- The chart of the cone attached to `j`, in the affine model `C(E) = Spec (ring φ)` of `φ j`:
an open immersion of the affine resolved cone into the global cone. -/
def coneChartι (j : 𝓔.J) : ResolvedCone.scheme (φ j) ⟶ 𝒞.coneScheme :=
  Spec.map (CommRingCat.ofHom (𝒞.chartCone j).toRingHom) ≫ affineι X 𝒞.cone (𝓔.chart j)

instance isOpenImmersion_coneChartι (j : 𝓔.J) : IsOpenImmersion (𝒞.coneChartι j) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ affineι X 𝒞.cone (𝓔.chart j)))

/-- **The chart square.**  Over the chart `j` the closed immersion `C ↪ E₁` is the affine closed
immersion `ResolvedCone.toBundle (φ j)` of the affine model. -/
theorem coneChartι_coneι (j : 𝓔.J) :
    𝒞.coneChartι j ≫ 𝒞.coneι = ResolvedCone.toBundle (φ j) ≫ 𝒞.bundleChartι j := by
  have hring : CommRingCat.ofHom (𝒞.inclusion.app (𝓔.chart j)).toRingHom ≫
      CommRingCat.ofHom (𝒞.chartCone j).toRingHom =
    CommRingCat.ofHom (𝒞.chartBundle j).toRingHom ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (ResolvedCone.ideal (φ j))) := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    exact RingHom.ext fun a ↦ 𝒞.chartCone_inclusion j a
  rw [coneChartι, coneι, Category.assoc, RelativeSpec.Hom.affineι_map, ← Category.assoc,
    ← Spec.map_comp, bundleChartι, ResolvedCone.toBundle, ← Category.assoc, ← Spec.map_comp,
    hring]

/-- The points of the affine cone chart cover the set-theoretic fibre product of the global cone
with the affine bundle chart.  This is the ingredient the chart comparison of cycles needs. -/
theorem exists_coneChartι (j : 𝓔.J) (z : 𝒞.coneScheme) (e : ResolvedCone.bundleSpace (φ j))
    (h : (𝒞.bundleChartι j).base e = 𝒞.coneι.base z) :
    ∃ z' : ResolvedCone.scheme (φ j),
      (ResolvedCone.toBundle (φ j)).base z' = e ∧ (𝒞.coneChartι j).base z' = z := by
  set s := Spec.map (CommRingCat.ofHom (𝒞.chartCone j).toRingHom) with hs
  have hsiso : IsIso s := 𝒞.isIso_specMap_chartCone j
  -- `z` lies over the chart, hence in the range of the affine piece of the cone.
  have hbase : (toBase X 𝒞.cone).base z ∈ (𝓔.chart j).1 := by
    have h₁ : (toBase X 𝒞.cone).base z = (toBase X 𝓔.algebra).base (𝒞.coneι.base z) := by
      rw [← comp_base_apply, 𝒞.coneι_toBase]
    have h₂ : (𝒞.bundleChartι j).base e ∈ (affineι X 𝓔.algebra (𝓔.chart j)).opensRange := by
      exact ⟨_, rfl⟩
    rw [opensRange_affineι X 𝓔.algebra (𝓔.chart j)] at h₂
    rw [h₁, ← h]
    exact h₂
  have hz : z ∈ (affineι X 𝒞.cone (𝓔.chart j)).opensRange := by
    rw [opensRange_affineι X 𝒞.cone (𝓔.chart j)]
    exact hbase
  obtain ⟨z₀, hz₀⟩ := hz
  have hsz : s.base ((inv s).base z₀) = z₀ := by
    have hid : (inv s ≫ s).base z₀ = z₀ := base_apply_congr (IsIso.inv_hom_id s) z₀
    rw [comp_base_apply] at hid
    exact hid
  have hcone : (𝒞.coneChartι j).base ((inv s).base z₀) = z := by
    rw [coneChartι, ← hs, comp_base_apply, hsz, hz₀]
  refine ⟨(inv s).base z₀, ?_, hcone⟩
  have hsq := base_apply_congr (𝒞.coneChartι_coneι j) ((inv s).base z₀)
  simp only [comp_base_apply] at hsq
  rw [hcone, ← h] at hsq
  exact (𝒞.bundleChartι j).isOpenEmbedding.injective hsq.symm

/-- The chart square of the cone, as a pullback square: the affine resolved cone of `φ j` is the
intersection of the global cone with the affine bundle chart. -/
theorem isPullback_coneChart (j : 𝓔.J) :
    IsPullback (Spec.map (CommRingCat.ofHom (𝒞.inclusion.app (𝓔.chart j)).toRingHom))
      (affineι X 𝒞.cone (𝓔.chart j)) (affineι X 𝓔.algebra (𝓔.chart j)) 𝒞.coneι :=
  RelativeSpec.Hom.isPullback_map _ (𝓔.chart j)

/-! ## The global cone cycle -/

/-- The cone scheme is locally Noetherian as soon as all its affine coordinate rings are. -/
theorem isLocallyNoetherian_coneScheme
    (h : ∀ U : X.affineOpens, IsNoetherianRing (𝒞.cone.ring U)) :
    IsLocallyNoetherian 𝒞.coneScheme :=
  isLocallyNoetherian_relativeSpec X 𝒞.cone h

variable [IsLocallyNoetherian 𝒞.coneScheme]

/-- **The global cone cycle** `[C] ∈ Z_*(E₁)`: the residue-degree pushforward of the fundamental
cycle of the cone along the closed immersion `C ↪ E₁`, for a weight function `w` on the total
space (in practice a `DimensionFunction`). -/
def coneCycleOf (w : 𝓔.totalSpace → ℤ) : AlgebraicCycle 𝓔.totalSpace ℚ :=
  AlgebraicCycle.map 𝒞.coneι (fun z ↦ w (𝒞.coneι.base z)) w 𝒞.coneScheme.fundamentalCycle

/-- **The chart comparison.**  The restriction of the global cone cycle to the affine bundle
chart of `φ j` is the affine resolved-cone cycle: the pushforward of the fundamental cycle of
`ResolvedCone.scheme (φ j)` along `ResolvedCone.toBundle (φ j)`.

The weight function `wE` on the affine chart is arbitrary: both sides are pushforwards along a
closed immersion with the pulled-back source weight, so every multiplicity is one and the
weights cancel.  In the intended application `wE` is the restriction of `w` along the chart. -/
theorem pullbackOpen_bundleChartι_coneCycleOf [∀ j, IsNoetherianRing (R j)]
    [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
    [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero]
    (j : 𝓔.J) (w : 𝓔.totalSpace → ℤ) (wE : ResolvedCone.bundleSpace (φ j) → ℤ) :
    IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞.bundleChartι j) (𝒞.coneCycleOf w) =
      AlgebraicCycle.map (ResolvedCone.toBundle (φ j))
        (fun z ↦ wE ((ResolvedCone.toBundle (φ j)).base z)) wE
        (ResolvedCone.scheme (φ j)).fundamentalCycle := by
  have hfund : IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞.coneChartι j)
      𝒞.coneScheme.fundamentalCycle = (ResolvedCone.scheme (φ j)).fundamentalCycle :=
    IntersectionTheory.AlgebraicCycle.pullbackOpen_fundamentalCycle (𝒞.coneChartι j)
  rw [coneCycleOf, ← hfund]
  refine pullbackOpen_map_of_isClosedImmersion 𝒞.coneι (𝒞.bundleChartι j) (𝒞.coneChartι j)
    (ResolvedCone.toBundle (φ j)) (𝒞.coneChartι_coneι j) (fun z e he ↦ ?_) w wE
    𝒞.coneScheme.fundamentalCycle
  exact 𝒞.exists_coneChartι j z e he

/-! ## The graded cone cycle, its class, and the global virtual class -/

variable (dimE : DimensionFunction 𝓔.totalSpace)

/-- The global cone cycle for a certified dimension function on the total space. -/
def coneCycle : AlgebraicCycle 𝓔.totalSpace ℚ :=
  𝒞.coneCycleOf (dimE : 𝓔.totalSpace → ℤ)

/-- **The graded global cone cycle** `[C] ∈ Z_d(E₁)`: the dimension-`d` part of the cone
cycle. -/
def coneCycleAt (d : ℤ) : cyclesOfDimension 𝓔.totalSpace dimE d :=
  cyclesOfDimension.project (𝒞.coneCycle dimE)

/-- **The global cone class** `[C] ∈ A_d(E₁)`. -/
def coneClassAt (d : ℤ) (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE d) : RE.ChowGroup :=
  RE.quotientMap (𝒞.coneCycleAt dimE d)

/-- **The graded chart comparison**: restricting the global cone cycle to the chart `j` and
truncating in dimension `d` gives exactly the affine resolved-cone cycle
`VirtualClass.resolvedConeCycleAt (φ j)` of the affine model, for any certified dimension
function `dimC` on the affine chart. -/
theorem coneCycleAt_eq_resolvedConeCycleAt [∀ j, IsNoetherianRing (R j)]
    [∀ j, Module.Free (R j ⧸ I j) (E j).degreeZero]
    [∀ j, Module.Finite (R j ⧸ I j) (E j).degreeZero]
    (j : 𝓔.J) (d : ℤ) (dimC : DimensionFunction (ResolvedCone.bundleSpace (φ j))) :
    cyclesOfDimension.project (dimension := dimC) (i := d)
        (IntersectionTheory.AlgebraicCycle.pullbackOpen (𝒞.bundleChartι j)
          (𝒞.coneCycle dimE)) =
      VirtualFundamentalClass.VirtualClass.resolvedConeCycleAt (φ j) dimC d := by
  rw [coneCycle, 𝒞.pullbackOpen_bundleChartι_coneCycleOf j _ (dimC : _ → ℤ)]
  rfl

variable (dimX : DimensionFunction X) (i d : ℤ)
  (RX : RationalEquivalenceSystem X dimX i)
  (RE : RationalEquivalenceSystem 𝓔.totalSpace dimE d)
  (pull : RX.ChowGroup →ₗ[ℚ] RE.ChowGroup)

/-- **The global virtual class, modulo the global homotopy property of Chow groups.**

`pull` is the flat pullback `π^* : A_i(X) → A_d(E₁)` along the bundle projection, `hmem` says
that the cone class is in its image and (in `virtualClassOf_unique`) `hinj` says that `π^*` is
injective.  These three are exactly the global homotopy property of Chow groups (Fulton,
Prop. 1.9 and 3.3), which is **not** proved in this repository for a non-affine base: the
available statement `VectorBundle.chowPullbackBundle` is for a trivialised affine bundle.  They
are therefore explicit hypotheses here. -/
def virtualClassOf (hmem : 𝒞.coneClassAt dimE d RE ∈ LinearMap.range pull) : RX.ChowGroup :=
  (LinearMap.mem_range.mp hmem).choose

/-- The global virtual class pulls back to the global cone class. -/
theorem pull_virtualClassOf (hmem : 𝒞.coneClassAt dimE d RE ∈ LinearMap.range pull) :
    pull (𝒞.virtualClassOf dimE dimX i d RX RE pull hmem) = 𝒞.coneClassAt dimE d RE :=
  (LinearMap.mem_range.mp hmem).choose_spec

/-- The global virtual class is the unique preimage of the cone class, if `π^*` is injective. -/
theorem virtualClassOf_unique (hinj : Function.Injective pull)
    (hmem : 𝒞.coneClassAt dimE d RE ∈ LinearMap.range pull) (α : RX.ChowGroup)
    (hα : pull α = 𝒞.coneClassAt dimE d RE) :
    α = 𝒞.virtualClassOf dimE dimX i d RX RE pull hmem :=
  hinj (hα.trans (𝒞.pull_virtualClassOf dimE dimX i d RX RE pull hmem).symm)

/-- Existence and uniqueness of the global virtual class under the global homotopy property. -/
theorem existsUnique_virtualClass (hinj : Function.Injective pull)
    (hmem : 𝒞.coneClassAt dimE d RE ∈ LinearMap.range pull) :
    ∃! α : RX.ChowGroup, pull α = 𝒞.coneClassAt dimE d RE :=
  ⟨𝒞.virtualClassOf dimE dimX i d RX RE pull hmem,
    𝒞.pull_virtualClassOf dimE dimX i d RX RE pull hmem,
    fun α hα ↦ 𝒞.virtualClassOf_unique dimE dimX i d RX RE pull hinj hmem α hα⟩

end GlobalConeData

end

end VirtualClass.GlobalCone

end GromovWitten.AlgebraicGeometry
