/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.RelativeSpec
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChernClasses

/-!
# The total space of a vector bundle over a scheme

A vector bundle of rank `r` over a scheme `X` is described here by the quasi-coherent algebra of
functions on its total space, together with an augmentation (the zero section) and a family of
trivialisations over affine opens covering `X`.  The data is packaged in `BundleData X ι`: a
`RelativeSpec.AlgebraData X`, a morphism of algebra data to the structure sheaf
(`structureData X`, the quasi-coherent algebra `𝒪_X` itself), an index type `J` of charts
`chart j : X.affineOpens` covering `X`, and algebra isomorphisms
`triv j : 𝓔.algebra.ring (chart j) ≃ₐ[Γ(X, chart j)] MvPolynomial ι Γ(X, chart j)` under which
the augmentation becomes evaluation at the origin.

The total space is the relative `Spec` of the algebra (`BundleData.totalSpace`), the projection is
its structure morphism (`BundleData.proj`, an affine morphism), and the zero section
(`BundleData.zeroSection`) is the morphism of relative spectra induced by the augmentation,
transported along the canonical isomorphism `relativeSpec X (structureData X) ≅ X` (`baseIso`).
It is a section of the projection (`BundleData.zeroSection_proj`) and a closed immersion
(`BundleData.isClosedImmersion_zeroSection`).

Over a chart the total space is the affine space `Spec (MvPolynomial ι Γ(X, chart j))`:
`BundleData.isPullback_chart` exhibits the square

```
Spec (MvPolynomial ι Γ(X, U))  →  total space
            ↓                          ↓
           U                    →      X
```

as cartesian, with the left leg the affine-space projection composed with
`IsAffineOpen.isoSpec.inv`, and `BundleData.zeroSection_chart` identifies the zero section over a
chart with the vertex section `GradedCone.vertexSection (MvPolynomial.aeval 0)` of that affine
space.

## Main declarations

* `structureData X` — the structure sheaf as quasi-coherent algebra, with
  `isIso_toBase_structureData` and `baseIso X : relativeSpec X (structureData X) ≅ X`;
* `BundleData X ι` — the data of a vector bundle with trivialising charts;
* `BundleData.totalSpace`, `BundleData.proj`, `BundleData.zeroSection`;
* `BundleData.zeroSection_proj`, `BundleData.isClosedImmersion_zeroSection`;
* `BundleData.chartIso`, `BundleData.chartι`, `BundleData.isPullback_chart`,
  `BundleData.zeroSection_chart`;
* `opensRange_affineι`, `BundleData.opensRange_chartι`, `BundleData.iSup_opensRange_chartι` —
  the charts of the total space are the preimages of the charts of the base, and they cover it;
* `BundleData.chartBundlePoint` and `BundleData.proj_chartBundlePoint` — the generic point of the
  fibre over a point of a chart.  Its independence of the chart is not proved here.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

open GlobalBlowup RelativeSpec IntersectionTheory

universe u

noncomputable section

/-! ### The structure sheaf as a quasi-coherent algebra -/

/- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
type of affine opens; as in Mathlib's own development of that cover, the unifier is told not to
respect transparency in this file. -/
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X`, viewed as a quasi-coherent algebra: the ring over an affine open
`U` is `Γ(X, U)` itself and the transition maps are the restriction maps. -/
def structureData : AlgebraData X where
  ring U := Γ(X, U.1)
  map h := res X h
  map_id U := res_refl X U
  map_comp hUV hVW := res_comp X hUV hVW
  isPushout {U V} h := by
    have hV : CommRingCat.ofHom (algebraMap Γ(X, V.1) Γ(X, V.1)) =
        𝟙 (CommRingCat.of Γ(X, V.1)) := rfl
    have hU : CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, U.1)) =
        𝟙 (CommRingCat.of Γ(X, U.1)) := rfl
    rw [hV, hU]
    exact IsPushout.of_horiz_isIso ⟨by simp⟩

@[simp]
theorem structureData_ring (U : X.affineOpens) : (structureData X).ring U = Γ(X, U.1) := rfl

theorem bijective_algebraMap_structureData (U : X.affineOpens) :
    Function.Bijective (algebraMap Γ(X, U.1) ((structureData X).ring U)) :=
  ⟨fun _ _ h ↦ h, fun a ↦ ⟨a, rfl⟩⟩

instance isIso_toBase_structureData : IsIso (toBase X (structureData X)) :=
  isIso_toBase_of_bijective X _ (bijective_algebraMap_structureData X)

/-- The affine piece of a relative `Spec` over an affine open `U` is exactly the preimage of `U`
under the structure morphism. -/
theorem opensRange_affineι (𝒜 : AlgebraData X) (U : X.affineOpens) :
    (affineι X 𝒜 U).opensRange = toBase X 𝒜 ⁻¹ᵁ U.1 := by
  have h : (X.directedAffineCover.f U).opensRange = U.1 := Scheme.Opens.opensRange_ι U.1
  change (colimit.ι (gluingData X 𝒜).functor U).opensRange =
    (gluingData X 𝒜).toBase ⁻¹ᵁ U.1
  conv_rhs => rw [← h]
  exact ((gluingData X 𝒜).toBase_preimage_eq_opensRange_ι U).symm

/-- The relative `Spec` of the structure sheaf is `X` itself. -/
def baseIso : relativeSpec X (structureData X) ≅ X := asIso (toBase X (structureData X))

@[simp]
theorem baseIso_hom : (baseIso X).hom = toBase X (structureData X) := rfl

/-- The affine chart of `relativeSpec X (structureData X)` over an affine open `U` is, after the
identification `baseIso X`, the inclusion of `U`. -/
theorem affineι_structureData_baseIso (U : X.affineOpens) :
    affineι X (structureData X) U ≫ (baseIso X).hom = (isAffineOpen X U).isoSpec.inv ≫ U.1.ι := by
  rw [baseIso_hom, affineι_toBase]
  congr 1
  change Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, U.1))) ≫ _ = _
  have hU : CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, U.1)) =
      𝟙 (CommRingCat.of Γ(X, U.1)) := rfl
  rw [hU, Spec.map_id, Category.id_comp]

/-! ### Vector bundle data -/

/-- The data of a vector bundle of rank `ι` over a scheme `X`, described by its algebra of
functions: a quasi-coherent algebra `algebra` (the total space is its relative `Spec`), an
augmentation `augmentation` to the structure sheaf (the zero section), and a family of affine
opens `chart j` covering `X` over which `algebra` is trivialised by `triv j` as a polynomial
algebra in the variables `ι`, in such a way that the augmentation becomes evaluation at the
origin.  No finiteness of `ι` is required here; it is imposed at the places where the rank
matters. -/
structure BundleData (X : Scheme.{u}) (ι : Type u) where
  /-- The quasi-coherent algebra of functions on the total space. -/
  algebra : AlgebraData X
  /-- The augmentation to the structure sheaf; it induces the zero section. -/
  augmentation : RelativeSpec.Hom X (structureData X) algebra
  /-- The index type of the trivialising charts. -/
  J : Type u
  /-- The trivialising charts, affine opens of `X`. -/
  chart : J → X.affineOpens
  /-- The charts cover `X`. -/
  iSup_chart : ⨆ j, (chart j).1 = ⊤
  /-- The trivialisation of the algebra over a chart. -/
  triv : ∀ j, algebra.ring (chart j) ≃ₐ[Γ(X, (chart j).1)] MvPolynomial ι Γ(X, (chart j).1)
  /-- In the chart coordinates the augmentation is evaluation at the origin. -/
  augmentation_triv : ∀ (j : J) (a : algebra.ring (chart j)),
    augmentation.app (chart j) a =
      MvPolynomial.aeval (fun _ ↦ (0 : Γ(X, (chart j).1))) (triv j a)

namespace BundleData

variable {X} {ι : Type u} (𝓔 : BundleData X ι)

/-- The total space of the bundle: the relative `Spec` of its algebra of functions. -/
abbrev totalSpace : Scheme.{u} := relativeSpec X 𝓔.algebra

/-- The projection from the total space to the base. -/
def proj : 𝓔.totalSpace ⟶ X := toBase X 𝓔.algebra

instance isAffineHom_proj : IsAffineHom 𝓔.proj := toBase_isAffineHom X 𝓔.algebra

/-- The augmentation is surjective on every affine open: it is a retraction of the structure
map of the algebra. -/
theorem surjective_augmentation_app (U : X.affineOpens) :
    Function.Surjective (𝓔.augmentation.app U) := fun a ↦
  ⟨algebraMap Γ(X, U.1) (𝓔.algebra.ring U) a, (𝓔.augmentation.app U).commutes a⟩

/-- The zero section of the bundle. -/
def zeroSection : X ⟶ 𝓔.totalSpace := (baseIso X).inv ≫ 𝓔.augmentation.map

theorem zeroSection_proj : 𝓔.zeroSection ≫ 𝓔.proj = 𝟙 X := by
  rw [zeroSection, proj, Category.assoc, RelativeSpec.Hom.map_toBase]
  exact (baseIso X).inv_hom_id

instance isClosedImmersion_zeroSection : IsClosedImmersion 𝓔.zeroSection := by
  have h : IsClosedImmersion 𝓔.augmentation.map :=
    RelativeSpec.Hom.map_isClosedImmersion _ 𝓔.surjective_augmentation_app
  change IsClosedImmersion ((baseIso X).inv ≫ 𝓔.augmentation.map)
  infer_instance

/-! ### Local trivialisations -/

/-- Evaluation at the origin of a chart: the augmentation of the trivialised bundle
`𝔸^ι_U = Spec (MvPolynomial ι Γ(X, U))`. -/
abbrev chartAugmentation (j : 𝓔.J) :
    MvPolynomial ι Γ(X, (𝓔.chart j).1) →ₐ[Γ(X, (𝓔.chart j).1)] Γ(X, (𝓔.chart j).1) :=
  MvPolynomial.aeval fun _ ↦ 0

/-- The trivialisation of the total space over a chart, as an isomorphism of affine schemes. -/
def chartIso (j : 𝓔.J) :
    Spec (CommRingCat.of (𝓔.algebra.ring (𝓔.chart j))) ≅
      Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))) :=
  (VectorBundle.specIsoOfAlgEquiv (𝓔.triv j)).symm

theorem chartIso_inv (j : 𝓔.J) :
    (𝓔.chartIso j).inv = Spec.map (CommRingCat.ofHom (𝓔.triv j).toRingHom) := rfl

/-- The trivialising chart of the total space: the affine space `𝔸^ι_U` over a chart `U`, as an
open subscheme of the total space. -/
def chartι (j : 𝓔.J) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.chart j).1))) ⟶ 𝓔.totalSpace :=
  (𝓔.chartIso j).inv ≫ affineι X 𝓔.algebra (𝓔.chart j)

instance isOpenImmersion_chartι (j : 𝓔.J) : IsOpenImmersion (𝓔.chartι j) := by
  change IsOpenImmersion ((𝓔.chartIso j).inv ≫ affineι X 𝓔.algebra (𝓔.chart j))
  infer_instance

/-- Under the trivialisation, the structure morphism of the affine piece of the total space over
a chart becomes the projection of the affine space `𝔸^ι_U`. -/
theorem chartIso_inv_projection (j : 𝓔.J) :
    (𝓔.chartIso j).inv ≫ projection X 𝓔.algebra (𝓔.chart j) =
      Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1)))) ≫
        (isAffineOpen X (𝓔.chart j)).isoSpec.inv := by
  have key : CommRingCat.ofHom (algebraMap Γ(X, (𝓔.chart j).1) (𝓔.algebra.ring (𝓔.chart j))) ≫
      CommRingCat.ofHom (𝓔.triv j).toRingHom =
      CommRingCat.ofHom
        (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1))) :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ (𝓔.triv j).commutes a)
  change Spec.map (CommRingCat.ofHom (𝓔.triv j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, (𝓔.chart j).1) (𝓔.algebra.ring (𝓔.chart j)))) ≫
      (isAffineOpen X (𝓔.chart j)).isoSpec.inv = _
  rw [← Category.assoc, ← Spec.map_comp, key]

/-- The local trivialisation of the total space: over a chart `U`, the total space is the affine
space `𝔸^ι_U = Spec (MvPolynomial ι Γ(X, U))`. -/
theorem isPullback_chart (j : 𝓔.J) :
    IsPullback (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1)))) ≫
        (isAffineOpen X (𝓔.chart j)).isoSpec.inv) (𝓔.chartι j) (𝓔.chart j).1.ι 𝓔.proj := by
  refine (isPullback_affine X 𝓔.algebra (𝓔.chart j)).of_iso (𝓔.chartIso j) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, ← chartIso_inv_projection, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, chartι, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  · simp
  · simp [proj]

/-- The trivialising chart of the total space is the preimage of the chart of the base. -/
theorem opensRange_chartι (j : 𝓔.J) :
    (𝓔.chartι j).opensRange = 𝓔.proj ⁻¹ᵁ (𝓔.chart j).1 :=
  (Scheme.Hom.opensRange_comp_of_isIso (𝓔.chartIso j).inv
    (affineι X 𝓔.algebra (𝓔.chart j))).trans (opensRange_affineι X 𝓔.algebra (𝓔.chart j))

/-- The trivialising charts cover the total space. -/
theorem iSup_opensRange_chartι : ⨆ j, (𝓔.chartι j).opensRange = ⊤ := by
  simp_rw [opensRange_chartι]
  exact 𝓔.proj.iSup_preimage_eq_top 𝓔.iSup_chart

/-- In the chart coordinates, the augmentation is evaluation at the origin. -/
theorem specMap_augmentation_app_chart (j : 𝓔.J) :
    Spec.map (CommRingCat.ofHom (𝓔.augmentation.app (𝓔.chart j)).toRingHom) =
      GradedCone.vertexSection (𝓔.chartAugmentation j) ≫ (𝓔.chartIso j).inv := by
  have key : CommRingCat.ofHom (𝓔.augmentation.app (𝓔.chart j)).toRingHom =
      CommRingCat.ofHom (𝓔.triv j).toRingHom ≫
        CommRingCat.ofHom (𝓔.chartAugmentation j).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ 𝓔.augmentation_triv j a)
  rw [key, Spec.map_comp]
  rfl

/-- Over a chart, the zero section of the bundle is the vertex section of the affine space
`𝔸^ι_U`. -/
theorem zeroSection_chart (j : 𝓔.J) :
    (isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι ≫ 𝓔.zeroSection =
      GradedCone.vertexSection (𝓔.chartAugmentation j) ≫ 𝓔.chartι j := by
  have h₁ : (isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι ≫ (baseIso X).inv =
      affineι X (structureData X) (𝓔.chart j) := by
    rw [← Category.assoc, ← affineι_structureData_baseIso X (𝓔.chart j), Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  calc (isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι ≫ 𝓔.zeroSection
      = ((isAffineOpen X (𝓔.chart j)).isoSpec.inv ≫ (𝓔.chart j).1.ι ≫ (baseIso X).inv) ≫
          𝓔.augmentation.map := by rw [zeroSection]; simp only [Category.assoc]
    _ = affineι X (structureData X) (𝓔.chart j) ≫ 𝓔.augmentation.map := by rw [h₁]
    _ = Spec.map (CommRingCat.ofHom (𝓔.augmentation.app (𝓔.chart j)).toRingHom) ≫
          affineι X 𝓔.algebra (𝓔.chart j) := 𝓔.augmentation.affineι_map (𝓔.chart j)
    _ = GradedCone.vertexSection (𝓔.chartAugmentation j) ≫ 𝓔.chartι j := by
        rw [specMap_augmentation_app_chart, chartι, Category.assoc]

/-! ### Generic points of the fibres over a chart -/

/-- A point of a chart of the base, read as a point of the spectrum of its section ring. -/
def chartBasePoint (j : 𝓔.J) (x : (𝓔.chart j).1.toScheme) :
    ↥(Spec (CommRingCat.of Γ(X, (𝓔.chart j).1))) :=
  (isAffineOpen X (𝓔.chart j)).isoSpec.hom.base x

/-- The generic point of the fibre of the bundle over a point of a chart, as a point of the total
space: the generic point of the fibre of the trivialised affine space `𝔸^ι_U`, pushed into the
total space along the chart.  Independence of the chart is not proved here. -/
def chartBundlePoint (j : 𝓔.J) (x : (𝓔.chart j).1.toScheme) : 𝓔.totalSpace :=
  (𝓔.chartι j).base (VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1))) (𝓔.chartBasePoint j x))

/-- The generic point of the fibre over `x` lies over `x`. -/
theorem proj_chartBundlePoint (j : 𝓔.J) (x : (𝓔.chart j).1.toScheme) :
    𝓔.proj.base (𝓔.chartBundlePoint j x) = (𝓔.chart j).1.ι.base x := by
  have h : 𝓔.proj.base (𝓔.chartBundlePoint j x) =
      (𝓔.chartι j ≫ 𝓔.proj).base (VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        (𝓔.chartBasePoint j x)) := rfl
  rw [h, ← (𝓔.isPullback_chart j).w]
  change (𝓔.chart j).1.ι.base ((isAffineOpen X (𝓔.chart j)).isoSpec.inv.base
    ((GradedCone.projection Γ(X, (𝓔.chart j).1)
      (MvPolynomial ι Γ(X, (𝓔.chart j).1))).base (VectorBundle.bundlePoint
        (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.chart j).1)))
        (𝓔.chartBasePoint j x)))) = _
  rw [VectorBundle.projection_base_bundlePoint]
  change (𝓔.chart j).1.ι.base (((isAffineOpen X (𝓔.chart j)).isoSpec.hom ≫
    (isAffineOpen X (𝓔.chart j)).isoSpec.inv).base x) = _
  rw [Iso.hom_inv_id]
  rfl

end BundleData

end

end GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
