/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ConeGluing
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.LocalisationCone
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Independence

/-!
# The overlap hypothesis of `LocalConeData` from local embeddings

`VirtualFundamentalClass/ConeGluing.lean` glues a global cone out of local affine obstruction
models `φ j` on the charts of a bundle `𝓔 : BundleData X ι`.  Its input `LocalConeData 𝓔 φ`
carries one geometric hypothesis, `LocalConeData.compat`: over every affine open `W` of the
overlap of two charts `i`, `j` the two resolved-cone ideals extend to the *same* ideal of
`𝓔.algebra.ring W`.  Stated like that the hypothesis is an ad-hoc equality of ideals.

This file shows that it is a *consequence* of the data one actually has in the geometric
situation, namely of local embeddings of `W` into the two affine models.  The input is packaged
in two steps.

* `LocalEmbeddingCore 𝓔 φ` carries, besides the chart identifications `chartBase`,
  `chartBundle`, `chartBundle_algebraMap` of `LocalConeData`, for every chart `j` and every
  affine open `W ≤ 𝓔.chart j`:
  - a flat, formally étale `R j`-algebra `chartRing j W h` together with a ring isomorphism
    `chartBaseExt j W h : (R' ⧸ (I j)·R') ≃+* Γ(X, W.1)` compatible with `chartBase j` and the
    restriction map `res X h` (field `chartBaseExt_algebraMap`) — that is, `W` is presented as a
    flat formally étale neighbourhood inside the affine model of the chart `j`;
  - a ring isomorphism `chartBundleExt j W h` of the bundle algebra `𝓔.algebra.ring W` with the
    bundle ring of the *base-changed* obstruction datum
    `LocalisationCone.baseChangeHom (I j) (chartRing j W h) (φ j)`, compatible with the
    transition map `𝓔.algebra.map h` and the canonical base-change map `baseChangeBundleHom`
    (field `chartBundleExt_map`).
* `LocalEmbeddingData 𝓔 φ` extends it with the comparison of two charts over the same `W`: an
  isomorphism `transition i j W hi hj` of the two base-changed bundle rings which is compatible
  with the two identifications of `𝓔.algebra.ring W` (`transition_chartBundleExt`) and which
  carries the resolved-cone ideal of one base-changed datum to that of the other
  (`transition_ideal`).

## Main results

* `ideal_map_baseChangeBundleHom` — the resolved-cone ideal of a flat formally étale base change
  is the extension of the resolved-cone ideal.  This is
  `LocalisationCone.ideal_map_bundleRingEquiv` rewritten along the canonical ring map
  `baseChangeBundleHom`, and it is what makes the reduction below work.
* `LocalEmbeddingData.map_chartIdeal_eq` — over `W` the extended chart ideal of the chart `i` is
  the transport of the resolved-cone ideal of the base-changed datum.  Only
  `LocalEmbeddingCore` data enters.
* `LocalEmbeddingData.compat` — **the overlap hypothesis of `LocalConeData` is a theorem**, and
  `LocalEmbeddingData.toLocalConeData` packages the whole input as a `LocalConeData 𝓔 φ`.
* `ideal_map_bundleEquiv_of_chainIso` — the way `transition_ideal` is discharged in practice:
  an isomorphism of two obstruction data over the *same* base ring, compatible with the maps to
  the conormal complex, induces `VirtualClass.bundleEquiv`, which carries the resolved-cone ideal
  to the resolved-cone ideal (round 15's `VirtualClass.ideal_map_bundleEquiv`).
* `LocalEmbeddingCore.toLocalEmbeddingDataOfAffine` — sanity check: for the round-17 affine
  bundle datum `GlobalConeAffine.bundleData φ`, whose chart index type is `PUnit`, the
  comparison data of `LocalEmbeddingData` can always be taken to be the identity, so every
  `LocalEmbeddingCore` is already a `LocalEmbeddingData`.

## What is an explicit hypothesis and what is proved

Everything in this file is unconditional given the fields of `LocalEmbeddingData`.  The field
`transition_ideal` is the only place where the independence of the resolved cone of the chosen
embedding is used; it is *not* derived from `transition` alone, because the two base-changed
obstruction data live over two different (though isomorphic) rings `chartRing i W hi ⧸ …` and
`chartRing j W hj ⧸ …`, and round 15's comparison
`VirtualClass.ideal_map_bundleEquiv` applies only to two obstruction data over the *same* ring.
The bridge lemma `ideal_map_bundleEquiv_of_chainIso` records that same-ring case verbatim; a
transport of `LinearTwoTermComplex`es along a ring isomorphism, which would turn the general
case into the same-ring case, is not available in the repository and is not attempted here.
-/

universe u

-- As in `ResolvedCone.lean` and `ConeGluing.lean`: the ring instances of the tensor products
-- occurring in `ResolvedCone.ideal` need one more level of pending instance problems.
set_option maxSynthPendingDepth 5

-- The index type of Mathlib's directed affine cover is definitionally, but not reducibly, the
-- type of affine opens; as in `ConeGluing.lean` the unifier is told not to respect transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace RelativeSpec
open NormalSheafPicard.AffineIntrinsicNormalSheaf
open VirtualFundamentalClass
open GlobalBlowup (res)

namespace VirtualClass.ConeGluing

noncomputable section

/-! ## A congruence lemma for `Ideal.map` -/

/-- Two ring homomorphisms (of possibly different bundled types) with the same underlying
function extend an ideal to the same ideal. -/
theorem ideal_map_congr_hom {A B : Type u} [Semiring A] [Semiring B] {F G : Type*}
    [FunLike F A B] [RingHomClass F A B] [FunLike G A B] [RingHomClass G A B] (f : F) (g : G)
    (h : ∀ a, f a = g a) (J : Ideal A) : J.map f = J.map g := by
  have himg : (f : A → B) '' (J : Set A) = (g : A → B) '' (J : Set A) :=
    Set.image_congr fun a _ => h a
  change Ideal.span _ = Ideal.span _
  rw [himg]

/-- Two ring homomorphisms (of possibly different bundled types) with the same underlying
function contract an ideal to the same ideal. -/
theorem ideal_comap_congr_hom {A B : Type u} [Semiring A] [Semiring B] {F G : Type*}
    [FunLike F A B] [RingHomClass F A B] [FunLike G A B] [RingHomClass G A B] (f : F) (g : G)
    (h : ∀ a, f a = g a) (J : Ideal B) : J.comap f = J.comap g := by
  ext a
  simp only [Ideal.mem_comap, h a]

/-! ## The canonical map to the base-changed bundle ring -/

section BaseChange

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)
variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra k R'] [IsScalarTower k R R']
variable [Module.Flat R R'] [Algebra.FormallyEtale R R']
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The canonical ring map from the bundle ring `Sym(E⁻¹)` of an affine obstruction datum to the
bundle ring of its base change along a flat formally étale extension `R → R'`.  It is the
inclusion `b ↦ 1 ⊗ b` of the right factor, read through
`LocalisationCone.bundleRingEquiv`. -/
def baseChangeBundleHom :
    ResolvedCone.bundleRing φ →+*
      ResolvedCone.bundleRing (LocalisationCone.baseChangeHom I R' φ) :=
  (LocalisationCone.bundleRingEquiv I R' φ).symm.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight :
      ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
        LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ).toRingHom

@[simp]
theorem baseChangeBundleHom_apply (a : ResolvedCone.bundleRing φ) :
    baseChangeBundleHom I R' φ a =
      (LocalisationCone.bundleRingEquiv I R' φ).symm
        ((1 : LocalisationCone.baseExt I R') ⊗ₜ[R ⧸ I] a) :=
  rfl

/-- **The resolved-cone ideal of a flat formally étale base change is the extension of the
resolved-cone ideal.**  This is `LocalisationCone.ideal_map_bundleRingEquiv` transported along
the canonical map `baseChangeBundleHom`. -/
theorem ideal_map_baseChangeBundleHom :
    Ideal.map (baseChangeBundleHom I R' φ) (ResolvedCone.ideal φ) =
      ResolvedCone.ideal (LocalisationCone.baseChangeHom I R' φ) := by
  have key : Ideal.map (Algebra.TensorProduct.includeRight :
        ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
          LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ).toRingHom
        (ResolvedCone.ideal φ) =
      Ideal.map (LocalisationCone.bundleRingEquiv I R' φ).toRingEquiv.toRingHom
        (ResolvedCone.ideal (LocalisationCone.baseChangeHom I R' φ)) := by
    refine Eq.trans (ideal_map_congr_hom _ (Algebra.TensorProduct.includeRight :
      ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
        LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ)
      (fun _ => rfl) _) ?_
    refine Eq.trans (LocalisationCone.ideal_map_bundleRingEquiv I R' φ).symm ?_
    exact ideal_map_congr_hom _ _ (fun _ => rfl) _
  have hcomp : (LocalisationCone.bundleRingEquiv I R' φ).symm.toRingEquiv.toRingHom.comp
      (LocalisationCone.bundleRingEquiv I R' φ).toRingEquiv.toRingHom = RingHom.id _ :=
    RingHom.ext fun x => (LocalisationCone.bundleRingEquiv I R' φ).symm_apply_apply x
  change Ideal.map ((LocalisationCone.bundleRingEquiv I R' φ).symm.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight :
      ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
        LocalisationCone.baseExt I R' ⊗[R ⧸ I] ResolvedCone.bundleRing φ).toRingHom)
    (ResolvedCone.ideal φ) = _
  rw [← Ideal.map_map, key, Ideal.map_map, hcomp, Ideal.map_id]

end BaseChange

/-! ## Comparing two obstruction data over the same ring -/

section ChainIso

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E E' : LinearTwoTermComplex (R ⧸ I)}

/-- **The form in which the field `LocalEmbeddingData.transition_ideal` is verified in
practice.**  If two affine obstruction data `φ`, `φ'` over the same ring are related by a chain
map `ψ` which is bijective in both degrees and compatible with the maps to the conormal complex,
then the induced isomorphism `VirtualClass.bundleEquiv` of bundle rings carries the
resolved-cone ideal of `φ` to the resolved-cone ideal of `φ'`.  This is round 15's
`VirtualClass.ideal_map_bundleEquiv`, restated for the `RingEquiv` underlying
`VirtualClass.bundleEquiv`. -/
theorem ideal_map_bundleEquiv_of_chainIso
    (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
    (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I))
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    Ideal.map (VirtualFundamentalClass.VirtualClass.bundleEquiv φ φ' ψ hψ0).toRingEquiv.toRingHom
        (ResolvedCone.ideal φ) = ResolvedCone.ideal φ' := by
  refine Eq.trans (ideal_map_congr_hom _ _ (fun _ => rfl) _) ?_
  exact VirtualFundamentalClass.VirtualClass.ideal_map_bundleEquiv φ φ' ψ hψ0 hψ1 hcomp

end ChainIso

/-! ## Local embedding data -/

/-- The *local embeddings* underlying a `LocalConeData`: besides the chart identifications of
`LocalConeData`, every affine open `W` of a chart `j` is presented as a flat, formally étale
neighbourhood `chartRing j W h` inside the affine model `R j` of that chart, compatibly with the
bundle algebra.  This is the input from which the overlap hypothesis of `LocalConeData` is
derived in `LocalEmbeddingData.compat`. -/
structure LocalEmbeddingCore {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
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
  /-- **(a)** The flat formally étale `R j`-algebra presenting an affine open `W` of the chart
  `j` inside the affine model of that chart. -/
  chartRing : ∀ (j : 𝓔.J) (W : X.affineOpens), W ≤ 𝓔.chart j → Type u
  [commRingChartRing : ∀ j W h, CommRing (chartRing j W h)]
  [algebraChartRing : ∀ j W h, Algebra (R j) (chartRing j W h)]
  [algebraBaseChartRing : ∀ j W h, Algebra k (chartRing j W h)]
  [isScalarTowerChartRing : ∀ j W h, IsScalarTower k (R j) (chartRing j W h)]
  [flatChartRing : ∀ j W h, Module.Flat (R j) (chartRing j W h)]
  [formallyEtaleChartRing : ∀ j W h, Algebra.FormallyEtale (R j) (chartRing j W h)]
  /-- The sections over `W` are the quotient of `chartRing j W h` by the extension of `I j`. -/
  chartBaseExt : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j),
    LocalisationCone.baseExt (I j) (chartRing j W h) ≃+* Γ(X, W.1)
  /-- `chartBaseExt` is compatible with `chartBase` and the restriction map of `X`. -/
  chartBaseExt_algebraMap : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j)
      (a : Γ(X, (𝓔.chart j).1)),
    chartBaseExt j W h (algebraMap (R j ⧸ I j)
        (LocalisationCone.baseExt (I j) (chartRing j W h)) (chartBase j a)) = res X h a
  /-- **(b)** The identification of the bundle algebra over `W` with the bundle ring of the
  base-changed obstruction datum of the chart `j`. -/
  chartBundleExt : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j),
    𝓔.algebra.ring W ≃+*
      ResolvedCone.bundleRing (LocalisationCone.baseChangeHom (I j) (chartRing j W h) (φ j))
  /-- The identification `chartBundleExt` intertwines the transition map `𝓔.algebra.map h` of
  the bundle algebra with the canonical base-change map of bundle rings. -/
  chartBundleExt_map : ∀ (j : 𝓔.J) (W : X.affineOpens) (h : W ≤ 𝓔.chart j)
      (a : 𝓔.algebra.ring (𝓔.chart j)),
    chartBundleExt j W h (𝓔.algebra.map h a) =
      baseChangeBundleHom (I j) (chartRing j W h) (φ j) (chartBundle j a)

attribute [instance] LocalEmbeddingCore.commRingChartRing LocalEmbeddingCore.algebraChartRing
  LocalEmbeddingCore.algebraBaseChartRing LocalEmbeddingCore.isScalarTowerChartRing
  LocalEmbeddingCore.flatChartRing LocalEmbeddingCore.formallyEtaleChartRing

/-- Local embedding data: `LocalEmbeddingCore` together with the comparison, over every affine
open `W` of the overlap of two charts, of the two base-changed obstruction data.  The comparison
is an isomorphism of the two bundle rings which is compatible with the two identifications of
`𝓔.algebra.ring W` and which matches the two resolved-cone ideals. -/
structure LocalEmbeddingData {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
    (𝓔 : BundleData X ι) {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
    {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
    (φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j)))
    extends LocalEmbeddingCore 𝓔 φ where
  /-- **(c)** The comparison isomorphism of the two base-changed bundle rings over an affine
  open of the overlap of two charts. -/
  transition : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i) (hj : W ≤ 𝓔.chart j),
    ResolvedCone.bundleRing (LocalisationCone.baseChangeHom (I i) (chartRing i W hi) (φ i)) ≃+*
      ResolvedCone.bundleRing (LocalisationCone.baseChangeHom (I j) (chartRing j W hj) (φ j))
  /-- The comparison isomorphism is compatible with the two identifications of the bundle
  algebra over `W`. -/
  transition_chartBundleExt : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i)
      (hj : W ≤ 𝓔.chart j) (a : 𝓔.algebra.ring W),
    transition i j W hi hj (chartBundleExt i W hi a) = chartBundleExt j W hj a
  /-- The comparison isomorphism carries the resolved-cone ideal of one base-changed datum to
  the resolved-cone ideal of the other.  This is the independence of the resolved cone of the
  chosen local embedding; see `ideal_map_bundleEquiv_of_chainIso`. -/
  transition_ideal : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i)
      (hj : W ≤ 𝓔.chart j),
    Ideal.map (transition i j W hi hj).toRingHom
        (ResolvedCone.ideal (LocalisationCone.baseChangeHom (I i) (chartRing i W hi) (φ i))) =
      ResolvedCone.ideal (LocalisationCone.baseChangeHom (I j) (chartRing j W hj) (φ j))

namespace LocalEmbeddingData

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι}
variable {R : 𝓔.J → Type u} [∀ j, CommRing (R j)] [∀ j, Algebra k (R j)]
variable {I : ∀ j, Ideal (R j)} {E : ∀ j, LinearTwoTermComplex (R j ⧸ I j)}
variable {φ : ∀ j, LinearTwoTermComplex.Hom (E j) (conormalComplex k (R j) (I j))}
variable (𝓛 : LocalEmbeddingData 𝓔 φ)

/-- The resolved-cone ideal of the chart `j`, pulled back to the bundle algebra of that chart.
It is the ideal called `LocalConeData.chartIdeal` in `ConeGluing.lean`. -/
def chartIdeal (j : 𝓔.J) : Ideal (𝓔.algebra.ring (𝓔.chart j)) :=
  (ResolvedCone.ideal (φ j)).comap (𝓛.chartBundle j).toRingHom

/-- The chart ideal is the transport of the resolved-cone ideal along `chartBundle`. -/
theorem chartIdeal_eq_map (j : 𝓔.J) :
    𝓛.chartIdeal j = Ideal.map (𝓛.chartBundle j).symm.toRingHom (ResolvedCone.ideal (φ j)) := by
  have h1 : Ideal.map (𝓛.chartBundle j).symm (ResolvedCone.ideal (φ j)) =
      Ideal.comap (𝓛.chartBundle j) (ResolvedCone.ideal (φ j)) :=
    Ideal.map_symm (𝓛.chartBundle j)
  change Ideal.comap (𝓛.chartBundle j).toRingHom (ResolvedCone.ideal (φ j)) = _
  rw [ideal_comap_congr_hom (𝓛.chartBundle j).toRingHom (𝓛.chartBundle j) (fun _ => rfl), ← h1]
  exact ideal_map_congr_hom _ _ (fun _ => rfl) _

/-- Over an affine open `W` of the chart `i`, the extension of the chart ideal of `i` is the
transport, along the identification `chartBundleExt i W hi`, of the resolved-cone ideal of the
base-changed obstruction datum.  This uses only the `LocalEmbeddingCore` fields. -/
theorem map_chartIdeal_eq (i : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i) :
    (𝓛.chartIdeal i).map (𝓔.algebra.map hi) =
      Ideal.map (𝓛.chartBundleExt i W hi).symm.toRingHom
        (ResolvedCone.ideal
          (LocalisationCone.baseChangeHom (I i) (𝓛.chartRing i W hi) (φ i))) := by
  have hmap : ((𝓔.algebra.map hi).comp (𝓛.chartBundle i).symm.toRingHom) =
      (𝓛.chartBundleExt i W hi).symm.toRingHom.comp
        (baseChangeBundleHom (I i) (𝓛.chartRing i W hi) (φ i)) := by
    refine RingHom.ext fun b => ?_
    have hb := 𝓛.chartBundleExt_map i W hi ((𝓛.chartBundle i).symm b)
    rw [(𝓛.chartBundle i).apply_symm_apply] at hb
    change 𝓔.algebra.map hi ((𝓛.chartBundle i).symm b) =
      (𝓛.chartBundleExt i W hi).symm
        (baseChangeBundleHom (I i) (𝓛.chartRing i W hi) (φ i) b)
    rw [← hb, (𝓛.chartBundleExt i W hi).symm_apply_apply]
  rw [𝓛.chartIdeal_eq_map i, Ideal.map_map, hmap, ← Ideal.map_map,
    ideal_map_baseChangeBundleHom]

/-- The two identifications of the bundle algebra over an affine open of an overlap differ by
the comparison isomorphism. -/
theorem symm_chartBundleExt_comp_transition (i j : 𝓔.J) (W : X.affineOpens)
    (hi : W ≤ 𝓔.chart i) (hj : W ≤ 𝓔.chart j) :
    (𝓛.chartBundleExt j W hj).symm.toRingHom.comp (𝓛.transition i j W hi hj).toRingHom =
      (𝓛.chartBundleExt i W hi).symm.toRingHom := by
  refine RingHom.ext fun b => ?_
  have hb := 𝓛.transition_chartBundleExt i j W hi hj ((𝓛.chartBundleExt i W hi).symm b)
  rw [(𝓛.chartBundleExt i W hi).apply_symm_apply] at hb
  change (𝓛.chartBundleExt j W hj).symm (𝓛.transition i j W hi hj b) =
    (𝓛.chartBundleExt i W hi).symm b
  rw [hb, (𝓛.chartBundleExt j W hj).symm_apply_apply]

/-- **The overlap hypothesis of `LocalConeData` is a theorem for local embedding data.**  Over
every affine open `W` of the overlap of two charts the two resolved-cone ideals extend to the
same ideal of the bundle algebra `𝓔.algebra.ring W`. -/
theorem compat : ∀ (i j : 𝓔.J) (W : X.affineOpens) (hi : W ≤ 𝓔.chart i) (hj : W ≤ 𝓔.chart j),
    (𝓛.chartIdeal i).map (𝓔.algebra.map hi) = (𝓛.chartIdeal j).map (𝓔.algebra.map hj) := by
  intro i j W hi hj
  rw [𝓛.map_chartIdeal_eq i W hi, 𝓛.map_chartIdeal_eq j W hj,
    ← 𝓛.transition_ideal i j W hi hj, Ideal.map_map, 𝓛.symm_chartBundleExt_comp_transition]

/-- **Local embedding data gives local cone data.**  The overlap hypothesis
`LocalConeData.compat` is discharged by `LocalEmbeddingData.compat`. -/
def toLocalConeData : LocalConeData 𝓔 φ where
  chartBase := 𝓛.chartBase
  chartBundle := 𝓛.chartBundle
  chartBundle_algebraMap := 𝓛.chartBundle_algebraMap
  compat := 𝓛.compat

@[simp]
theorem toLocalConeData_chartBundle (j : 𝓔.J) :
    𝓛.toLocalConeData.chartBundle j = 𝓛.chartBundle j :=
  rfl

@[simp]
theorem toLocalConeData_chartBase (j : 𝓔.J) : 𝓛.toLocalConeData.chartBase j = 𝓛.chartBase j :=
  rfl

/-- The chart ideal of the associated `LocalConeData` is the chart ideal. -/
theorem toLocalConeData_chartIdeal (j : 𝓔.J) :
    𝓛.toLocalConeData.chartIdeal j = 𝓛.chartIdeal j :=
  rfl

end LocalEmbeddingData

/-! ## The single-chart case

For the round-17 affine bundle datum `GlobalConeAffine.bundleData φ` the chart index type is
`PUnit` and the single chart is `⊤`.  Two charts `i`, `j` and two proofs `hi`, `hj` are then
definitionally equal (structure eta for `PUnit`, proof irrelevance), so the comparison data of
`LocalEmbeddingData` can be taken to be the identity: every `LocalEmbeddingCore` over that
bundle datum is already a `LocalEmbeddingData`. -/

section Affine

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
  {E : LinearTwoTermComplex (R ⧸ I)} [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero]
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}

/-- **Sanity check for the single-chart case**: over the affine bundle datum of round 17 the
comparison data (c) of `LocalEmbeddingData` is trivial, so any choice of local embeddings (a),
(b) already constitutes local embedding data. -/
def LocalEmbeddingCore.toLocalEmbeddingDataOfAffine
    (𝓒 : LocalEmbeddingCore (k := k) (GlobalConeAffine.bundleData φ)
      (R := fun _ ↦ R) (I := fun _ ↦ I) (E := fun _ ↦ E) (fun _ ↦ φ)) :
    LocalEmbeddingData (k := k) (GlobalConeAffine.bundleData φ)
      (R := fun _ ↦ R) (I := fun _ ↦ I) (E := fun _ ↦ E) (fun _ ↦ φ) where
  toLocalEmbeddingCore := 𝓒
  transition _ _ _ _ _ := RingEquiv.refl _
  transition_chartBundleExt _ _ _ _ _ _ := rfl
  transition_ideal i j W hi hj := by
    refine Eq.trans (ideal_map_congr_hom _ (RingHom.id _) (fun _ => rfl) _) ?_
    exact Ideal.map_id _

end Affine

end

end VirtualClass.ConeGluing

end GromovWitten.AlgebraicGeometry
