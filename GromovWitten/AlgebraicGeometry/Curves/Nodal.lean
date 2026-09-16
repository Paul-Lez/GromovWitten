/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import GromovWitten.AlgebraicGeometry.Curves.RelativeDimension
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.LocalNode

/-!
# Nodal curves and nodal families

This file provides the shared nodal-family predicate used by the stable-reduction and stable-map
layers.  The definition is geometric: after every field-valued base change, every point admits
an étale neighbourhood which is either smooth over the field or étale over the standard node
`xy = 0`.  Flatness, finite presentation, and geometric pure relative dimension one are recorded
separately, so they are available without unpacking local charts.

The geometric-fibre clause is stated for arbitrary pullback squares rather than only the chosen
`pullback`.  This makes stability under arbitrary base change a direct pasting argument.

## Locality for surjective étale covers of the source

For `e : Y ⟶ X` surjective étale and `f : X ⟶ S`, all four fields of `AtWorstNodal` descend from
`e ≫ f` to `f`: flatness (`flat_of_precomp_surjective_etale`), finite presentation
(`locallyOfFinitePresentation_of_precomp_surjective_etale`, which rests on the étale source
descent of finite presentation proved in `RelativeDimension`), geometric pure relative dimension
one (`geometricPureRelativeDimension_of_precomp_surjective_etale`), and the geometric-fibre charts
(`geometricFibers_of_precomp_surjective_etale`).  `AtWorstNodal.of_precomp_surjective_etale`
assembles them, with no hypothesis on `f`.

The *ascending* direction is different.  `AtWorstNodal.precomp_etale` carries geometric pure
relative dimension one of `e ≫ f` as an explicit hypothesis, so
`AtWorstNodal.iff_precomp_surjective_etale` states the equivalence with that datum on the side of
the cover.  The hypothesis is true for the geometric fibres at hand, which are locally of finite
type over a field, but it is not currently derivable: it does not follow topologically (a
surjective étale
cover of a scheme may have a component of strictly smaller dimension, as for the disjoint union of
a scheme with a proper open subscheme), and deducing it uses dimension theory of schemes of finite
type over a field, which the pinned Mathlib does not provide.
-/

open CategoryTheory Limits
open TensorProduct
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {X S : Scheme.{u}}

/-- Flatness of ring maps descends through a faithfully flat map on the target. -/
private lemma ringHomFlat_of_comp_of_faithfullyFlat
    {R T U : Type u} [CommRing R] [CommRing T] [CommRing U]
    {f : R →+* T} {g : T →+* U}
    (hg : g.FaithfullyFlat) (hgf : (g.comp f).Flat) : f.Flat := by
  algebraize [f, g, g.comp f]
  rw [RingHom.Flat] at hgf ⊢
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  let _ : Module.FaithfullyFlat T U := hg
  rw [← AlgebraTensorModule.coe_lTensor (A := T)]
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective T U
    (AlgebraTensorModule.lTensor T T N.subtype)).mp
  rw [← AlgebraTensorModule.coe_lTensor (A := T)]
  rw [← EquivLike.comp_injective _ (AlgebraTensorModule.cancelBaseChange R T T U P),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp,
    ← AlgebraTensorModule.lTensor_comp_cancelBaseChange, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- The standard nodal curve `Spec(K[x,y]/(xy)) → Spec K`. -/
abbrev standardNodeToSpec (K : Type u) [CommRing K] :
    Spec (.of (StableReduction.LocalNode.Ring K 0 1)) ⟶ Spec (.of K) :=
  StableReduction.LocalNode.toBaseSpec K 0 1

/-- A smooth étale neighbourhood of a specified point of a curve over a field. -/
structure SmoothChartAt {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) (x : X) where
  source : Scheme.{u}
  point : source
  toCurve : source ⟶ X
  etale_toCurve : Etale toCurve
  mapsToPoint : toCurve point = x
  smooth_toBase : Smooth (toCurve ≫ f)

/-- An étale neighbourhood of a specified point equipped with an étale map to the standard
node over the same field. -/
structure NodeChartAt {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) (x : X) where
  source : Scheme.{u}
  point : source
  toCurve : source ⟶ X
  toNode : source ⟶ Spec (.of (StableReduction.LocalNode.Ring K 0 1))
  etale_toCurve : Etale toCurve
  etale_toNode : Etale toNode
  mapsToPoint : toCurve point = x
  overBase : toCurve ≫ f = toNode ≫ standardNodeToSpec K

namespace NodeChartAt

/-- A node chart transports along an isomorphism of its ambient curve over the field. -/
def postcompIso {Y : Scheme.{u}} {K : Type u} [Field K]
    {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {x : X}
    (c : NodeChartAt f x) (e : X ≅ Y) (he : e.hom ≫ g = f) :
    NodeChartAt g (e.hom x) where
  source := c.source
  point := c.point
  toCurve := c.toCurve ≫ e.hom
  toNode := c.toNode
  etale_toCurve := by
    let _ : Etale c.toCurve := c.etale_toCurve
    let _ : Etale e.hom := by infer_instance
    infer_instance
  etale_toNode := c.etale_toNode
  mapsToPoint := by
    simp only [Scheme.Hom.comp_apply, c.mapsToPoint]
  overBase := by
    rw [Category.assoc, he, c.overBase]

end NodeChartAt

/-- A curve over a field is at worst nodal when every point has either a smooth étale chart
or an étale chart over the standard node. -/
def IsNodalCurveOverField {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) : Prop :=
  ∀ x : X, Nonempty (SmoothChartAt f x) ∨ Nonempty (NodeChartAt f x)

namespace IsNodalCurveOverField

/-- A smooth relative curve is at worst nodal. -/
theorem of_smooth {K : Type u} [Field K] (f : X ⟶ Spec (.of K))
    (h : Smooth f) : IsNodalCurveOverField f := by
  let _ : Smooth f := h
  intro x
  left
  exact ⟨
    { source := X
      point := x
      toCurve := 𝟙 X
      etale_toCurve := by infer_instance
      mapsToPoint := rfl
      smooth_toBase := by simpa using h }⟩

/-- A curve isomorphic over the field to the standard node is at worst nodal. -/
theorem of_overIso_standardNode {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K))
    (e : Over.mk f ≅ Over.mk (standardNodeToSpec K)) :
    IsNodalCurveOverField f := by
  intro x
  right
  have hi : IsIso e.hom.left := by
    change IsIso ((Over.forget (Spec (.of K))).map e.hom)
    infer_instance
  exact ⟨
    { source := X
      point := x
      toCurve := 𝟙 X
      toNode := e.hom.left
      etale_toCurve := by infer_instance
      etale_toNode := by infer_instance
      mapsToPoint := rfl
      overBase := by simpa using e.hom.w.symm }⟩

/-- Nodal curve charts transport across an isomorphism of source schemes. -/
theorem precomp_iso {Y : Scheme.{u}} {K : Type u} [Field K]
    (e : X ≅ Y) (f : Y ⟶ Spec (.of K)) (h : IsNodalCurveOverField f) :
    IsNodalCurveOverField (e.hom ≫ f) := by
  intro x
  rcases h (e.hom x) with hs | hn
  · left
    rcases hs with ⟨hs⟩
    let _ : Etale hs.toCurve := hs.etale_toCurve
    let _ : IsIso e.inv := by infer_instance
    let _ : Etale e.inv := by infer_instance
    exact ⟨
      { source := hs.source
        point := hs.point
        toCurve := hs.toCurve ≫ e.inv
        etale_toCurve := by infer_instance
        mapsToPoint := by
          simp only [Scheme.Hom.comp_apply, hs.mapsToPoint]
          have hi := congrArg (fun q : X ⟶ X ↦ q x) e.hom_inv_id
          have hid : (𝟙 X : X ⟶ X) x = x := rfl
          have hi' : e.inv (e.hom x) = (𝟙 X : X ⟶ X) x := by
            simpa only [Scheme.Hom.comp_apply] using hi
          exact hi'.trans hid
        smooth_toBase := by simpa [Category.assoc] using hs.smooth_toBase }⟩
  · right
    rcases hn with ⟨hn⟩
    let _ : Etale hn.toCurve := hn.etale_toCurve
    let _ : IsIso e.inv := by infer_instance
    let _ : Etale e.inv := by infer_instance
    exact ⟨
      { source := hn.source
        point := hn.point
        toCurve := hn.toCurve ≫ e.inv
        toNode := hn.toNode
        etale_toCurve := by infer_instance
        etale_toNode := hn.etale_toNode
        mapsToPoint := by
          simp only [Scheme.Hom.comp_apply, hn.mapsToPoint]
          have hi := congrArg (fun q : X ⟶ X ↦ q x) e.hom_inv_id
          have hid : (𝟙 X : X ⟶ X) x = x := rfl
          have hi' : e.inv (e.hom x) = (𝟙 X : X ⟶ X) x := by
            simpa only [Scheme.Hom.comp_apply] using hi
          exact hi'.trans hid
        overBase := by simpa [Category.assoc] using hn.overBase }⟩

/-- Pulling a nodal curve back along an étale morphism of source schemes preserves its
pointwise smooth-or-node charts. -/
theorem precomp_etale {Y : Scheme.{u}} {K : Type u} [Field K]
    (e : Y ⟶ X) (f : X ⟶ Spec (.of K))
    (he : Etale e) (h : IsNodalCurveOverField f) :
    IsNodalCurveOverField (e ≫ f) := by
  let _ : Etale e := he
  intro y
  rcases h (e y) with hs | hn
  · left
    rcases hs with ⟨hs⟩
    let _ : Etale hs.toCurve := hs.etale_toCurve
    obtain ⟨z, -, hzY⟩ :=
      Scheme.Pullback.exists_preimage_pullback hs.point y hs.mapsToPoint
    let _ : Etale (pullback.fst hs.toCurve e) := by infer_instance
    let _ : Etale (pullback.snd hs.toCurve e) := by infer_instance
    have hsmooth : Smooth (pullback.snd hs.toCurve e ≫ e ≫ f) := by
      have heq : pullback.snd hs.toCurve e ≫ e =
          pullback.fst hs.toCurve e ≫ hs.toCurve := pullback.condition.symm
      rw [← Category.assoc, heq, Category.assoc]
      let _ : Smooth (pullback.fst hs.toCurve e) := by infer_instance
      let _ : Smooth (hs.toCurve ≫ f) := hs.smooth_toBase
      infer_instance
    exact ⟨
      { source := pullback hs.toCurve e
        point := z
        toCurve := pullback.snd hs.toCurve e
        etale_toCurve := by infer_instance
        mapsToPoint := hzY
        smooth_toBase := hsmooth }⟩
  · right
    rcases hn with ⟨hn⟩
    let _ : Etale hn.toCurve := hn.etale_toCurve
    let _ : Etale hn.toNode := hn.etale_toNode
    obtain ⟨z, -, hzY⟩ :=
      Scheme.Pullback.exists_preimage_pullback hn.point y hn.mapsToPoint
    let _ : Etale (pullback.fst hn.toCurve e) := by infer_instance
    let _ : Etale (pullback.snd hn.toCurve e) := by infer_instance
    exact ⟨
      { source := pullback hn.toCurve e
        point := z
        toCurve := pullback.snd hn.toCurve e
        toNode := pullback.fst hn.toCurve e ≫ hn.toNode
        etale_toCurve := by infer_instance
        etale_toNode := by infer_instance
        mapsToPoint := hzY
        overBase := by
          have heq : pullback.snd hn.toCurve e ≫ e =
              pullback.fst hn.toCurve e ≫ hn.toCurve := pullback.condition.symm
          rw [← Category.assoc, heq, Category.assoc, hn.overBase]
          simp only [Category.assoc] }⟩

/-- Pointwise nodality descends along a surjective étale cover of the source: a chart at a
chosen lift of a point remains an étale chart after composition with the cover. -/
theorem of_comp_surjective_etale {Y : Scheme.{u}} {K : Type u} [Field K]
    (e : Y ⟶ X) (f : X ⟶ Spec (.of K))
    (he : Etale e) (hsurj : Surjective e)
    (h : IsNodalCurveOverField (e ≫ f)) : IsNodalCurveOverField f := by
  let _ : Etale e := he
  let _ : Surjective e := hsurj
  intro x
  obtain ⟨y, hy⟩ := e.surjective x
  rcases h y with hs | hn
  · left
    rcases hs with ⟨hs⟩
    let _ : Etale hs.toCurve := hs.etale_toCurve
    exact ⟨
      { source := hs.source
        point := hs.point
        toCurve := hs.toCurve ≫ e
        etale_toCurve := by infer_instance
        mapsToPoint := by simpa only [Scheme.Hom.comp_apply, hs.mapsToPoint] using hy
        smooth_toBase := by simpa only [Category.assoc] using hs.smooth_toBase }⟩
  · right
    rcases hn with ⟨hn⟩
    let _ : Etale hn.toCurve := hn.etale_toCurve
    exact ⟨
      { source := hn.source
        point := hn.point
        toCurve := hn.toCurve ≫ e
        toNode := hn.toNode
        etale_toCurve := by infer_instance
        etale_toNode := hn.etale_toNode
        mapsToPoint := by simpa only [Scheme.Hom.comp_apply, hn.mapsToPoint] using hy
        overBase := by simpa only [Category.assoc] using hn.overBase }⟩

/-- Pointwise nodality is local for a surjective étale cover of the source. -/
theorem iff_precomp_surjective_etale {Y : Scheme.{u}} {K : Type u} [Field K]
    (e : Y ⟶ X) (f : X ⟶ Spec (.of K))
    (he : Etale e) (hsurj : Surjective e) :
    IsNodalCurveOverField (e ≫ f) ↔ IsNodalCurveOverField f :=
  ⟨of_comp_surjective_etale e f he hsurj, precomp_etale e f he⟩

end IsNodalCurveOverField

/-- A flat finitely presented family of geometric pure dimension one whose every geometric
fibre is at worst nodal. -/
class AtWorstNodal (f : X ⟶ S) : Prop where
  flat : Flat f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  geometricPureRelativeDimension : GeometricPureRelativeDimension 1 f
  geometricFibers : ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    (Z : Scheme.{u}) (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)),
    IsPullback fst snd f y → IsNodalCurveOverField snd

namespace AtWorstNodal

/-- Flatness of a family can be checked after a surjective étale cover of its source. -/
theorem flat_of_precomp_surjective_etale {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : Flat (e ≫ f)) : Flat f := by
  let _ : Etale e := he
  let _ : Surjective e := hsurj
  let _ : Flat (e ≫ f) := hcomp
  apply Flat.of_stalkMap f
  intro x
  obtain ⟨y, hy⟩ := e.surjective x
  subst x
  have heflat : (e.stalkMap y).hom.Flat := Flat.stalkMap e y
  have heff : (e.stalkMap y).hom.FaithfullyFlat := by
    algebraize [(e.stalkMap y).hom]
    let _ : IsLocalHom (algebraMap (X.presheaf.stalk (e y))
        (Y.presheaf.stalk y)) := by
      rw [(e.stalkMap y).hom.algebraMap_toAlgebra]
      infer_instance
    rw [← (e.stalkMap y).hom.algebraMap_toAlgebra,
      RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply ringHomFlat_of_comp_of_faithfullyFlat heff
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact Flat.stalkMap (e ≫ f) y

/-- The geometric-fibre chart condition descends through a surjective étale cover of the
source.  The cover is first pulled back to the chosen geometric fibre and then pointwise
nodality is descended along that base-changed cover. -/
theorem geometricFibers_of_precomp_surjective_etale {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : AtWorstNodal (e ≫ f)) :
    ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
      (Z : Scheme.{u}) (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)),
      IsPullback fst snd f y → IsNodalCurveOverField snd := by
  let _ : Etale e := he
  let _ : Surjective e := hsurj
  intro K _ y Z fst snd hsquare
  let q : pullback e fst ⟶ Z := pullback.snd e fst
  have hqEtale : Etale q := by
    dsimp [q]
    infer_instance
  have hqSurjective : Surjective q := by
    dsimp [q]
    infer_instance
  have hcovered : IsNodalCurveOverField (q ≫ snd) :=
    hcomp.geometricFibers K y (pullback e fst) (pullback.fst e fst) (q ≫ snd)
      ((IsPullback.of_hasPullback e fst).paste_vert hsquare)
  exact IsNodalCurveOverField.of_comp_surjective_etale q snd hqEtale hqSurjective hcovered

/-- Geometric pure relative dimension one descends through a surjective étale cover of the
source. -/
theorem geometricPureRelativeDimension_of_precomp_surjective_etale {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : GeometricPureRelativeDimension 1 (e ≫ f)) :
    GeometricPureRelativeDimension 1 f :=
  GeometricPureRelativeDimension.of_precomp_surjective_etale e f he hsurj hcomp

/-- Finite presentation descends through a surjective étale cover of the source. -/
theorem locallyOfFinitePresentation_of_precomp_surjective_etale {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : LocallyOfFinitePresentation (e ≫ f)) : LocallyOfFinitePresentation f :=
  Curves.locallyOfFinitePresentation_of_precomp_surjective_etale e f he hsurj hcomp

/-- At-worst-nodality descends through a surjective étale cover of the source.

All four fields descend: flatness by faithfully flat reflection on stalks, finite presentation by
`locallyOfFinitePresentation_of_precomp_surjective_etale` (étale source descent of finite
presentation, proved in `RelativeDimension`), geometric pure relative dimension one by
`geometricPureRelativeDimension_of_precomp_surjective_etale`, and the geometric-fibre charts by
pulling the cover into each chosen geometric fibre. -/
theorem of_precomp_surjective_etale {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hcomp : AtWorstNodal (e ≫ f)) : AtWorstNodal f where
  flat := flat_of_precomp_surjective_etale e f he hsurj hcomp.flat
  locallyOfFinitePresentation :=
    locallyOfFinitePresentation_of_precomp_surjective_etale e f he hsurj
      hcomp.locallyOfFinitePresentation
  geometricPureRelativeDimension :=
    geometricPureRelativeDimension_of_precomp_surjective_etale e f he hsurj
      hcomp.geometricPureRelativeDimension
  geometricFibers := geometricFibers_of_precomp_surjective_etale e f he hsurj hcomp

/-- The geometric-fibre chart condition is stable under precomposition with an étale morphism:
the chosen geometric fibre of `e ≫ f` is an étale cover of the corresponding geometric fibre of
`f`, so its pointwise smooth-or-node charts pull back. -/
theorem geometricFibers_precomp_etale {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (h : AtWorstNodal f) :
    ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
      (Z : Scheme.{u}) (fst : Z ⟶ Y) (snd : Z ⟶ Spec (.of K)),
      IsPullback fst snd (e ≫ f) y → IsNodalCurveOverField snd := by
  let _ : Etale e := he
  intro K _ y Z fst snd hsquare
  let u : Z ⟶ pullback f y :=
    pullback.lift (fst ≫ e) snd (by rw [Category.assoc]; exact hsquare.w)
  have huFst : u ≫ pullback.fst f y = fst ≫ e := pullback.lift_fst _ _ _
  have huSnd : u ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
  have houter : IsPullback fst (u ≫ pullback.snd f y) (e ≫ f) y := by
    simpa only [huSnd] using hsquare
  have htop : IsPullback fst u e (pullback.fst f y) :=
    IsPullback.of_bot houter huFst.symm (IsPullback.of_hasPullback f y)
  have hu : Etale u := MorphismProperty.of_isPullback (P := @Etale) htop inferInstance
  have hfib : IsNodalCurveOverField (pullback.snd f y) :=
    h.geometricFibers K y (pullback f y) (pullback.fst f y) (pullback.snd f y)
      (IsPullback.of_hasPullback f y)
  rw [← huSnd]
  exact IsNodalCurveOverField.precomp_etale u (pullback.snd f y) hu hfib

/-- At-worst-nodality is stable under precomposition with an étale morphism, given geometric
pure relative dimension one of the composite.

That last hypothesis is not derivable here.  It does not follow topologically: a surjective étale
cover of a scheme may have a component of strictly smaller dimension (as for the disjoint union of
a scheme with a proper open subscheme).  Nor does it follow from the chart data, since
`SmoothChartAt` records no relative dimension.  It is true for the geometric fibres at hand, which
are locally of finite type over a field, but deducing it needs the dimension theory of such
schemes, which the pinned Mathlib does not provide. -/
theorem precomp_etale {Y : Scheme.{u}} (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e)
    (h : AtWorstNodal f) (hdim : GeometricPureRelativeDimension 1 (e ≫ f)) :
    AtWorstNodal (e ≫ f) where
  flat := by
    let _ : Etale e := he
    let _ : Flat f := h.flat
    infer_instance
  locallyOfFinitePresentation := by
    let _ : Etale e := he
    let _ : LocallyOfFinitePresentation f := h.locallyOfFinitePresentation
    infer_instance
  geometricPureRelativeDimension := hdim
  geometricFibers := geometricFibers_precomp_etale e f he h

/-- At-worst-nodality is local for surjective étale covers of the source: the cover is at worst
nodal exactly when the base is, together with the geometric pure relative dimension of the cover.

The second conjunct is not redundant.  It descends from the cover (that is part of
`of_precomp_surjective_etale`) but does not ascend from `f`, for the reasons recorded at
`precomp_etale`; putting it on the left of the equivalence is therefore the strongest form
available here, and it needs no hypothesis beyond `e` being surjective étale. -/
theorem iff_precomp_surjective_etale {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e) :
    AtWorstNodal (e ≫ f) ↔ (AtWorstNodal f ∧ GeometricPureRelativeDimension 1 (e ≫ f)) :=
  ⟨fun hcomp ↦ ⟨of_precomp_surjective_etale e f he hsurj hcomp,
      hcomp.geometricPureRelativeDimension⟩,
    fun h ↦ precomp_etale e f he h.1 h.2⟩

/-- The plain two-sided form of `iff_precomp_surjective_etale`, for a cover whose geometric pure
relative dimension is already known. -/
theorem iff_precomp_surjective_etale_of_geometricPureRelativeDimension {Y : Scheme.{u}}
    (e : Y ⟶ X) (f : X ⟶ S) (he : Etale e) (hsurj : Surjective e)
    (hdim : GeometricPureRelativeDimension 1 (e ≫ f)) :
    AtWorstNodal (e ≫ f) ↔ AtWorstNodal f :=
  ⟨fun hcomp ↦ of_precomp_surjective_etale e f he hsurj hcomp,
    fun h ↦ precomp_etale e f he h hdim⟩

variable (f : X ⟶ S) [h : AtWorstNodal f]

/-- A smooth family of geometric pure relative dimension one is at worst nodal.

The dimension hypothesis is kept explicit: the proof uses only smooth base-change and the
fact that a smooth curve over a field has smooth charts.  The comparison between
`SmoothOfRelativeDimension 1` and geometric fibre dimension is proved separately in
`SmoothLocusDimension.lean`.
-/
theorem of_smooth (f : X ⟶ S) (hsm : Smooth f)
    (hpure : GeometricPureRelativeDimension 1 f) : AtWorstNodal f := by
  let _ : Smooth f := hsm
  refine
    { flat := by infer_instance
      locallyOfFinitePresentation := by infer_instance
      geometricPureRelativeDimension := hpure
      geometricFibers := ?_ }
  intro K _ y Z fst snd hsquare
  have hsmooth : Smooth snd :=
    MorphismProperty.of_isPullback (P := @Smooth) hsquare hsm
  exact IsNodalCurveOverField.of_smooth snd hsmooth

instance : Flat f := h.flat
instance : LocallyOfFinitePresentation f := h.locallyOfFinitePresentation
instance : LocallyOfFiniteType f := inferInstance

theorem toGeometricPureRelativeDimension : GeometricPureRelativeDimension 1 f :=
  h.geometricPureRelativeDimension

theorem toPureRelativeDimension : PureRelativeDimension 1 f :=
  h.geometricPureRelativeDimension.toPureRelativeDimension

/-- The chosen geometric fibre of an at-worst-nodal family is a nodal curve over its field. -/
theorem pullback_fiber {K : Type u} [Field K] (y : Spec (.of K) ⟶ S) :
    IsNodalCurveOverField (pullback.snd f y) :=
  h.geometricFibers K y (pullback f y) _ _ (IsPullback.of_hasPullback f y)

/-- At-worst-nodality transports across an arbitrary Cartesian base-change square. -/
theorem of_isPullback {Y Y' T : Scheme.{u}} {g : Y ⟶ S} {b : T ⟶ S}
    {fst : Y' ⟶ Y} {g' : Y' ⟶ T} (sq : IsPullback fst g' g b)
    (hg : AtWorstNodal g) : AtWorstNodal g' where
  flat := MorphismProperty.of_isPullback (P := @Flat) sq hg.flat
  locallyOfFinitePresentation :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq
      hg.locallyOfFinitePresentation
  geometricPureRelativeDimension :=
    MorphismProperty.of_isPullback
      (P := fun {_ _} q ↦ GeometricPureRelativeDimension 1 q) sq
      hg.geometricPureRelativeDimension
  geometricFibers := by
    intro K _ y Z p q hpq
    exact hg.geometricFibers K (y ≫ b) Z (p ≫ fst) q (hpq.paste_horiz sq)

/-- Arbitrary chosen base change preserves at-worst-nodality. -/
theorem pullback_snd {T : Scheme.{u}} (b : T ⟶ S) :
    AtWorstNodal (pullback.snd f b) :=
  of_isPullback (IsPullback.of_hasPullback f b) h

instance : MorphismProperty.IsStableUnderBaseChange (@AtWorstNodal) where
  of_isPullback sq hg := of_isPullback sq hg

end AtWorstNodal

end

end GromovWitten.AlgebraicGeometry.Curves
