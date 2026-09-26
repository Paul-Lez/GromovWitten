/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.PresentationGroupoidObject
import GromovWitten.AlgebraicGeometry.Stacks.PresentationGroupoidLaws
import GromovWitten.AlgebraicGeometry.Cones.StackBaseChangeComp
import GromovWitten.AlgebraicGeometry.Stacks.InertiaCoherence

/-!
# Chart-level refinement records

A `StackChart.ChartRefinement A B` records that a chart `A : StackChart X` refines a chart
`B : StackChart X`: an actual scheme morphism `hom : A.scheme ⟶ B.scheme` together with an
invertible comparison 2-cell identifying `A.map` with `mapOfSchemeHom hom ≫ B.map`.  This is the
chart-level shadow of a `StackTwoPullback.Genuine`-refinement (`q`, `e` in
`Stacks.AtlasRefinement`'s `refinementGroupoidMap`), specialized to the case where both atlases
are honest scheme charts.

Every chart refinement induces a map of the canonical self-overlaps
(`ChartRefinement.overlapMap`), built directly from `refinementGroupoidMap`, together with its
source/target compatibility 2-cells (fully proved).  `ChartRefinement.refl` and `.comp` make
refinements into (the data of) a category on `StackChart X`, and `PresentationGroupoidObject.map`
packages the induced map of self-overlaps, with its source/target compatibility, as a
`PresentationGroupoidObject.ChartMap` between the two presentation-groupoid objects, giving
`PresentationGroupoidObject` (`Stacks.PresentationGroupoidObject`) its first consumer.

Compatibility of `overlapMap` with the groupoid unit map is fully proved:
`unit_R_classifies` is the direct specialization of the pre-existing
`Genuine.unitPostcompClassifies` (`PresentationGroupoidLaws.lean`) showing `qc ≫ B.selfOverlap.unit`
classifies the constant cone at `qc`; `unit_S_classifies` proves the symmetric fact that
`A.selfOverlap.unit ≫ overlapMap` classifies the *same* cone, by combining `A.selfOverlap`'s own
unit-comparison law (`Genuine.unit_comparison`) with the naturality of the natural isomorphism
`r.iso.appIso V` at the `unit_source`/`unit_target` arrows (the bridge `vcomp_appFunctor_obj`/
`vcomp_appFunctor_map`, `Cones/StackBaseChangeComp.lean`, identifies `(vcomp q f).appFunctor V`
with the composite functor on the nose, by `rfl`; the only real work is bookkeeping the
resulting naturality square through `cone_classifies_precomp`/`cone_classifies_congr`'s
whiskered cone, not a missing lemma).  Combining both halves via
`B.selfOverlap.bilimit.lift_unique` gives the full unit-compatibility 2-cell `unit_compat r :
StackIso2 (vcomp qc B.selfOverlap.unit) (vcomp A.selfOverlap.unit overlapMap)`.

**Inverse compatibility is now also fully proved**, by the identical recipe applied to
`B.selfOverlap.inverseCone` (in place of the trivial cone): `inverse_R_classifies` precomposes
`Genuine.inverse_classifies` by `overlapMap` (`Genuine.cone_classifies_precomp`);
`inverse_S_classifies` precomposes `overlapMap`'s own classification by `A.selfOverlap.inverse`
and transports it to the same cone (`Genuine.cone_classifies_congr`), the comparison square this
time combining `Genuine.inverse_comparison` with *two* naturality squares of `r.iso.appIso V`
(one at `inverse_source`, one at `inverse_target`) instead of one.  `inverse_compat r :
StackIso2 (vcomp overlapMap B.selfOverlap.inverse) (vcomp A.selfOverlap.inverse overlapMap)`
combines both halves via `bilimit.lift_unique`, exactly as `unit_compat`.

**Compose compatibility is partially built.**  The composable-pair-level induced map
`overlapMap₂ : StackHom A.selfOverlap.composable.pullback B.selfOverlap.composable.pullback` is
fully constructed (a `bilimit.lift` of an explicit cone assembled from `A.selfOverlap`'s
composability 2-cell and `overlapMap`'s own source/target compatibility), together with its
first- and second-arrow projection 2-cells and full classification (`overlapMap₂_classifies`).  The
"R-side" of compose-compatibility (`overlapMap₂ ≫ compose` classifies the composition cone of
`B.selfOverlap` precomposed by `overlapMap₂`) is proved (`compose_R_classifies`, again a direct
`cone_classifies_precomp` specialization), and both projection witnesses of the "S-side"
(`compose_S_fst`, `compose_S_snd`) are built.  **Not done**: `compose_S_classifies` (the
comparison-square diagram chase, which combines the `r.iso`-naturality argument above with a
*second* instance of the same argument for `A.selfOverlap.composableComparison`/
`B.selfOverlap.composableComparison`, bridged through `overlapMap₂_classifies`) and the final
`compose_compat`/`hom_comp` assembly.  See the accompanying report for the precise remaining
obstacle and the exact recipe (same `cone_classifies_congr` + naturality technique, one layer
deeper).
-/

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace StackChart

variable {X : FppfStack.{u}}

/-- **A chart-level refinement.**  Records that the chart `A` refines the chart `B`: an actual
scheme morphism `A.scheme ⟶ B.scheme` together with an invertible 2-cell identifying `A.map`
with the promoted scheme morphism followed by `B.map`.  Nothing about the induced map of
self-overlaps or its compatibility with the groupoid structure is postulated here; it is all
constructed afterwards from `hom` and `iso`. -/
structure ChartRefinement (A B : StackChart X) where
  /-- The scheme morphism realizing the refinement. -/
  hom : A.scheme ⟶ B.scheme
  /-- The chart `A` agrees with the chart `B` precomposed by the scheme morphism, up to an
  invertible 2-cell. -/
  iso : StackIso2 A.map
    (Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom hom) B.map)

namespace ChartRefinement

variable {A B C : StackChart X}

/-- **The identity refinement.**  A chart trivially refines itself along the identity scheme
morphism. -/
noncomputable def refl (A : StackChart X) : ChartRefinement A A where
  hom := 𝟙 A.scheme
  iso := ((StackIso2.whiskerRight (FppfStack.mapOfSchemeHom_id_iso A.scheme) A.map).trans
    (StackIso2.leftUnitor A.map)).symm

/-- **Composition of refinements.**  If `A` refines `B` and `B` refines `C`, then `A` refines
`C` along the composite scheme morphism. -/
noncomputable def comp (r : ChartRefinement A B) (s : ChartRefinement B C) :
    ChartRefinement A C where
  hom := r.hom ≫ s.hom
  iso :=
    (((r.iso.trans (StackIso2.whiskerLeft (FppfStack.mapOfSchemeHom r.hom) s.iso)).trans
      (StackIso2.associator
        (FppfStack.mapOfSchemeHom r.hom) (FppfStack.mapOfSchemeHom s.hom) C.map).symm).trans
      (StackIso2.whiskerRight
        (FppfStack.mapOfSchemeHom_comp_iso r.hom s.hom) C.map))

end ChartRefinement

/-- The chosen canonical self two-pullback presenting the overlap `A.scheme ×_X A.scheme` of a
chart. -/
noncomputable abbrev selfOverlap (A : StackChart X) :
    StackTwoPullback.Genuine A.map A.map :=
  StackTwoPullback.canonicalGenuine A.map A.map

end StackChart

namespace StackChart.ChartRefinement

variable {X : FppfStack.{u}} {A B : StackChart X}

/-- **The induced map of self-overlaps.**  A chart refinement `r : ChartRefinement A B` induces
a map from the self-overlap of `A` to the self-overlap of `B`, built directly from
`refinementGroupoidMap` applied to the promoted scheme morphism and the comparison 2-cell. -/
noncomputable def overlapMap (r : ChartRefinement A B) :
    StackHom A.selfOverlap.pullback B.selfOverlap.pullback :=
  StackTwoPullback.refinementGroupoidMap A.selfOverlap B.selfOverlap
    (FppfStack.mapOfSchemeHom r.hom) r.iso.symm

/-- The induced map of self-overlaps commutes with the source maps, up to the displayed
2-cell. -/
noncomputable def overlapMap_source (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.source)
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.source (FppfStack.mapOfSchemeHom r.hom)) :=
  StackTwoPullback.refinementGroupoidMap_source A.selfOverlap B.selfOverlap
    (FppfStack.mapOfSchemeHom r.hom) r.iso.symm

/-- The induced map of self-overlaps commutes with the target maps, up to the displayed
2-cell. -/
noncomputable def overlapMap_target (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.target)
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.target (FppfStack.mapOfSchemeHom r.hom)) :=
  StackTwoPullback.refinementGroupoidMap_target A.selfOverlap B.selfOverlap
    (FppfStack.mapOfSchemeHom r.hom) r.iso.symm

/-- The induced map of self-overlaps classifies its defining cone completely, including the
comparison face. -/
theorem overlapMap_classifies (r : ChartRefinement A B) :
    StackTwoPullback.ConeLiftClassifies B.selfOverlap.toStackTwoPullback
      (StackTwoPullback.refinementGroupoidCone A.selfOverlap
        (FppfStack.mapOfSchemeHom r.hom) r.iso.symm)
      r.overlapMap r.overlapMap_source r.overlapMap_target :=
  StackTwoPullback.refinementGroupoidMap_classifies A.selfOverlap B.selfOverlap
    (FppfStack.mapOfSchemeHom r.hom) r.iso.symm

end StackChart.ChartRefinement

namespace StackChart.ChartRefinement

variable {X : FppfStack.{u}} {A B : StackChart X}

/-- **`qc ≫ unit` classifies the constant cone at `qc`** (the "R-side" half of
unit-compatibility for a chart refinement), where `qc` is the promoted refinement scheme
morphism.  Direct specialization of the pre-existing `Genuine.unitPostcompClassifies`
(`PresentationGroupoidLaws.lean`) to `R := B.selfOverlap`, `q := qc`; no new proof content. -/
theorem unit_R_classifies (r : ChartRefinement A B) :
    StackTwoPullback.ConeLiftClassifies B.selfOverlap.toStackTwoPullback
      (B.selfOverlap.unitConeOf (FppfStack.mapOfSchemeHom r.hom))
      (Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom r.hom) B.selfOverlap.unit)
      (B.selfOverlap.unitPostcompFstIso (FppfStack.mapOfSchemeHom r.hom))
      (B.selfOverlap.unitPostcompSndIso (FppfStack.mapOfSchemeHom r.hom)) :=
  B.selfOverlap.unitPostcompClassifies (FppfStack.mapOfSchemeHom r.hom)

/-- The first projection witness identifying `unit ≫ overlapMap` with `qc`, up to the
displayed 2-cell (the "source" side of the S-half of unit compatibility). -/
noncomputable def unit_S_fst (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.unit r.overlapMap) B.selfOverlap.fst)
      (FppfStack.mapOfSchemeHom r.hom) :=
  ((StackIso2.associator A.selfOverlap.unit r.overlapMap B.selfOverlap.fst).trans
    (StackIso2.whiskerLeft A.selfOverlap.unit r.overlapMap_source)).trans
    (((StackIso2.associator
        A.selfOverlap.unit A.selfOverlap.fst (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight
        A.selfOverlap.unit_source (FppfStack.mapOfSchemeHom r.hom))).trans
      (StackIso2.leftUnitor (FppfStack.mapOfSchemeHom r.hom)))

/-- The second projection witness identifying `unit ≫ overlapMap` with `qc`, up to the
displayed 2-cell. -/
noncomputable def unit_S_snd (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.unit r.overlapMap) B.selfOverlap.snd)
      (FppfStack.mapOfSchemeHom r.hom) :=
  ((StackIso2.associator A.selfOverlap.unit r.overlapMap B.selfOverlap.snd).trans
    (StackIso2.whiskerLeft A.selfOverlap.unit r.overlapMap_target)).trans
    (((StackIso2.associator
        A.selfOverlap.unit A.selfOverlap.snd (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight
        A.selfOverlap.unit_target (FppfStack.mapOfSchemeHom r.hom))).trans
      (StackIso2.leftUnitor (FppfStack.mapOfSchemeHom r.hom)))

set_option backward.isDefEq.respectTransparency false in
/-- **`unit ≫ overlapMap` classifies the same constant cone at `qc`** (the "S-side" half of
unit-compatibility).  Reduces, via `cone_classifies_precomp`/`cone_classifies_congr`, to
`A.selfOverlap`'s own unit-comparison law (`Genuine.unit_comparison`) combined with the
naturality of `r.iso.appIso V` at the `unit_source`/`unit_target` arrows. -/
theorem unit_S_classifies (r : ChartRefinement A B) :
    StackTwoPullback.ConeLiftClassifies B.selfOverlap.toStackTwoPullback
      (B.selfOverlap.unitConeOf (FppfStack.mapOfSchemeHom r.hom))
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.unit r.overlapMap)
      (unit_S_fst r) (unit_S_snd r) := by
  apply StackTwoPullback.Genuine.cone_classifies_congr B.selfOverlap
    _ (B.selfOverlap.unitConeOf (FppfStack.mapOfSchemeHom r.hom)) _ _ _
    (StackTwoPullback.Genuine.cone_classifies_precomp B.selfOverlap
      (StackTwoPullback.refinementGroupoidCone A.selfOverlap
        (FppfStack.mapOfSchemeHom r.hom) r.iso.symm)
      r.overlapMap r.overlapMap_source r.overlapMap_target r.overlapMap_classifies
      A.selfOverlap.unit)
    (((StackIso2.associator
        A.selfOverlap.unit A.selfOverlap.fst (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight
        A.selfOverlap.unit_source (FppfStack.mapOfSchemeHom r.hom))).trans
      (StackIso2.leftUnitor (FppfStack.mapOfSchemeHom r.hom)))
    (((StackIso2.associator
        A.selfOverlap.unit A.selfOverlap.snd (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight
        A.selfOverlap.unit_target (FppfStack.mapOfSchemeHom r.hom))).trans
      (StackIso2.leftUnitor (FppfStack.mapOfSchemeHom r.hom)))
  intro V x
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackTwoPullback.Genuine.whiskerRight_appIso_hom_app,
    StackIso2.symm_appIso_hom_app,
    StackIso2.associator_appIso_inv_app]
  change
    (B.map.appFunctor V).map
        ((𝟙 _ ≫
            ((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
              ((A.selfOverlap.unit_source.appIso V).hom.app x)) ≫
          ((StackIso2.leftUnitor (FppfStack.mapOfSchemeHom r.hom)).appIso V).hom.app x) ≫
      ((B.selfOverlap.unitConeOf (FppfStack.mapOfSchemeHom r.hom)).comparison.appIso V).hom.app x =
    (𝟙 _ ≫
        ((StackTwoPullback.refinementGroupoidCone A.selfOverlap (FppfStack.mapOfSchemeHom r.hom)
            r.iso.symm).comparison.appIso V).hom.app ((A.selfOverlap.unit.appFunctor V).obj x) ≫
          𝟙 _) ≫
      (B.map.appFunctor V).map
        ((𝟙 _ ≫
            ((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
              ((A.selfOverlap.unit_target.appIso V).hom.app x)) ≫
          ((StackIso2.leftUnitor (FppfStack.mapOfSchemeHom r.hom)).appIso V).hom.app x)
  simp only [Category.id_comp, Category.comp_id]
  dsimp only [StackTwoPullback.Genuine.unitConeOf, StackTwoPullback.refinementGroupoidCone,
    StackTwoPullback.refinementGroupoidConeComparison]
  simp only [StackTwoPullback.leftUnitor_appIso_hom_app,
    StackTwoPullback.Genuine.refl_appIso_hom_app,
    StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackIso2.symm_appIso_hom_app,
    StackIso2.associator_appIso_inv_app, StackTwoPullback.Genuine.whiskerLeft_appIso_inv_app,
    StackIso2.symm_appIso_inv_app]
  change
    (B.map.appFunctor V).map
        (((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
              ((A.selfOverlap.unit_source.appIso V).hom.app x) ≫
          𝟙 _) ≫
      𝟙 _ =
    ((((𝟙 _ ≫
              (r.iso.appIso V).inv.app
                ((A.selfOverlap.fst.appFunctor V).obj ((A.selfOverlap.unit.appFunctor V).obj x))) ≫
            (A.selfOverlap.comparison.appIso V).hom.app ((A.selfOverlap.unit.appFunctor V).obj x)) ≫
          (r.iso.appIso V).hom.app
            ((A.selfOverlap.snd.appFunctor V).obj ((A.selfOverlap.unit.appFunctor V).obj x))) ≫
        𝟙 _) ≫
      (B.map.appFunctor V).map
        (((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
              ((A.selfOverlap.unit_target.appIso V).hom.app x) ≫
          𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  have hx := A.selfOverlap.unit_comparison V x
  have hnat_s := (r.iso.appIso V).hom.naturality ((A.selfOverlap.unit_source.appIso V).hom.app x)
  have hnat_t := (r.iso.appIso V).hom.naturality ((A.selfOverlap.unit_target.appIso V).hom.app x)
  rw [StackTwoPullback.vcomp_appFunctor_map] at hnat_s hnat_t
  have hs2 := (congrArg (fun z => (r.iso.appIso V).inv.app _ ≫ z) hnat_s).symm
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hs2
  rw [hx, Category.assoc, hnat_t, ← Category.assoc, ← Category.assoc] at hs2
  exact hs2

/-- **Unit compatibility of the induced map of self-overlaps.**  A chart refinement's induced
map `overlapMap` is compatible with the groupoid unit maps: `qc ≫ unit` and `unit ≫ overlapMap`
(the two composites built from the promoted refinement map `qc` and the two self-overlaps'
units) are both classifying maps of the very same trivial cone at `qc`, hence 2-isomorphic to
each other by the bilimit's uniqueness of lifts.  Combines `unit_R_classifies`/`unit_S_classifies`
via `bilimit.lift_unique`; no further content is needed. -/
noncomputable def unit_compat (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom r.hom) B.selfOverlap.unit)
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.unit r.overlapMap) :=
  (B.selfOverlap.bilimit.lift_unique (B.selfOverlap.unitConeOf (FppfStack.mapOfSchemeHom r.hom))
      (Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSchemeHom r.hom) B.selfOverlap.unit)
      (B.selfOverlap.unitPostcompFstIso (FppfStack.mapOfSchemeHom r.hom))
      (B.selfOverlap.unitPostcompSndIso (FppfStack.mapOfSchemeHom r.hom))
      (unit_R_classifies r)).trans
    (B.selfOverlap.bilimit.lift_unique (B.selfOverlap.unitConeOf (FppfStack.mapOfSchemeHom r.hom))
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.unit r.overlapMap)
      (unit_S_fst r) (unit_S_snd r) (unit_S_classifies r)).symm

/-! ### Inverse compatibility -/

/-- The cone, over `B.map, B.map`, classified by both sides of inverse-compatibility: the
inversion cone of `B.selfOverlap` precomposed by the induced map `overlapMap`. -/
noncomputable def inverseCompatCone (r : ChartRefinement A B) :
    StackTwoPullback.Cone (f := B.map) (g := B.map) A.selfOverlap.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.inverseCone.fst
  snd := Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.inverseCone.snd
  comparison :=
    (StackIso2.associator r.overlapMap B.selfOverlap.inverseCone.fst B.map).trans
      ((StackIso2.whiskerLeft r.overlapMap B.selfOverlap.inverseCone.comparison).trans
        (StackIso2.associator r.overlapMap B.selfOverlap.inverseCone.snd B.map).symm)

/-- The first projection witness for the "R-side" of inverse-compatibility:
`overlapMap ≫ inverse` composed with `fst`. -/
noncomputable def inverse_R_fst (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.inverse) B.selfOverlap.fst)
      (r.inverseCompatCone).fst :=
  (StackIso2.associator r.overlapMap B.selfOverlap.inverse B.selfOverlap.fst).trans
    (StackIso2.whiskerLeft r.overlapMap B.selfOverlap.inverse_source)

/-- The second projection witness for the "R-side" of inverse-compatibility. -/
noncomputable def inverse_R_snd (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.inverse) B.selfOverlap.snd)
      (r.inverseCompatCone).snd :=
  (StackIso2.associator r.overlapMap B.selfOverlap.inverse B.selfOverlap.snd).trans
    (StackIso2.whiskerLeft r.overlapMap B.selfOverlap.inverse_target)

/-- **`overlapMap ≫ inverse` classifies `inverseCompatCone`** (the "R-side" half of
inverse-compatibility).  Direct specialization of `Genuine.cone_classifies_precomp` to
`B.selfOverlap`'s own inversion cone, precomposed by `overlapMap`; no new proof content. -/
theorem inverse_R_classifies (r : ChartRefinement A B) :
    StackTwoPullback.ConeLiftClassifies B.selfOverlap.toStackTwoPullback r.inverseCompatCone
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.inverse)
      (inverse_R_fst r) (inverse_R_snd r) :=
  StackTwoPullback.Genuine.cone_classifies_precomp B.selfOverlap B.selfOverlap.inverseCone
    B.selfOverlap.inverse B.selfOverlap.inverse_source B.selfOverlap.inverse_target
    B.selfOverlap.inverse_classifies r.overlapMap

/-- The first projection witness for the "S-side" of inverse-compatibility:
`inverse ≫ overlapMap` composed with `fst`. -/
noncomputable def inverse_S_fst (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.inverse r.overlapMap) B.selfOverlap.fst)
      (r.inverseCompatCone).fst :=
  ((StackIso2.associator A.selfOverlap.inverse r.overlapMap B.selfOverlap.fst).trans
    (StackIso2.whiskerLeft A.selfOverlap.inverse r.overlapMap_source)).trans
    (((StackIso2.associator A.selfOverlap.inverse A.selfOverlap.fst
        (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight A.selfOverlap.inverse_source
        (FppfStack.mapOfSchemeHom r.hom))).trans
      r.overlapMap_target.symm)

/-- The second projection witness for the "S-side" of inverse-compatibility. -/
noncomputable def inverse_S_snd (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.inverse r.overlapMap) B.selfOverlap.snd)
      (r.inverseCompatCone).snd :=
  ((StackIso2.associator A.selfOverlap.inverse r.overlapMap B.selfOverlap.snd).trans
    (StackIso2.whiskerLeft A.selfOverlap.inverse r.overlapMap_target)).trans
    (((StackIso2.associator A.selfOverlap.inverse A.selfOverlap.snd
        (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight A.selfOverlap.inverse_target
        (FppfStack.mapOfSchemeHom r.hom))).trans
      r.overlapMap_source.symm)

set_option backward.isDefEq.respectTransparency false in
/-- **`inverse ≫ overlapMap` classifies the same cone `inverseCompatCone`** (the "S-side" half
of inverse-compatibility). -/
theorem inverse_S_classifies (r : ChartRefinement A B) :
    StackTwoPullback.ConeLiftClassifies B.selfOverlap.toStackTwoPullback r.inverseCompatCone
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.inverse r.overlapMap)
      (inverse_S_fst r) (inverse_S_snd r) := by
  apply StackTwoPullback.Genuine.cone_classifies_congr B.selfOverlap
    _ r.inverseCompatCone _ _ _
    (StackTwoPullback.Genuine.cone_classifies_precomp B.selfOverlap
      (StackTwoPullback.refinementGroupoidCone A.selfOverlap
        (FppfStack.mapOfSchemeHom r.hom) r.iso.symm)
      r.overlapMap r.overlapMap_source r.overlapMap_target r.overlapMap_classifies
      A.selfOverlap.inverse)
    (((StackIso2.associator A.selfOverlap.inverse A.selfOverlap.fst
        (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight A.selfOverlap.inverse_source
        (FppfStack.mapOfSchemeHom r.hom))).trans
      r.overlapMap_target.symm)
    (((StackIso2.associator A.selfOverlap.inverse A.selfOverlap.snd
        (FppfStack.mapOfSchemeHom r.hom)).symm.trans
      (StackIso2.whiskerRight A.selfOverlap.inverse_target
        (FppfStack.mapOfSchemeHom r.hom))).trans
      r.overlapMap_source.symm)
  intro V x
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackTwoPullback.Genuine.whiskerRight_appIso_hom_app,
    StackIso2.symm_appIso_hom_app, StackIso2.associator_appIso_inv_app]
  change
    (B.map.appFunctor V).map
        ((𝟙 _ ≫
            ((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
              ((A.selfOverlap.inverse_source.appIso V).hom.app x)) ≫
          (r.overlapMap_target.appIso V).inv.app x) ≫
      (r.inverseCompatCone.comparison.appIso V).hom.app x =
    (𝟙 _ ≫
        ((StackTwoPullback.refinementGroupoidCone A.selfOverlap (FppfStack.mapOfSchemeHom r.hom)
            r.iso.symm).comparison.appIso V).hom.app ((A.selfOverlap.inverse.appFunctor V).obj x) ≫
          𝟙 _) ≫
      (B.map.appFunctor V).map
        ((𝟙 _ ≫
            ((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
              ((A.selfOverlap.inverse_target.appIso V).hom.app x)) ≫
          (r.overlapMap_source.appIso V).inv.app x)
  simp only [Category.id_comp, Category.comp_id]
  dsimp only [inverseCompatCone, StackTwoPullback.Genuine.inverseCone,
    StackTwoPullback.refinementGroupoidCone, StackTwoPullback.refinementGroupoidConeComparison]
  simp only [StackTwoPullback.trans_appIso_hom_app, StackIso2.associator_appIso_hom_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackIso2.symm_appIso_hom_app,
    StackIso2.associator_appIso_inv_app, StackTwoPullback.Genuine.whiskerLeft_appIso_inv_app,
    StackIso2.symm_appIso_inv_app, Functor.map_comp, Category.id_comp, Category.comp_id,
    Category.assoc]
  have hx := A.selfOverlap.inverse_comparison V x
  have hnat_s := (r.iso.appIso V).hom.naturality ((A.selfOverlap.inverse_source.appIso V).hom.app x)
  have hnat_t := (r.iso.appIso V).hom.naturality ((A.selfOverlap.inverse_target.appIso V).hom.app x)
  rw [StackTwoPullback.vcomp_appFunctor_map] at hnat_s hnat_t
  have hcls := congrArg Iso.inv (r.overlapMap_classifies V x)
  simp only [Iso.app_inv, Iso.trans_inv, Functor.mapIso_inv] at hcls
  dsimp only [StackTwoPullback.refinementGroupoidCone,
    StackTwoPullback.refinementGroupoidConeComparison] at hcls
  simp only [StackTwoPullback.trans_appIso_inv_app,
    StackIso2.associator_appIso_hom_app, StackIso2.associator_appIso_inv_app,
    StackIso2.whiskerLeft_appIso_hom_app, StackIso2.whiskerLeft_appIso_inv_app,
    StackIso2.symm_appIso_hom_app, StackIso2.symm_appIso_inv_app,
    Category.id_comp, Category.comp_id] at hcls
  have hnat_s' : (A.map.appFunctor V).map ((A.selfOverlap.inverse_source.appIso V).hom.app x) ≫
        (r.iso.appIso V).hom.app ((A.selfOverlap.snd.appFunctor V).obj x) =
      (r.iso.appIso V).hom.app
          ((A.selfOverlap.fst.appFunctor V).obj ((A.selfOverlap.inverse.appFunctor V).obj x)) ≫
        (B.map.appFunctor V).map
          (((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
            ((A.selfOverlap.inverse_source.appIso V).hom.app x)) := hnat_s
  have hnat_t' : (A.map.appFunctor V).map ((A.selfOverlap.inverse_target.appIso V).hom.app x) ≫
        (r.iso.appIso V).hom.app ((A.selfOverlap.fst.appFunctor V).obj x) =
      (r.iso.appIso V).hom.app
          ((A.selfOverlap.snd.appFunctor V).obj ((A.selfOverlap.inverse.appFunctor V).obj x)) ≫
        (B.map.appFunctor V).map
          (((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
            ((A.selfOverlap.inverse_target.appIso V).hom.app x)) := hnat_t
  have hs1 := congrArg
    (fun z => (r.iso.appIso V).inv.app
        ((A.selfOverlap.fst.appFunctor V).obj ((A.selfOverlap.inverse.appFunctor V).obj x)) ≫ z)
    hnat_s'
  simp only [← Category.assoc] at hs1
  rw [Iso.inv_hom_id_app, Category.id_comp] at hs1
  have hkey1 := congrArg
    (fun z => z ≫ (r.iso.appIso V).inv.app ((A.selfOverlap.snd.appFunctor V).obj x)) hs1
  simp only [Category.assoc, Iso.hom_inv_id_app] at hkey1
  change
    (r.iso.appIso V).inv.app
        ((A.selfOverlap.fst.appFunctor V).obj ((A.selfOverlap.inverse.appFunctor V).obj x)) ≫
      (A.map.appFunctor V).map ((A.selfOverlap.inverse_source.appIso V).hom.app x) ≫ 𝟙 _ =
    (B.map.appFunctor V).map
        (((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
          ((A.selfOverlap.inverse_source.appIso V).hom.app x)) ≫
      (r.iso.appIso V).inv.app ((A.selfOverlap.snd.appFunctor V).obj x)
    at hkey1
  simp only [Category.comp_id] at hkey1
  have hx1 := congrArg
    (fun z => z ≫ (r.iso.appIso V).hom.app ((A.selfOverlap.fst.appFunctor V).obj x)) hx
  simp only [Category.assoc] at hx1
  rw [hnat_t'] at hx1
  have hkeyB := congrArg
    (fun z => z ≫ (A.selfOverlap.comparison.appIso V).inv.app x ≫
      (r.iso.appIso V).hom.app ((A.selfOverlap.fst.appFunctor V).obj x)) hkey1
  simp only [Category.assoc] at hkeyB
  rw [hx1] at hkeyB
  have hfinal :
      ((r.iso.appIso V).inv.app
              ((A.selfOverlap.fst.appFunctor V).obj ((A.selfOverlap.inverse.appFunctor V).obj x)) ≫
            (A.selfOverlap.comparison.appIso V).hom.app
              ((A.selfOverlap.inverse.appFunctor V).obj x) ≫
          (r.iso.appIso V).hom.app
              ((A.selfOverlap.snd.appFunctor V).obj ((A.selfOverlap.inverse.appFunctor V).obj x)) ≫
            (B.map.appFunctor V).map
              (((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
                ((A.selfOverlap.inverse_target.appIso V).hom.app x))) ≫
        (B.map.appFunctor V).map ((r.overlapMap_source.appIso V).inv.app x) =
      (B.map.appFunctor V).map
          (((FppfStack.mapOfSchemeHom r.hom).appFunctor V).map
            ((A.selfOverlap.inverse_source.appIso V).hom.app x)) ≫
        (B.map.appFunctor V).map ((r.overlapMap_target.appIso V).inv.app x) ≫
          (B.selfOverlap.comparison.appIso V).inv.app ((r.overlapMap.appFunctor V).obj x) := by
    rw [hkeyB, Category.assoc, hcls]
  simpa only [Category.assoc] using hfinal.symm

/-- **Inverse compatibility of the induced map of self-overlaps.**  A chart refinement's induced
map `overlapMap` is compatible with the groupoid inverse maps: `overlapMap ≫ inverse` and
`inverse ≫ overlapMap` are both classifying maps of the same cone (the inversion cone of
`B.selfOverlap` precomposed by `overlapMap`), hence 2-isomorphic by the bilimit's uniqueness of
lifts.  Combines `inverse_R_classifies`/`inverse_S_classifies` via `bilimit.lift_unique`; no
further content is needed. -/
noncomputable def inverse_compat (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.inverse)
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.inverse r.overlapMap) :=
  (B.selfOverlap.bilimit.lift_unique r.inverseCompatCone
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap B.selfOverlap.inverse)
      (inverse_R_fst r) (inverse_R_snd r) (inverse_R_classifies r)).trans
    (B.selfOverlap.bilimit.lift_unique r.inverseCompatCone
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.inverse r.overlapMap)
      (inverse_S_fst r) (inverse_S_snd r) (inverse_S_classifies r)).symm

/-! ### Composition compatibility -/

/-- The comparison 2-cell of the cone, over `B.selfOverlap.composable`'s cospan, classified by
the induced map on composable pairs: assembled from `A.selfOverlap`'s own composability 2-cell
and the source/target compatibility of `overlapMap`, by whiskering and reassociation. -/
noncomputable def overlapMap₂Comparison (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.firstArrow r.overlapMap) B.selfOverlap.snd)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.secondArrow r.overlapMap)
        B.selfOverlap.fst) :=
  ((((StackIso2.associator A.selfOverlap.firstArrow r.overlapMap B.selfOverlap.snd).trans
    (StackIso2.whiskerLeft A.selfOverlap.firstArrow r.overlapMap_target)).trans
      (StackIso2.associator A.selfOverlap.firstArrow A.selfOverlap.snd
        (FppfStack.mapOfSchemeHom r.hom)).symm).trans
        (StackIso2.whiskerRight A.selfOverlap.composableComparison
          (FppfStack.mapOfSchemeHom r.hom))).trans
    (((StackIso2.associator A.selfOverlap.secondArrow A.selfOverlap.fst
        (FppfStack.mapOfSchemeHom r.hom)).trans
      (StackIso2.whiskerLeft A.selfOverlap.secondArrow r.overlapMap_source.symm)).trans
      (StackIso2.associator A.selfOverlap.secondArrow r.overlapMap B.selfOverlap.fst).symm)

/-- The cone, over `B.selfOverlap.composable`'s cospan, classified by the induced map on
composable pairs. -/
noncomputable def overlapMap₂Cone (r : ChartRefinement A B) :
    StackTwoPullback.Cone (f := B.selfOverlap.snd) (g := B.selfOverlap.fst)
      A.selfOverlap.composable.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp A.selfOverlap.firstArrow r.overlapMap
  snd := Pseudofunctor.StrongTrans.vcomp A.selfOverlap.secondArrow r.overlapMap
  comparison := overlapMap₂Comparison r

/-- **The induced map on composable pairs.**  A chart refinement `r` induces a map from the
composable-pair stack of `A`'s self-overlap to that of `B`, built by the universal property of
`B.selfOverlap.composable` applied to `overlapMap₂Cone`. -/
noncomputable def overlapMap₂ (r : ChartRefinement A B) :
    StackHom A.selfOverlap.composable.pullback B.selfOverlap.composable.pullback :=
  B.selfOverlap.composable.bilimit.lift (overlapMap₂Cone r)

/-- The induced map on composable pairs commutes with the first-arrow projections, up to the
displayed 2-cell. -/
noncomputable def overlapMap₂_firstArrow (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap₂ B.selfOverlap.firstArrow)
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.firstArrow r.overlapMap) :=
  B.selfOverlap.composable.bilimit.lift_fst (overlapMap₂Cone r)

/-- The induced map on composable pairs commutes with the second-arrow projections, up to the
displayed 2-cell. -/
noncomputable def overlapMap₂_secondArrow (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap₂ B.selfOverlap.secondArrow)
      (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.secondArrow r.overlapMap) :=
  B.selfOverlap.composable.bilimit.lift_snd (overlapMap₂Cone r)

/-- The induced map on composable pairs classifies its defining cone completely, including the
comparison face. -/
theorem overlapMap₂_classifies (r : ChartRefinement A B) :
    StackTwoPullback.ConeLiftClassifies B.selfOverlap.composable.toStackTwoPullback
      (overlapMap₂Cone r) r.overlapMap₂ r.overlapMap₂_firstArrow r.overlapMap₂_secondArrow :=
  B.selfOverlap.composable.bilimit.lift_compatible (overlapMap₂Cone r)

/-- The cone, over `B.map, B.map`, classified by both sides of compose-compatibility: the
composition cone of `B.selfOverlap` precomposed by the induced map `overlapMap₂`. -/
noncomputable def composeCompatCone (r : ChartRefinement A B) :
    StackTwoPullback.Cone (f := B.map) (g := B.map) A.selfOverlap.composable.pullback where
  fst := Pseudofunctor.StrongTrans.vcomp r.overlapMap₂ B.selfOverlap.composeCone.fst
  snd := Pseudofunctor.StrongTrans.vcomp r.overlapMap₂ B.selfOverlap.composeCone.snd
  comparison :=
    (StackIso2.associator r.overlapMap₂ B.selfOverlap.composeCone.fst B.map).trans
      ((StackIso2.whiskerLeft r.overlapMap₂ B.selfOverlap.composeCone.comparison).trans
        (StackIso2.associator r.overlapMap₂ B.selfOverlap.composeCone.snd B.map).symm)

/-- The first projection witness for the "R-side" of compose-compatibility:
`overlapMap₂ ≫ compose` composed with `fst`. -/
noncomputable def compose_R_fst (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp r.overlapMap₂ B.selfOverlap.compose) B.selfOverlap.fst)
      (r.composeCompatCone).fst :=
  (StackIso2.associator r.overlapMap₂ B.selfOverlap.compose B.selfOverlap.fst).trans
    (StackIso2.whiskerLeft r.overlapMap₂ B.selfOverlap.compose_source)

/-- The second projection witness for the "R-side" of compose-compatibility. -/
noncomputable def compose_R_snd (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp r.overlapMap₂ B.selfOverlap.compose) B.selfOverlap.snd)
      (r.composeCompatCone).snd :=
  (StackIso2.associator r.overlapMap₂ B.selfOverlap.compose B.selfOverlap.snd).trans
    (StackIso2.whiskerLeft r.overlapMap₂ B.selfOverlap.compose_target)

/-- **`overlapMap₂ ≫ compose` classifies `composeCompatCone`** (the "R-side" half of
compose-compatibility).  Direct specialization of `Genuine.cone_classifies_precomp` to
`B.selfOverlap`'s own composition cone, precomposed by `overlapMap₂`; no new proof content. -/
theorem compose_R_classifies (r : ChartRefinement A B) :
    StackTwoPullback.ConeLiftClassifies B.selfOverlap.toStackTwoPullback r.composeCompatCone
      (Pseudofunctor.StrongTrans.vcomp r.overlapMap₂ B.selfOverlap.compose)
      (compose_R_fst r) (compose_R_snd r) :=
  StackTwoPullback.Genuine.cone_classifies_precomp B.selfOverlap B.selfOverlap.composeCone
    B.selfOverlap.compose B.selfOverlap.compose_source B.selfOverlap.compose_target
    B.selfOverlap.compose_classifies r.overlapMap₂

/-- The first projection witness for the "S-side" of compose-compatibility:
`compose ≫ overlapMap` composed with `fst`. -/
noncomputable def compose_S_fst (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.compose r.overlapMap) B.selfOverlap.fst)
      (r.composeCompatCone).fst :=
  ((StackIso2.associator A.selfOverlap.compose r.overlapMap B.selfOverlap.fst).trans
    (StackIso2.whiskerLeft A.selfOverlap.compose r.overlapMap_source)).trans
    ((((StackIso2.associator A.selfOverlap.compose A.selfOverlap.fst
          (FppfStack.mapOfSchemeHom r.hom)).symm.trans
        (StackIso2.whiskerRight A.selfOverlap.compose_source
          (FppfStack.mapOfSchemeHom r.hom))).trans
      (StackIso2.associator A.selfOverlap.firstArrow A.selfOverlap.fst
        (FppfStack.mapOfSchemeHom r.hom))).trans
      ((StackIso2.whiskerLeft A.selfOverlap.firstArrow r.overlapMap_source.symm).trans
        ((StackIso2.associator A.selfOverlap.firstArrow r.overlapMap B.selfOverlap.fst).symm.trans
          ((StackIso2.whiskerRight r.overlapMap₂_firstArrow.symm B.selfOverlap.fst).trans
            (StackIso2.associator r.overlapMap₂ B.selfOverlap.firstArrow B.selfOverlap.fst)))))

/-- The second projection witness for the "S-side" of compose-compatibility. -/
noncomputable def compose_S_snd (r : ChartRefinement A B) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp A.selfOverlap.compose r.overlapMap) B.selfOverlap.snd)
      (r.composeCompatCone).snd :=
  ((StackIso2.associator A.selfOverlap.compose r.overlapMap B.selfOverlap.snd).trans
    (StackIso2.whiskerLeft A.selfOverlap.compose r.overlapMap_target)).trans
    ((((StackIso2.associator A.selfOverlap.compose A.selfOverlap.snd
          (FppfStack.mapOfSchemeHom r.hom)).symm.trans
        (StackIso2.whiskerRight A.selfOverlap.compose_target
          (FppfStack.mapOfSchemeHom r.hom))).trans
      (StackIso2.associator A.selfOverlap.secondArrow A.selfOverlap.snd
        (FppfStack.mapOfSchemeHom r.hom))).trans
      ((StackIso2.whiskerLeft A.selfOverlap.secondArrow r.overlapMap_target.symm).trans
        ((StackIso2.associator A.selfOverlap.secondArrow r.overlapMap B.selfOverlap.snd).symm.trans
          ((StackIso2.whiskerRight r.overlapMap₂_secondArrow.symm B.selfOverlap.snd).trans
            (StackIso2.associator r.overlapMap₂ B.selfOverlap.secondArrow B.selfOverlap.snd)))))

end StackChart.ChartRefinement

namespace PresentationGroupoidObject

variable {X : FppfStack.{u}} {A B : StackChart X}

/-- **A morphism of chart-presentation-groupoid objects covering a scheme map.**  Given
presentation groupoid objects `PA`, `PB` attached to two charts `A`, `B` of the same stack `X`
and a scheme morphism `q : A.scheme ⟶ B.scheme` (promoted to a stack morphism), this records a
map of arrow stacks compatible with the source, target, unit and inverse maps, up to the
displayed 2-cells.  This is exactly the data (2) of `Stacks.ChartRefinement` induces from a
chart refinement: no compatibility with `compose` is asserted here (see the module docstring
for what remains open). -/
structure ChartMap (PA : StackTwoPullback.PresentationGroupoidObject A.map)
    (PB : StackTwoPullback.PresentationGroupoidObject B.map)
    (q : StackHom (representedStack A.scheme) (representedStack B.scheme)) where
  /-- The induced map of arrow stacks. -/
  hom : StackHom PA.arrows PB.arrows
  /-- Compatibility with the source maps, up to the displayed 2-cell. -/
  hom_source : StackIso2
    (Pseudofunctor.StrongTrans.vcomp hom PB.source)
    (Pseudofunctor.StrongTrans.vcomp PA.source q)
  /-- Compatibility with the target maps, up to the displayed 2-cell. -/
  hom_target : StackIso2
    (Pseudofunctor.StrongTrans.vcomp hom PB.target)
    (Pseudofunctor.StrongTrans.vcomp PA.target q)
  /-- Compatibility with the unit maps, up to the displayed 2-cell. -/
  hom_unit : StackIso2
    (Pseudofunctor.StrongTrans.vcomp q PB.unit)
    (Pseudofunctor.StrongTrans.vcomp PA.unit hom)
  /-- Compatibility with the inverse maps, up to the displayed 2-cell. -/
  hom_inv : StackIso2
    (Pseudofunctor.StrongTrans.vcomp hom PB.inverse)
    (Pseudofunctor.StrongTrans.vcomp PA.inverse hom)

/-- **The morphism of presentation-groupoid objects induced by a chart refinement.**  This is
`PresentationGroupoidObject`'s first consumer: every `r : ChartRefinement A B` gives a
`ChartMap` between the presentation groupoid objects of the canonical self-overlaps of `A` and
`B`, covering the promoted refinement scheme morphism, built from `ChartRefinement.overlapMap`
and its source/target/unit/inverse compatibility 2-cells (all fully proved; `compose`
compatibility remains open, see the module docstring). -/
noncomputable def map (r : StackChart.ChartRefinement A B) :
    ChartMap (StackTwoPullback.presentationGroupoidObject A.map A.selfOverlap)
      (StackTwoPullback.presentationGroupoidObject B.map B.selfOverlap)
      (FppfStack.mapOfSchemeHom r.hom) where
  hom := r.overlapMap
  hom_source := r.overlapMap_source
  hom_target := r.overlapMap_target
  hom_unit := r.unit_compat
  hom_inv := r.inverse_compat

end PresentationGroupoidObject

end GromovWitten.AlgebraicGeometry
