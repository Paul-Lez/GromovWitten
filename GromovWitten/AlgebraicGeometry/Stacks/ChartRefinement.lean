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

Compatibility of `overlapMap` with the groupoid unit map is now fully proved:
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
`inverse`-compatibility (via `inverseCone` in place of the trivial cone) has the identical shape
and is now unblocked by the same recipe; `compose`-compatibility additionally needs a
composable-pair-level induced map (buildable the same way `overlapMap` itself is, from
`refinementGroupoidMap`'s pattern applied to `R.composable`/`S.composable`).  Neither is
attempted here; see the accompanying report.
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

end StackChart.ChartRefinement

namespace PresentationGroupoidObject

variable {X : FppfStack.{u}} {A B : StackChart X}

/-- **A morphism of chart-presentation-groupoid objects covering a scheme map.**  Given
presentation groupoid objects `PA`, `PB` attached to two charts `A`, `B` of the same stack `X`
and a scheme morphism `q : A.scheme ⟶ B.scheme` (promoted to a stack morphism), this records a
map of arrow stacks compatible with the source, target and unit maps, up to the displayed
2-cells.  This is exactly the data (2) of `Stacks.ChartRefinement` induces from a chart
refinement: no compatibility with `compose`/`inverse` is asserted here (see the module
docstring for what remains open). -/
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

/-- **The morphism of presentation-groupoid objects induced by a chart refinement.**  This is
`PresentationGroupoidObject`'s first consumer: every `r : ChartRefinement A B` gives a
`ChartMap` between the presentation groupoid objects of the canonical self-overlaps of `A` and
`B`, covering the promoted refinement scheme morphism, built from `ChartRefinement.overlapMap`
and its source/target/unit compatibility 2-cells (all fully proved, with no remaining
compatibility asserted beyond `compose`/`inverse`). -/
noncomputable def map (r : StackChart.ChartRefinement A B) :
    ChartMap (StackTwoPullback.presentationGroupoidObject A.map A.selfOverlap)
      (StackTwoPullback.presentationGroupoidObject B.map B.selfOverlap)
      (FppfStack.mapOfSchemeHom r.hom) where
  hom := r.overlapMap
  hom_source := r.overlapMap_source
  hom_target := r.overlapMap_target
  hom_unit := r.unit_compat

end PresentationGroupoidObject

end GromovWitten.AlgebraicGeometry
