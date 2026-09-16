/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.Geometry
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Bundled prestable maps

This file packages the geometric predicate on `MarkedMap` as its full subcategory.  A
`PrestableMap q I` therefore contains exactly a marked map to `q` and a proof that its pointed
source is prestable; morphisms are the already-defined morphisms of marked maps.  The full
subcategory construction keeps the categorical identity, composition, isomorphism, and
automorphism APIs definitionally aligned with the unbundled one.

Base change, restriction of markings, and target postcomposition lift to this category.  The
canonical chosen-pullback comparisons are also lifted, so bundling prestability does not discard
the choice-independence data of `MarkedMap`.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps

universe u v w

noncomputable section

/-- The object property selecting marked maps whose pointed source is prestable. -/
def prestableMapProperty {V S : Scheme.{u}} (q : V ⟶ S) (I : Type v) :
    ObjectProperty (MarkedMap q I) :=
  fun F ↦ MarkedMap.Prestable F

/-- The full category of marked maps whose pointed source is a prestable family. -/
abbrev PrestableMap {V S : Scheme.{u}} (q : V ⟶ S) (I : Type v) :=
  (prestableMapProperty q I).FullSubcategory

namespace PrestableMap

variable {V S : Scheme.{u}} {q : V ⟶ S} {I : Type v}

/-- Forget prestability and retain the underlying marked map. -/
abbrev markedMap (F : PrestableMap q I) : MarkedMap q I := F.obj

/-- The geometric prestability proof carried by a bundled prestable map. -/
theorem prestable (F : PrestableMap q I) : MarkedMap.Prestable F.markedMap := F.property

/-- The fully faithful inclusion of prestable maps into all marked maps. -/
abbrev inclusion : PrestableMap q I ⥤ MarkedMap q I :=
  (prestableMapProperty q I).ι

/-- Forget the target map and retain the pointed prestable source. -/
def pointedSourceFunctor : PrestableMap q I ⥤ PointedPrestableFamily S I where
  obj F := F.property.toPointedPrestableFamily
  map f :=
    { hom := f.hom.hom
      over_base := f.hom.over_base
      marking_comm := f.hom.marking_comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Arbitrary base change as a functor on bundled prestable maps. -/
def baseChangeFunctor {T : Scheme.{u}} (b : T ⟶ S) :
    PrestableMap q I ⥤ PrestableMap (pullback.snd q b) I :=
  (prestableMapProperty (pullback.snd q b) I).lift
    (inclusion (q := q) (I := I) ⋙ MarkedMap.baseChangeFunctor b)
    (fun F ↦ F.property.baseChange b)

@[simp]
theorem baseChangeFunctor_obj_markedMap {T : Scheme.{u}} (b : T ⟶ S)
    (F : PrestableMap q I) :
    ((baseChangeFunctor b).obj F).markedMap = F.markedMap.baseChange b := rfl

/-- Restrict the marking set along an injection. -/
def restrictMarkingsFunctor {J : Type w} (r : J → I) (hr : Function.Injective r) :
    PrestableMap q I ⥤ PrestableMap q J :=
  (prestableMapProperty q J).lift
    (inclusion (q := q) (I := I) ⋙ MarkedMap.restrictMarkingsFunctor r)
    (fun F ↦ F.property.restrictMarkings r hr)

/-- Postcomposition on the target as a functor on bundled prestable maps. -/
def postcomposeFunctor {W : Scheme.{u}} {q' : W ⟶ S} (a : V ⟶ W)
    (ha : a ≫ q' = q) : PrestableMap q I ⥤ PrestableMap q' I :=
  (prestableMapProperty q' I).lift
    (inclusion (q := q) (I := I) ⋙ MarkedMap.postcomposeFunctor a ha)
    (fun F ↦ F.property.postcompose a ha)

/-- A targeted isomorphism transports prestability, even though its two marked maps may have
different (isomorphic) targets. -/
theorem prestable_of_targetedIso {W : Scheme.{u}} {q' : W ⟶ S}
    {F : MarkedMap q I} {G : MarkedMap q' I} (e : MarkedMap.TargetedIso F G)
    (hF : MarkedMap.Prestable F) : MarkedMap.Prestable G :=
  MarkedMap.Prestable.of_iso e.toIso
    (hF.postcompose e.targetIso.hom e.targetIso_toBase)

/-- Prestability is invariant under a targeted isomorphism. -/
theorem prestable_targetedIso_iff {W : Scheme.{u}} {q' : W ⟶ S}
    {F : MarkedMap q I} {G : MarkedMap q' I} (e : MarkedMap.TargetedIso F G) :
    MarkedMap.Prestable F ↔ MarkedMap.Prestable G :=
  ⟨prestable_of_targetedIso e, prestable_of_targetedIso e.symm⟩

/-- Identity base change, after its canonical target transport, is canonically isomorphic to the
original bundled prestable map. -/
def baseChangeIdIso (F : PrestableMap q I) :
    (⟨(F.markedMap.baseChange (𝟙 S)).postcompose
        (MarkedMap.baseChangeIdTargetIso q).hom
        (MarkedMap.baseChangeIdComparison F.markedMap).targetIso_toBase,
      (F.property.baseChange (𝟙 S)).postcompose
        (MarkedMap.baseChangeIdTargetIso q).hom
        (MarkedMap.baseChangeIdComparison F.markedMap).targetIso_toBase⟩ :
      PrestableMap q I) ≅ F :=
  ObjectProperty.isoMk _ (MarkedMap.baseChangeIdIso F.markedMap)

/-- Iterated chosen base change, after canonical target transport, is canonically isomorphic to
direct base change in the category of bundled prestable maps. -/
def iteratedBaseChangeIso (F : PrestableMap q I) {T U : Scheme.{u}}
    (b : T ⟶ S) (c : U ⟶ T) :
    (⟨((F.markedMap.baseChange b).baseChange c).postcompose
        (MarkedMap.iteratedBaseChangeTargetIso q b c).hom
        (MarkedMap.iteratedBaseChangeComparison F.markedMap b c).targetIso_toBase,
      ((F.property.baseChange b).baseChange c).postcompose
        (MarkedMap.iteratedBaseChangeTargetIso q b c).hom
        (MarkedMap.iteratedBaseChangeComparison F.markedMap b c).targetIso_toBase⟩ :
      PrestableMap (pullback.snd q (c ≫ b)) I) ≅
      (baseChangeFunctor (c ≫ b)).obj F :=
  ObjectProperty.isoMk _ (MarkedMap.iteratedBaseChangeIso F.markedMap b c)

end PrestableMap

end

end GromovWitten.AlgebraicGeometry.Curves.StableMaps
