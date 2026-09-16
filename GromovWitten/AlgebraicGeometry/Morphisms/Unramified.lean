/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Unramified morphisms of schemes

This file packages the standard scheme-level notion missing from the pinned Mathlib version:
a morphism is unramified when it is formally unramified and locally of finite type.  The class
is local on source and target and is stable under composition and arbitrary base change.

The affine comparison theorem `Unramified.SpecMap_algebraMap_iff` identifies this definition
with Mathlib's ring-theoretic `Algebra.Unramified` class.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- A scheme morphism is unramified when it is formally unramified and locally of finite type. -/
@[mk_iff]
class Unramified {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  formallyUnramified : _root_.AlgebraicGeometry.FormallyUnramified f := by infer_instance
  locallyOfFiniteType : _root_.AlgebraicGeometry.LocallyOfFiniteType f := by infer_instance

namespace Unramified

attribute [instance] formallyUnramified locallyOfFiniteType

/-- Unramified morphisms contain identities and are stable under composition. -/
instance : MorphismProperty.IsMultiplicative @Unramified where
  id_mem X :=
    { formallyUnramified := by infer_instance
      locallyOfFiniteType := by infer_instance }
  comp_mem f g hf hg :=
    { formallyUnramified := MorphismProperty.comp_mem _ f g
        hf.formallyUnramified hg.formallyUnramified
      locallyOfFiniteType := MorphismProperty.comp_mem _ f g
        hf.locallyOfFiniteType hg.locallyOfFiniteType }

/-- Unramified morphisms are stable under arbitrary base change. -/
instance : MorphismProperty.IsStableUnderBaseChange @Unramified where
  of_isPullback sq hg :=
    { formallyUnramified := MorphismProperty.of_isPullback
        (P := @_root_.AlgebraicGeometry.FormallyUnramified) sq hg.formallyUnramified
      locallyOfFiniteType := MorphismProperty.of_isPullback
        (P := @_root_.AlgebraicGeometry.LocallyOfFiniteType) sq hg.locallyOfFiniteType }

instance : MorphismProperty.RespectsIso @Unramified :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Every immersion is unramified. -/
instance (priority := 900) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsImmersion f] : Unramified f where

set_option backward.isDefEq.respectTransparency false in
/-- Being unramified is Zariski-local on the target. -/
instance : IsZariskiLocalAtTarget @Unramified := by
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    exact
      { formallyUnramified := IsZariskiLocalAtTarget.restrict hf.formallyUnramified U
        locallyOfFiniteType := IsZariskiLocalAtTarget.restrict hf.locallyOfFiniteType U }
  · intro X Y f ι U hU hf
    exact
      { formallyUnramified := IsZariskiLocalAtTarget.of_iSup_eq_top U hU
          (fun i ↦ (hf i).formallyUnramified)
        locallyOfFiniteType := IsZariskiLocalAtTarget.of_iSup_eq_top U hU
          (fun i ↦ (hf i).locallyOfFiniteType) }

set_option backward.isDefEq.respectTransparency false in
/-- Being unramified is Zariski-local on the source. -/
instance : IsZariskiLocalAtSource @Unramified := by
  apply IsZariskiLocalAtSource.mk'
  · intro X Y f U hf
    exact
      { formallyUnramified := IsZariskiLocalAtSource.comp hf.formallyUnramified U.ι
        locallyOfFiniteType := IsZariskiLocalAtSource.comp hf.locallyOfFiniteType U.ι }
  · intro X Y f ι U hU hf
    exact
      { formallyUnramified := IsZariskiLocalAtSource.of_iSup_eq_top U hU
          (fun i ↦ (hf i).formallyUnramified)
        locallyOfFiniteType := IsZariskiLocalAtSource.of_iSup_eq_top U hU
          (fun i ↦ (hf i).locallyOfFiniteType) }

set_option backward.isDefEq.respectTransparency false in
/-- A composition of unramified morphisms is unramified. -/
instance {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Unramified f] [Unramified g] : Unramified (f ≫ g) :=
  MorphismProperty.comp_mem _ f g inferInstance inferInstance

/-- If a composite is unramified, then its first factor is unramified. -/
theorem of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Unramified (f ≫ g)] : Unramified f where
  formallyUnramified :=
    _root_.AlgebraicGeometry.FormallyUnramified.of_comp f g
  locallyOfFiniteType :=
    _root_.AlgebraicGeometry.locallyOfFiniteType_of_comp f g

set_option backward.isDefEq.respectTransparency false in
instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Unramified g] :
    Unramified (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency false in
instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Unramified f] :
    Unramified (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency false in
instance {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) [Unramified f] :
    Unramified (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict (P := @Unramified) inferInstance V

set_option backward.isDefEq.respectTransparency false in
instance {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e)
    [Unramified f] : Unramified (f.resLE V U e) := by
  delta Scheme.Hom.resLE
  exact IsZariskiLocalAtSource.comp (P := @Unramified)
    (IsZariskiLocalAtTarget.restrict (P := @Unramified) inferInstance V) (X.homOfLE e)

/-- On affine spectra, scheme-theoretic unramifiedness is formal unramifiedness plus finite
type for the corresponding ring homomorphism. -/
theorem Spec_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    Unramified (Spec.map f) ↔ f.hom.FormallyUnramified ∧ f.hom.FiniteType := by
  rw [unramified_iff,
    HasRingHomProperty.Spec_iff (P := @_root_.AlgebraicGeometry.FormallyUnramified),
    HasRingHomProperty.Spec_iff (P := @_root_.AlgebraicGeometry.LocallyOfFiniteType)]

set_option backward.isDefEq.respectTransparency.types false in
/-- An unramified morphism is equivalently a locally finite-type morphism with open diagonal. -/
theorem iff_isOpenImmersion_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Unramified f ↔
      _root_.AlgebraicGeometry.IsOpenImmersion (pullback.diagonal f) ∧
        _root_.AlgebraicGeometry.LocallyOfFiniteType f := by
  constructor
  · intro hf
    let _ := hf.formallyUnramified
    let _ := hf.locallyOfFiniteType
    exact ⟨inferInstance, hf.locallyOfFiniteType⟩
  · intro hf
    let _ := hf.1
    exact ⟨inferInstance, hf.2⟩

/-- The scheme definition agrees with `Algebra.Unramified` for a displayed algebra map. -/
theorem SpecMap_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Unramified (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
      Algebra.Unramified R S := by
  rw [Spec_iff]
  change (algebraMap R S).FormallyUnramified ∧ (algebraMap R S).FiniteType ↔ _
  rw [RingHom.formallyUnramified_algebraMap, RingHom.finiteType_algebraMap]
  constructor
  · intro h
    exact
      { formallyUnramified := h.1
        finiteType := h.2 }
  · intro h
    exact ⟨h.formallyUnramified, h.finiteType⟩

end Unramified

end GromovWitten.AlgebraicGeometry
