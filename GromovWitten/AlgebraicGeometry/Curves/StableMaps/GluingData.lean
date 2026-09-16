/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.BaseChange

/-!
# Gluing input data for marked maps

Clutching two mapped curves requires more than a choice of markings: the two evaluation maps at
the markings must agree.  This file packages precisely that input, both for two different marked
maps and for two distinct markings of one marked map.  It does not assert that a pushout of source
schemes exists, nor does it construct a glued marked map.

The constructions below show that the evaluation-equality gate is invariant under morphisms of
marked maps, target-changing isomorphisms, changes of marking labels, target postcomposition, and
chosen-pullback base change.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap

universe u v w v' w'

noncomputable section

variable {V S : Scheme.{u}} {q : V ⟶ S}
variable {I : Type v} {J : Type w}

/-- Input for external gluing of two marked maps.  The equality field is the compatibility
condition needed for the two selected sections to map to the same point of the target family. -/
structure ExternalGluingData (F : MarkedMap q I) (G : MarkedMap q J) where
  left : I
  right : J
  evaluation_eq : F.evaluation left = G.evaluation right

/-- Input for self-gluing a marked map.  The markings are required to be distinct even though
their evaluation maps agree. -/
structure SelfGluingData (F : MarkedMap q I) where
  first : I
  second : I
  distinct : first ≠ second
  evaluation_eq : F.evaluation first = F.evaluation second

namespace ExternalGluingData

variable {F F' F'' : MarkedMap q I} {G G' G'' : MarkedMap q J}

@[ext]
theorem ext {D E : ExternalGluingData F G} (hleft : D.left = E.left)
    (hright : D.right = E.right) : D = E := by
  cases D
  cases E
  cases hleft
  cases hright
  rfl

/-- Marked-map morphisms preserve admissible external gluing input. -/
def map (D : ExternalGluingData F G) (f : F ⟶ F') (g : G ⟶ G') :
    ExternalGluingData F' G' where
  left := D.left
  right := D.right
  evaluation_eq := by
    calc
      F'.evaluation D.left = F.evaluation D.left := (evaluation_naturality f D.left).symm
      _ = G.evaluation D.right := D.evaluation_eq
      _ = G'.evaluation D.right := evaluation_naturality g D.right

@[simp]
lemma map_left (D : ExternalGluingData F G) (f : F ⟶ F') (g : G ⟶ G') :
    (D.map f g).left = D.left := rfl

@[simp]
lemma map_right (D : ExternalGluingData F G) (f : F ⟶ F') (g : G ⟶ G') :
    (D.map f g).right = D.right := rfl

@[simp]
lemma map_id (D : ExternalGluingData F G) : D.map (𝟙 F) (𝟙 G) = D := by
  ext <;> rfl

@[simp]
lemma map_comp (D : ExternalGluingData F G) (f : F ⟶ F') (f' : F' ⟶ F'')
    (g : G ⟶ G') (g' : G' ⟶ G'') :
    (D.map f g).map f' g' = D.map (f ≫ f') (g ≫ g') := by
  ext <;> rfl

/-- Relabel both sets of markings.  The selected markings are transported by the inverse
equivalences, so no choice of a preimage is needed. -/
def reindex {I' : Type v'} {J' : Type w'} (D : ExternalGluingData F G)
    (eI : I' ≃ I) (eJ : J' ≃ J) :
    ExternalGluingData (F.reindex eI) (G.reindex eJ) where
  left := eI.symm D.left
  right := eJ.symm D.right
  evaluation_eq := by
    simpa only [evaluation_reindex, Equiv.apply_symm_apply] using D.evaluation_eq

@[simp]
lemma reindex_left {I' : Type v'} {J' : Type w'} (D : ExternalGluingData F G)
    (eI : I' ≃ I) (eJ : J' ≃ J) :
    (D.reindex eI eJ).left = eI.symm D.left := rfl

@[simp]
lemma reindex_right {I' : Type v'} {J' : Type w'} (D : ExternalGluingData F G)
    (eI : I' ≃ I) (eJ : J' ≃ J) :
    (D.reindex eI eJ).right = eJ.symm D.right := rfl

/-- Postcomposition of the target preserves admissible external gluing input. -/
def postcompose {W : Scheme.{u}} {q' : W ⟶ S} (D : ExternalGluingData F G)
    (f : V ⟶ W) (hf : f ≫ q' = q) :
    ExternalGluingData (F.postcompose f hf) (G.postcompose f hf) where
  left := D.left
  right := D.right
  evaluation_eq := by
    simpa only [evaluation_postcompose] using
      congrArg (fun k : S ⟶ V ↦ k ≫ f) D.evaluation_eq

@[simp]
lemma postcompose_left {W : Scheme.{u}} {q' : W ⟶ S} (D : ExternalGluingData F G)
    (f : V ⟶ W) (hf : f ≫ q' = q) : (D.postcompose f hf).left = D.left := rfl

@[simp]
lemma postcompose_right {W : Scheme.{u}} {q' : W ⟶ S} (D : ExternalGluingData F G)
    (f : V ⟶ W) (hf : f ≫ q' = q) : (D.postcompose f hf).right = D.right := rfl

/-- Chosen-pullback base change preserves admissible external gluing input. -/
def baseChange (D : ExternalGluingData F G) {T : Scheme.{u}} (b : T ⟶ S) :
    ExternalGluingData (F.baseChange b) (G.baseChange b) where
  left := D.left
  right := D.right
  evaluation_eq := by
    rw [evaluation_baseChange, evaluation_baseChange]
    apply pullback.hom_ext
    · simp only [baseChangedEvaluation_fst]
      rw [D.evaluation_eq]
    · simp only [baseChangedEvaluation_snd]

@[simp]
lemma baseChange_left (D : ExternalGluingData F G) {T : Scheme.{u}} (b : T ⟶ S) :
    (D.baseChange b).left = D.left := rfl

@[simp]
lemma baseChange_right (D : ExternalGluingData F G) {T : Scheme.{u}} (b : T ⟶ S) :
    (D.baseChange b).right = D.right := rfl

/-- Transport external gluing input through target-changing isomorphisms having the same target
comparison.  Equality of the two target comparisons is essential: unrelated target
automorphisms need not carry two equal evaluations to equal evaluations. -/
def targetedIso {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    {G' : MarkedMap q' J} (D : ExternalGluingData F G) (eF : TargetedIso F F')
    (eG : TargetedIso G G') (htarget : eF.targetIso = eG.targetIso) :
    ExternalGluingData F' G' where
  left := D.left
  right := D.right
  evaluation_eq := by
    calc
      F'.evaluation D.left = F.evaluation D.left ≫ eF.targetIso.hom :=
        (eF.evaluation_targetIso D.left).symm
      _ = G.evaluation D.right ≫ eF.targetIso.hom :=
        congrArg (fun k : S ⟶ V ↦ k ≫ eF.targetIso.hom) D.evaluation_eq
      _ = G.evaluation D.right ≫ eG.targetIso.hom := by rw [htarget]
      _ = G'.evaluation D.right := eG.evaluation_targetIso D.right

@[simp]
lemma targetedIso_left {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    {G' : MarkedMap q' J} (D : ExternalGluingData F G) (eF : TargetedIso F F')
    (eG : TargetedIso G G') (htarget : eF.targetIso = eG.targetIso) :
    (D.targetedIso eF eG htarget).left = D.left := rfl

@[simp]
lemma targetedIso_right {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    {G' : MarkedMap q' J} (D : ExternalGluingData F G) (eF : TargetedIso F F')
    (eG : TargetedIso G G') (htarget : eF.targetIso = eG.targetIso) :
    (D.targetedIso eF eG htarget).right = D.right := rfl

@[simp]
lemma targetedIso_refl (D : ExternalGluingData F G) :
    D.targetedIso (TargetedIso.refl F) (TargetedIso.refl G) rfl = D := by
  ext <;> rfl

/-- Transporting external gluing input through target-changing isomorphisms and then their
inverses recovers the original input. -/
lemma targetedIso_symm {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    {G' : MarkedMap q' J} (D : ExternalGluingData F G) (eF : TargetedIso F F')
    (eG : TargetedIso G G') (htarget : eF.targetIso = eG.targetIso) :
    let hsymm : eF.symm.targetIso = eG.symm.targetIso :=
      congrArg (fun e : V ≅ W ↦ e.symm) htarget
    (D.targetedIso eF eG htarget).targetedIso eF.symm eG.symm hsymm = D := by
  dsimp
  ext <;> rfl

/-- Transport of external gluing input respects composition of targeted isomorphisms. -/
lemma targetedIso_trans {W Z : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S}
    {F' : MarkedMap q' I} {G' : MarkedMap q' J} {F'' : MarkedMap q'' I}
    {G'' : MarkedMap q'' J} (D : ExternalGluingData F G) (eF : TargetedIso F F')
    (eG : TargetedIso G G') (fF : TargetedIso F' F'') (fG : TargetedIso G' G'')
    (he : eF.targetIso = eG.targetIso) (hf : fF.targetIso = fG.targetIso) :
    let htrans : (eF.trans fF).targetIso = (eG.trans fG).targetIso := by
      rw [TargetedIso.trans_targetIso, TargetedIso.trans_targetIso, he, hf]
    (D.targetedIso eF eG he).targetedIso fF fG hf =
      D.targetedIso (eF.trans fF) (eG.trans fG) htrans := by
  dsimp
  ext <;> rfl

/-- For fixed markings, external gluing data exists exactly when the evaluation maps agree.
Thus merely choosing two markings does not bypass the evaluation-equality gate. -/
theorem exists_with_indices_iff (i : I) (j : J) :
    (∃ D : ExternalGluingData F G, D.left = i ∧ D.right = j) ↔
      F.evaluation i = G.evaluation j := by
  constructor
  · rintro ⟨D, hi, hj⟩
    simpa only [hi, hj] using D.evaluation_eq
  · intro h
    exact ⟨⟨i, j, h⟩, rfl, rfl⟩

/-- In particular, unequal evaluations rule out external gluing input at the selected markings. -/
theorem not_exists_with_indices_of_evaluation_ne (i : I) (j : J)
    (h : F.evaluation i ≠ G.evaluation j) :
    ¬ ∃ D : ExternalGluingData F G, D.left = i ∧ D.right = j := by
  rw [exists_with_indices_iff]
  exact h

end ExternalGluingData

namespace SelfGluingData

variable {F F' F'' : MarkedMap q I}

@[ext]
theorem ext {D E : SelfGluingData F} (hfirst : D.first = E.first)
    (hsecond : D.second = E.second) : D = E := by
  cases D
  cases E
  cases hfirst
  cases hsecond
  rfl

/-- A marked-map morphism preserves admissible self-gluing input. -/
def map (D : SelfGluingData F) (f : F ⟶ F') : SelfGluingData F' where
  first := D.first
  second := D.second
  distinct := D.distinct
  evaluation_eq := by
    calc
      F'.evaluation D.first = F.evaluation D.first := (evaluation_naturality f D.first).symm
      _ = F.evaluation D.second := D.evaluation_eq
      _ = F'.evaluation D.second := evaluation_naturality f D.second

@[simp]
lemma map_first (D : SelfGluingData F) (f : F ⟶ F') : (D.map f).first = D.first := rfl

@[simp]
lemma map_second (D : SelfGluingData F) (f : F ⟶ F') :
    (D.map f).second = D.second := rfl

@[simp]
lemma map_id (D : SelfGluingData F) : D.map (𝟙 F) = D := by
  ext <;> rfl

@[simp]
lemma map_comp (D : SelfGluingData F) (f : F ⟶ F') (f' : F' ⟶ F'') :
    (D.map f).map f' = D.map (f ≫ f') := by
  ext <;> rfl

/-- Relabel the markings in self-gluing input. -/
def reindex {I' : Type v'} (D : SelfGluingData F) (e : I' ≃ I) :
    SelfGluingData (F.reindex e) where
  first := e.symm D.first
  second := e.symm D.second
  distinct := fun h ↦ D.distinct (e.symm.injective h)
  evaluation_eq := by
    simpa only [evaluation_reindex, Equiv.apply_symm_apply] using D.evaluation_eq

@[simp]
lemma reindex_first {I' : Type v'} (D : SelfGluingData F) (e : I' ≃ I) :
    (D.reindex e).first = e.symm D.first := rfl

@[simp]
lemma reindex_second {I' : Type v'} (D : SelfGluingData F) (e : I' ≃ I) :
    (D.reindex e).second = e.symm D.second := rfl

/-- Target postcomposition preserves admissible self-gluing input. -/
def postcompose {W : Scheme.{u}} {q' : W ⟶ S} (D : SelfGluingData F)
    (f : V ⟶ W) (hf : f ≫ q' = q) : SelfGluingData (F.postcompose f hf) where
  first := D.first
  second := D.second
  distinct := D.distinct
  evaluation_eq := by
    simpa only [evaluation_postcompose] using
      congrArg (fun k : S ⟶ V ↦ k ≫ f) D.evaluation_eq

@[simp]
lemma postcompose_first {W : Scheme.{u}} {q' : W ⟶ S} (D : SelfGluingData F)
    (f : V ⟶ W) (hf : f ≫ q' = q) : (D.postcompose f hf).first = D.first := rfl

@[simp]
lemma postcompose_second {W : Scheme.{u}} {q' : W ⟶ S} (D : SelfGluingData F)
    (f : V ⟶ W) (hf : f ≫ q' = q) : (D.postcompose f hf).second = D.second := rfl

/-- Chosen-pullback base change preserves admissible self-gluing input. -/
def baseChange (D : SelfGluingData F) {T : Scheme.{u}} (b : T ⟶ S) :
    SelfGluingData (F.baseChange b) where
  first := D.first
  second := D.second
  distinct := D.distinct
  evaluation_eq := by
    rw [evaluation_baseChange, evaluation_baseChange]
    apply pullback.hom_ext
    · simp only [baseChangedEvaluation_fst]
      rw [D.evaluation_eq]
    · simp only [baseChangedEvaluation_snd]

@[simp]
lemma baseChange_first (D : SelfGluingData F) {T : Scheme.{u}} (b : T ⟶ S) :
    (D.baseChange b).first = D.first := rfl

@[simp]
lemma baseChange_second (D : SelfGluingData F) {T : Scheme.{u}} (b : T ⟶ S) :
    (D.baseChange b).second = D.second := rfl

/-- Transport self-gluing input through a target-changing isomorphism. -/
def targetedIso {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    (D : SelfGluingData F) (e : TargetedIso F F') : SelfGluingData F' where
  first := D.first
  second := D.second
  distinct := D.distinct
  evaluation_eq := by
    calc
      F'.evaluation D.first = F.evaluation D.first ≫ e.targetIso.hom :=
        (e.evaluation_targetIso D.first).symm
      _ = F.evaluation D.second ≫ e.targetIso.hom :=
        congrArg (fun k : S ⟶ V ↦ k ≫ e.targetIso.hom) D.evaluation_eq
      _ = F'.evaluation D.second := e.evaluation_targetIso D.second

@[simp]
lemma targetedIso_first {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    (D : SelfGluingData F) (e : TargetedIso F F') :
    (D.targetedIso e).first = D.first := rfl

@[simp]
lemma targetedIso_second {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    (D : SelfGluingData F) (e : TargetedIso F F') :
    (D.targetedIso e).second = D.second := rfl

@[simp]
lemma targetedIso_refl (D : SelfGluingData F) :
    D.targetedIso (TargetedIso.refl F) = D := by
  ext <;> rfl

@[simp]
lemma targetedIso_symm {W : Scheme.{u}} {q' : W ⟶ S} {F' : MarkedMap q' I}
    (D : SelfGluingData F) (e : TargetedIso F F') :
    (D.targetedIso e).targetedIso e.symm = D := by
  ext <;> rfl

/-- Transport of self-gluing input respects composition of targeted isomorphisms. -/
lemma targetedIso_trans {W Z : Scheme.{u}} {q' : W ⟶ S} {q'' : Z ⟶ S}
    {F' : MarkedMap q' I} {F'' : MarkedMap q'' I} (D : SelfGluingData F)
    (e : TargetedIso F F') (f : TargetedIso F' F'') :
    (D.targetedIso e).targetedIso f = D.targetedIso (e.trans f) := by
  ext <;> rfl

/-- For fixed markings, self-gluing data exists exactly when they are distinct and their
evaluation maps agree.  This is the self-gluing equality gate in an executable form. -/
theorem exists_with_indices_iff (i j : I) :
    (∃ D : SelfGluingData F, D.first = i ∧ D.second = j) ↔
      i ≠ j ∧ F.evaluation i = F.evaluation j := by
  constructor
  · rintro ⟨D, hi, hj⟩
    constructor
    · simpa only [hi, hj] using D.distinct
    · simpa only [hi, hj] using D.evaluation_eq
  · rintro ⟨hij, heval⟩
    exact ⟨⟨i, j, hij, heval⟩, rfl, rfl⟩

/-- Unequal evaluations rule out self-gluing input at the selected markings. -/
theorem not_exists_with_indices_of_evaluation_ne (i j : I)
    (h : F.evaluation i ≠ F.evaluation j) :
    ¬ ∃ D : SelfGluingData F, D.first = i ∧ D.second = j := by
  rw [exists_with_indices_iff]
  exact fun h' ↦ h h'.2

end SelfGluingData

end

end GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
