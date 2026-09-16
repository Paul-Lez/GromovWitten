/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableMaps.Basic

/-!
# Evaluation maps for marked maps

Evaluation at a marking is the composite from the base through that section to the source and
then to the target.  The results below record compatibility with every diagram operation defined
in `Basic`.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap

universe u v w

variable {V S : Scheme.{u}} {q : V ⟶ S} {I : Type v}

/-- Evaluation of a family of marked maps at its `i`-th marking. -/
def evaluation (F : MarkedMap q I) (i : I) : S ⟶ V := F.marking i ≫ F.map

/-- Evaluation is a section of the target over the base. -/
@[reassoc]
lemma evaluation_toBase (F : MarkedMap q I) (i : I) : F.evaluation i ≫ q = 𝟙 S := by
  rw [evaluation, Category.assoc, F.map_toBase, F.marking_toBase]

/-- A morphism of marked maps preserves every evaluation map. -/
lemma evaluation_naturality {F G : MarkedMap q I} (f : F ⟶ G) (i : I) :
    F.evaluation i = G.evaluation i := by
  rw [evaluation, evaluation, ← f.map_comm, ← Category.assoc, f.marking_comm]

@[simp]
lemma evaluation_restrictMarkings {J : Type w} (F : MarkedMap q I) (ρ : J → I) (j : J) :
    (F.restrictMarkings ρ).evaluation j = F.evaluation (ρ j) := rfl

@[simp]
lemma evaluation_reindex {J : Type w} (F : MarkedMap q I) (e : J ≃ I) (j : J) :
    (F.reindex e).evaluation j = F.evaluation (e j) := rfl

@[reassoc]
lemma evaluation_postcompose {W : Scheme.{u}} {q' : W ⟶ S} (F : MarkedMap q I)
    (f : V ⟶ W) (hf : f ≫ q' = q) (i : I) :
    (F.postcompose f hf).evaluation i = F.evaluation i ≫ f := by
  simp only [evaluation, postcompose_marking, postcompose_map, Category.assoc]
  rfl

end GromovWitten.AlgebraicGeometry.Curves.StableMaps.MarkedMap
