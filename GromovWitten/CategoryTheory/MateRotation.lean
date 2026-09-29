/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Rotation of adjunction mates

This file records the generic mate rotation used to move a base-change
unit formula across a square of adjunctions.
-/

open CategoryTheory
noncomputable section

namespace CategoryTheory

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
variable {A : C ⥤ D} {Ar : D ⥤ C} {B : C ⥤ E} {Br : E ⥤ C}
  {Cf : D ⥤ F} {Cr : F ⥤ D} {Df : E ⥤ F} {Dr : F ⥤ E}

/-- Rotate a right-adjoint unit formula into the corresponding left-adjoint one. -/
lemma mate_rotation (a : A ⊣ Ar) (b : B ⊣ Br) (c : Cf ⊣ Cr) (d : Df ⊣ Dr)
    (μ : A ⋙ Cf ⟶ B ⋙ Df) (e : Br ⋙ A ⟶ Df ⋙ Cr)
    (he : ∀ N, a.homEquiv _ _ (e.app N) =
      Br.map (d.unit.app N) ≫
        (conjugateEquiv (b.comp d) (a.comp c) μ).app (Df.obj N)) (M : C) :
    c.homEquiv _ _ (μ.app M) = A.map (b.unit.app M) ≫ e.app (B.obj M) := by
  apply (a.homEquiv _ _).injective
  rw [a.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  have heM := he (B.obj M)
  dsimp only [Functor.comp_obj] at heM
  rw [heM]
  have hcomp := congrFun (congrFun (Adjunction.comp_homEquiv a c) M)
    (Df.obj (B.obj M))
  have hcomp' := congrArg (fun q => q (μ.app M)) hcomp
  simp only [Equiv.trans_apply] at hcomp'
  rw [← hcomp']
  rw [Adjunction.homEquiv_unit]
  rw [← unit_conjugateEquiv (b.comp d) (a.comp c) μ]
  rw [Adjunction.comp_unit_app]
  simp only [Functor.comp_obj, Category.assoc]

end CategoryTheory
