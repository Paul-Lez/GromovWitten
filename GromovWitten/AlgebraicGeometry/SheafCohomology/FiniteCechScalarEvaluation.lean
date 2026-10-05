/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechScalarMap

/-!
# Evaluated scalar comparisons for finite Čech complexes

Evaluation on an open commutes with an additive coefficient functor. Applying
it to the augmented presheaf comparison gives a comparison of module complexes.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w
namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
variable {X : TopCat.{u}} {R : Type v} [Ring R] {T : Type w} [Ring T]

lemma evaluate_mapPresheafComplexFunctor_obj
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R) (W : Opens X) :
    (evaluatePresheafComplex ((mapPresheafComplexFunctor (X := X) H).obj F)).obj (op W) =
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((evaluatePresheafComplex F).obj (op W)) := by
  rfl

lemma evaluate_mapPresheafComplexFunctor_map
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    {F G : PresheafComplex X R} (f : F ⟶ G)
    (W : Opens X) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((evaluatePresheafComplexMap f).app (op W)) =
      (evaluatePresheafComplexMap
        ((mapPresheafComplexFunctor (X := X) H).map f)).app (op W) := by
  rfl

/-- Evaluation of the additive finite Čech comparison at an arbitrary open. -/
noncomputable def finiteCechScalarComparisonAt
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R)
    (U : List (Opens X)) (W : Opens X) :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((finiteCechComplex F U).obj (op W)) ≅
      (finiteCechComplex
        ((mapPresheafComplexFunctor (X := X) H).obj F) U).obj (op W) := by
  let E : PresheafComplex X T ⥤ CochainComplex (ModuleCat T) ℤ :=
    ((evaluation (Opens X)ᵒᵖ (ModuleCat T)).obj (op W)).mapHomologicalComplex
      (ComplexShape.up ℤ)
  exact E.mapIso
    (finiteCechScalarMapData (X := X) H F U).complexIso

/-- The evaluated scalar comparison preserves the finite Čech augmentation. -/
lemma finiteCechScalarComparisonAt_augmentation
    (H : ModuleCat R ⥤ ModuleCat T) [H.Additive]
    (F : PresheafComplex X R)
    (U : List (Opens X)) (W : Opens X) :
    (evaluatePresheafComplexMap
      ((mapPresheafComplexFunctor (X := X) H).map
        (finiteCechData F U).augmentation)).app (op W) ≫
      (finiteCechScalarComparisonAt (X := X) H F U W).hom =
    (evaluatePresheafComplexMap
      (finiteCechData ((mapPresheafComplexFunctor (X := X) H).obj F) U).augmentation).app
        (op W) := by
  let E : PresheafComplex X T ⥤ CochainComplex (ModuleCat T) ℤ :=
    ((evaluation (Opens X)ᵒᵖ (ModuleCat T)).obj (op W)).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let d := finiteCechScalarMapData (X := X) H F U
  have h := congrArg
    (fun f : (mapPresheafComplexFunctor (X := X) H).obj F ⟶
        (finiteCechData ((mapPresheafComplexFunctor (X := X) H).obj F) U).complex => E.map f)
    d.augmentation_natural
  rw [E.map_comp] at h
  simpa [evaluatePresheafComplexMap,
    finiteCechComplex,
    evaluatePresheafComplex,
    finiteCechScalarComparisonAt] using h

end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
