/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.SnakeFunctor
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Functoriality of the connecting morphism

An additive functor preserving homology carries the connecting morphism of a short exact
homological-complex sequence to the connecting morphism after applying the functor.  The
comparison is expressed using the canonical homology isomorphisms in each degree.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open HomologicalComplex

namespace CategoryTheory.ShortComplex
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
set_option backward.isDefEq.respectTransparency false in
private lemma mapHomologyIso_hom_homologyπ :
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ =
      (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom := by
  rw [S.leftHomologyData.mapHomologyIso_eq F,
    S.leftHomologyData.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  change _ ≫ F.map _ ≫ F.map _ = _ ≫ F.map _ ≫ F.map _
  rw [← F.map_comp, ← F.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

set_option backward.isDefEq.respectTransparency false in
private lemma mapHomologyIso_hom_homologyι :
    (S.mapHomologyIso F).hom ≫ F.map S.homologyι =
      (S.map F).homologyι ≫ (S.mapOpcyclesIso F).hom := by
  rw [← S.mapHomologyIso'_eq_mapHomologyIso F,
    S.homologyData.right.mapHomologyIso'_eq F,
    S.homologyData.right.mapOpcyclesIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← F.map_comp, ShortComplex.RightHomologyData.homologyIso_inv_comp_homologyι]
  rw [F.map_comp]
  rw [← S.homologyData.right.map_ι F]
  change (S.homologyData.right.map F).homologyIso.hom ≫
      (S.homologyData.right.map F).ι ≫ F.map S.homologyData.right.opcyclesIso.inv =
    (S.map F).homologyι ≫ (S.homologyData.right.map F).opcyclesIso.hom ≫
      F.map S.homologyData.right.opcyclesIso.inv
  rw [ShortComplex.RightHomologyData.homologyIso_hom_comp_ι_assoc]

end CategoryTheory.ShortComplex

namespace HomologicalComplex.HomologySequence
variable {C D ι : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {c : ComplexShape ι} (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (S : ShortComplex (HomologicalComplex C c))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homologyRowMap (i : ι) :
    (homologyFunctor D c i).mapShortComplex.obj (S.map (F.mapHomologicalComplex c)) ⟶
      ((homologyFunctor C c i).mapShortComplex.obj S).map F where
  τ₁ := ((S.X₁.sc i).mapHomologyIso F).hom
  τ₂ := ((S.X₂.sc i).mapHomologyIso F).hom
  τ₃ := ((S.X₃.sc i).mapHomologyIso F).hom
  comm₁₂ := (ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor C c i).map S.f) F).symm
  comm₂₃ := (ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor C c i).map S.g) F).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def opcyclesRowMap (i : ι) :
    (opcyclesFunctor D c i).mapShortComplex.obj (S.map (F.mapHomologicalComplex c)) ⟶
      ((opcyclesFunctor C c i).mapShortComplex.obj S).map F where
  τ₁ := ((S.X₁.sc i).mapOpcyclesIso F).hom
  τ₂ := ((S.X₂.sc i).mapOpcyclesIso F).hom
  τ₃ := ((S.X₃.sc i).mapOpcyclesIso F).hom
  comm₁₂ := (ShortComplex.mapOpcyclesIso_hom_naturality
    ((shortComplexFunctor C c i).map S.f) F).symm
  comm₂₃ := (ShortComplex.mapOpcyclesIso_hom_naturality
    ((shortComplexFunctor C c i).map S.g) F).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def cyclesRowMap (i : ι) :
    (cyclesFunctor D c i).mapShortComplex.obj (S.map (F.mapHomologicalComplex c)) ⟶
      ((cyclesFunctor C c i).mapShortComplex.obj S).map F where
  τ₁ := ((S.X₁.sc i).mapCyclesIso F).hom
  τ₂ := ((S.X₂.sc i).mapCyclesIso F).hom
  τ₃ := ((S.X₃.sc i).mapCyclesIso F).hom
  comm₁₂ := (ShortComplex.mapCyclesIso_hom_naturality
    ((shortComplexFunctor C c i).map S.f) F).symm
  comm₂₃ := (ShortComplex.mapCyclesIso_hom_naturality
    ((shortComplexFunctor C c i).map S.g) F).symm

variable (K : HomologicalComplex C c) (i j : ι)

set_option backward.isDefEq.respectTransparency false in
private lemma opcyclesComparison_p :
    ((F.mapHomologicalComplex c).obj K).pOpcycles i ≫
      ((K.sc i).mapOpcyclesIso F).hom = F.map (K.pOpcycles i) := by
  exact ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom
    ((K.sc i).rightHomologyData.map F)

set_option backward.isDefEq.respectTransparency false in
private lemma opcyclesToCycles_map :
    ((K.sc i).mapOpcyclesIso F).hom ≫ F.map (K.opcyclesToCycles i j) =
      ((F.mapHomologicalComplex c).obj K).opcyclesToCycles i j ≫
        ((K.sc j).mapCyclesIso F).hom := by
  let L := (F.mapHomologicalComplex c).obj K
  apply (cancel_epi (L.pOpcycles i)).mp
  apply (cancel_mono (F.map (K.iCycles j))).mp
  simp only [Category.assoc]
  rw [← Category.assoc (L.pOpcycles i), opcyclesComparison_p]
  rw [← F.map_comp, ← F.map_comp, K.pOpcycles_opcyclesToCycles_iCycles]
  have hc : ((K.sc j).mapCyclesIso F).hom ≫ F.map (K.iCycles j) =
      L.iCycles j := ShortComplex.mapCyclesIso_hom_iCycles (K.sc j) F
  rw [hc]
  exact (L.pOpcycles_opcyclesToCycles_iCycles i j).symm
end HomologicalComplex.HomologySequence

namespace HomologicalComplex.HomologySequence
variable {C D ι : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {c : ComplexShape ι} (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (hSF : (S.map (F.mapHomologicalComplex c)).ShortExact) (i j : ι) (hij : c.Rel i j)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def snakeInputComparison :
    snakeInput hSF i j hij ⟶ (snakeInput hS i j hij).mapExact F where
  f₀ := homologyRowMap F S i
  f₁ := opcyclesRowMap F S i
  f₂ := cyclesRowMap F S j
  f₃ := homologyRowMap F S j
  comm₀₁ := by
    ext
    all_goals exact ShortComplex.mapHomologyIso_hom_homologyι _ F
  comm₁₂ := by
    ext
    all_goals exact opcyclesToCycles_map F _ i j
  comm₂₃ := by
    ext
    all_goals exact ShortComplex.mapHomologyIso_hom_homologyπ _ F

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison square for the connecting morphism. -/
lemma map_δ :
    hSF.δ i j hij ≫ ((S.X₁.sc j).mapHomologyIso F).hom =
      ((S.X₃.sc i).mapHomologyIso F).hom ≫ F.map (hS.δ i j hij) := by
  have h := ShortComplex.SnakeInput.naturality_δ (snakeInputComparison F hS hSF i j hij)
  change hSF.δ i j hij ≫ ((S.X₁.sc j).mapHomologyIso F).hom =
      ((S.X₃.sc i).mapHomologyIso F).hom ≫ ((snakeInput hS i j hij).mapExact F).δ at h
  rw [← ShortComplex.SnakeInput.mapExact_δ] at h
  exact h

end HomologicalComplex.HomologySequence
