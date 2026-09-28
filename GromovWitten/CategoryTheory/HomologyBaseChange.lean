/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Functor

/-!
# Homology comparison for right exact functors

A functor preserving zero morphisms sends cycles to cycles. If it also preserves finite
colimits, this induces the canonical map `F(H(S)) ⟶ H(F(S))`. In particular, extension of
scalars gives a homology base-change map without a flatness assumption on the algebra.

The comparison is natural in the complex and compatible with composition of functors.
If the functor preserves the kernel of the outgoing differential, it agrees with the
inverse of Mathlib's homology isomorphism. Thus the last nonzero degree always commutes
with a right exact functor. These are algebraic comparisons of actual complex homology;
identifying a complex with geometric cohomology requires a separate comparison theorem.
-/

open CategoryTheory Limits
noncomputable section
namespace CategoryTheory.ShortComplex
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The canonical map from the image of cycles to the cycles of the image complex. -/
def cyclesComparison : F.obj S.cycles ⟶ (S.map F).cycles :=
  (S.map F).liftCycles (F.map S.iCycles) (by
    change F.map S.iCycles ≫ F.map S.g = 0
    rw [← F.map_comp, S.iCycles_g, F.map_zero])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma cyclesComparison_iCycles : S.cyclesComparison F ≫ (S.map F).iCycles =
    F.map S.iCycles := by
  simp [cyclesComparison]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma map_toCycles_cyclesComparison :
    F.map S.toCycles ≫ S.cyclesComparison F = (S.map F).toCycles := by
  apply (S.map F).cycles_ext
  simp only [Category.assoc, cyclesComparison_iCycles, ← F.map_comp, toCycles_i, map_f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma cyclesComparison_naturality {T : ShortComplex C} (φ : S ⟶ T) :
    F.map (cyclesMap φ) ≫ T.cyclesComparison F =
      S.cyclesComparison F ≫ cyclesMap (F.mapShortComplex.map φ) := by
  apply (T.map F).cycles_ext
  change (F.map (cyclesMap φ) ≫ T.cyclesComparison F) ≫ (T.map F).iCycles =
    (S.cyclesComparison F ≫ cyclesMap (F.mapShortComplex.map φ)) ≫
      (F.mapShortComplex.obj T).iCycles
  rw [Category.assoc, cyclesComparison_iCycles, ← F.map_comp, cyclesMap_i,
    Category.assoc, cyclesMap_i]
  change F.map (S.iCycles ≫ φ.τ₂) =
    S.cyclesComparison F ≫ (S.map F).iCycles ≫ F.map φ.τ₂
  rw [← Category.assoc, cyclesComparison_iCycles, F.map_comp]

variable [PreservesFiniteColimits F]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical homology comparison for a right exact functor. -/
def homologyComparison : F.obj S.homology ⟶ (S.map F).homology :=
  (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F).desc
    (CokernelCofork.ofπ (S.cyclesComparison F ≫ (S.map F).homologyπ) (by
      rw [← Category.assoc, map_toCycles_cyclesComparison, toCycles_comp_homologyπ]))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma map_homologyπ_homologyComparison :
    F.map S.homologyπ ≫ S.homologyComparison F =
      S.cyclesComparison F ≫ (S.map F).homologyπ :=
  Cofork.IsColimit.π_desc (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homologyComparison_naturality {T : ShortComplex C} (φ : S ⟶ T) :
    F.map (homologyMap φ) ≫ T.homologyComparison F =
      S.homologyComparison F ≫ homologyMap (F.mapShortComplex.map φ) := by
  apply (cancel_epi (F.map S.homologyπ)).mp
  simp only [← Category.assoc, ← F.map_comp, homologyπ_naturality]
  simp only [F.map_comp, Category.assoc, map_homologyπ_homologyComparison,
    homologyπ_naturality, ← cyclesComparison_naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Compute the canonical comparison using any preserved left homology data. -/
lemma homologyComparison_eq (h : S.LeftHomologyData) [h.IsPreservedBy F] :
    S.homologyComparison F =
      F.map h.homologyIso.hom ≫ (h.map F).homologyIso.inv := by
  have hc : S.cyclesComparison F =
      F.map h.cyclesIso.hom ≫ (h.map F).cyclesIso.inv := by
    apply (S.map F).cycles_ext
    rw [cyclesComparison_iCycles, Category.assoc,
      LeftHomologyData.cyclesIso_inv_comp_iCycles]
    change F.map S.iCycles = F.map h.cyclesIso.hom ≫ F.map h.i
    rw [← F.map_comp, LeftHomologyData.cyclesIso_hom_comp_i]
  apply (cancel_epi (F.map S.homologyπ)).mp
  rw [map_homologyπ_homologyComparison, ← Category.assoc, ← F.map_comp,
    LeftHomologyData.homologyπ_comp_homologyIso_hom, F.map_comp, Category.assoc]
  change S.cyclesComparison F ≫ (S.map F).homologyπ =
    F.map h.cyclesIso.hom ≫ (h.map F).π ≫ (h.map F).homologyIso.inv
  rw [LeftHomologyData.π_comp_homologyIso_inv, hc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Where homology is preserved, the comparison agrees with the canonical isomorphism. -/
lemma homologyComparison_eq_mapHomologyIso_inv [F.PreservesLeftHomologyOf S] :
    S.homologyComparison F = (S.mapHomologyIso F).inv := by
  rw [S.homologyComparison_eq F S.leftHomologyData,
    S.leftHomologyData.mapHomologyIso_eq F]
  rfl

/-- Preserving the kernel of the outgoing differential suffices for homology base change. -/
lemma isIso_homologyComparison_of_preservesKernel
    [PreservesLimit (parallelPair S.g 0) F] : IsIso (S.homologyComparison F) := by
  have : F.PreservesLeftHomologyOf S := ⟨fun _ => ⟨inferInstance, inferInstance⟩⟩
  rw [homologyComparison_eq_mapHomologyIso_inv]
  infer_instance

/-- Homology in the last nonzero degree commutes with any right exact functor. -/
lemma isIso_homologyComparison_of_g_eq_zero (hg : S.g = 0) :
    IsIso (S.homologyComparison F) := by
  have : PreservesLimit (parallelPair S.g 0) F := by rw [hg]; infer_instance
  exact S.isIso_homologyComparison_of_preservesKernel F

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma cyclesComparison_id : S.cyclesComparison (𝟭 C) = 𝟙 _ := by
  apply S.cycles_ext
  exact (S.cyclesComparison_iCycles (𝟭 C)).trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma homologyComparison_id : S.homologyComparison (𝟭 C) = 𝟙 _ := by
  apply (cancel_epi S.homologyπ).mp
  simpa using S.map_homologyπ_homologyComparison (𝟭 C)

variable {E : Type*} [Category E] [Abelian E] (G : D ⥤ E)
    [G.PreservesZeroMorphisms] [PreservesFiniteColimits G]

omit [PreservesFiniteColimits F] [PreservesFiniteColimits G] in
set_option backward.isDefEq.respectTransparency false in
lemma cyclesComparison_comp : S.cyclesComparison (F ⋙ G) =
    G.map (S.cyclesComparison F) ≫ (S.map F).cyclesComparison G := by
  apply (S.map (F ⋙ G)).cycles_ext
  change S.cyclesComparison (F ⋙ G) ≫ (S.map (F ⋙ G)).iCycles =
    (G.map (S.cyclesComparison F) ≫ (S.map F).cyclesComparison G) ≫
      ((S.map F).map G).iCycles
  rw [cyclesComparison_iCycles, Category.assoc, cyclesComparison_iCycles,
    ← G.map_comp, cyclesComparison_iCycles]
  rfl

attribute [local instance] comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
lemma homologyComparison_comp : S.homologyComparison (F ⋙ G) =
    G.map (S.homologyComparison F) ≫ (S.map F).homologyComparison G := by
  apply (cancel_epi ((F ⋙ G).map S.homologyπ)).mp
  change (F ⋙ G).map S.homologyπ ≫ S.homologyComparison (F ⋙ G) =
    G.map (F.map S.homologyπ) ≫
      G.map (S.homologyComparison F) ≫ (S.map F).homologyComparison G
  rw [map_homologyπ_homologyComparison, ← Category.assoc, ← G.map_comp,
    map_homologyπ_homologyComparison, G.map_comp, Category.assoc,
    map_homologyπ_homologyComparison, cyclesComparison_comp, Category.assoc]
  rfl

end CategoryTheory.ShortComplex

namespace HomologicalComplex
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] (i : ι)

/-- The canonical homology comparison in a fixed degree of a complex. -/
def homologyComparison :
    F.obj (K.homology i) ⟶ ((F.mapHomologicalComplex c).obj K).homology i :=
  (K.sc i).homologyComparison F

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homologyComparison_naturality {L : HomologicalComplex C c} (φ : K ⟶ L) :
    F.map (homologyMap φ i) ≫ L.homologyComparison F i =
      K.homologyComparison F i ≫
        homologyMap ((F.mapHomologicalComplex c).map φ) i :=
  (K.sc i).homologyComparison_naturality F ((shortComplexFunctor C c i).map φ)

/-- At a degree with zero outgoing differential, homology commutes with a right exact functor. -/
lemma isIso_homologyComparison_of_d_eq_zero (hd : K.d i (c.next i) = 0) :
    IsIso (K.homologyComparison F i) :=
  (K.sc i).isIso_homologyComparison_of_g_eq_zero F hd

end HomologicalComplex
