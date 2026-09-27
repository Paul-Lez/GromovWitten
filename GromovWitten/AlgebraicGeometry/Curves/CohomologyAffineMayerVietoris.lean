/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris

/-!
# Derived sections in a two-open Mayer–Vietoris cover

The maps below are the maps induced on actual right-derived sections by the
restriction difference sequence.  The exactness theorem is obtained from the
short exact sequence of section complexes on an injective resolution; it does
not assume an exact sequence for derived sections.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open TopologicalSpace Opposite
open GromovWitten.AlgebraicGeometry.SheafCohomology
open CochainComplex

noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves

variable {X : TopCat.{u}}

private lemma sectionsToPairNat_comp_zero (U V : Opens X) :
    sectionsToPairNat U V ≫ sectionsFromPairNat U V = 0 := by
  apply NatTrans.ext
  funext F
  exact sectionsToPair_fromPair F U V

/-- The canonical derived map from sections on a union to the pair of sections. -/
noncomputable def mvRightDerivedToPair
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    ((sections (U ⊔ V)).rightDerived n).obj F ⟶
      ((sectionsPairFunctor U V).rightDerived n).obj F :=
  (NatTrans.rightDerived (sectionsToPairNat U V) n).app F

/-- The canonical derived restriction-difference map to an intersection. -/
noncomputable def mvRightDerivedFromPair
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    ((sectionsPairFunctor U V).rightDerived n).obj F ⟶
      ((sections (U ⊓ V)).rightDerived n).obj F :=
  (NatTrans.rightDerived (sectionsFromPairNat U V) n).app F

/-- Consecutive maps in the derived Mayer–Vietoris sequence compose to zero. -/
lemma mvRightDerivedToPair_comp_mvRightDerivedFromPair
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (U V : Opens X) (n : ℕ) :
    mvRightDerivedToPair (F := F) U V n ≫
      mvRightDerivedFromPair (F := F) U V n = 0 := by
  change ((NatTrans.rightDerived (sectionsToPairNat U V) n ≫
    NatTrans.rightDerived (sectionsFromPairNat U V) n).app F) = 0
  rw [← NatTrans.rightDerived_comp, sectionsToPairNat_comp_zero]
  let I := InjectiveResolution.of F
  rw [InjectiveResolution.rightDerived_app_eq (P := I)]
  have hz := (show
      (NatTrans.mapHomologicalComplex
        (0 : sections (U ⊔ V) ⟶ sections (U ⊓ V)) (.up ℕ)).app
        I.cocomplex = 0 by
      ext i
      rfl)
  simp only [hz, Functor.map_zero, zero_comp, comp_zero]

/-- Degreewise exactness of the actual derived Mayer–Vietoris sequence.

The pair term is the product of derived sections on the two opens, and its
map to the intersection is the difference of the two restriction maps. -/
theorem mvRightDerived_exact
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U V : Opens X) (n : ℕ) :
    (ShortComplex.mk (mvRightDerivedToPair (F := F) U V n)
      (mvRightDerivedFromPair (F := F) U V n)
      (mvRightDerivedToPair_comp_mvRightDerivedFromPair (F := F) U V n)).Exact := by
  let S := sectionsComplexMV I.cocomplex U V
  let hS := sectionsComplexMV_shortExact I.cocomplex
    (fun k => TopCat.Sheaf.isFlasque_of_injective X _) U V
  let f :=
    (NatTrans.mapHomologicalComplex (sectionsToPairNat U V) (.up ℕ)).app
      I.cocomplex
  let g :=
    (NatTrans.mapHomologicalComplex (sectionsFromPairNat U V) (.up ℕ)).app
      I.cocomplex
  let Hfun := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
  have hfg : f ≫ g = 0 := by
    change ((NatTrans.mapHomologicalComplex (sectionsToPairNat U V) (.up ℕ) ≫
      NatTrans.mapHomologicalComplex (sectionsFromPairNat U V) (.up ℕ)).app
        I.cocomplex) = 0
    rw [← NatTrans.mapHomologicalComplex_comp,
      sectionsToPairNat_comp_zero]
    rfl
  have htemp := hS.homology_exact₂ n
  dsimp [sectionsComplexMV] at htemp
  let hLocal :
      (ShortComplex.mk (HomologicalComplex.homologyMap f n)
        (HomologicalComplex.homologyMap g n) (by
          rw [← HomologicalComplex.homologyMap_comp, hfg,
            HomologicalComplex.homologyMap_zero])).Exact := by
    simpa [S, f, g] using htemp
  let A :=
    ((sections (U ⊔ V)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let B :=
    ((sectionsPairFunctor U V).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let C :=
    ((sections (U ⊓ V)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let eA : Hfun.obj A ≅ A.homology n :=
    eqToIso (HomologicalComplex.homologyFunctor_obj
      AddCommGrpCat (.up ℕ) n A)
  let eB : Hfun.obj B ≅ B.homology n :=
    eqToIso (HomologicalComplex.homologyFunctor_obj
      AddCommGrpCat (.up ℕ) n B)
  let eC : Hfun.obj C ≅ C.homology n :=
    eqToIso (HomologicalComplex.homologyFunctor_obj
      AddCommGrpCat (.up ℕ) n C)
  let Hlocal :=
    ShortComplex.mk (HomologicalComplex.homologyMap f n)
      (HomologicalComplex.homologyMap g n) (by
        rw [← HomologicalComplex.homologyMap_comp, hfg,
          HomologicalComplex.homologyMap_zero])
  let HfunC := ShortComplex.mk (Hfun.map f) (Hfun.map g) (by
    rw [← Hfun.map_comp, hfg, Functor.map_zero])
  let E : Hlocal ≅ HfunC := ShortComplex.isoMk eA.symm eB.symm eC.symm
    (by
      dsimp [eA, eB, Hfun]
      cases HomologicalComplex.homologyFunctor_obj
        AddCommGrpCat (.up ℕ) n A
      cases HomologicalComplex.homologyFunctor_obj
        AddCommGrpCat (.up ℕ) n B
      rfl)
    (by
      dsimp [eB, eC, Hfun]
      cases HomologicalComplex.homologyFunctor_obj
        AddCommGrpCat (.up ℕ) n B
      cases HomologicalComplex.homologyFunctor_obj
        AddCommGrpCat (.up ℕ) n C
      rfl)
  let hFun : HfunC.Exact := ShortComplex.exact_of_iso E.symm hLocal
  let e₁ := I.isoRightDerivedObj (sections (U ⊔ V)) n
  let e₂ := I.isoRightDerivedObj (sectionsPairFunctor U V) n
  let e₃ := I.isoRightDerivedObj (sections (U ⊓ V)) n
  let R := ShortComplex.mk (mvRightDerivedToPair (F := F) U V n)
    (mvRightDerivedFromPair (F := F) U V n)
    (mvRightDerivedToPair_comp_mvRightDerivedFromPair (F := F) U V n)
  let e : R ≅ HfunC := ShortComplex.isoMk e₁ e₂ e₃
    (by
      change e₁.hom ≫ Hfun.map f =
        (NatTrans.rightDerived (sectionsToPairNat U V) n).app F ≫ e₂.hom
      rw [InjectiveResolution.rightDerived_app_eq (P := I)]
      change e₁.hom ≫ Hfun.map f =
        e₁.hom ≫ Hfun.map f ≫ e₂.inv ≫ e₂.hom
      simp)
    (by
      change e₂.hom ≫ Hfun.map g =
        (NatTrans.rightDerived (sectionsFromPairNat U V) n).app F ≫ e₃.hom
      rw [InjectiveResolution.rightDerived_app_eq (P := I)]
      change e₂.hom ≫ Hfun.map g =
        e₂.hom ≫ Hfun.map g ≫ e₃.inv ≫ e₃.hom
      simp)
  exact ShortComplex.exact_of_iso e.symm hFun

end GromovWitten.AlgebraicGeometry.Curves
