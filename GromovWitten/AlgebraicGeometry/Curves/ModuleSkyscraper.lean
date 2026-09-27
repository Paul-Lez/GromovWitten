/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleStalk
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Skyscraper presheaves of modules

This file equips Mathlib's additive-group-valued skyscraper presheaf with the
module structure obtained by evaluating coefficient sections at a germ.  The
underlying additive presheaf is kept literally equal to `skyscraperPresheaf`.
The restriction-map semilinearity law is exposed as a small characteristic
input, so later constructions can use the object without unfolding its
module structures.
-/

open CategoryTheory Limits Opposite TopologicalSpace
noncomputable section
universe u

attribute [local instance] Classical.propDecidable

namespace PresheafOfModules

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u}) (x : X)
  (M : ModuleCat.{u} (R.stalk x))

variable {K : Type u} [Semiring K] {A B : AddCommGrpCat.{u}} [Module K B]

@[instance_reducible]
private def castModule (e : A = B) : Module K A :=
  e.symm ▸ (inferInstance : Module K B)

private lemma castModule_smul (e : A = B) (r : K) (m : A) :
    letI := castModule (K := K) e
    (eqToHom e) (r • m) = r • (eqToHom e) m := by
  subst e
  rfl

/-- The additive presheaf underlying the skyscraper module at `x`. -/
abbrev skyscraperModuleUnderlying : X.Presheaf AddCommGrpCat.{u} :=
  skyscraperPresheaf x (AddCommGrpCat.of M)

/-- The module structure on the skyscraper value over an open. -/
@[instance_reducible]
def skyscraperModuleAt (U : (Opens X)ᵒᵖ) :
    Module (R.obj U) ((skyscraperModuleUnderlying R x M).obj U) := by
  by_cases h : x ∈ U.unop
  · let e : (skyscraperModuleUnderlying R x M).obj U = AddCommGrpCat.of M := if_pos h
    exact e.symm ▸ ((ModuleCat.restrictScalars (R.germ U.unop x h).hom).obj M).isModule
  · let e : (skyscraperModuleUnderlying R x M).obj U = ⊤_ AddCommGrpCat.{u} := if_neg h
    have hz : IsZero (⊤_ AddCommGrpCat.{u}) :=
      (isZero_zero AddCommGrpCat.{u}).of_iso HasZeroObject.zeroIsoTerminal.symm
    letI := AddCommGrpCat.subsingleton_of_isZero hz
    have hmodule : Module (R.obj U) (⊤_ AddCommGrpCat.{u}) :=
      { smul := fun _ _ => 0
        one_smul := fun _ => Subsingleton.elim _ _
        mul_smul := fun _ _ _ => Subsingleton.elim _ _
        smul_zero := fun _ => Subsingleton.elim _ _
        smul_add := fun _ _ _ => Subsingleton.elim _ _
        add_smul := fun _ _ _ => Subsingleton.elim _ _
        zero_smul := fun _ => Subsingleton.elim _ _ }
    exact e.symm ▸ hmodule

set_option backward.isDefEq.respectTransparency false in
lemma skyscraperModuleAt_eq (U : (Opens X)ᵒᵖ) (h : x ∈ U.unop) :
    skyscraperModuleAt R x M U =
      @castModule (R.obj U) _ ((skyscraperModuleUnderlying R x M).obj U)
        (AddCommGrpCat.of M)
        ((ModuleCat.restrictScalars (R.germ U.unop x h).hom).obj M).isModule (if_pos h) := by
  simp only [skyscraperModuleAt, dif_pos h, castModule]

set_option backward.isDefEq.respectTransparency false in
lemma skyscraperModuleAt_smul (U : (Opens X)ᵒᵖ) (h : x ∈ U.unop)
    (r : R.obj U) (m : (skyscraperModuleUnderlying R x M).obj U) :
    letI := skyscraperModuleAt R x M U
    (eqToHom (show (skyscraperModuleUnderlying R x M).obj U = AddCommGrpCat.of M
      from if_pos h)) (r • m) =
      R.germ U.unop x h r •
        (eqToHom (show (skyscraperModuleUnderlying R x M).obj U = AddCommGrpCat.of M
          from if_pos h)) m := by
  dsimp only
  simp +instances only [skyscraperModuleAt_eq R x M U h]
  exact @castModule_smul (R.obj U) _ ((skyscraperModuleUnderlying R x M).obj U)
    (AddCommGrpCat.of M)
    ((ModuleCat.restrictScalars (R.germ U.unop x h).hom).obj M).isModule (if_pos h) r m

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma skyscraperModule_map_smul ⦃U V : (Opens X)ᵒᵖ⦄ (f : U ⟶ V)
    (r : R.obj U) (m : (skyscraperModuleUnderlying R x M).obj U) :
    letI := skyscraperModuleAt R x M U
    letI := skyscraperModuleAt R x M V
    (skyscraperModuleUnderlying R x M).map f (r • m) =
      R.map f r • (skyscraperModuleUnderlying R x M).map f m := by
  let _ := skyscraperModuleAt R x M U
  let _ := skyscraperModuleAt R x M V
  by_cases hV : x ∈ V.unop
  · have hU : x ∈ U.unop := leOfHom f.unop hV
    let eU : (skyscraperModuleUnderlying R x M).obj U = AddCommGrpCat.of M := if_pos hU
    let eV : (skyscraperModuleUnderlying R x M).obj V = AddCommGrpCat.of M := if_pos hV
    apply (ConcreteCategory.bijective_of_isIso (eqToHom eV)).1
    rw [skyscraperModuleAt_smul R x M V hV]
    change ((skyscraperModuleUnderlying R x M).map f ≫ eqToHom eV) (r • m) =
      R.germ V.unop x hV (R.map f r) •
        ((skyscraperModuleUnderlying R x M).map f ≫ eqToHom eV) m
    have he : (skyscraperModuleUnderlying R x M).map f ≫ eqToHom eV = eqToHom eU := by
      simp [skyscraperModuleUnderlying, skyscraperPresheaf_map, hV]
    rw [he, skyscraperModuleAt_smul R x M U hU]
    congr 1
    exact (ConcreteCategory.congr_hom (R.germ_res f.unop x hV) r).symm
  · have hz : IsZero ((skyscraperModuleUnderlying R x M).obj V) := by
      rw [show (skyscraperModuleUnderlying R x M).obj V = ⊤_ AddCommGrpCat.{u} from if_neg hV]
      exact (isZero_zero AddCommGrpCat.{u}).of_iso HasZeroObject.zeroIsoTerminal.symm
    exact @Subsingleton.elim ((skyscraperModuleUnderlying R x M).obj V)
      (AddCommGrpCat.subsingleton_of_isZero hz) _ _

/-- The presheaf of modules carried by Mathlib's skyscraper presheaf. -/
noncomputable def skyscraperModule :
    PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) := by
  letI : ∀ U, Module ((R ⋙ forget₂ CommRingCat RingCat).obj U)
      ((skyscraperModuleUnderlying R x M).obj U) :=
    fun U ↦ skyscraperModuleAt R x M U
  exact PresheafOfModules.ofPresheaf (skyscraperModuleUnderlying R x M)
    (by
      intro U V f r m
      exact skyscraperModule_map_smul R x M f r m)

@[simp]
lemma skyscraperModule_presheaf :
    (skyscraperModule R x M).presheaf = skyscraperModuleUnderlying R x M := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The skyscraper construction sends a stalk-module hom to the induced module
hom of skyscraper presheaves. -/
noncomputable def skyscraperModuleMap {M N : ModuleCat.{u} (R.stalk x)}
    (f : M ⟶ N) : skyscraperModule R x M ⟶ skyscraperModule R x N :=
  PresheafOfModules.homMk
    ((skyscraperPresheafFunctor x).map
      ((forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map f)) (by
      intro U r m
      let _ : Module (R.stalk x) (N : Type u) := N.isModule
      by_cases h : x ∈ U.unop
      · let eM : (skyscraperModuleUnderlying R x M).obj U = AddCommGrpCat.of M := if_pos h
        let eN : (skyscraperModuleUnderlying R x N).obj U = AddCommGrpCat.of N := if_pos h
        apply (ConcreteCategory.bijective_of_isIso (eqToHom eN)).1
        erw [skyscraperModuleAt_smul R x N U h]
        simp only [skyscraperPresheafFunctor, SkyscraperPresheafFunctor.map'_app]
        erw [dif_pos h]
        change ((eqToHom eM ≫
            (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map f ≫
              eqToHom eN.symm) ≫ eqToHom eN) (r • m) =
          R.germ U.unop x h r •
            ((eqToHom eM ≫
              (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map f ≫
                eqToHom eN.symm) ≫ eqToHom eN) m
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
        change ((forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map f)
            (ConcreteCategory.hom (eqToHom eM) (r • m)) =
          R.germ U.unop x h r •
            ((forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map f)
              (ConcreteCategory.hom (eqToHom eM) m)
        erw [skyscraperModuleAt_smul R x M U h]
        exact f.hom'.map_smul (R.germ U.unop x h r)
          (ConcreteCategory.hom (eqToHom eM) m)
      · have hz : IsZero ((skyscraperModuleUnderlying R x N).obj U) := by
          rw [show (skyscraperModuleUnderlying R x N).obj U = ⊤_ AddCommGrpCat.{u} from if_neg h]
          exact (isZero_zero AddCommGrpCat.{u}).of_iso HasZeroObject.zeroIsoTerminal.symm
        exact @Subsingleton.elim ((skyscraperModuleUnderlying R x N).obj U)
          (AddCommGrpCat.subsingleton_of_isZero hz) _ _)

/-- The module-valued skyscraper construction is functorial in the stalk module. -/
noncomputable def skyscraperModuleFunctor :
    ModuleCat.{u} (R.stalk x) ⥤ PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) where
  obj M := skyscraperModule R x M
  map f := skyscraperModuleMap R x f
  map_id M := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    change (skyscraperPresheafFunctor x).map
        ((forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map (𝟙 M)) = 𝟙 _
    rw [(forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map_id]
    exact (skyscraperPresheafFunctor x).map_id _
  map_comp f g := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    change (skyscraperPresheafFunctor x).map
        ((forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map (f ≫ g)) =
      (skyscraperPresheafFunctor x).map
          ((forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map f) ≫
        (skyscraperPresheafFunctor x).map
          ((forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat).map g)
    rw [Functor.map_comp, Functor.map_comp]

/-- The module skyscraper is a sheaf of modules when the coefficient presheaf
is supplied as a sheaf of rings. -/
noncomputable def skyscraperModuleSheaf {𝓡 : X.Sheaf CommRingCat.{u}} (x : X)
    (M : ModuleCat.{u} (𝓡.presheaf.stalk x)) :
    SheafOfModules ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat)).obj 𝓡) :=
  { val := skyscraperModule 𝓡.presheaf x M
    isSheaf := by
      change Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (skyscraperModuleUnderlying 𝓡.presheaf x M)
      exact skyscraperPresheaf_isSheaf x (AddCommGrpCat.of M) }

/-- The sheaf-level skyscraper functor on modules over the coefficient stalk. -/
noncomputable def skyscraperModuleSheafFunctor {𝓡 : X.Sheaf CommRingCat.{u}} (x : X) :
    ModuleCat.{u} (𝓡.presheaf.stalk x) ⥤
      SheafOfModules ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat)).obj 𝓡) where
  obj M := skyscraperModuleSheaf x M
  map f := { val := skyscraperModuleMap 𝓡.presheaf x f }
  map_id M := by
    apply SheafOfModules.hom_ext
    exact (skyscraperModuleFunctor 𝓡.presheaf x).map_id M
  map_comp f g := by
    apply SheafOfModules.hom_ext
    exact (skyscraperModuleFunctor 𝓡.presheaf x).map_comp f g

end PresheafOfModules
