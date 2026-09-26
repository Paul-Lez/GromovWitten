/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.ProjectiveBaseChange

/-!
# Scalar extension on projective-perfect derived modules

Termwise extension of scalars is functorial on bounded finite-projective representatives.  The
K-projective lifting theorem makes this into an actual functor on the full subcategory of derived
objects admitting such representatives: the map attached to a derived morphism is independent of
the chosen chain-map lift because scalar extension carries homotopies to homotopies.

This construction is intentionally restricted to projective-perfect objects.  It does not define
an underived tensor functor on the whole derived category.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

section ScalarExtension

attribute [local instance] HasDerivedCategory.standard

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Scalar extension does not distinguish chain maps out of a bounded finite-projective complex
which have the same image in the derived category. -/
theorem Q_map_baseChange_map_congr
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    {φ ψ : K ⟶ L} (h : DerivedCategory.Q.map φ = DerivedCategory.Q.map ψ) :
    DerivedCategory.Q.map ((Modules.Derived.baseChangeFunctor f).map φ) =
      DerivedCategory.Q.map ((Modules.Derived.baseChangeFunctor f).map ψ) := by
  have _ := hK.isKProjective
  have key : ∀ χ : K ⟶ L,
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map χ) =
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app K ≫
          DerivedCategory.Q.map χ ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app L := by
    intro χ
    have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality χ
    rw [Functor.comp_map] at hnat
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hq :
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ =
        (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map ψ := by
    refine (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L)).injective ?_
    rw [key φ, key ψ, h]
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} S)
    (Functor.mapHomotopy (ModuleCat.extendScalars f)
      (HomotopyCategory.homotopyOfEq _ _ hq))

/-- A chosen chain-map lift of a morphism between projective-perfect derived objects. -/
noncomputable def projectiveDerivedChainMap
    {E F : DerivedCategory (ModuleCat.{u} R)}
    (hE : IsProjectivePerfect E) (hF : IsProjectivePerfect F)
    (u : E ⟶ F) : hE.rep ⟶ hF.rep :=
  (exists_chainMap_of_projectiveDerivedMap hE.rep_isStrictlyProjective
    (hE.repIso.hom ≫ u ≫ hF.repIso.inv)).choose

@[simp]
theorem Q_map_projectiveDerivedChainMap
    {E F : DerivedCategory (ModuleCat.{u} R)}
    (hE : IsProjectivePerfect E) (hF : IsProjectivePerfect F)
    (u : E ⟶ F) :
    DerivedCategory.Q.map (projectiveDerivedChainMap hE hF u) =
      hE.repIso.hom ≫ u ≫ hF.repIso.inv :=
  (exists_chainMap_of_projectiveDerivedMap hE.rep_isStrictlyProjective
    (hE.repIso.hom ≫ u ≫ hF.repIso.inv)).choose_spec

/-- The object property of projective-perfect derived modules. -/
abbrev projectivePerfectObjects :
    ObjectProperty (DerivedCategory (ModuleCat.{u} R)) := IsProjectivePerfect

/-- Scalar extension on projective-perfect derived modules, as a functor between full
subcategories. -/
noncomputable def projectivePerfectBaseChangeFunctor :
    (projectivePerfectObjects (R := R)).FullSubcategory ⥤
      (projectivePerfectObjects (R := S)).FullSubcategory where
  obj E := ⟨IsProjectivePerfect.derivedBaseChange f E.property,
    IsProjectivePerfect.derivedBaseChange_isProjectivePerfect f E.property⟩
  map {E F} u := ObjectProperty.homMk
    (DerivedCategory.Q.map ((Modules.Derived.baseChangeFunctor f).map
      (projectiveDerivedChainMap E.property F.property u.hom)))
  map_id E := by
    apply ObjectProperty.hom_ext
    let φ := projectiveDerivedChainMap E.property E.property (𝟙 E.obj)
    have hφ : DerivedCategory.Q.map φ = DerivedCategory.Q.map (𝟙 E.property.rep) := by
      rw [Q_map_projectiveDerivedChainMap]
      simp
    change DerivedCategory.Q.map ((Modules.Derived.baseChangeFunctor f).map φ) =
      𝟙 (DerivedCategory.Q.obj ((Modules.Derived.baseChangeFunctor f).obj E.property.rep))
    exact Q_map_baseChange_map_congr f E.property.rep_isStrictlyProjective hφ |>.trans (by simp)
  map_comp {E F G} u v := by
    apply ObjectProperty.hom_ext
    let φ := projectiveDerivedChainMap E.property G.property (u ≫ v).hom
    let ψ := projectiveDerivedChainMap E.property F.property u.hom ≫
      projectiveDerivedChainMap F.property G.property v.hom
    have hφψ : DerivedCategory.Q.map φ = DerivedCategory.Q.map ψ := by
      rw [Q_map_projectiveDerivedChainMap, Functor.map_comp,
        Q_map_projectiveDerivedChainMap, Q_map_projectiveDerivedChainMap]
      simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, Iso.inv_hom_id_assoc]
    change DerivedCategory.Q.map ((Modules.Derived.baseChangeFunctor f).map φ) =
      DerivedCategory.Q.map ((Modules.Derived.baseChangeFunctor f).map
        (projectiveDerivedChainMap E.property F.property u.hom)) ≫
        DerivedCategory.Q.map ((Modules.Derived.baseChangeFunctor f).map
          (projectiveDerivedChainMap F.property G.property v.hom))
    rw [Q_map_baseChange_map_congr f E.property.rep_isStrictlyProjective hφψ]
    dsimp [ψ]
    rw [Functor.map_comp, Functor.map_comp]

end ScalarExtension

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
