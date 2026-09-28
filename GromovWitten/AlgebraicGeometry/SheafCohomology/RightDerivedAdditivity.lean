/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedHomology
/-! # Additivity of the right-derived map on natural transformations -/

open CategoryTheory CategoryTheory.Abelian
noncomputable section
universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-! Right-derived functors inherit additivity from the injective-resolution construction. -/
noncomputable instance rightDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).Additive := by
  constructor
  intro Y Z f g
  let I := injectiveResolution Y
  let J := injectiveResolution Z
  let φf := InjectiveResolution.desc f J I
  let φg := InjectiveResolution.desc g J I
  let φsum := InjectiveResolution.desc (f + g) J I
  have wf : I.ι ≫ φf = (CochainComplex.single₀ C).map f ≫ J.ι :=
    InjectiveResolution.desc_commutes f J I
  have wg : I.ι ≫ φg = (CochainComplex.single₀ C).map g ≫ J.ι :=
    InjectiveResolution.desc_commutes g J I
  have wsum : I.ι ≫ φsum = (CochainComplex.single₀ C).map (f + g) ≫ J.ι :=
    InjectiveResolution.desc_commutes (f + g) J I
  have hφ : Homotopy φsum (φf + φg) := by
    apply InjectiveResolution.descHomotopy (f + g)
    · exact wsum
    · simp only [Preadditive.comp_add, wf, wg, Functor.map_add, Preadditive.add_comp]
  have hh'' := (F.mapHomotopy hφ).homologyMap_eq n
  rw [Functor.map_add] at hh''
  rw [HomologicalComplex.homologyMap_add] at hh''
  have hsum := I.rightDerived_map_eq_homologyMap J (f + g) φsum wsum F n
  have hf := I.rightDerived_map_eq_homologyMap J f φf wf F n
  have hg := I.rightDerived_map_eq_homologyMap J g φg wg F n
  rw [hsum, hf, hg]
  rw [hh'']
  rw [← Category.assoc, Preadditive.comp_add, Preadditive.add_comp]
  simp only [Category.assoc]
end CategoryTheory.Functor

namespace CategoryTheory.NatTrans
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
set_option backward.isDefEq.respectTransparency false in
/-- Right derivation preserves addition of natural transformations. -/
@[simp]
lemma rightDerived_add (α β : F ⟶ G) (n : ℕ) :
    rightDerived (α + β) n = rightDerived α n + rightDerived β n := by
  ext X
  let I := InjectiveResolution.of X
  rw [I.rightDerived_app_eq (α + β) n]
  change _ = (rightDerived α n).app X + (rightDerived β n).app X
  rw [I.rightDerived_app_eq α n, I.rightDerived_app_eq β n]
  have h : (mapHomologicalComplex (α + β) (.up ℕ)).app I.cocomplex =
      (mapHomologicalComplex α (.up ℕ)).app I.cocomplex +
      (mapHomologicalComplex β (.up ℕ)).app I.cocomplex := by
    ext i
    rfl
  rw [h, Functor.map_add]
  simp only [Preadditive.comp_add, Preadditive.add_comp]
set_option backward.isDefEq.respectTransparency false in
/-- Right derivation sends the zero natural transformation to zero. -/
@[simp]
lemma rightDerived_zero (n : ℕ) : rightDerived (0 : F ⟶ G) n = 0 := by
  have h := rightDerived_add (0 : F ⟶ G) 0 n
  simp only [zero_add] at h
  have hh : rightDerived (0 : F ⟶ G) n + 0 =
      rightDerived (0 : F ⟶ G) n + rightDerived (0 : F ⟶ G) n := by
    simpa only [add_zero] using h
  exact (add_left_cancel hh).symm
end CategoryTheory.NatTrans
