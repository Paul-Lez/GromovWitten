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
