/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
/-!
# The two descriptions of a Beck--Chevalley mate

A square of left adjoints induces a base-change morphism by using a counit and
then one adjunction. Its adjoint through the other side is the corresponding
unit followed by the conjugate square of right adjoints.
-/

open CategoryTheory
namespace CategoryTheory
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lb : A ⥤ C} {Rb : C ⥤ A}
  {Lp : B ⥤ D} {Rp : D ⥤ B} {Lg : C ⥤ D} {Rg : D ⥤ C}
  (af : Lf ⊣ Rf) (ab : Lb ⊣ Rb) (ap : Lp ⊣ Rp) (ag : Lg ⊣ Rg)
/-- The counit and unit constructions of a Beck--Chevalley mate agree. -/
lemma beckChevalley_unit_formula (σ : Lb ⋙ Lg ⟶ Lf ⋙ Lp) (M : B) :
    ab.homEquiv _ _ (ag.homEquiv _ _
      (σ.app (Rf.obj M) ≫ Lp.map (af.counit.app M))) =
    Rf.map (ap.unit.app M) ≫
      (conjugateEquiv (af.comp ap) (ab.comp ag) σ).app (Lp.obj M) := by
  let ρ := conjugateEquiv (af.comp ap) (ab.comp ag) σ
  change _ = Rf.map (ap.unit.app M) ≫ ρ.app _
  suffices h : (ab.comp ag).homEquiv _ _
      (σ.app (Rf.obj M) ≫ Lp.map (af.counit.app M)) =
      Rf.map (ap.unit.app M) ≫ ρ.app (Lp.obj M) by
    simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply] using h
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← unit_conjugateEquiv (af.comp ap) (ab.comp ag) σ]
  change ((af.comp ap).unit.app (Rf.obj M) ≫ ρ.app _) ≫
    (Rg ⋙ Rb).map (Lp.map (af.counit.app M)) = _
  rw [Category.assoc, ← ρ.naturality, ← Category.assoc, Adjunction.comp_unit_app]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  have hnat := ap.unit.naturality (af.counit.app M)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hnat
  rw [← hnat]
  simp only [Functor.map_comp, ← Category.assoc, af.right_triangle_components]
  simp only [Functor.id_obj, Category.id_comp]
end CategoryTheory

namespace CategoryTheory.Adjunction
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
 [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
 {L : A ⥤ B} {R : B ⥤ A} {P : B ⥤ C} {Q : C ⥤ B}
 (a : L ⊣ R) (b : P ⊣ Q)
/-- Transposing the image of the first counit through a composite adjunction
gives the image of the second unit. -/
lemma comp_homEquiv_map_counit (M : B) :
    (a.comp b).homEquiv _ _ (P.map (a.counit.app M)) = R.map (b.unit.app M) := by
  rw [comp_homEquiv]
  simp only [Equiv.trans_apply, homEquiv_unit]
  have h := b.unit.naturality (a.counit.app M)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h
  rw [← h]
  simp only [Functor.map_comp, ← Category.assoc, a.right_triangle_components]
  simp only [Category.id_comp]
end CategoryTheory.Adjunction

namespace CategoryTheory
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
 [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
 {F : B ⥤ A} {G : D ⥤ C} {L L' : A ⥤ C} {R : C ⥤ A}
 {P P' : B ⥤ D} {Q : D ⥤ B}
 (ab : L ⊣ R) (ab' : L' ⊣ R) (ap : P ⊣ Q) (ap' : P' ⊣ Q)
/-- The unit formula for a base-change map is preserved by the canonical
comparison between two choices of left adjoints. -/
lemma baseChange_unit_leftAdjointUniq (ρ : Q ⋙ F ⟶ G ⋙ R) (M : B)
    (β' : L'.obj (F.obj M) ⟶ G.obj (P'.obj M))
    (h : ab'.homEquiv _ _ β' = F.map (ap'.unit.app M) ≫ ρ.app (P'.obj M)) :
    ab.homEquiv _ _ ((ab'.leftAdjointUniq ab).inv.app (F.obj M) ≫ β' ≫
      G.map ((ap'.leftAdjointUniq ap).hom.app M)) =
      F.map (ap.unit.app M) ≫ ρ.app (P.obj M) := by
  have hx : ab.homEquiv _ _ ((ab'.leftAdjointUniq ab).inv.app (F.obj M) ≫ β') =
      ab'.homEquiv _ _ β' := by
    rw [ab.homEquiv_naturality_right, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ab'.homEquiv_unit]
  rw [← Category.assoc, ab.homEquiv_naturality_right, hx, h]
  have hρ := ρ.naturality ((ap'.leftAdjointUniq ap).hom.app M)
  dsimp only [Functor.comp_map] at hρ
  rw [Category.assoc, ← hρ, ← Category.assoc, ← F.map_comp,
    Adjunction.unit_leftAdjointUniq_hom_app]
end CategoryTheory
