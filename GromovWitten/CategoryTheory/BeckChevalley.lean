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

namespace CategoryTheory
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
 [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
 {F : B ⥤ A} {G : D ⥤ C} {L₀ L : A ⥤ C} {R₀ R : C ⥤ A}
 {P₀ P : B ⥤ D} {Q₀ Q : D ⥤ B}
 (ab₀ : L₀ ⊣ R₀) (ab : L ⊣ R) (ap₀ : P₀ ⊣ Q₀) (ap : P ⊣ Q)
/-- Precomposition by a map of left adjoints corresponds to postcomposition
by its conjugate map of right adjoints. -/
lemma homEquiv_precomp_conjugate (σ : L ⟶ L₀) {X : A} {Y : C}
    (f : L₀.obj X ⟶ Y) :
    ab.homEquiv _ _ (σ.app X ≫ f) =
      ab₀.homEquiv _ _ f ≫ (conjugateEquiv ab₀ ab σ).app Y := by
  rw [ab.homEquiv_unit, ab₀.homEquiv_unit, R.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv ab₀ ab σ]
  rw [Category.assoc, ← (conjugateEquiv ab₀ ab σ).naturality]
  simp only [Category.assoc]
/-- Unit formulas identify base-change maps after transporting both adjunctions
along conjugate transformations. -/
lemma baseChange_eq_of_unit_transport
    (σ : L ⟶ L₀) (τ : P ⟶ P₀)
    (ρ₀ : Q₀ ⋙ F ⟶ G ⋙ R₀) (ρ : Q ⋙ F ⟶ G ⋙ R)
    (hρ : ∀ N, ρ₀.app N ≫ (conjugateEquiv ab₀ ab σ).app (G.obj N) =
      F.map ((conjugateEquiv ap₀ ap τ).app N) ≫ ρ.app N)
    (M : B) (β₀ : L₀.obj (F.obj M) ⟶ G.obj (P₀.obj M))
    (β : L.obj (F.obj M) ⟶ G.obj (P.obj M))
    (hβ₀ : ab₀.homEquiv _ _ β₀ = F.map (ap₀.unit.app M) ≫ ρ₀.app (P₀.obj M))
    (hβ : ab.homEquiv _ _ β = F.map (ap.unit.app M) ≫ ρ.app (P.obj M)) :
    σ.app (F.obj M) ≫ β₀ = β ≫ G.map (τ.app M) := by
  apply (ab.homEquiv _ _).injective
  rw [homEquiv_precomp_conjugate, hβ₀, ab.homEquiv_naturality_right, hβ,
    Category.assoc, hρ, ← Category.assoc, ← F.map_comp,
    unit_conjugateEquiv ap₀ ap τ, F.map_comp, Category.assoc]
  have hn := ρ.naturality (τ.app M)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [Category.assoc]
end CategoryTheory

namespace CategoryTheory
universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  {E : Type u₅} {H : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  [Category.{v₅} E] [Category.{v₆} H]
  {F : B ⥤ A} {G : D ⥤ C} {K : H ⥤ E}
  {L : A ⥤ C} {R : C ⥤ A} {P : B ⥤ D} {Q : D ⥤ B}
  {L' : C ⥤ E} {R' : E ⥤ C} {P' : D ⥤ H} {Q' : H ⥤ D}
  (ab : L ⊣ R) (ap : P ⊣ Q) (ac : L' ⊣ R') (aq : P' ⊣ Q')
/-- The unit formula for a pasted base-change map is the composite of the
unit formulas for its two squares. -/
lemma baseChange_unit_pasting
    (ρ : Q ⋙ F ⟶ G ⋙ R) (ρ' : Q' ⋙ G ⟶ K ⋙ R') (M : B)
    (β : L.obj (F.obj M) ⟶ G.obj (P.obj M))
    (β' : L'.obj (G.obj (P.obj M)) ⟶ K.obj (P'.obj (P.obj M)))
    (hβ : ab.homEquiv _ _ β = F.map (ap.unit.app M) ≫ ρ.app (P.obj M))
    (hβ' : ac.homEquiv _ _ β' = G.map (aq.unit.app (P.obj M)) ≫
      ρ'.app (P'.obj (P.obj M))) :
    (ab.comp ac).homEquiv _ _ (L'.map β ≫ β') =
      F.map ((ap.comp aq).unit.app M) ≫
        ρ.app (Q'.obj (P'.obj (P.obj M))) ≫
          R.map (ρ'.app (P'.obj (P.obj M))) := by
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  rw [ac.homEquiv_naturality_left, hβ', ← Category.assoc,
    ab.homEquiv_naturality_right, ab.homEquiv_naturality_right, hβ]
  have hn := ρ.naturality (aq.unit.app (P.obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [Adjunction.comp_unit_app, F.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
end CategoryTheory

namespace CategoryTheory
universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  {E : Type u₅} {H : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  [Category.{v₅} E] [Category.{v₆} H]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : D ⥤ E} {G₂ : E ⥤ H}
  {L : C ⥤ H} {R : H ⥤ C} {P : B ⥤ E} {Q : E ⥤ B}
  {N : A ⥤ D} {O : D ⥤ A}
  (ab : L ⊣ R) (ap : P ⊣ Q) (an : N ⊣ O)
/-- The unit formula for base change is compatible with composition of the
vertical functors in two squares. -/
lemma baseChange_unit_vertical_pasting
    (ρ₁ : O ⋙ F₁ ⟶ G₁ ⋙ Q) (ρ₂ : Q ⋙ F₂ ⟶ G₂ ⋙ R) (M : A)
    (β₁ : P.obj (F₁.obj M) ⟶ G₁.obj (N.obj M))
    (β₂ : L.obj (F₂.obj (F₁.obj M)) ⟶ G₂.obj (P.obj (F₁.obj M)))
    (hβ₁ : ap.homEquiv _ _ β₁ = F₁.map (an.unit.app M) ≫ ρ₁.app (N.obj M))
    (hβ₂ : ab.homEquiv _ _ β₂ = F₂.map (ap.unit.app (F₁.obj M)) ≫
      ρ₂.app (P.obj (F₁.obj M))) :
    ab.homEquiv _ _ (β₂ ≫ G₂.map β₁) =
      (F₁ ⋙ F₂).map (an.unit.app M) ≫
        F₂.map (ρ₁.app (N.obj M)) ≫ ρ₂.app (G₁.obj (N.obj M)) := by
  rw [ab.homEquiv_naturality_right, hβ₂, Category.assoc]
  have hn := ρ₂.naturality β₁
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← F₂.map_comp]
  rw [ap.homEquiv_unit] at hβ₁
  rw [hβ₁, F₂.map_comp]
  simp only [Functor.comp_map, Category.assoc]
end CategoryTheory

namespace CategoryTheory
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
 [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
 {F₀ F : B ⥤ A} {G₀ G : D ⥤ C} {L : A ⥤ C} {R : C ⥤ A}
 {P : B ⥤ D} {Q : D ⥤ B} (ab : L ⊣ R) (ap : P ⊣ Q)
/-- Unit formulas identify base-change maps after transporting the
vertical functors in a square. -/
lemma baseChange_eq_of_functor_transport
    (ε : F₀ ⟶ F) (δ : G ⟶ G₀)
    (ρ₀ : Q ⋙ F₀ ⟶ G₀ ⋙ R) (ρ : Q ⋙ F ⟶ G ⋙ R)
    (hρ : ∀ N, ρ₀.app N = ε.app (Q.obj N) ≫ ρ.app N ≫ R.map (δ.app N))
    (M : B) (β₀ : L.obj (F₀.obj M) ⟶ G₀.obj (P.obj M))
    (β : L.obj (F.obj M) ⟶ G.obj (P.obj M))
    (hβ₀ : ab.homEquiv _ _ β₀ = F₀.map (ap.unit.app M) ≫ ρ₀.app (P.obj M))
    (hβ : ab.homEquiv _ _ β = F.map (ap.unit.app M) ≫ ρ.app (P.obj M)) :
    β₀ = L.map (ε.app M) ≫ β ≫ δ.app (P.obj M) := by
  apply (ab.homEquiv _ _).injective
  rw [hβ₀, ab.homEquiv_naturality_left, ab.homEquiv_naturality_right, hβ, hρ]
  simp only [← Category.assoc]
  have hn := ε.naturality (ap.unit.app M)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [hn]
end CategoryTheory
