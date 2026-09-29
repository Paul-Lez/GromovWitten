/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris
import GromovWitten.AlgebraicGeometry.SheafCohomology.RightDerivedAdditivity
/-!
# The pair term in derived Mayer–Vietoris

The projections and inclusions split the pair-of-sections functor. Right derivation preserves
these identities, giving an isomorphism with the biproduct of the two derived section groups.
The isomorphism uses the actual derived projection and inclusion maps.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X : TopCat.{u}} (U V : Opens X)
/-- Projection to sections on the first open. -/
def sectionsPairFstNat : sectionsPairFunctor U V ⟶ sections U where
  app F := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  naturality _ _ _ := by ext x; rfl
/-- Projection to sections on the second open. -/
def sectionsPairSndNat : sectionsPairFunctor U V ⟶ sections V where
  app F := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  naturality _ _ _ := by ext x; rfl
/-- Inclusion of sections on the first open into the pair. -/
def sectionsPairInlNat : sections U ⟶ sectionsPairFunctor U V where
  app F := AddCommGrpCat.ofHom (AddMonoidHom.inl _ _)
  naturality F G f := by
    ext x
    change (f.hom.app (op U) x, 0) = (f.hom.app (op U) x, f.hom.app (op V) 0)
    simp
/-- Inclusion of sections on the second open into the pair. -/
def sectionsPairInrNat : sections V ⟶ sectionsPairFunctor U V where
  app F := AddCommGrpCat.ofHom (AddMonoidHom.inr _ _)
  naturality F G f := by
    ext x
    change (0, f.hom.app (op V) x) = (f.hom.app (op U) 0, f.hom.app (op V) x)
    simp
@[simp]
lemma sectionsPairInl_fst : sectionsPairInlNat U V ≫ sectionsPairFstNat U V = 𝟙 _ := by
  ext F x
  rfl
@[simp]
lemma sectionsPairInl_snd : sectionsPairInlNat U V ≫ sectionsPairSndNat U V = 0 := by
  ext F x
  rfl
@[simp]
lemma sectionsPairInr_fst : sectionsPairInrNat U V ≫ sectionsPairFstNat U V = 0 := by
  ext F x
  rfl
@[simp]
lemma sectionsPairInr_snd : sectionsPairInrNat U V ≫ sectionsPairSndNat U V = 𝟙 _ := by
  ext F x
  rfl
@[simp]
lemma sectionsPair_total :
    sectionsPairFstNat U V ≫ sectionsPairInlNat U V +
      sectionsPairSndNat U V ≫ sectionsPairInrNat U V = 𝟙 _ := by
  ext F x
  change (x.1, 0) + (0, x.2) = x
  exact Prod.ext (add_zero _) (zero_add _)
set_option backward.isDefEq.respectTransparency false in
/-- Derived sections of a pair split into the two derived section groups. -/
def sectionsPairRightDerivedIso (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ((sectionsPairFunctor U V).rightDerived n).obj M ≅
      ((sections U).rightDerived n).obj M ⊞ ((sections V).rightDerived n).obj M := by
  let p₁ := (NatTrans.rightDerived (sectionsPairFstNat U V) n).app M
  let p₂ := (NatTrans.rightDerived (sectionsPairSndNat U V) n).app M
  let i₁ := (NatTrans.rightDerived (sectionsPairInlNat U V) n).app M
  let i₂ := (NatTrans.rightDerived (sectionsPairInrNat U V) n).app M
  have h₁₁ : i₁ ≫ p₁ = 𝟙 _ := by
    change (NatTrans.rightDerived (sectionsPairInlNat U V) n ≫
      NatTrans.rightDerived (sectionsPairFstNat U V) n).app M = _
    rw [← NatTrans.rightDerived_comp, sectionsPairInl_fst, NatTrans.rightDerived_id]
    rfl
  have h₁₂ : i₁ ≫ p₂ = 0 := by
    change (NatTrans.rightDerived (sectionsPairInlNat U V) n ≫
      NatTrans.rightDerived (sectionsPairSndNat U V) n).app M = _
    rw [← NatTrans.rightDerived_comp, sectionsPairInl_snd, NatTrans.rightDerived_zero]
    rfl
  have h₂₁ : i₂ ≫ p₁ = 0 := by
    change (NatTrans.rightDerived (sectionsPairInrNat U V) n ≫
      NatTrans.rightDerived (sectionsPairFstNat U V) n).app M = _
    rw [← NatTrans.rightDerived_comp, sectionsPairInr_fst, NatTrans.rightDerived_zero]
    rfl
  have h₂₂ : i₂ ≫ p₂ = 𝟙 _ := by
    change (NatTrans.rightDerived (sectionsPairInrNat U V) n ≫
      NatTrans.rightDerived (sectionsPairSndNat U V) n).app M = _
    rw [← NatTrans.rightDerived_comp, sectionsPairInr_snd, NatTrans.rightDerived_id]
    rfl
  have ht : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 _ := by
    change (NatTrans.rightDerived (sectionsPairFstNat U V) n ≫
        NatTrans.rightDerived (sectionsPairInlNat U V) n +
      NatTrans.rightDerived (sectionsPairSndNat U V) n ≫
        NatTrans.rightDerived (sectionsPairInrNat U V) n).app M = _
    rw [← NatTrans.rightDerived_comp, ← NatTrans.rightDerived_comp,
      ← NatTrans.rightDerived_add, sectionsPair_total, NatTrans.rightDerived_id]
    rfl
  refine ⟨biprod.lift p₁ p₂, biprod.desc i₁ i₂, ?_, ?_⟩
  · rw [biprod.lift_desc]
    exact ht
  · apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [Category.assoc, h₁₁, h₁₂, h₂₁, h₂₂]

end GromovWitten.AlgebraicGeometry.SheafCohomology
