/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.SectionsMayerVietoris
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero
/-!
# Local vanishing and higher direct images

Exactness of abelian sheaves can be checked by taking sections on a basis and then
passing to stalks. Applied to a pushed-forward injective resolution, this proves that
vanishing of derived sections on the inverse images of a basis implies vanishing of
the actual higher direct image sheaf.
-/

open CategoryTheory Limits Opposite TopologicalSpace
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.SheafCohomology
variable {X : TopCat.{u}}
instance stalk_preservesHomology (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).PreservesHomology := by
  let W := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (OpenNhds.inclusion x).op
  have : W.Additive := ⟨by intros; rfl⟩
  have : W.PreservesHomology := by dsimp [W]; infer_instance
  change (W ⋙ colim).PreservesHomology
  infer_instance

lemma isZero_stalk_of_basis (F : TopCat.Presheaf AddCommGrpCat.{u} X)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hF : ∀ U ∈ B, IsZero (F.obj (op U))) (x : X) : IsZero (F.stalk x) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  suffices h : ∀ s : F.stalk x, s = 0 from ⟨fun s t => (h s).trans (h t).symm⟩
  intro s
  obtain ⟨U, hx, hU, t, rfl⟩ := F.exists_mem_germ_eq_of_isBasis hB x s
  have := AddCommGrpCat.subsingleton_of_isZero (hF U hU)
  have ht : t = 0 := Subsingleton.elim _ _
  rw [ht, map_zero]

lemma exact_of_sections_basis (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hS : ∀ U ∈ B, (S.map (sections U)).Exact) : S.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mpr
  intro x
  let P := S.map (TopCat.Sheaf.forget AddCommGrpCat X)
  have hP (U : Opens X) (hU : U ∈ B) : IsZero (P.homology.obj (op U)) := by
    let E : TopCat.Presheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
      (evaluation _ _).obj (op U)
    have : E.Additive := ⟨by intros; rfl⟩
    have : E.PreservesHomology := by
      exact inferInstanceAs
        (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).PreservesHomology)
    have he := (ShortComplex.exact_iff_isZero_homology _).mp (hS U hU)
    exact he.of_iso (P.mapHomologyIso E).symm
  have hz := isZero_stalk_of_basis P.homology hB hP x
  apply (ShortComplex.exact_iff_isZero_homology _).mpr
  change IsZero ((P.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).homology)
  exact hz.of_iso (P.mapHomologyIso (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))

lemma exactAt_of_sections_basis
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) (n : ℕ)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hK : ∀ U ∈ B, (((sections U).mapHomologicalComplex (.up ℕ)).obj K).ExactAt n) :
    K.ExactAt n := by
  apply exact_of_sections_basis (K.sc n) hB
  intro U hU
  exact hK U hU

/-- Local vanishing on a basis forces vanishing of the actual higher direct image. -/
lemma isZero_rightDerived_pushforward_of_basis {Y : TopCat.{u}} (f : X ⟶ Y)
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    (hF : ∀ U ∈ B,
      IsZero (((sections ((Opens.map f).obj U)).rightDerived n).obj F)) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived n).obj F) := by
  let I := InjectiveResolution.of F
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f
  apply IsZero.of_iso _ (I.isoRightDerivedObj P n)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply exactAt_of_sections_basis _ n hB
  intro U hU
  have hz := (hF U hU).of_iso
    (I.isoRightDerivedObj (sections ((Opens.map f).obj U)) n).symm
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hz
end GromovWitten.AlgebraicGeometry.SheafCohomology
