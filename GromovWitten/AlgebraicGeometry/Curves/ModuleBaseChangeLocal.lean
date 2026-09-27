/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangePasting
import GromovWitten.AlgebraicGeometry.Curves.ModuleOpenBaseChange
/-!
# Checking canonical module base change locally

A module morphism is invertible if its pullbacks to an open neighbourhood of every
point are invertible. Pasting with open base change consequently reduces a
base-change isomorphism to its restrictions on an open cover of the new base.
-/

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X S T Z V W : Scheme.{u}}
/-- Invertibility of the second and outer squares implies invertibility of the
pullback of the first comparison. -/
lemma moduleBaseChange_pullback_isIso_of_paste
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (h₁ : IsPullback p g f b) (h₂ : IsPullback q k g c) (M : X.Modules)
    [IsIso ((modulePushforwardBaseChangeNatTrans f (c ≫ b) (q ≫ p) k
      (h₂.paste_horiz h₁)).app M)]
    [IsIso ((modulePushforwardBaseChangeNatTrans g c q k h₂).app
      ((Scheme.Modules.pullback p).obj M))] :
    IsIso ((Scheme.Modules.pullback c).map
      ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M)) := by
  let β := (Scheme.Modules.pullback c).map
    ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M)
  let δ := (modulePushforwardBaseChangeNatTrans g c q k h₂).app
    ((Scheme.Modules.pullback p).obj M) ≫
      (Scheme.Modules.pushforward k).map ((Scheme.Modules.pullbackComp q p).hom.app M)
  have : IsIso δ := by dsimp only [δ]; infer_instance
  have : IsIso (β ≫ δ) := by
    dsimp only [β, δ]
    rw [← moduleBaseChange_pasting]
    infer_instance
  exact IsIso.of_isIso_comp_right β δ

/-- A module morphism is an isomorphism if its open restrictions are locally isomorphisms. -/
lemma module_isIso_of_open_restrictions {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (U : X.Opens) (_hx : x ∈ U),
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) : IsIso φ := by
  suffices hφ : IsIso ((moduleToSheafAb X).map φ) by
    exact isIso_of_reflects_iso φ (moduleToSheafAb X)
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso ((moduleToSheafAb X).map φ)).mpr
  intro x
  obtain ⟨U, hx, hφ⟩ := h x
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := hφ
  let y : U.toScheme := ⟨x, hx⟩
  have hi : IsIso (((Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.toPresheaf U.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι y) φ).mp hi

/-- A module morphism is an isomorphism if its open pullbacks are locally isomorphisms. -/
lemma module_isIso_of_open_pullbacks {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (U : X.Opens) (_hx : x ∈ U),
      IsIso ((Scheme.Modules.pullback U.ι).map φ)) : IsIso φ := by
  apply module_isIso_of_open_restrictions φ
  intro x
  obtain ⟨U, hx, hφ⟩ := h x
  exact ⟨U, hx, (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) φ).mpr hφ⟩

/-- Canonical module base change is an isomorphism if it is so on an open cover of the new base. -/
lemma moduleBaseChange_isIso_of_open_cover
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) (M : X.Modules)
    (hlocal : ∀ x : T, ∃ (U : T.Opens) (_hx : x ∈ U),
      IsIso ((modulePushforwardBaseChangeNatTrans f (U.ι ≫ b) ((g ⁻¹ᵁ U).ι ≫ p)
        (g ∣_ U) ((isPullback_morphismRestrict g U).flip.paste_horiz h)).app M)) :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  apply module_isIso_of_open_pullbacks
  intro x
  obtain ⟨U, hx, hU⟩ := hlocal x
  have := hU
  have := moduleBaseChange_open_isIso g U ((Scheme.Modules.pullback p).obj M)
  exact ⟨U, hx, moduleBaseChange_pullback_isIso_of_paste
    f b p g U.ι (g ⁻¹ᵁ U).ι (g ∣_ U) h (isPullback_morphismRestrict g U).flip M⟩
end
end GromovWitten.AlgebraicGeometry.Curves
