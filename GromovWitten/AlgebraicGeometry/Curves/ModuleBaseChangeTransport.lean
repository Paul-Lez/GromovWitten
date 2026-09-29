/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeIsomorphism
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeLocal
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeVerticalPasting
/-!
# Transporting invertibility of module base change

Pasting combines invertible comparison maps. If the intervening map is an
isomorphism, its pullback or pushforward reflects isomorphisms, giving a converse.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X S T Z V W : Scheme.{u}}
/-- Successive invertible base changes give an invertible composite. -/
lemma moduleBaseChange_paste_isIso
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (h₁ : IsPullback p g f b) (h₂ : IsPullback q k g c) (M : X.Modules)
    [IsIso ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M)]
    [IsIso ((modulePushforwardBaseChangeNatTrans g c q k h₂).app
      ((Scheme.Modules.pullback p).obj M))] :
    IsIso ((modulePushforwardBaseChangeNatTrans f (c ≫ b) (q ≫ p) k
      (h₂.paste_horiz h₁)).app M) := by
  have he := moduleBaseChange_pasting f b p g c q k h₁ h₂ M
  have : IsIso ((Scheme.Modules.pullbackComp c b).hom.app
      ((Scheme.Modules.pushforward f).obj M) ≫
      (modulePushforwardBaseChangeNatTrans f (c ≫ b) (q ≫ p) k (h₂.paste_horiz h₁)).app M) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.pullbackComp c b).hom.app
    ((Scheme.Modules.pushforward f).obj M)) _

/-- Changing the new base by an isomorphism preserves and reflects base-change invertibility. -/
lemma moduleBaseChange_paste_isIso_iff_of_isIso
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (c : V ⟶ T) (q : W ⟶ Z) (k : W ⟶ V)
    (h₁ : IsPullback p g f b) (h₂ : IsPullback q k g c) [IsIso c] (M : X.Modules) :
    IsIso ((modulePushforwardBaseChangeNatTrans f (c ≫ b) (q ≫ p) k
      (h₂.paste_horiz h₁)).app M) ↔
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h₁).app M) := by
  have := moduleBaseChange_isIso_of_isIso_base g c q k h₂
    ((Scheme.Modules.pullback p).obj M)
  constructor
  · intro h
    have := h
    have := moduleBaseChange_pullback_isIso_of_paste f b p g c q k h₁ h₂ M
    exact isIso_of_reflects_iso _ (Scheme.Modules.pullback c)
  · intro h
    have := h
    exact moduleBaseChange_paste_isIso f b p g c q k h₁ h₂ M
variable {Y : Scheme.{u}}
/-- Invertible comparisons for two original maps give one for their composite. -/
lemma moduleBaseChange_vertical_paste_isIso
    (f : X ⟶ Y) (a : Y ⟶ S) (b : T ⟶ S) (p : Z ⟶ Y) (g : Z ⟶ T)
    (q : W ⟶ X) (k : W ⟶ Z)
    (h₁ : IsPullback q k f p) (h₂ : IsPullback p g a b) (M : X.Modules)
    [IsIso ((modulePushforwardBaseChangeNatTrans f p q k h₁).app M)]
    [IsIso ((modulePushforwardBaseChangeNatTrans a b p g h₂).app
      ((Scheme.Modules.pushforward f).obj M))] :
    IsIso ((modulePushforwardBaseChangeNatTrans (f ≫ a) b q (k ≫ g)
      (h₁.paste_vert h₂)).app M) := by
  rw [moduleBaseChange_vertical_pasting f a b p g q k h₁ h₂ M]
  infer_instance

/-- Postcomposing the original map by an isomorphism preserves base-change invertibility. -/
lemma moduleBaseChange_vertical_paste_isIso_iff_of_isIso
    (f : X ⟶ Y) (a : Y ⟶ S) (b : T ⟶ S) (p : Z ⟶ Y) (g : Z ⟶ T)
    (q : W ⟶ X) (k : W ⟶ Z)
    (h₁ : IsPullback q k f p) (h₂ : IsPullback p g a b) [IsIso a] (M : X.Modules) :
    IsIso ((modulePushforwardBaseChangeNatTrans (f ≫ a) b q (k ≫ g)
      (h₁.paste_vert h₂)).app M) ↔
    IsIso ((modulePushforwardBaseChangeNatTrans f p q k h₁).app M) := by
  have : IsIso g := h₂.isIso_snd_of_isIso
  have := moduleBaseChange_isIso_of_isIso_map a b p g h₂
    ((Scheme.Modules.pushforward f).obj M)
  constructor
  · intro h
    let α := (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pushforwardComp f a).inv.app M) ≫
      (modulePushforwardBaseChangeNatTrans a b p g h₂).app
        ((Scheme.Modules.pushforward f).obj M)
    let β := (Scheme.Modules.pushforward g).map
      ((modulePushforwardBaseChangeNatTrans f p q k h₁).app M)
    let δ := (Scheme.Modules.pushforwardComp k g).hom.app
      ((Scheme.Modules.pullback q).obj M)
    have : IsIso α := by dsimp only [α]; infer_instance
    have : IsIso δ := by dsimp only [δ]; infer_instance
    have : IsIso (α ≫ β ≫ δ) := by
      dsimp only [α, β, δ]
      rw [Category.assoc, ← moduleBaseChange_vertical_pasting]
      exact h
    have : IsIso (β ≫ δ) := IsIso.of_isIso_comp_left α _
    have : IsIso β := IsIso.of_isIso_comp_right β δ
    exact isIso_of_reflects_iso _ (Scheme.Modules.pushforward g)
  · intro h
    have := h
    exact moduleBaseChange_vertical_paste_isIso f a b p g q k h₁ h₂ M
/-- Precomposing the original map by an isomorphism transports base-change invertibility
along its pushforward on modules. -/
lemma moduleBaseChange_vertical_paste_isIso_iff_of_isIso_first
    (f : X ⟶ Y) (a : Y ⟶ S) (b : T ⟶ S) (p : Z ⟶ Y) (g : Z ⟶ T)
    (q : W ⟶ X) (k : W ⟶ Z)
    (h₁ : IsPullback q k f p) (h₂ : IsPullback p g a b) [IsIso f] (M : X.Modules) :
    IsIso ((modulePushforwardBaseChangeNatTrans (f ≫ a) b q (k ≫ g)
      (h₁.paste_vert h₂)).app M) ↔
    IsIso ((modulePushforwardBaseChangeNatTrans a b p g h₂).app
      ((Scheme.Modules.pushforward f).obj M)) := by
  have := moduleBaseChange_isIso_of_isIso_map f p q k h₁ M
  constructor
  · intro h
    let α := (Scheme.Modules.pullback b).map
        ((Scheme.Modules.pushforwardComp f a).inv.app M)
    let β := (modulePushforwardBaseChangeNatTrans a b p g h₂).app
      ((Scheme.Modules.pushforward f).obj M)
    let δ := (Scheme.Modules.pushforward g).map
        ((modulePushforwardBaseChangeNatTrans f p q k h₁).app M) ≫
      (Scheme.Modules.pushforwardComp k g).hom.app ((Scheme.Modules.pullback q).obj M)
    have : IsIso α := by dsimp only [α]; infer_instance
    have : IsIso δ := by dsimp only [δ]; infer_instance
    have : IsIso (α ≫ β ≫ δ) := by
      dsimp only [α, β, δ]
      rw [← moduleBaseChange_vertical_pasting f a b p g q k h₁ h₂ M]
      exact h
    have : IsIso (β ≫ δ) := IsIso.of_isIso_comp_left α _
    exact IsIso.of_isIso_comp_right β δ
  · intro h
    have := h
    exact moduleBaseChange_vertical_paste_isIso f a b p g q k h₁ h₂ M
end
end GromovWitten.AlgebraicGeometry.Curves
