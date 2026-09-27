/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeMate
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-!
# Module base change along isomorphisms

An isomorphism of schemes induces equivalences on sheaves of modules. The unit
formula for canonical base change therefore proves invertibility whenever either
of the two maps to the base is an isomorphism.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry
namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X S T Z : Scheme.{u}}
/-- Pushforward along a scheme isomorphism is an equivalence of module categories. -/
def modulePushforwardEquivalence (f : X ⟶ S) [IsIso f] : X.Modules ≌ S.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward (inv f))
    ((Scheme.Modules.pushforwardComp f (inv f) ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id f) ≪≫ Scheme.Modules.pushforwardId X).symm)
    (Scheme.Modules.pushforwardComp (inv f) f ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pushforwardId S)
instance modulePushforward_isEquivalence (f : X ⟶ S) [IsIso f] :
    (Scheme.Modules.pushforward f).IsEquivalence :=
  (modulePushforwardEquivalence f).isEquivalence_functor
instance modulePullback_isEquivalence (f : X ⟶ S) [IsIso f] :
    (Scheme.Modules.pullback f).IsEquivalence :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isEquivalence_left_of_isEquivalence_right

/-- Canonical module base change along a base isomorphism is invertible. -/
lemma moduleBaseChange_isIso_of_isIso_base
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsIso b] (M : X.Modules) :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  have : IsIso p := h.isIso_fst_of_isIso
  let β := (modulePushforwardBaseChangeNatTrans f b p g h).app M
  have he := moduleBaseChange_unit_formula f b p g h M
  rw [Adjunction.homEquiv_unit] at he
  have ht : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
      ((Scheme.Modules.pushforward f).obj M) ≫ (Scheme.Modules.pushforward b).map β) := by
    rw [he]
    infer_instance
  have : IsIso ((Scheme.Modules.pushforward b).map β) :=
    IsIso.of_isIso_comp_left ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
      ((Scheme.Modules.pushforward f).obj M)) _
  exact isIso_of_reflects_iso β (Scheme.Modules.pushforward b)

/-- Canonical module base change of an isomorphism is invertible. -/
lemma moduleBaseChange_isIso_of_isIso_map
    (f : X ⟶ S) (b : T ⟶ S) (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g f b) [IsIso f] (M : X.Modules) :
    IsIso ((modulePushforwardBaseChangeNatTrans f b p g h).app M) := by
  have : IsIso g := h.isIso_snd_of_isIso
  have : IsIso (moduleBaseChangePullbackMap f b p g h M) := by
    dsimp [moduleBaseChangePullbackMap]
    infer_instance
  change IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    (moduleBaseChangePullbackMap f b p g h M))
  rw [Adjunction.homEquiv_unit]
  infer_instance
end
end GromovWitten.AlgebraicGeometry.Curves
