/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeLocal
import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChangeTransport
import GromovWitten.AlgebraicGeometry.Curves.OpenAffineSectionsFlat

/-!
# Reduction of canonical base change to affine targets

Invertibility of the canonical pushforward base-change comparison can be checked after
all affine base changes of an affine base. Pasting with affine chart isomorphisms and
locality on the target give the comparison for arbitrary target schemes.
-/

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X Z : Scheme.{u}}

private lemma modulePushforwardBaseChange_isIso_transport
    (s : X ⟶ Spec R) {T : Scheme.{u}}
    (b b' : T ⟶ Spec R) {Z : Scheme.{u}}
    (p : Z ⟶ X) (g : Z ⟶ T)
    (h : IsPullback p g s b) (h' : IsPullback p g s b') (hb : b = b')
    (M : X.Modules)
    (hi : IsIso ((modulePushforwardBaseChangeNatTrans s b' p g h').app M)) :
    IsIso ((modulePushforwardBaseChangeNatTrans s b p g h).app M) := by
  subst b'
  exact hi

set_option backward.isDefEq.respectTransparency false in
private lemma modulePushforwardBaseChange_isIso_of_affine_target_open
    (s : X ⟶ Spec R) {S : Scheme.{u}}
    (b : S ⟶ Spec R) (p : Z ⟶ X) (g : Z ⟶ S)
    (h : IsPullback p g s b) (M : X.Modules)
    (W : S.Opens) (hW : IsAffineOpen W)
    (hring : ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) {Y : Scheme.{u}}
      (q : Y ⟶ X) (k : Y ⟶ Spec T) (h' : IsPullback q k s (Spec.map φ)),
      IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) q k h')) :
    IsIso ((modulePushforwardBaseChangeNatTrans s (W.ι ≫ b)
      ((g ⁻¹ᵁ W).ι ≫ p) (g ∣_ W)
      ((isPullback_morphismRestrict g W).flip.paste_horiz h)).app M) := by
  let b₀ : W.toScheme ⟶ Spec R := W.ι ≫ b
  let p₀ : (g ⁻¹ᵁ W).toScheme ⟶ X := (g ⁻¹ᵁ W).ι ≫ p
  let g₀ : (g ⁻¹ᵁ W).toScheme ⟶ W.toScheme := g ∣_ W
  let h₀ : IsPullback p₀ g₀ s b₀ := (isPullback_morphismRestrict g W).flip.paste_horiz h
  let c : Spec Γ(S, W) ⟶ W.toScheme := hW.isoSpec.inv
  let q : pullback g₀ c ⟶ (g ⁻¹ᵁ W).toScheme := pullback.fst g₀ c
  let k : pullback g₀ c ⟶ Spec Γ(S, W) := pullback.snd g₀ c
  let h₁ : IsPullback q k g₀ c := IsPullback.of_hasPullback g₀ c
  apply (moduleBaseChange_paste_isIso_iff_of_isIso s b₀ p₀ g₀ c q k h₀ h₁ M).mp
  have hb : c ≫ b₀ = Spec.map (baseToSections b W) := by
    dsimp [c, b₀]
    rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι, affineFromSpec_comp_base]
  have h₂ : IsPullback (q ≫ p₀) k s (Spec.map (baseToSections b W)) :=
    hb ▸ h₁.paste_horiz h₀
  have hh := hring _ (baseToSections b W) (q ≫ p₀) k h₂
  have hh' : IsIso ((modulePushforwardBaseChangeNatTrans s
      (Spec.map (baseToSections b W)) (q ≫ p₀) k h₂).app M) := by
    rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical]
    exact hh
  exact modulePushforwardBaseChange_isIso_transport s (c ≫ b₀)
    (Spec.map (baseToSections b W)) (q ≫ p₀) k
    (h₁.paste_horiz h₀) h₂ hb M hh'

set_option backward.isDefEq.respectTransparency false in
/-- If canonical base change is invertible after every affine base change of `Spec R`,
then it is invertible after every scheme-valued base change of `Spec R`. -/
lemma canonicalPushforwardBaseChangeComparison_isIso_of_affine_target_local
    (s : X ⟶ Spec R) (M : X.Modules)
    (hring : ∀ (T : CommRingCat.{u}) (φ : R ⟶ T) {Y : Scheme.{u}}
      (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ)),
      IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h))
    {S : Scheme.{u}} (b : S ⟶ Spec R) {Z : Scheme.{u}}
    (p : Z ⟶ X) (g : Z ⟶ S) (h : IsPullback p g s b) :
    IsIso (canonicalPushforwardBaseChangeComparison s M b p g h) := by
  have hnat : IsIso ((modulePushforwardBaseChangeNatTrans s b p g h).app M) := by
    apply moduleBaseChange_isIso_of_open_cover s b p g h M
    intro x
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
      (x := x) (by simp)
    exact ⟨W, hxW,
      modulePushforwardBaseChange_isIso_of_affine_target_open s b p g h M W hW hring⟩
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical] at hnat
  exact hnat

end GromovWitten.AlgebraicGeometry.Curves
