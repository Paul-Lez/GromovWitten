/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineSheafBaseChange

/-!
# Arbitrary-target base change from a two-affine source

For a locally Noetherian source over an affine base, the two-affine Čech comparison gives
isomorphisms for the canonical module pushforward base-change map over an arbitrary target.
The source module has to be quasicoherent, its chosen affine two-open cover has affine overlap,
and the relative stalks and degree-one cohomology must be flat over the original base ring.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X T Z : Scheme.{u}}

private lemma modulePushforwardBaseChange_isIso_transport
    (s : X ⟶ Spec R) (b b' : T ⟶ Spec R)
    (p : Z ⟶ X) (g : Z ⟶ T) (h : IsPullback p g s b)
    (h' : IsPullback p g s b') (hb : b = b') (M : X.Modules)
    (hi : IsIso ((modulePushforwardBaseChangeNatTrans s b' p g h').app M)) :
    IsIso ((modulePushforwardBaseChangeNatTrans s b p g h).app M) := by
  subst b'
  exact hi

set_option backward.isDefEq.respectTransparency false in
private lemma modulePushforwardBaseChange_isIso_of_affine_target_open
    (s : X ⟶ Spec R) (b : T ⟶ Spec R)
    (p : Z ⟶ X) (g : Z ⟶ T) (h : IsPullback p g s b)
    (M : X.Modules) (W : T.Opens) (hW : IsAffineOpen W)
    (hc : ∀ (A : CommRingCat.{u}) (φ : R ⟶ A) (Y : Scheme.{u})
      (q : Y ⟶ X) (k : Y ⟶ Spec A) (h' : IsPullback q k s (Spec.map φ)),
      IsIso ((modulePushforwardBaseChangeNatTrans s (Spec.map φ) q k h').app M)) :
    IsIso ((modulePushforwardBaseChangeNatTrans s (W.ι ≫ b)
      ((g ⁻¹ᵁ W).ι ≫ p) (g ∣_ W)
      ((isPullback_morphismRestrict g W).flip.paste_horiz h)).app M) := by
  let b₀ : W.toScheme ⟶ Spec R := W.ι ≫ b
  let p₀ : (g ⁻¹ᵁ W).toScheme ⟶ X := (g ⁻¹ᵁ W).ι ≫ p
  let g₀ : (g ⁻¹ᵁ W).toScheme ⟶ W.toScheme := g ∣_ W
  let h₀ : IsPullback p₀ g₀ s b₀ := (isPullback_morphismRestrict g W).flip.paste_horiz h
  let c : Spec Γ(T, W) ⟶ W.toScheme := hW.isoSpec.inv
  let q : pullback g₀ c ⟶ (g ⁻¹ᵁ W).toScheme := pullback.fst g₀ c
  let k : pullback g₀ c ⟶ Spec Γ(T, W) := pullback.snd g₀ c
  let h₁ : IsPullback q k g₀ c := IsPullback.of_hasPullback g₀ c
  apply (moduleBaseChange_paste_isIso_iff_of_isIso s b₀ p₀ g₀ c q k h₀ h₁ M).mp
  have hb : c ≫ b₀ = Spec.map (baseToSections b W) := by
    dsimp [c, b₀]
    rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι, affineFromSpec_comp_base]
  have h₂ : IsPullback (q ≫ p₀) k s (Spec.map (baseToSections b W)) :=
    hb ▸ h₁.paste_horiz h₀
  have hh := hc _ (baseToSections b W) _ (q ≫ p₀) k h₂
  exact modulePushforwardBaseChange_isIso_transport s _ _ _ _
    (h₁.paste_horiz h₀) h₂ hb M hh

set_option backward.isDefEq.respectTransparency false in
/-- The module pushforward base-change map is an isomorphism over an arbitrary target when the
source has a locally Noetherian two-affine cover with affine overlap and the stated flatness
hypotheses. -/
lemma modulePushforwardBaseChange_isIso_of_twoAffine_flat_cohomology
    [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (b : T ⟶ Spec R)
    (p : Z ⟶ X) (g : Z ⟶ T) (h : IsPullback p g s b)
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    IsIso ((modulePushforwardBaseChangeNatTrans s b p g h).app M) := by
  apply moduleBaseChange_isIso_of_open_cover s b p g h M
  intro x
  obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := x) (by simp)
  refine ⟨W, hxW, ?_⟩
  apply modulePushforwardBaseChange_isIso_of_affine_target_open s b p g h M W hW
  intro A φ Y q k h'
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical]
  exact canonicalPushforwardBaseChangeComparison_isIso_of_twoAffine_flat_cohomology
    s φ q k h' M U V hU hV hI hcover hflat

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Beck--Chevalley map is an isomorphism for the same arbitrary-target
two-affine hypotheses. -/
lemma canonicalPushforwardBaseChangeComparison_isIso_of_twoAffine_flat_cohomology_arbitrary_base
    [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (b : T ⟶ Spec R)
    (p : Z ⟶ X) (g : Z ⟶ T) (h : IsPullback p g s b)
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    IsIso (canonicalPushforwardBaseChangeComparison s M b p g h) := by
  have result := modulePushforwardBaseChange_isIso_of_twoAffine_flat_cohomology
    s b p g h M U V hU hV hI hcover hflat
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical] at result
  exact result

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary pushforward base-change data follows from the arbitrary-target two-affine theorem. -/
theorem pushforwardBaseChangeData_of_twoAffine
    [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    PushforwardBaseChangeData s M where
  comparison_isIso := by
    intro T Z b p g h
    exact canonicalPushforwardBaseChangeComparison_isIso_of_twoAffine_flat_cohomology_arbitrary_base
      s b p g h M U V hU hV hI hcover hflat

end GromovWitten.AlgebraicGeometry.Curves
