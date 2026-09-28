/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineQuasiCoherentPushforward
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFlatBaseChange
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineCohomologyZeroBaseChangeCanonical

/-!
# Sheaf-level Beck--Chevalley base change on a two-affine cover

These lemmas turn the computed degree-zero sections isomorphisms into genuine isomorphisms of
module-sheaf Beck--Chevalley morphisms over affine bases.  The flat-base theorem is valid without
Noetherian hypotheses; the relative-flat cohomology theorem assumes local Noetherianity of the
source and flatness of relative stalks and degree-one cohomology over an arbitrary ring.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf-level comparison is an isomorphism when the computed sections map is an isomorphism.
The two-affine hypotheses supply quasi-coherence on both pushforwards. -/
private lemma twoAffineSheafBaseChange_isIso_of_sections
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    [IsIso (sectionsBaseChangeMap s φ p g h M)] :
    IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  have : ((Scheme.Modules.pushforward s).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_twoAffine s M U V hU hV hI hcover
  have : IsAffineHom p :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  have hc : (p ⁻¹ᵁ U) ⊔ (p ⁻¹ᵁ V) = ⊤ := by
    change p ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have : ((Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.pullback p).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_twoAffine g ((Scheme.Modules.pullback p).obj M)
      (p ⁻¹ᵁ U) (p ⁻¹ᵁ V) (IsAffineHom.isAffine_preimage _ hU)
      (IsAffineHom.isAffine_preimage _ hV) (IsAffineHom.isAffine_preimage _ hI) hc
  let c : (Scheme.Modules.pullback (Spec.map φ)).obj
      ((Scheme.Modules.pushforward s).obj M) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) :=
    (modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M
  have hΓ : IsIso (moduleSpecΓFunctor.map c) := by
    apply (isIso_comp_left_iff
      (affinePullbackGammaMap φ ((Scheme.Modules.pushforward s).obj M))
      (moduleSpecΓFunctor.map c)).mp
    exact ‹IsIso (sectionsBaseChangeMap s φ p g h M)›
  have hciso : IsIso c := isIso_of_isIso_fromTildeΓ c
  change IsIso ((modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M) at hciso
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical] at hciso
  exact hciso

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf-level Beck--Chevalley comparison is an isomorphism for flat base-ring change on a
two-affine cover, with no Noetherian hypotheses. -/
lemma canonicalPushforwardBaseChangeComparison_isIso_of_twoAffine_flat_base
    (s : X ⟶ Spec R) (φ : R ⟶ T) (hφ : φ.hom.Flat)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤) :
    IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  have := sectionsBaseChangeMap_isIso_of_twoAffine_flat_base s φ hφ p g h M U V
    hU hV hI hcover
  exact twoAffineSheafBaseChange_isIso_of_sections s φ p g h M U V hU hV hI hcover

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf-level Beck--Chevalley comparison is an isomorphism under relative stalk flatness and
flat degree-one cohomology over an arbitrary base ring. -/
lemma canonicalPushforwardBaseChangeComparison_isIso_of_twoAffine_flat_cohomology
    [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    [Module.Flat R (cohomologyModuleCat R s M 1)] :
    IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  have := sectionsBaseChangeMap_isIso_of_twoAffine s φ p g h M U V hU hV hI hcover hflat
  exact twoAffineSheafBaseChange_isIso_of_sections s φ p g h M U V hU hV hI hcover

end GromovWitten.AlgebraicGeometry.Curves
