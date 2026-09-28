/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineQuasiCoherenceCriterion
import GromovWitten.AlgebraicGeometry.Curves.OpenImmersionBaseChange
import GromovWitten.AlgebraicGeometry.Curves.TwoAffineFlatBaseChange

/-!
# Quasi-coherent pushforward from a two-affine source

The affine localization criterion applied to the flat two-affine sections comparison proves
quasi-coherence of pushforward modules.  This statement does not assume Noetherianity.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
private lemma affinePullbackGammaMap_isIso_of_twoAffine_localization
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤) (r : R) :
    IsIso (affinePullbackGammaMap
      (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
        ((Scheme.Modules.pushforward s).obj M)) := by
  let T := CommRingCat.of (Localization.Away r)
  let φ : R ⟶ T := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let p := pullback.fst s (Spec.map φ)
  let g := pullback.snd s (Spec.map φ)
  let h := IsPullback.of_hasPullback s (Spec.map φ)
  have hφ : φ.hom.Flat := RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (Localization.Away r) (Submonoid.powers r))
  have hi := sectionsBaseChangeMap_isIso_of_twoAffine_flat_base s φ hφ p g h M U V
    hU hV hI hcover
  have := moduleBaseChange_isIso_of_isOpenImmersion s (Spec.map φ) p g h M
  exact (isIso_comp_right_iff
    (affinePullbackGammaMap φ ((Scheme.Modules.pushforward s).obj M))
    (moduleSpecΓFunctor.map
      ((modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M))).mp hi

/-- A quasi-coherent module on a source with a two-affine cover and affine overlap has
quasi-coherent pushforward to an affine base. -/
lemma isQuasicoherent_pushforward_of_twoAffine
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤) :
    ((Scheme.Modules.pushforward s).obj M).IsQuasicoherent := by
  apply isQuasicoherent_of_affinePullbackGammaMap_isIso
  intro r
  exact affinePullbackGammaMap_isIso_of_twoAffine_localization s M U V hU hV hI hcover r

end GromovWitten.AlgebraicGeometry.Curves
