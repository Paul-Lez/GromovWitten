/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffinePullbackLocalization
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsLinear
import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSectionsNaturality

/-!
# An affine localization criterion for quasi-coherence

A module on `Spec R` is quasi-coherent when its affine pullback/global-sections comparison is an
isomorphism after every principal localization.  The criterion is formulated directly in terms
of the existing affine pullback map, so geometric arguments can supply those isomorphisms
independently.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

set_option backward.isDefEq.respectTransparency false in
/-- The affine pullback unit restricts to the original module along the image of a localization. -/
lemma openPullbackSectionsIso_unit
    {R T : CommRingCat.{u}} (φ : R ⟶ T)
    [IsOpenImmersion (Spec.map φ)] (M : (Spec R).Modules)
    (m : moduleSpecΓFunctor.obj M) :
    (openPullbackSectionsIso (Spec.map φ) M).hom (affinePullbackGammaUnit φ M m) =
      M.presheaf.map (homOfLE (show (Spec.map φ).opensRange ≤ ⊤ from le_top)).op m := by
  change Γ(M, ⊤) at m
  have hu := congrArg (fun k => k.app ⊤)
    (pullbackPushforwardAdjunction_unit_restrict (Spec.map φ) M)
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app] at hu
  have hx := ConcreteCategory.congr_hom hu m
  have hx' : ((restrictFunctorIsoPullback (Spec.map φ)).inv.app M).app ⊤
      (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m) =
      M.presheaf.map (homOfLE (show Spec.map φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op m := hx
  change M.presheaf.map (eqToIso (Scheme.Hom.image_top_eq_opensRange (Spec.map φ)).symm).op.hom
    (((restrictFunctorIsoPullback (Spec.map φ)).inv.app M).app ⊤
      (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m)) = _
  calc
    _ = M.presheaf.map
        (eqToIso (Scheme.Hom.image_top_eq_opensRange (Spec.map φ)).symm).op.hom
        (M.presheaf.map (homOfLE (show Spec.map φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op m) :=
      congrArg (fun z => M.presheaf.map
        (eqToIso (Scheme.Hom.image_top_eq_opensRange (Spec.map φ)).symm).op.hom z) hx'
    _ = _ := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Principal-local affine pullback isomorphisms characterize quasi-coherence on `Spec R`. -/
lemma isQuasicoherent_of_affinePullbackGammaMap_isIso
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (h : ∀ r : R, IsIso (affinePullbackGammaMap
      (CommRingCat.ofHom (algebraMap R (Localization.Away r))) M)) :
    M.IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing M).mpr
  intro r
  let T := Localization.Away r
  let φ : R ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap R T)
  have : IsIso (affinePullbackGammaMap φ M) := h r
  have hloc := affinePullbackGammaUnit_isLocalizedModule_of_isIso
    (R := R) (S := T) (Submonoid.powers r) M
  let e := (openPullbackSectionsLinearEquiv (𝟙 (Spec R)) (Spec.map φ) φ
    (Category.comp_id _) M).trans
      (baseSectionCongr (𝟙 (Spec R)) M (Scheme.Hom.opensRange_localizationAway r))
  have ht := IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    (affinePullbackGammaUnit φ M).hom e
  have heq : e.toLinearMap.comp (affinePullbackGammaUnit φ M).hom =
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom := by
    ext m
    change M.presheaf.map _
      ((openPullbackSectionsIso (Spec.map φ) M).hom (affinePullbackGammaUnit φ M m)) = _
    rw [openPullbackSectionsIso_unit]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [heq] at ht
  exact ht

end GromovWitten.AlgebraicGeometry.Curves
