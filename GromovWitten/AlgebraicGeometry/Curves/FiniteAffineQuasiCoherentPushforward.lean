/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineQuasiCoherenceCriterion
import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineCechComplex
import GromovWitten.AlgebraicGeometry.Curves.OpenImmersionBaseChange
import GromovWitten.AlgebraicGeometry.Curves.FiniteCechCanonicalBaseChange
import GromovWitten.AlgebraicGeometry.Curves.SheafBaseChangeOfSections

/-!
# Quasicoherence and canonical base change from finite affine covers

For a separated source with a finite affine cover, canonical flat base change on
sections proves quasi-coherence of pushforward to an affine base. This also
promotes invertibility of the finite Čech degree-zero homology comparison to
invertibility of the canonical sheaf-level base-change map.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
private lemma affinePullbackGammaMap_isIso_of_finiteAffineCover
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) (hcover : coverUnion U = ⊤)
    [X.IsSeparated] (r : R) :
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
  have hi := sectionsBaseChangeMap_isIso_of_finiteCech_flat_base
    s φ hφ p g h M U hU hcover
  have := moduleBaseChange_isIso_of_isOpenImmersion s (Spec.map φ) p g h M
  exact (isIso_comp_right_iff
    (affinePullbackGammaMap φ ((Scheme.Modules.pushforward s).obj M))
    (moduleSpecΓFunctor.map
      ((modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M))).mp hi

/-- A quasi-coherent module on a separated source with a finite affine cover has quasi-coherent
pushforward to an affine base. -/
lemma isQuasicoherent_pushforward_of_finiteAffineCover
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) (hcover : coverUnion U = ⊤)
    [X.IsSeparated] :
    ((Scheme.Modules.pushforward s).obj M).IsQuasicoherent := by
  apply isQuasicoherent_of_affinePullbackGammaMap_isIso
  intro r
  exact affinePullbackGammaMap_isIso_of_finiteAffineCover s M U hU hcover r

/-- Finite-cover scalar comparison on affine-base sections promotes to the canonical
sheaf-level pushforward base-change comparison. -/
lemma canonicalPushforwardBaseChangeComparison_isIso_of_finiteCech_comparison
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] [X.IsSeparated]
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) (hcover : coverUnion U = ⊤)
    [IsIso ((baseFiniteCechComplex s M U).homologyComparison
      (ModuleCat.extendScalars φ.hom) (0 : ℤ))] :
    IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  let P := (Scheme.Modules.pushforward s).obj M
  let _ : P.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_finiteAffineCover s M U hU hcover
  have hpAffine : IsAffineHom p :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  have hySep : Y.IsSeparated := by
    constructor
    rw [← terminal.comp_from p]
    infer_instance
  let M' := (Scheme.Modules.pullback p).obj M
  let _ : M'.IsQuasicoherent := inferInstance
  let Up := U.map (TopologicalSpace.Opens.map p.base).obj
  have hUp : ∀ W ∈ Up, IsAffineOpen W := by
    intro W hW
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hW
    exact (hU V hV).preimage p
  have hcoverp : coverUnion Up = ⊤ := by
    rw [coverUnion_preimage, hcover]
    rfl
  let _ : Y.IsSeparated := hySep
  let _ : ((Scheme.Modules.pushforward g).obj M').IsQuasicoherent :=
    isQuasicoherent_pushforward_of_finiteAffineCover g M' Up hUp hcoverp
  let _ : IsIso (sectionsBaseChangeMap s φ p g h M) :=
    sectionsBaseChangeMap_isIso_of_finiteCech_comparison s φ p g h M U hU hcover
  exact canonicalPushforwardBaseChangeComparison_isIso_of_sections s φ p g h M

end GromovWitten.AlgebraicGeometry.Curves
