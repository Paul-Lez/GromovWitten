/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineSectionsBaseChange
import GromovWitten.AlgebraicGeometry.Curves.AffineQuasiCoherenceCriterion

/-!
# Detecting sheaf base change on affine global sections

When both pushforwards are quasi-coherent, invertibility of the scalar-extension
comparison on global sections implies invertibility of the canonical
Beck–Chevalley morphism of module sheaves.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- If the two pushforwards are quasi-coherent, an isomorphism on their affine-base
sections detects that the canonical sheaf-level base-change comparison is an isomorphism. -/
lemma canonicalPushforwardBaseChangeComparison_isIso_of_sections
    (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules)
    [((Scheme.Modules.pushforward s).obj M).IsQuasicoherent]
    [((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M)).IsQuasicoherent]
    [IsIso (sectionsBaseChangeMap s φ p g h M)] :
    IsIso (canonicalPushforwardBaseChangeComparison s M (Spec.map φ) p g h) := by
  let c : (Scheme.Modules.pullback (Spec.map φ)).obj
      ((Scheme.Modules.pushforward s).obj M) ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback p).obj M) :=
    (modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M
  have hΓ : IsIso (moduleSpecΓFunctor.map c) := by
    apply (isIso_comp_left_iff
      (affinePullbackGammaMap φ ((Scheme.Modules.pushforward s).obj M))
      (moduleSpecΓFunctor.map c)).mp
    exact ‹IsIso (sectionsBaseChangeMap s φ p g h M)›
  let : IsIso (moduleSpecΓFunctor.map c) := hΓ
  have hciso : IsIso c := isIso_of_isIso_fromTildeΓ c
  change IsIso ((modulePushforwardBaseChangeNatTrans s (Spec.map φ) p g h).app M) at hciso
  rw [modulePushforwardBaseChangeNatTrans_app_eq_canonical] at hciso
  exact hciso

end GromovWitten.AlgebraicGeometry.Curves
