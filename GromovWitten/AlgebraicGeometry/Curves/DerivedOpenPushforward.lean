/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.HigherOpenBaseChange
import GromovWitten.AlgebraicGeometry.Curves.AffineHigherDirectImage

/-!
# Derived pushforward after restriction to an open subscheme

Restriction to an open subscheme is identified with pullback for derived pushforward.
Consequently, affine open pieces have no positive higher direct images for quasicoherent
modules under the stated local Noetherian and affine hypotheses.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {X Y : Scheme.{u}}

instance moduleRestrictFunctor_additive (j : X ⟶ Y) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).Additive :=
  Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback j).symm

set_option backward.isDefEq.respectTransparency false in
/-- Restriction followed by pushforward has the expected right-derived comparison. -/
def restrictPushforwardRightDerivedIso (f : X ⟶ Y) (U : X.Opens)
    (M : X.Modules) (n : ℕ) :
    (((Scheme.Modules.restrictFunctor U.ι ⋙
        Scheme.Modules.pushforward (U.ι ≫ f)).rightDerived n).obj M) ≅
      higherDirectImageModule (U.ι ≫ f) (M.restrict U.ι) n := by
  have := moduleOpenPullback_rightDerivedPrecomp_isIso U.ι (U.ι ≫ f) M n
  exact ((NatIso.rightDerivedIso
      (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι)
        (Scheme.Modules.pushforward (U.ι ≫ f))) n).app M) ≪≫
    asIso ((Functor.rightDerivedPrecompComparison (Scheme.Modules.pullback U.ι)
      (Scheme.Modules.pushforward (U.ι ≫ f)) n).app M) ≪≫
    ((Scheme.Modules.pushforward (U.ι ≫ f)).rightDerived n).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M)

/-- Positive higher direct images vanish for affine open pieces under the standard hypotheses. -/
lemma isZero_restrictPushforwardRightDerived_succ (f : X ⟶ Y) (U : X.Opens)
    [IsAffineHom (U.ι ≫ f)] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.pushforward (U.ι ≫ f)).rightDerived (n + 1)).obj M) :=
  (isZero_higherDirectImageModule_affine_succ (U.ι ≫ f) (M.restrict U.ι) n).of_iso
    (restrictPushforwardRightDerivedIso f U M (n + 1))

end GromovWitten.AlgebraicGeometry.Curves
