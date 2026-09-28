/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.AffineRelativeStalk
import GromovWitten.AlgebraicGeometry.Curves.QuasiCoherentPullback

/-!
# Flatness of sections on affine open pullbacks

This file transfers flatness of the relative stalks of a quasi-coherent module
to the sections on an affine open which is presented as a pullback from an
affine base.  The transfer uses the affine stalk criterion and the canonical
base-linear identification of relative and affine stalk modules.
-/

open CategoryTheory TopCat AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

/-- Sections on an affine open pullback are flat over the base when the
relative stalks of the original module are flat over that base. -/
lemma affineOpenSections_flat_of_relative_stalks
    (R S : CommRingCat.{u}) [Algebra R S]
    (X : Scheme.{u}) (s : X ⟶ Spec R)
    (f : Spec S ⟶ X) [IsOpenImmersion f]
    (hcomp : f ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (M : X.Modules) [M.IsQuasicoherent]
    (h : ∀ x : X, Module.Flat R (relativeStalkBase s M x)) :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback f).obj M))) := by
  apply affineSections_flat_of_stalks R
  intro x
  have hrel := relativeOpenPullbackStalk_flat s f M h x
  rw [hcomp] at hrel
  let _ : Module.Flat R
      (relativeStalkBase (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        ((Scheme.Modules.pullback f).obj M) x) := hrel
  exact Module.Flat.of_linearEquiv
    (affineRelativeStalkLinearEquiv (R := R) ((Scheme.Modules.pullback f).obj M) x).symm

end GromovWitten.AlgebraicGeometry.Curves
