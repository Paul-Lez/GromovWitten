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

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- The affine morphism from an affine open, followed by the structure morphism, is induced by
the base-ring map on sections of that open. -/
lemma affineFromSpec_comp_base (s : X ⟶ Spec R) (U : X.Opens) (hU : IsAffineOpen U) :
    hU.fromSpec ≫ s = Spec.map (baseToSections s U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

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

/-- Sections of an affine open are flat over the base when all relative stalks of the original
quasicoherent module are flat over that base. -/
lemma baseSections_flat_of_relative_stalks (s : X ⟶ Spec R) (M : X.Modules)
    [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (h : ∀ x : X, Module.Flat R (relativeStalkBase s M x)) :
    Module.Flat R (baseSectionModule s U M) := by
  let : Algebra R Γ(X, U) := (baseToSections s U).hom.toAlgebra
  have hcomp : hU.fromSpec ≫ s =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) :=
    affineFromSpec_comp_base s U hU
  have := affineOpenSections_flat_of_relative_stalks R (CommRingCat.of Γ(X, U)) X s
    hU.fromSpec hcomp M h
  exact Module.Flat.of_linearEquiv ((openPullbackSectionsLinearEquiv s hU.fromSpec
    (baseToSections s U) (affineFromSpec_comp_base s U hU) M).trans
      (baseSectionCongr s M hU.opensRange_fromSpec)).symm

end GromovWitten.AlgebraicGeometry.Curves
