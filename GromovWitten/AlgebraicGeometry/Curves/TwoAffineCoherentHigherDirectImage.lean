/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.RelativeCechDerived
import GromovWitten.AlgebraicGeometry.Curves.RelativeCechGlobalSectionsDerived
import GromovWitten.AlgebraicGeometry.Curves.FinitePushforward

/-!
# Finite presentation of the first higher direct image on a two-affine cover

Over a Noetherian affine base, finite first cohomology on an affine two-open cover gives finite
presentation of the first higher direct image.  The Čech comparison supplies quasicoherence and
the global-sections comparison transports finite generation to the affine module of sections.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A finite first cohomology module makes a two-affine first higher direct image finitely
presented. -/
lemma isFinitePresentation_higherDirectImageModule_one_of_twoAffine
    [IsNoetherianRing R] [IsLocallyNoetherian X]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (h1 : Module.Finite R (cohomologyModuleCat R s M 1)) :
    (higherDirectImageModule s M 1).IsFinitePresentation := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine V.toScheme := hV
  let _ : IsAffine (U ⊓ V).toScheme := hI
  let hQ : (higherDirectImageModule s M 1).IsQuasicoherent :=
    isQuasicoherent_higherDirectImageModule_one_of_twoAffine s M U V hcover
  let _ : (higherDirectImageModule s M 1).IsQuasicoherent := hQ
  let _ : Module.Finite R (cohomologyModuleCat R s M 1) := h1
  let _ : Module.Finite R
      (moduleSpecΓFunctor.obj (higherDirectImageModule s M 1) : Type u) := by
    exact Module.Finite.equiv
      (higherDirectImageOneSectionsIsoCohomology s M U V hU hV hI hcover).symm.toLinearEquiv
  let _ : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj (higherDirectImageModule s M 1) : Type u) :=
    Module.finitePresentation_of_finite R
      (moduleSpecΓFunctor.obj (higherDirectImageModule s M 1) : Type u)
  exact spec_module_isFinitePresentation (higherDirectImageModule s M 1)

end GromovWitten.AlgebraicGeometry.Curves
