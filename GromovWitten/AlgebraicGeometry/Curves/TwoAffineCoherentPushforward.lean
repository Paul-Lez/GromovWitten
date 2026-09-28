/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TwoAffineQuasiCoherentPushforward
import GromovWitten.AlgebraicGeometry.Curves.CohomologyZeroBaseChangeMap
import GromovWitten.AlgebraicGeometry.Curves.FinitePushforward

/-!
# Finite presentation of a two-affine pushforward

Over a Noetherian affine base, finite degree-zero cohomology on a two-affine cover gives finite
presentation of the pushforward module.  The proof first obtains quasi-coherence from the
localization criterion and then transports finite generation through the canonical degree-zero
cohomology identification.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A finite degree-zero cohomology module makes a two-affine pushforward finitely presented. -/
lemma isFinitePresentation_pushforward_of_twoAffine
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hI : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    (h0 : Module.Finite R (cohomologyModuleCat R s M 0)) :
    ((Scheme.Modules.pushforward s).obj M).IsFinitePresentation := by
  let P := (Scheme.Modules.pushforward s).obj M
  let hP : P.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_twoAffine s M U V hU hV hI hcover
  let _ : P.IsQuasicoherent := hP
  let _ : Module.Finite R (cohomologyModuleCat R s M 0) := h0
  let _ : Module.Finite R ((moduleSpecΓFunctor.obj P : Type u)) := by
    exact Module.Finite.equiv (cohomologyZeroPushforwardSectionsIso s M).toLinearEquiv
  let _ : Module.FinitePresentation R ((moduleSpecΓFunctor.obj P : Type u)) :=
    Module.finitePresentation_of_finite R (moduleSpecΓFunctor.obj P : Type u)
  exact spec_module_isFinitePresentation P

end GromovWitten.AlgebraicGeometry.Curves
