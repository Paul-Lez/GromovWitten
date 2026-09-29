/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.ModuleCatScalarExtension
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization of scalar-extension adjoints

The adjoint of an isomorphism from an extended module to a target module is a localized module
map.  This packages the scalar-extension presentation needed by affine base-change arguments.
-/

open CategoryTheory Limits TensorProduct
open scoped ChangeOfRings

noncomputable section
universe u

namespace ModuleCat

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

set_option backward.isDefEq.respectTransparency false in
/-- The adjoint of an isomorphism from scalar extension to a `T`-module is localized. -/
lemma isLocalizedModule_adjunct_of_isIso
    (S : Submonoid R) [IsLocalization S T]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} T)
    (e : (extendScalars (algebraMap R T)).obj M ⟶ N) [IsIso e] :
    IsLocalizedModule S
      (((extendRestrictScalarsAdj (algebraMap R T)).homEquiv M N e).hom) := by
  let φ := algebraMap R T
  let Tsrc := (restrictScalars φ).obj ((extendScalars φ).obj M)
  let mk' : M →ₗ[R] Tsrc := ((extendRestrictScalarsAdj φ).unit.app M).hom
  let e0 : ModuleCat.of R (T ⊗[R] M) ≅ Tsrc :=
    restrictExtendScalarsAlgebraIso (C := R) (D := T) M
  have hmk_eq : mk' = e0.toLinearEquiv.toLinearMap.comp (TensorProduct.mk R T M 1) := by
    ext x
    change (1 : T) ⊗ₜ[R, φ] x = e0.hom ((1 : T) ⊗ₜ[R] x)
    exact (restrictExtendScalarsAlgebraIso_hom_tmul M 1 x).symm
  have hmk : IsLocalizedModule S mk' := by
    rw [hmk_eq]
    exact IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R T M 1) e0.toLinearEquiv
  let eR := ((restrictScalars φ).mapIso (asIso e)).toLinearEquiv
  have h := IsLocalizedModule.of_linearEquiv S mk' eR
  change IsLocalizedModule S (((extendRestrictScalarsAdj φ).homEquiv M N e).hom)
  convert h using 1
  ext x
  rfl

end ModuleCat
