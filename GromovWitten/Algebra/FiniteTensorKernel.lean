/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.FiniteFlatTwoTerm

/-!
# Finiteness of scalar-extended two-term kernels

Finite flat two-term replacements identify the kernel after scalar extension
with a submodule of the scalar extension of the finite replacement term. This
gives finiteness over any Noetherian target ring under flatness and finite
cohomology hypotheses over the source ring.
-/

open CategoryTheory Limits
open scoped TensorProduct

noncomputable section
universe u

namespace ModuleCat

variable {R T : Type u} [CommRing R] [CommRing T] [IsNoetherianRing T]
variable {A B : ModuleCat.{u} R} (d : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
/-- The kernel after scalar extension is finite over a Noetherian target ring. -/
theorem finite_kernel_extendScalars_of_flat_finite_cohomology
    (φ : R →+* T) [IsNoetherianRing R] [Module.Flat R A] [Module.Flat R B]
    [Module.Finite R d.hom.ker] [Module.Finite R (B ⧸ d.hom.range)] :
    Module.Finite T (kernel (C := ModuleCat T) ((extendScalars φ).map d) : Type u) := by
  obtain ⟨n, q, hq, hflat, hfinite, hproj⟩ := d.hom.exists_finiteFlatTwoTerm
  let K := LinearMap.ker (LinearMap.finiteFlatTwoTermMap d.hom q)
  let _ : Module.Finite R K := hfinite
  let _ : Algebra R T := φ.toAlgebra
  let E := extendScalars φ
  let d' := ModuleCat.ofHom (LinearMap.finiteFlatTwoTermDifferential d.hom q)
  have : Module.Finite T (E.obj (ModuleCat.of R K)) := by
    change Module.Finite T (T ⊗[R] K)
    infer_instance
  have : Module.Finite T ((E.map d').hom.ker) := inferInstance
  have : Module.Finite T (kernel (C := ModuleCat T) (E.map d') : Type u) :=
    Module.Finite.equiv (ModuleCat.kernelIsoKer (E.map d')).toLinearEquiv.symm
  let c := kernel.map (E.map d') (E.map d)
    (E.map (ModuleCat.ofHom (LinearMap.finiteFlatTwoTermLeft d.hom q)))
    (E.map (ModuleCat.ofHom q))
    (LinearMap.finiteFlatTwoTerm_extendScalars_isPullback φ d.hom q hq).w
  have : IsIso c := LinearMap.finiteFlatTwoTerm_extendScalars_kernel_map_isIso φ d.hom q hq
  exact Module.Finite.equiv (asIso c).toLinearEquiv

end ModuleCat
