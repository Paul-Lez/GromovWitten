/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
/-!
# Exactness of the associated-sheaf functor

The tilde construction preserves monomorphisms because localization does. Its existing
left adjunction gives preservation of cokernels, and therefore preservation of homology
and finite limits.
-/

open CategoryTheory Limits AlgebraicGeometry
universe u
noncomputable section
namespace AlgebraicGeometry.tilde
variable (R : CommRingCat.{u})
/-- Injective module maps remain injective on the sheaves of local fractions. -/
instance preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U s t h
    apply Subtype.ext
    funext x
    let _ := x.1.isPrime
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N) f.hom
      ((ModuleCat.mono_iff_injective f).mp hf)
    exact congrArg (fun z => z.val x) h
/-- Associated sheaves preserve exactness of module complexes. -/
instance preservesHomology : (tilde.functor R).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _
/-- The associated-sheaf functor is left exact. -/
instance preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  Functor.preservesFiniteLimits_of_preservesHomology _
end AlgebraicGeometry.tilde
