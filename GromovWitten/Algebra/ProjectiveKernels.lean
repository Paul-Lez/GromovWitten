/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, OpenAI Codex
-/

import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Kernels of split surjections of projective modules

The kernel of a surjection onto a projective module is a direct summand of the source.
Consequently it is projective when the source is projective, and finitely generated when
the source is finitely generated.
-/

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-! ## Kernels of split surjections -/

/-- The retraction of the kernel of a split surjection: `x ↦ x - s (f x)` for a section `s`. -/
def kerRetraction (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y) :
    M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) (by
    intro x
    rw [LinearMap.mem_ker]
    change f (x - s (f x)) = 0
    rw [map_sub, hs, sub_self])

@[simp]
theorem kerRetraction_apply_coe (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y)
    (x : M) : ((kerRetraction f hs x : LinearMap.ker f) : M) = x - s (f x) :=
  rfl

/-- The retraction restricts to the identity on the kernel. -/
theorem kerRetraction_comp_subtype (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y) :
    (kerRetraction f hs).comp (LinearMap.ker f).subtype = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  change (x : M) - s (f (x : M)) = (x : M)
  have hx : f (x : M) = 0 := x.2
  rw [hx, map_zero, sub_zero]

/-- The retraction onto the kernel of a split surjection is surjective. -/
theorem kerRetraction_surjective (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y) :
    Function.Surjective (kerRetraction f hs) := by
  intro x
  refine ⟨(x : M), ?_⟩
  exact congrArg (fun m : LinearMap.ker f →ₗ[R] LinearMap.ker f => m x)
    (kerRetraction_comp_subtype f hs)

/-- **The kernel of a surjection of projective modules is projective**: the surjection splits, so
the kernel is a direct summand of the source. -/
theorem projective_ker_of_surjective [Module.Projective R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ y, f (s y) = y := fun y =>
    congrArg (fun m : N →ₗ[R] N => m y) hs
  exact Module.Projective.of_split (LinearMap.ker f).subtype (kerRetraction f hs')
    (kerRetraction_comp_subtype f hs')

/-- The kernel of a surjection onto a projective module, from a finitely generated module, is
finitely generated. -/
theorem finite_ker_of_surjective [Module.Finite R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Finite R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ y, f (s y) = y := fun y =>
    congrArg (fun m : N →ₗ[R] N => m y) hs
  exact Module.Finite.of_surjective (kerRetraction f hs') (kerRetraction_surjective f hs')

end LinearMap
