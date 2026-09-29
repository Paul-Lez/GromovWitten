/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Kernel comparison for exact short complexes

For a morphism of short complexes, exactness of the source, monomorphy of both
left differentials, and an isomorphism on the middle component together with a
monomorphism on the right component imply that the left component is an isomorphism.
-/

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- If a morphism `S ⟶ T` has exact source, monic left differentials, an invertible
middle component, and a monic right component, then its left component is invertible. -/
lemma isIso_τ₁_of_exact_of_mono_f
    {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : S.Exact) [Mono S.f] [Mono T.f] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso φ.τ₁ := by
  have hz : (T.f ≫ inv φ.τ₂) ≫ S.g = 0 := by
    apply (cancel_mono φ.τ₃).1
    rw [Category.assoc, ← φ.comm₂₃, Category.assoc,
      IsIso.inv_hom_id_assoc, T.zero, zero_comp]
  let b : T.X₁ ⟶ S.X₁ := hS.lift (T.f ≫ inv φ.τ₂) hz
  have hb : b ≫ S.f = T.f ≫ inv φ.τ₂ := hS.lift_f _ hz
  let e : S.X₁ ≅ T.X₁ := {
    hom := φ.τ₁
    inv := b
    hom_inv_id := by
      apply (cancel_mono S.f).1
      simp only [Category.assoc, hb]
      rw [← Category.assoc, φ.comm₁₂, Category.assoc, IsIso.hom_inv_id]
      simp
    inv_hom_id := by
      apply (cancel_mono T.f).1
      rw [Category.assoc, φ.comm₁₂, ← Category.assoc, hb, Category.assoc,
        IsIso.inv_hom_id]
      simp
  }
  exact e.isIso_hom

end CategoryTheory.ShortComplex
