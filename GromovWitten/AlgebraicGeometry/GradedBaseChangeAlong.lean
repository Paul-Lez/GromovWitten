/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.ProjBaseChange
/-!
# Comparing scalar conventions in graded base change

A degreewise base-change witness for a scalar tower also gives base change along its explicit
coefficient ring homomorphism. The two formulations use equal algebra structures; quantifying
over the tower proof permits transporting the witness across those equalities.
-/

universe u
namespace GromovWitten.AlgebraicGeometry.ProjBaseChange
variable {A B S T : Type u} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
  [Algebra A B] [Algebra A S] [Algebra B T] [Algebra A T] [IsScalarTower A B T]
  {𝒜 : ℕ → Submodule A S} [GradedAlgebra 𝒜]
  {ℬ : ℕ → Submodule B T} [GradedAlgebra ℬ]
omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- A graded base-change witness is independent of the explicit scalar-tower convention. -/
lemma IsGradedBaseChangeAlong.of_isBaseChange (ψ : GradedHomOver 𝒜 ℬ)
    (h : ψ.IsBaseChange) :
    IsGradedBaseChangeAlong (algebraMap A B) 𝒜 ℬ ψ.toGradedRingHom := by
  let φ : 𝒜 →+*ᵍ ℬ := ψ.toGradedRingHom
  let P (iAB : Algebra A B) (iAT : Algebra A T) : Prop :=
    letI := iAB
    letI := iAT
    ∀ ht : IsScalarTower A B T,
      letI := ht
      ∃ ψ' : GradedHomOver 𝒜 ℬ, ψ'.toGradedRingHom = φ ∧ ψ'.IsBaseChange
  have hP : P inferInstance inferInstance := fun _ => ⟨ψ, rfl, h⟩
  have hAT : ((algebraMap B T).comp (algebraMap A B)).toAlgebra =
      (inferInstance : Algebra A T) :=
    Algebra.algebra_ext _ _ fun a => (IsScalarTower.algebraMap_apply A B T a).symm
  have hP' : P (algebraMap A B).toAlgebra
      ((algebraMap B T).comp (algebraMap A B)).toAlgebra := by
    rw [toAlgebra_algebraMap, hAT]
    exact hP
  exact hP' _
end GromovWitten.AlgebraicGeometry.ProjBaseChange
