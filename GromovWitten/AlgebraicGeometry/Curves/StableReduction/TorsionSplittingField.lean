/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Fixed fields of finite representations

This file isolates the finite Galois-theoretic part of a torsion splitting argument.  Given a
finite Galois extension `L / K` and a representation of its Galois group in a finite group `G`,
the fixed field of the kernel is a finite Galois extension of `K`.  Its degree is the cardinality
of the image, hence is bounded by the cardinality of `G`.

The construction is deliberately made with `IntermediateField.fixedField`; the finiteness,
separability, normality, and degree statements below are consequences of the ambient extension.
The geometric input producing a finite Galois extension and a torsion representation remains to be
constructed elsewhere.
-/

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u v

noncomputable section

open scoped IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

namespace FiniteRepresentation

variable {G : Type*} [Group G]

/-- The subfield of `L` fixed by the kernel of a finite representation of `Gal(L/K)`. -/
noncomputable def fixedField (ρ : Gal(L/K) →* G) : IntermediateField K L :=
  IntermediateField.fixedField ρ.ker

instance fixedField.finiteDimensional (ρ : Gal(L/K) →* G) :
    FiniteDimensional K (fixedField ρ) := by
  exact IntermediateField.finiteDimensional_left (IntermediateField.fixedField ρ.ker)

instance fixedField.isGalois (ρ : Gal(L/K) →* G) : IsGalois K (fixedField ρ) := by
  exact IsGalois.of_fixedField_normal_subgroup ρ.ker

omit [FiniteDimensional K L] in
theorem fixedField.isSeparable (ρ : Gal(L/K) →* G) :
    Algebra.IsSeparable K (fixedField ρ) := by
  exact (IsGalois.of_fixedField_normal_subgroup ρ.ker).to_isSeparable

omit [FiniteDimensional K L] in
theorem fixedField.isNormal (ρ : Gal(L/K) →* G) :
    Normal K (fixedField ρ) := by
  exact (IsGalois.of_fixedField_normal_subgroup ρ.ker).to_normal

theorem fixedField.finrank_eq_card_range (ρ : Gal(L/K) →* G) :
    Module.finrank K (fixedField ρ) = Nat.card ρ.range := by
  rw [show fixedField ρ = IntermediateField.fixedField ρ.ker by rfl]
  rw [IntermediateField.finrank_eq_fixingSubgroup_index L]
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact Subgroup.index_ker ρ

theorem fixedField.finrank_dvd_card (ρ : Gal(L/K) →* G) [Finite G] :
    Module.finrank K (fixedField ρ) ∣ Nat.card G := by
  rw [fixedField.finrank_eq_card_range]
  exact ρ.range.card_subgroup_dvd_card

theorem fixedField.finrank_le_card (ρ : Gal(L/K) →* G) [Finite G] :
    Module.finrank K (fixedField ρ) ≤ Nat.card G := by
  rw [fixedField.finrank_eq_card_range]
  exact Nat.card_le_card_of_injective (fun x : ρ.range => (x : G))
    Subtype.val_injective

omit [FiniteDimensional K L] [IsGalois K L] in
theorem fixedField.mem_iff (ρ : Gal(L/K) →* G) (x : L) :
    x ∈ fixedField ρ ↔ ∀ σ ∈ ρ.ker, σ x = x := by
  simpa only [fixedField] using IntermediateField.mem_fixedField_iff ρ.ker x

/- Every element of the kernel acts trivially on the constructed fixed field. -/
omit [FiniteDimensional K L] [IsGalois K L] in
theorem fixedField.kernel_restriction (ρ : Gal(L/K) →* G)
    {σ : Gal(L/K)} (hσ : σ ∈ ρ.ker) (x : fixedField ρ) :
    σ (x : L) = (x : L) := by
  exact (fixedField.mem_iff ρ (x : L)).mp x.property σ hσ

omit [IsGalois K L] in
/- The kernel is exactly the subgroup of automorphisms whose restriction to the fixed field is
trivial. -/
theorem fixedField.kernel_iff_restriction_trivial (ρ : Gal(L/K) →* G)
    (σ : Gal(L/K)) :
    σ ∈ ρ.ker ↔ ∀ x : fixedField ρ, σ (x : L) = (x : L) := by
  refine ⟨(fun hσ x => fixedField.kernel_restriction ρ hσ x), ?_⟩
  intro hσ
  have hfix : σ ∈ (fixedField ρ).fixingSubgroup := fun x => by
    simpa only [AlgEquiv.smul_def] using hσ x
  rw [show (fixedField ρ).fixingSubgroup = ρ.ker by
    exact IntermediateField.fixingSubgroup_fixedField ρ.ker] at hfix
  exact hfix

/-- Restriction of an automorphism over the fixed field to an automorphism over `K`. -/
noncomputable def fixedField.restrictToBase (ρ : Gal(L/K) →* G) :
    Gal(L/fixedField ρ) →* Gal(L/K) where
  toFun σ := AlgEquiv.restrictScalars K σ
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

omit [IsGalois K L] in
theorem fixedField.restrictToBase_mem_ker (ρ : Gal(L/K) →* G)
    (σ : Gal(L/fixedField ρ)) :
    fixedField.restrictToBase ρ σ ∈ ρ.ker := by
  apply (fixedField.kernel_iff_restriction_trivial ρ _).mpr
  intro x
  change (AlgEquiv.restrictScalars K σ) (x : L) = (x : L)
  rw [AlgEquiv.restrictScalars_apply]
  exact σ.commutes x

omit [IsGalois K L] in
/- The representation is trivial on the Galois group over its fixed field. -/
theorem fixedField.restrictToBase_rho_eq_one (ρ : Gal(L/K) →* G)
    (σ : Gal(L/fixedField ρ)) :
    ρ (fixedField.restrictToBase ρ σ) = 1 := by
  exact MonoidHom.mem_ker.mp (fixedField.restrictToBase_mem_ker ρ σ)

end FiniteRepresentation

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
